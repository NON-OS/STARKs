// NONOS Operating System (AGPL-3.0-or-later)
//! Client data version 0x01: a note's opening sealed to its payee under X-Wing
//! (ML-KEM-768 + X25519), byte for byte the format `note_seal` writes.
//! See docs/14-client.md.

const std = @import("std");
const field = @import("field.zig");
const digest = @import("digest.zig");
const key = @import("key.zig");
const note = @import("note.zig");
const Digest = digest.Digest;
const Note = note.Note;
const MlKem = @import("vendor/ml_kem_fips.zig").nist.MLKem768;
const X25519 = std.crypto.dh.X25519;
const Sha3 = std.crypto.hash.sha3.Sha3_256;
const Shake = std.crypto.hash.sha3.Shake256;
const Aead = std.crypto.aead.chacha_poly.ChaCha20Poly1305;
const Blake3 = std.crypto.hash.Blake3;

pub const VERSION: u8 = 0x01;

const SEED_DOMAIN = "NOX-NOTE-XWING-SEED-v1";
const TAG_DOMAIN = "NOX-NOTE-VIEW-TAG-v1";
const KEY_DOMAIN = "NOX-NOTE-SEAL-KEY-v1";
/// The X-Wing combiner's label, `\.//^\`.
const XWING_LABEL = [_]u8{ 0x5c, 0x2e, 0x2f, 0x2f, 0x5e, 0x5c };

const PK_M = MlKem.PublicKey.bytes_length;
const CT_M = MlKem.ciphertext_length;
/// The encapsulation key: ML-KEM-768's 1,184 bytes, then X25519's 32.
pub const EK_BYTES = PK_M + 32;
/// The X-Wing ciphertext: ML-KEM-768's 1,088 bytes, then X25519's 32.
pub const CT_BYTES = CT_M + 32;
/// value 8 | asset_id 8 | blinding 4 x 8, little endian.
pub const OPENING_BYTES = 48;
/// version 1 | view tag 1 | ciphertext 1,120 | sealed opening 48 | tag 16.
pub const LEN = 2 + CT_BYTES + OPENING_BYTES + Aead.tag_length;
pub const Memo = [LEN]u8;

pub const Error = error{ NotForUs, MalformedAddress } || field.Error;

/// version 1 | spend_pk as four little-endian words 32 | encapsulation key 1,216.
pub const Address = struct {
    spend_pk: Digest,
    ek: [EK_BYTES]u8,

    pub const BYTES = 1 + 32 + EK_BYTES;

    pub fn bytes(self: *const Address) [BYTES]u8 {
        var out: [BYTES]u8 = undefined;
        out[0] = VERSION;
        for (0..4) |i| std.mem.writeInt(u64, out[1 + 8 * i ..][0..8], self.spend_pk[i], .little);
        out[33..].* = self.ek;
        return out;
    }

    pub fn fromBytes(b: *const [BYTES]u8) Error!Address {
        if (b[0] != VERSION) return error.MalformedAddress;
        _ = MlKem.PublicKey.fromBytes(b[33..][0..PK_M]) catch return error.MalformedAddress;
        var pk: Digest = undefined;
        for (0..4) |i| pk[i] = try field.canonical(std.mem.readInt(u64, b[1 + 8 * i ..][0..8], .little));
        return .{ .spend_pk = pk, .ek = b[33..].* };
    }
};

/// A payee's receiving key, expanded from its 32-byte X-Wing seed.
pub const ViewKey = struct {
    pair: MlKem.KeyPair,
    sk_x: [32]u8,
    ek: [EK_BYTES]u8,

    /// X-Wing key generation: SHAKE256(seed) gives 96 bytes, the ML-KEM-768
    /// seed `d || z` and the X25519 secret.
    pub fn fromSeed(seed: *const [32]u8) Error!ViewKey {
        var expanded: [96]u8 = undefined;
        defer field.wipe(u8, &expanded);
        Shake.hash(seed, &expanded, .{});
        const pair = MlKem.KeyPair.generateDeterministic(expanded[0..64].*) catch return error.MalformedAddress;
        const sk_x = expanded[64..96].*;
        const pk_x = X25519.recoverPublicKey(sk_x) catch return error.MalformedAddress;
        var ek: [EK_BYTES]u8 = undefined;
        ek[0..PK_M].* = pair.public_key.toBytes();
        ek[PK_M..].* = pk_x;
        return .{ .pair = pair, .sk_x = sk_x, .ek = ek };
    }

    /// The seed is the BLAKE3 of the domain and the wallet secret, so a
    /// wallet restores its view key from its seed alone.
    pub fn fromSecret(secret: *const key.Secret) Error!ViewKey {
        var sk_bytes = secret.bytes();
        defer field.wipe(u8, &sk_bytes);
        var seed: [32]u8 = undefined;
        defer field.wipe(u8, &seed);
        var h = Blake3.init(.{});
        h.update(SEED_DOMAIN);
        h.update(&sk_bytes);
        h.final(&seed);
        return fromSeed(&seed);
    }

    pub fn address(self: *const ViewKey, spend_pk: Digest) Address {
        return .{ .spend_pk = spend_pk, .ek = self.ek };
    }

    pub fn wipe(self: *ViewKey) void {
        field.wipe(u8, std.mem.asBytes(&self.pair.secret_key));
        field.wipe(u8, &self.sk_x);
    }
};

/// What a payee needs to spend a note besides its own key.
pub const Opening = struct {
    value: u64,
    asset_id: u64,
    blinding: Digest,

    pub fn bytes(self: *const Opening) [OPENING_BYTES]u8 {
        var b: [OPENING_BYTES]u8 = undefined;
        std.mem.writeInt(u64, b[0..8], self.value, .little);
        std.mem.writeInt(u64, b[8..16], self.asset_id, .little);
        for (0..4) |i| std.mem.writeInt(u64, b[16 + 8 * i ..][0..8], self.blinding[i], .little);
        return b;
    }

    /// A blinding word at or above p is refused, so one note has one encoding.
    pub fn fromBytes(b: *const [OPENING_BYTES]u8) field.Error!Opening {
        var bl: Digest = undefined;
        for (0..4) |i| bl[i] = try field.canonical(std.mem.readInt(u64, b[16 + 8 * i ..][0..8], .little));
        return .{
            .value = std.mem.readInt(u64, b[0..8], .little),
            .asset_id = std.mem.readInt(u64, b[8..16], .little),
            .blinding = bl,
        };
    }
};

/// SHA3-256(ss_M || ss_X || ct_X || pk_X || label), the X-Wing combiner.
fn combine(ss_m: *const [32]u8, ss_x: *const [32]u8, ct_x: *const [32]u8, pk_x: *const [32]u8) [32]u8 {
    var h = Sha3.init(.{});
    h.update(ss_m);
    h.update(ss_x);
    h.update(ct_x);
    h.update(pk_x);
    h.update(&XWING_LABEL);
    var ss: [32]u8 = undefined;
    h.final(&ss);
    return ss;
}

fn derive(domain: []const u8, ss: *const [32]u8) [32]u8 {
    var h = Sha3.init(.{});
    h.update(domain);
    h.update(ss);
    var out: [32]u8 = undefined;
    h.final(&out);
    return out;
}

fn aad(tag: u8, leaf: *const [32]u8) [34]u8 {
    var a: [34]u8 = undefined;
    a[0] = VERSION;
    a[1] = tag;
    a[2..].* = leaf.*;
    return a;
}

const NONCE = [_]u8{0} ** Aead.nonce_length;

/// Seal `o` to `ek` for the output whose leaf commitment is `leaf`, with the 64
/// bytes of encapsulation randomness given: ML-KEM's message, then X25519's
/// ephemeral secret.
pub fn sealWith(ek: *const [EK_BYTES]u8, o: *const Opening, leaf: *const [32]u8, eseed: *const [64]u8) Error!Memo {
    const pk_m = MlKem.PublicKey.fromBytes(ek[0..PK_M]) catch return error.MalformedAddress;
    const pk_x = ek[PK_M..][0..32];
    const ct_x = X25519.recoverPublicKey(eseed[32..64].*) catch return error.MalformedAddress;
    var ss_x = X25519.scalarmult(eseed[32..64].*, pk_x.*) catch return error.MalformedAddress;
    defer field.wipe(u8, &ss_x);
    var enc = pk_m.encaps(eseed[0..32].*);
    defer field.wipe(u8, &enc.shared_secret);
    var ss = combine(&enc.shared_secret, &ss_x, &ct_x, pk_x);
    defer field.wipe(u8, &ss);

    const tag = derive(TAG_DOMAIN, &ss)[0];
    var k = derive(KEY_DOMAIN, &ss);
    defer field.wipe(u8, &k);
    var plain = o.bytes();
    defer field.wipe(u8, &plain);
    var m: Memo = undefined;
    m[0] = VERSION;
    m[1] = tag;
    m[2..][0..CT_M].* = enc.ciphertext;
    m[2 + CT_M ..][0..32].* = ct_x;
    const body = 2 + CT_BYTES;
    Aead.encrypt(m[body..][0..OPENING_BYTES], m[body + OPENING_BYTES ..][0..Aead.tag_length], &plain, &aad(tag, leaf), NONCE, k);
    return m;
}

/// Seal note `n`, whose commitment is `cm`, to `to` with fresh randomness.
pub fn seal(rng: std.Random, to: *const Address, n: *const Note, cm: *const Digest) Error!Memo {
    var eseed: [64]u8 = undefined;
    rng.bytes(&eseed);
    defer field.wipe(u8, &eseed);
    const o = Opening{ .value = n.value, .asset_id = n.asset_id, .blinding = n.blinding };
    return sealWith(&to.ek, &o, &digest.toBytes(cm), &eseed);
}

/// The opening in `m` if it is a version 0x01 note for `view` bound to `leaf`.
/// Every failure is NotForUs: a memo is opened by trial, and a failing trial
/// says nothing about who it was for. ML-KEM returns an implicit secret on a
/// bent ciphertext, so the view tag or the AEAD tag is what rejects it.
pub fn openOpening(view: *const ViewKey, m: *const Memo, leaf: *const [32]u8) Error!Opening {
    if (m[0] != VERSION) return error.NotForUs;
    var ss_m = view.pair.secret_key.decaps(m[2..][0..CT_M]) catch return error.NotForUs;
    defer field.wipe(u8, &ss_m);
    const ct_x = m[2 + CT_M ..][0..32];
    var ss_x = X25519.scalarmult(view.sk_x, ct_x.*) catch return error.NotForUs;
    defer field.wipe(u8, &ss_x);
    var ss = combine(&ss_m, &ss_x, ct_x, view.ek[PK_M..][0..32]);
    defer field.wipe(u8, &ss);

    const tag = derive(TAG_DOMAIN, &ss)[0];
    if (m[1] != tag) return error.NotForUs;
    var k = derive(KEY_DOMAIN, &ss);
    defer field.wipe(u8, &k);
    var plain: [OPENING_BYTES]u8 = undefined;
    defer field.wipe(u8, &plain);
    const body = 2 + CT_BYTES;
    Aead.decrypt(&plain, m[body..][0..OPENING_BYTES], m[body + OPENING_BYTES ..][0..Aead.tag_length].*, &aad(tag, leaf), NONCE, k) catch return error.NotForUs;
    return Opening.fromBytes(&plain) catch error.NotForUs;
}

/// The note in `m` for `view`, owned by `owner`: the opening carries no key,
/// so the payee supplies its own spend key and the caller checks that the note
/// commits to the leaf.
pub fn open(view: *const ViewKey, m: *const Memo, cm: *const Digest, owner: Digest) Error!Note {
    const o = try openOpening(view, m, &digest.toBytes(cm));
    return .{ .value = o.value, .asset_id = o.asset_id, .spend_pk = owner, .blinding = o.blinding };
}
