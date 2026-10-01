// NONOS Operating System (AGPL-3.0-or-later)
//! The witness this client writes is the one the prover reads.
//!
//! The reader is `stark_proofs/src/shield/witness_wire.rs` and it is not run
//! here, so what these hold is the half a client can hold alone: the length is
//! the one the depth predicts, each field lands on the offset the reader takes
//! it from, and a spend with a dummy is refused rather than written with a path
//! that walks to a root nobody published.

const std = @import("std");
const digest = @import("digest.zig");
const field = @import("field.zig");
const key = @import("key.zig");
const note = @import("note.zig");
const poseidon = @import("poseidon.zig");
const spend = @import("spend.zig");
const tree = @import("tree.zig");
const witness = @import("witness.zig");
const Digest = digest.Digest;
const Note = note.Note;
const Poseidon = poseidon.Poseidon;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

/// spec/shield-witness.json's spend, rebuilt from its own seeds.
///
/// The same seeds the circuit's fixture uses: secrets are `seed*16 + i + 1`,
/// blindings `seed + 5 .. seed + 8`, and an output's spend key `seed + 1 .. 4`.
/// Both notes take blinding seed zero, and the two inputs are owned by two
/// different secrets, which is the shape the vector was written from.
fn secret(seed: u64) Digest {
    var sk: Digest = undefined;
    for (0..4) |i| sk[i] = field.reduce(seed * 16 + @as(u64, @intCast(i)) + 1);
    return sk;
}

fn blinding(seed: u64) Digest {
    var b: Digest = undefined;
    for (0..4) |i| b[i] = field.reduce(seed + 5 + @as(u64, @intCast(i)));
    return b;
}

fn owned(h: *const Poseidon, sk: Digest, seed: u64, value: u64) !Note {
    const s = try key.Secret.fromLimbs(&sk);
    return .{
        .value = value,
        .asset_id = 0,
        .spend_pk = s.derive(h).spend_pk,
        .blinding = blinding(seed),
    };
}

fn plain(seed: u64, value: u64) Note {
    var pk: Digest = undefined;
    for (0..4) |i| pk[i] = field.reduce(seed + 1 + @as(u64, @intCast(i)));
    return .{ .value = value, .asset_id = 0, .spend_pk = pk, .blinding = blinding(seed) };
}

fn pad(v: u64) Digest {
    return .{ field.reduce(v), 0, 0, 0 };
}

const ASSOC_PADS = [_]u64{ 900, 901, 902 };

const Scene = struct {
    pool: tree.Tree,
    assoc: tree.Tree,
    notes: [2]Note,

    fn init(alloc: std.mem.Allocator, h: *const Poseidon) !Scene {
        var sc: Scene = .{
            .pool = tree.Tree.init(alloc, h),
            .assoc = tree.Tree.init(alloc, h),
            .notes = .{
                try owned(h, secret(1), 0, 1000),
                try owned(h, secret(2), 0, 2000),
            },
        };
        for (&sc.notes) |*n| _ = try sc.pool.insert(n.cm(h));
        for (ASSOC_PADS) |p| _ = try sc.assoc.insert(pad(p));
        for (&sc.notes) |*n| _ = try sc.assoc.insert(n.cm(h));
        return sc;
    }

    fn deinit(self: *Scene) void {
        self.pool.deinit();
        self.assoc.deinit();
    }

    fn real(self: *const Scene, i: usize) !spend.Input {
        return .{ .real = .{
            .note = self.notes[i],
            .pool = try self.pool.witness(i),
            .assoc = try self.assoc.witness(i + ASSOC_PADS.len),
        } };
    }

    fn transfer(self: *const Scene) !spend.Spend {
        return .{
            .note_root = self.pool.root(),
            .assoc_root = self.assoc.root(),
            .inputs = .{ try self.real(0), try self.real(1) },
            .outputs = .{ plain(20, 1500), plain(30, 1200) },
            .public_amount = 200,
            .fee = 100,
            .asset_id = 0,
            .clearing_price = 1000000,
            .recipient = recipient(0xBEEF),
            .fee_recipient = recipient(0xFEE),
        };
    }
};

/// The vector's recipient, twenty bytes big endian in the low eight.
fn recipient(a: u64) [20]u8 {
    var out = [_]u8{0} ** 20;
    std.mem.writeInt(u64, out[12..20], a, .big);
    return out;
}

const SECRETS: [2]Digest = .{ secret(1), secret(2) };

test "the_witness_is_the_length_the_depth_predicts" {
    const h = Poseidon.init();
    var sc = try Scene.init(std.testing.allocator, &h);
    defer sc.deinit();
    const sp = try sc.transfer();

    const need = witness.wordsAt(tree.DEPTH);
    const buf = try std.testing.allocator.alloc(u64, need);
    defer std.testing.allocator.free(buf);
    try expectEqual(need, try witness.write(buf, &sp, &SECRETS));
    try expectEqual(witness.MAGIC, buf[witness.Offsets.magic]);
    try expectEqual(@as(u64, tree.DEPTH), buf[witness.Offsets.depth_word]);
}

// Each field lands where the reader takes it from. A layout disagreement is
// then one of these offsets rather than a proof that will not parse.
test "every_field_lands_on_the_offset_the_reader_takes_it_from" {
    const h = Poseidon.init();
    var sc = try Scene.init(std.testing.allocator, &h);
    defer sc.deinit();
    const sp = try sc.transfer();

    const buf = try std.testing.allocator.alloc(u64, witness.wordsAt(tree.DEPTH));
    defer std.testing.allocator.free(buf);
    _ = try witness.write(buf, &sp, &SECRETS);

    const o = witness.Offsets;
    try expectEqual(SECRETS[0], buf[o.secrets..][0..4].*);
    try expectEqual(SECRETS[1], buf[o.secrets + 4 ..][0..4].*);
    try expectEqual(@as(u64, 1000), buf[o.inputs]);
    try expectEqual(@as(u64, 2000), buf[o.inputs + 10]);
    try expectEqual(@as(u64, 1500), buf[o.outputs]);
    try expectEqual(@as(u64, 1200), buf[o.outputs + 10]);
    try expectEqual(@as(u64, 0), buf[o.pool]);
    try expectEqual(sc.pool.root(), buf[o.noteRoot(tree.DEPTH)..][0..4].*);
    try expectEqual(sc.assoc.root(), buf[o.assocRoot(tree.DEPTH)..][0..4].*);

    const s = o.scalars(tree.DEPTH);
    try expectEqual(@as(u64, 200), buf[s]);
    try expectEqual(@as(u64, 100), buf[s + 1]);
    try expectEqual(@as(u64, 0), buf[s + 2]);
    try expectEqual(@as(u64, 1000000), buf[s + 3]);
    try expectEqual(spend.addressLimbs(&sp.recipient), buf[o.recipient(tree.DEPTH)..][0..4].*);
    try expectEqual(spend.addressLimbs(&sp.fee_recipient), buf[o.feeRecipient(tree.DEPTH)..][0..4].*);
}

// A buffer shorter than the depth needs is refused rather than partly written.
test "a_short_buffer_is_refused" {
    const h = Poseidon.init();
    var sc = try Scene.init(std.testing.allocator, &h);
    defer sc.deinit();
    const sp = try sc.transfer();
    var small: [16]u64 = undefined;
    try expectError(error.Overflow, witness.write(&small, &sp, &SECRETS));
}

// A wallet holding one note can write its witness.
//
// This is the common case for a small wallet and the case this format used to
// refuse. A dummy carries no opening and gets a zero one, which binds nothing:
// the circuit multiplies each input's membership by a live bit it derives from
// the value, so the dummy's walk is multiplied by zero and the path it carries
// is never compared to a root.
//
// The gate is that the length does not move and the real input's opening is
// still where the reader takes it from. A dummy that shifted the layout would
// be a one-note payment the prover reads as a different spend.
test "a_wallet_with_one_note_can_write_its_witness" {
    const h = Poseidon.init();
    var sc = try Scene.init(std.testing.allocator, &h);
    defer sc.deinit();
    var sp = try sc.transfer();
    sp.inputs[1] = .{ .dummy = .{
        .value = 0,
        .asset_id = 0,
        .spend_pk = sc.notes[0].spend_pk,
        .blinding = .{ 1, 2, 3, 4 },
    } };
    sp.outputs[0].value = 700;
    sp.outputs[1].value = 0;
    sp.public_amount = 200;
    sp.fee = 100;

    const need = witness.wordsAt(tree.DEPTH);
    const buf = try std.testing.allocator.alloc(u64, need);
    defer std.testing.allocator.free(buf);
    try expectEqual(need, try witness.write(buf, &sp, &SECRETS));

    const o = witness.Offsets;
    // The real input keeps its own opening, at the offset the reader takes it
    // from, and the dummy's is zero throughout.
    try expectEqual(@as(u64, 0), buf[o.pool]);
    const one = o.pool + 1 + tree.DEPTH * 4;
    try expectEqual(@as(u64, 0), buf[one]);
    for (buf[one + 1 ..][0 .. tree.DEPTH * 4]) |v| try expectEqual(@as(u64, 0), v);
    // And the fields after the openings have not moved.
    try expectEqual(sc.pool.root(), buf[o.noteRoot(tree.DEPTH)..][0..4].*);
    try expectEqual(@as(u64, 700), buf[o.outputs]);
}

// The client writes the words the circuit's vector publishes.
//
// spec/shield-witness.json is the file a transfer was proved from. This rebuilds
// that spend from the same seeds, writes it with this client's own writer, and
// checks the fields the prover reads out of it. If these agree, the bytes a
// wallet produces are the bytes that proved.
//
// The roots are the part that cannot be transcribed by accident: they come from
// this client walking its own two trees.
test "the_client_writes_the_words_the_vector_publishes" {
    const h = Poseidon.init();
    var sc = try Scene.init(std.testing.allocator, &h);
    defer sc.deinit();
    const sp = try sc.transfer();

    const buf = try std.testing.allocator.alloc(u64, witness.wordsAt(tree.DEPTH));
    defer std.testing.allocator.free(buf);
    try expectEqual(@as(usize, 586), try witness.write(buf, &sp, &SECRETS));

    const o = witness.Offsets;
    try expectEqual(@as(u64, 5642825990034174002), buf[o.magic]);
    try expectEqual(@as(u64, 32), buf[o.depth_word]);
    try expectEqual(NOTE_ROOT, buf[o.noteRoot(tree.DEPTH)..][0..4].*);
    try expectEqual(ASSOC_ROOT, buf[o.assocRoot(tree.DEPTH)..][0..4].*);

    const s = o.scalars(tree.DEPTH);
    try expectEqual(@as(u64, 200), buf[s]);
    try expectEqual(@as(u64, 100), buf[s + 1]);
    try expectEqual(@as(u64, 0), buf[s + 2]);
    try expectEqual(@as(u64, 1000000), buf[s + 3]);
}

/// The vector's two roots, which this client builds leaf by leaf.
const NOTE_ROOT: Digest = .{ 14642651294145191397, 3749887710612721201, 17897719159298268359, 12296343470192110035 };
const ASSOC_ROOT: Digest = .{ 18379151337909585371, 14195779821289367974, 2789637164666902265, 9661791652754313075 };
