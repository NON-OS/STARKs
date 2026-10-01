// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const field = @import("field.zig");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const key = @import("key.zig");
const note = @import("note.zig");
const Poseidon = poseidon.Poseidon;
const Note = note.Note;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

/// spec/shield-key-hierarchy.json, every case, every field.
const Case = struct {
    sk: [4]u64,
    spend_pk: [4]u64,
    nk: [4]u64,
    value: u64,
    blinding: [4]u64,
    owner: [4]u64,
    cm: [4]u64,
    leaf_index: u64,
    nf: [4]u64,
    /// The same note retired as a dummy. The pool burns both nullifiers of an
    /// intent and cannot see which input was real, so the two words differ.
    nf_dead: [4]u64,
};

const CASES = [_]Case{
    .{
        .sk = .{ 17, 18, 19, 20 },
        .spend_pk = .{ 4694351271964731477, 13108437350425652204, 5798317474614717104, 1920752407353108018 },
        .nk = .{ 15814050617089658304, 14074457603087699110, 7066257536958022981, 409298277147620234 },
        .value = 1000,
        .blinding = .{ 6, 7, 8, 9 },
        .owner = .{ 7086614788471361598, 8408166648078634149, 3807849277495844233, 10724578368436512877 },
        .cm = .{ 14283787337774760342, 14262542622847402319, 8832486248617731798, 2886913695765355959 },
        .leaf_index = 0,
        .nf = .{ 18127595421004252247, 15638740712573195931, 1988593558659992483, 8784545353334866955 },
        .nf_dead = .{ 6591784810785565194, 1001680803551979266, 6257210831936886853, 10941386090625757917 },
    },
    .{
        .sk = .{ 33, 34, 35, 36 },
        .spend_pk = .{ 628882199730616774, 18142586265531521073, 17375397127191741149, 12477445664067751145 },
        .nk = .{ 15675217044256070859, 16798109433239495445, 2249341761480692431, 14255279437495361173 },
        .value = 5000000,
        .blinding = .{ 7, 8, 9, 10 },
        .owner = .{ 8122974718690795284, 551948206427378373, 9619622840581871864, 11876928875042502847 },
        .cm = .{ 15697667491804642895, 17679214572932052289, 8350575414177513736, 6644586293454566641 },
        .leaf_index = 7,
        .nf = .{ 7860319393429466910, 14362320200900675334, 16136895672508284464, 14559735438747214735 },
        .nf_dead = .{ 18300814875946068775, 7953861498957587760, 2246915918073995004, 16174778028311639464 },
    },
    .{
        .sk = .{ 49, 50, 51, 52 },
        .spend_pk = .{ 16591103671410030242, 1589515733628357315, 12621351688733757311, 1072175519502322740 },
        .nk = .{ 18375594795749578908, 14539507745738116517, 4821571194616792316, 4934120422233671945 },
        .value = 4294967295,
        .blinding = .{ 8, 9, 10, 11 },
        .owner = .{ 10228867929420546044, 10268274735543138890, 2272460967760641368, 12575433155610528961 },
        .cm = .{ 8273888769543054764, 17921011876742310177, 13488087496070835509, 13841458787604530257 },
        .leaf_index = 31,
        .nf = .{ 10964050946363414603, 16643771908598597199, 12580629618225389775, 5738526930805311453 },
        .nf_dead = .{ 12522470471829787320, 13022621159257272193, 13262254744502768473, 9374527191864731823 },
    },
};

test "the_published_key_hierarchy_vector_derives" {
    const h = Poseidon.init();
    for (CASES) |c| {
        const s = try key.Secret.fromLimbs(&c.sk);
        const k = s.derive(&h);
        try expectEqual(c.spend_pk, k.spend_pk);
        try expectEqual(c.nk, k.nk);
        const n: Note = .{ .value = c.value, .asset_id = 0, .spend_pk = k.spend_pk, .blinding = c.blinding };
        try expectEqual(c.owner, n.owner(&h));
        const cm = n.cm(&h);
        try expectEqual(c.cm, cm);
        try expectEqual(c.nf, key.nullifier(&h, &k.nk, &cm, c.leaf_index, true));
        try expectEqual(c.nf_dead, key.nullifier(&h, &k.nk, &cm, c.leaf_index, false));
    }
}

/// Leaf 1 of pool 0xa760D749adfe15BafFfeC8E7301CEA89B150c046 on Sepolia. The
/// key hierarchy is checked against it; the commitment is not, because that
/// pool's leaves were committed before the public and secret halves were cut
/// onto separate quads, and its leaf is a digest this hash does not produce.
const A_SK = "9c4b73105bd8c464250d949588b61807aee31121ea9d916ff6bf6105dab3ff7e";
const A_SPEND = "34fa40101c68ad0be214e8f04c7213b9be559c9db4c40b8ab99e0875c28df6b4";
const A_NK = "476caa1bc9f1a6a13ee910f1d823aed193dec6105a19aae8c8599b7fe7c2acbe";
const A_BLINDING = "feb675b9c81199eac575cd15116a9215f5289e96d9706e1afffa4e4fcd9affe1";
const A_VALUE: u64 = 1_995_000_000_000_000;

test "the_live_sepolia_note_derives_its_keys_from_its_secret" {
    const h = Poseidon.init();
    const sk = try digest.fromHex(A_SK);
    const s = try key.Secret.fromLimbs(&sk);
    const k = s.derive(&h);
    try expectEqual(try digest.fromHex(A_SPEND), k.spend_pk);
    try expectEqual(try digest.fromHex(A_NK), k.nk);
    try expectEqual([4]u64{ 13375137245205231284, 13715040441383259018, 16290901870878266297, 3817434072090193163 }, k.spend_pk);
    // The note is still a note; only the digest its commitment lands on moved.
    const n: Note = .{ .value = A_VALUE, .asset_id = 0, .spend_pk = k.spend_pk, .blinding = try digest.fromHex(A_BLINDING) };
    try expectEqual(h.commitOwner(&k.spend_pk, &n.blinding), n.owner(&h));
}

test "a_secret_from_a_seed_is_canonical_and_deterministic" {
    const seed = [_]u8{7} ** 32;
    const s1 = key.Secret.fromSeed(&seed);
    const s2 = key.Secret.fromSeed(&seed);
    try expectEqual(s1.sk, s2.sk);
    for (s1.sk) |l| try expect(l < field.P);
    const other = [_]u8{8} ** 32;
    try expect(!digest.eql(&s1.sk, &key.Secret.fromSeed(&other).sk));
}

test "spend_pk_and_nk_do_not_reveal_each_other_or_the_secret" {
    const h = Poseidon.init();
    const s = try key.Secret.fromLimbs(&.{ 17, 18, 19, 20 });
    const k = s.derive(&h);
    try expect(!digest.eql(&k.spend_pk, &k.nk));
    try expect(!digest.eql(&k.spend_pk, &s.sk));
    try expect(!digest.eql(&k.nk, &s.sk));
}

test "the_nullifier_moves_with_the_leaf_index" {
    const h = Poseidon.init();
    const s = try key.Secret.fromLimbs(&.{ 17, 18, 19, 20 });
    const k = s.derive(&h);
    const cm = digest.tag(5);
    try expect(!digest.eql(&key.nullifier(&h, &k.nk, &cm, 0, true), &key.nullifier(&h, &k.nk, &cm, 1, true)));
}

test "wipe_clears_the_secret" {
    var s = try key.Secret.fromLimbs(&.{ 17, 18, 19, 20 });
    s.wipe();
    try expectEqual(digest.ZERO, s.sk);
}
