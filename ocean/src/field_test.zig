// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const field = @import("field.zig");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

fn slow(a: u64, b: u64) u64 {
    return @intCast((@as(u128, a) * b) % field.P);
}

test "reduce_maps_p_to_zero_and_the_top_word_to_epsilon_minus_one" {
    try expectEqual(0, field.reduce(field.P));
    try expectEqual(field.P - 1, field.reduce(field.P - 1));
    try expectEqual(field.EPSILON - 1, field.reduce(std.math.maxInt(u64)));
}

test "canonical_refuses_p_and_above" {
    try expectEqual(field.P - 1, try field.canonical(field.P - 1));
    try expectError(error.NonCanonical, field.canonical(field.P));
    try expectError(error.NonCanonical, field.canonical(std.math.maxInt(u64)));
}

test "mul_agrees_with_u128_modulo_on_edges_and_random_inputs" {
    const edges = [_]u64{ 0, 1, 2, field.EPSILON, field.EPSILON + 1, field.P - 1, field.P - 2, 1 << 32, 1 << 63, (1 << 63) + 1 };
    for (edges) |a| {
        for (edges) |b| try expectEqual(slow(a, b), field.mul(a, b));
    }
    var prng = std.Random.DefaultPrng.init(1);
    const rng = prng.random();
    for (0..4096) |_| {
        const a = field.random(rng);
        const b = field.random(rng);
        try expectEqual(slow(a, b), field.mul(a, b));
    }
}

test "add_and_sub_invert_each_other_across_the_wrap" {
    const a = field.P - 1;
    const s = field.add(a, 5);
    try expectEqual(4, s);
    try expectEqual(a, field.sub(s, 5));
    try expectEqual(field.P - 5, field.sub(0, 5));
    try expectEqual(0, field.add(a, field.neg(a)));
}

test "inv_times_a_is_one_and_zero_has_no_inverse" {
    var prng = std.Random.DefaultPrng.init(2);
    const rng = prng.random();
    for (0..64) |_| {
        const a = field.random(rng);
        if (a == 0) continue;
        try expectEqual(field.ONE, field.mul(a, try field.inv(a)));
    }
    try expectError(error.ZeroInverse, field.inv(0));
}

test "sbox7_is_the_seventh_power" {
    var prng = std.Random.DefaultPrng.init(3);
    const rng = prng.random();
    for (0..64) |_| {
        const a = field.random(rng);
        try expectEqual(field.pow(a, 7), field.sbox7(a));
    }
}

test "random_elements_are_canonical" {
    var prng = std.Random.DefaultPrng.init(4);
    const rng = prng.random();
    for (0..4096) |_| try expect(field.random(rng) < field.P);
}

test "wipe_zeroes_every_word" {
    var s = [_]u64{ 1, 2, 3, 4 };
    field.wipe(u64, &s);
    try expectEqual([4]u64{ 0, 0, 0, 0 }, s);
    var b = [_]u8{ 9, 9, 9 };
    field.wipe(u8, &b);
    try expectEqual([3]u8{ 0, 0, 0 }, b);
}
