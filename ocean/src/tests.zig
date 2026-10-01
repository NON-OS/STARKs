// NONOS Operating System (AGPL-3.0-or-later)

test {
    _ = @import("field_test.zig");
    _ = @import("poseidon_test.zig");
    _ = @import("digest_test.zig");
    _ = @import("key_test.zig");
    _ = @import("tree_test.zig");
    _ = @import("imt/leaf_test.zig");
    _ = @import("imt/order_test.zig");
    _ = @import("imt/set_test.zig");
    _ = @import("imt/batch_test.zig");
    _ = @import("absorb/call_test.zig");
    _ = @import("codec/header_test.zig");
    _ = @import("spend_test.zig");
    _ = @import("intent_test.zig");
    _ = @import("witness_test.zig");
    _ = @import("memo_test.zig");
    _ = @import("wallet_test.zig");
    _ = @import("anon/anon_test.zig");
    _ = @import("wallet_vectors_test.zig");
    _ = @import("activity_test.zig");
}
