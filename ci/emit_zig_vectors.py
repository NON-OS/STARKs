#!/usr/bin/env python3
# NONOS Operating System (AGPL-3.0-or-later)
"""Write the Zig test that checks the client against the pinned wallet vectors.

    python3 ci/emit_zig_vectors.py --vectors spec/wallet-vectors spec/wallet-vectors-not-before \
        --out ocean/src/wallet_vectors_test.zig

<dir> holds one directory per vector (emit_wallet_vectors): request.json,
seed.json and proof.json. The test rebuilds each spend in Zig from the seed
notes and the created notes, with the client's own trees, keys, nullifiers,
commitments and address limbs, and requires the public words the Rust prover
put in the proof: 36, or 37 with `not_before`. The numbers are copied verbatim; nothing is
recomputed here.
"""

import argparse
import json
import os
import sys


def addr(hexstr):
    h = hexstr[2:] if hexstr.startswith("0x") else hexstr
    if len(h) != 40:
        sys.exit(f"not a 20-byte address: {hexstr}")
    return "[20]u8{ " + ", ".join(f"0x{h[i:i + 2]}" for i in range(0, 40, 2)) + " }"


def digest(v):
    if len(v) != 4:
        sys.exit(f"not four limbs: {v}")
    return "digest.Digest{ " + ", ".join(str(x) for x in v) + " }"


def note(n):
    return (f"note.Note{{ .value = {n['value']}, .asset_id = {n['asset_id']}, "
            f".spend_pk = {digest(n['spend_pk'])}, .blinding = {digest(n['blinding'])} }}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--vectors", required=True, nargs="+")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()

    cases = []
    dirs = [(root, name) for root in a.vectors for name in sorted(os.listdir(root))]
    for root, name in dirs:
        d = os.path.join(root, name)
        if not os.path.isdir(d):
            continue
        req = json.load(open(os.path.join(d, "request.json")))
        seed = json.load(open(os.path.join(d, "seed.json")))
        proof = json.load(open(os.path.join(d, "proof.json")))
        if seed["secrets"][0] != seed["secrets"][1]:
            sys.exit(f"{name}: the client models one wallet; the two inputs need one secret")
        not_before = req.get("not_before", 0)
        want = 37 if not_before else 36
        if len(proof["publics"]) != want:
            sys.exit(f"{name}: {len(proof['publics'])} public words, not {want}")
        outs = proof["outputs"]
        cases.append(f"""    .{{
        .name = "{os.path.basename(root)}/{name}",
        .sk = .{{ {", ".join(str(x) for x in seed["secrets"][0])} }},
        .inputs = .{{ {note(seed["notes"][0])}, {note(seed["notes"][1])} }},
        .outputs = .{{ {note(outs[0])}, {note(outs[1])} }},
        .public_amount = {req["public_amount"]},
        .fee = {req["fee"]},
        .asset_id = {seed["notes"][0]["asset_id"]},
        .clearing_price = {req["clearing_price"]},
        .recipient = {addr(req["recipient"])},
        .fee_recipient = {addr(req.get("fee_recipient", "0x" + "00" * 20))},
        .not_before = {not_before},
        .publics = &.{{ {", ".join(str(x) for x in proof["publics"])} }},
    }},""")
    if not cases:
        sys.exit("no vectors found")

    body = f"""// NONOS Operating System (AGPL-3.0-or-later)
//! The client against the pinned wallet vectors. Written by
//! ci/emit_zig_vectors.py from the vectors emit_wallet_vectors made; edit
//! those, not this.
//!
//! Each spend is rebuilt here from its seed notes and the notes the prover
//! created, with this client's trees, keys, nullifiers, commitments and
//! address limbs, and must land on the words the Rust prover proved: 36, or 37
//! with `not_before`.

const std = @import("std");
const digest = @import("digest.zig");
const note = @import("note.zig");
const key = @import("key.zig");
const poseidon = @import("poseidon.zig");
const spend = @import("spend.zig");
const tree = @import("tree.zig");

const Case = struct {{
    name: []const u8,
    sk: [4]u64,
    inputs: [2]note.Note,
    outputs: [2]note.Note,
    public_amount: u64,
    fee: u64,
    asset_id: u64,
    clearing_price: u64,
    recipient: [20]u8,
    fee_recipient: [20]u8,
    not_before: u64,
    publics: []const u64,
}};

const CASES = [_]Case{{
{chr(10).join(cases)}
}};

test "the_client_reproduces_the_pinned_wallet_vectors" {{
    const h = poseidon.Poseidon.init();
    for (CASES) |c| {{
        const secret = try key.Secret.fromLimbs(&c.sk);
        const keys = secret.derive(&h);
        var t = tree.Tree.init(std.testing.allocator, &h);
        defer t.deinit();
        for (c.inputs) |n| _ = try t.insert(n.cm(&h));
        const sp = spend.Spend{{
            .note_root = t.root(),
            .assoc_root = t.root(),
            .inputs = .{{
                .{{ .real = .{{ .note = c.inputs[0], .pool = try t.witness(0), .assoc = try t.witness(0) }} }},
                .{{ .real = .{{ .note = c.inputs[1], .pool = try t.witness(1), .assoc = try t.witness(1) }} }},
            }},
            .outputs = c.outputs,
            .public_amount = c.public_amount,
            .fee = c.fee,
            .asset_id = c.asset_id,
            .clearing_price = c.clearing_price,
            .recipient = c.recipient,
            .fee_recipient = c.fee_recipient,
        }};
        if (c.not_before == 0) {{
            const words = try sp.intent(&h, &keys.nk);
            std.testing.expectEqualSlices(u64, c.publics, &words) catch |e| {{
                std.debug.print("vector {{s}} disagrees\\n", .{{c.name}});
                return e;
            }};
            continue;
        }}
        const words = try spend.intentNotBefore(&sp, &h, &keys.nk, c.not_before);
        std.testing.expectEqualSlices(u64, c.publics, &words) catch |e| {{
            std.debug.print("vector {{s}} disagrees\\n", .{{c.name}});
            return e;
        }};
    }}
}}
"""
    open(a.out, "w").write(body)
    print(f"wrote {a.out}: {len(cases)} vectors")


if __name__ == "__main__":
    main()
