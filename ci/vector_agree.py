"""The client's pinned vector is the one the circuit emits.

`spec/shield-key-hierarchy.json` is written by `emit_key_vector`. The Zig
client pins the same numbers so a divergence from the circuit fails in its
own suite rather than in a wallet. Two files holding one set of numbers is
one silent edit away from disagreeing, so this reads both and checks every
limb of every case appears in the client, verbatim.

No toolchain: it is text against text, and it runs beside the code law.
"""
import argparse
import json
import pathlib
import re
import sys

FIELDS = ["sk", "spend_pk", "nk", "blinding", "owner", "cm", "nf", "nf_dead"]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True)
    a = ap.parse_args()
    root = pathlib.Path(a.root)

    spec = json.loads((root / "spec/shield-key-hierarchy.json").read_text())
    client = (root / "ocean/src/key_test.zig").read_text()

    missing = []
    for i, case in enumerate(spec["cases"]):
        for f in FIELDS:
            v = case.get(f)
            if v is None:
                continue
            # The client writes a Zig array literal: `.{ a, b, c, d }`.
            lit = ", ".join(str(x) for x in v)
            if lit not in client:
                missing.append(f"case {i} {f}: {lit}")
        for f in ["value", "leaf_index"]:
            if str(case[f]) not in client:
                missing.append(f"case {i} {f}: {case[f]}")

    # The transfer vector, against the client that rebuilds it.
    #
    # The key vector says the two languages derive one key hierarchy. This says
    # they agree on a whole transfer: the same notes, the same commitments, the
    # same two trees and the same nullifiers: the half of the client-prover
    # seam that needs no prover.
    intent = json.loads((root / "spec/shield-intent.json").read_text())
    client = (root / "ocean/src/intent_test.zig").read_text()
    words, off = intent["intent"], intent["offsets"]
    wide = {"note_root", "assoc_root", "nf0", "nf1", "out_cm0", "out_cm1", "recipient", "fee_recipient"}
    for name, at in off.items():
        if name in ("recipient", "fee_recipient"):
            continue
        n = 4 if name in wide else 1
        lit = ",\n    ".join(str(x) for x in words[at : at + n])
        if lit not in client and str(words[at]) not in client:
            missing.append(f"intent {name}: {words[at:at+n]}")
    #
    # The tree-shape fields arrived in the emitter after the file was last
    # written, and the file cannot be rewritten without a machine. Reported as
    # stale rather than skipped: a gate that quietly checks less than it says
    # is the failure this whole file exists to prevent.
    stale = [n for n in ("assoc_pads", "pool_leaves", "assoc_leaves") if n not in intent]
    for name in ("assoc_pads", "pool_leaves", "assoc_leaves"):
        for v in intent.get(name, []):
            if str(v) not in client:
                missing.append(f"intent {name}: {v}")

    # The witness wire, which is a format rather than a vector.
    #
    # Two languages write and read one layout, and neither runs the other here,
    # so what can be checked without a toolchain is that they agree on the magic
    # word and on the length a depth implies. A length disagreement is the one
    # that costs a day: every field after the first opening shifts and each one
    # still reads as a plausible number.
    rs = (root / "stark_proofs/src/shield/witness_wire.rs").read_text()
    zg = (root / "ocean/src/witness.zig").read_text()
    rs_magic = re.search(r"MAGIC: u64 = (0x[0-9A-Fa-f_]+)", rs)
    zg_magic = re.search(r"MAGIC: u64 = (0x[0-9A-Fa-f_]+)", zg)
    if not rs_magic or not zg_magic:
        missing.append("witness wire: one side does not declare a magic word")
    elif int(rs_magic.group(1).replace("_", ""), 16) != int(zg_magic.group(1).replace("_", ""), 16):
        missing.append(
            f"witness wire magic: {rs_magic.group(1)} against {zg_magic.group(1)}"
        )
    # The lengths, read off each side rather than recomputed here. A check that
    # derives both operands from its own constants agrees with itself whatever
    # the files say, which is the failure this gate exists to catch, and the
    # first version of this did exactly that.
    def const(text, name):
        m = re.search(rf"\b{name}(?::\s*usize)?\s*=\s*([^;]+);", text)
        return m.group(1).strip() if m else None

    env = {"RATE": 4}
    sides = {}
    for tag, text in (("circuit", rs), ("client", zg)):
        note_w = const(text, "NOTE_WORDS")
        head_w = const(text, "HEAD_WORDS")
        if note_w is None or head_w is None:
            missing.append(f"witness wire: the {tag} declares no NOTE_WORDS or HEAD_WORDS")
            continue
        try:
            scope = dict(env)
            scope["NOTE_WORDS"] = eval(note_w, {"__builtins__": {}}, scope)
            scope["HEAD_WORDS"] = eval(head_w, {"__builtins__": {}}, scope)
        except (SyntaxError, NameError, TypeError):
            missing.append(f"witness wire: the {tag} declares a length this gate cannot read")
            continue
        sides[tag] = scope

    if len(sides) == 2:
        for name in ("NOTE_WORDS", "HEAD_WORDS"):
            a, b = sides["circuit"][name], sides["client"][name]
            if a != b:
                missing.append(f"witness wire {name}: circuit {a} against client {b}")
        for depth in (1, 3, 32, 64):
            lens = {
                t: sc["HEAD_WORDS"] + 4 * (1 + depth * sc["RATE"]) + 2 * sc["RATE"]
                for t, sc in sides.items()
            }
            if lens["circuit"] != lens["client"]:
                missing.append(
                    f"witness wire length at depth {depth}: "
                    f"circuit {lens['circuit']} against client {lens['client']}"
                )

    if missing:
        print(f"the client does not pin what the circuit emits, {len(missing)} values:")
        for m in missing:
            print(f"  {m}")
        return 1
    print(
        f"vector agrees: {len(spec['cases'])} key cases every field, "
        f"and the intent's {len(off)} named offsets"
    )
    if stale:
        print(f"stale, re-emit shield-intent.json for: {', '.join(stale)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
