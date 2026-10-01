#!/usr/bin/env python3
# NONOS Operating System (AGPL-3.0-or-later)
"""One quantity, one home.

Counts homes by constant name and never by value. Three quantities in this tree
are all equal to seven: the evaluation coset offset, the extension's tower
modulus, and a domain generator. A tool that grouped by value would report
twenty six homes for "seven" and invite someone to collapse them, which is a
worse bug than the one being fixed and a quieter one, because those three agree
today for exactly the reason every copy of the coset agreed.

Three things are not second homes and the gate says so rather than being argued
with each time:

A constant defined from another constant's path is a reference. It cannot drift
because it has no value of its own.

A constant declared inside an `impl` or a `mod` is that scope's own quantity.
The three soundness points each declare `N_QUERIES` and each means a different
number of queries.

A name declared twice with different values is two quantities sharing a
spelling, not one quantity in two places. `RATE` is four for the pool hash and
eight for the sponge. Merging those would be the failure this gate exists to
prevent, so they are reported apart from the duplicates and never counted as
one.

Two severities for what is left. A PUBLISHED quantity is one the structure file
carries, so a verifier is generated from it, and a second home puts the prover
and the verifier on different parameters while both compile and both pass their
own tests. That exits 1. An INTERNAL quantity is one nothing emits, where a
wrong value breaks arithmetic in every direction at once, so it is reported and
counted rather than blocking. The difference is not how wrong the code would
be. It is how loudly it would say so.
"""

import argparse
import collections
import pathlib
import re
import sys

# Named in the emitted structure file, so a verifier is generated from them.
PUBLISHED = {
    "SHIFT",
    "COSET_SHIFT",
    "GRIND_BITS",
    "N_QUERIES",
    "EXTRA_BLOWUP_BITS",
    "TREE_DEPTH",
    "POOL_LOG_ROUNDS",
    "LOG_ROUNDS",
    "RATE",
    "WIDTH",
}

# Column zero only, and the initialiser is captured so a reference can be told
# from a value.
DECL = re.compile(r"^(?:pub(?:\([a-z: ]+\))?\s+)?const\s+([A-Z][A-Z0-9_]*)\s*:[^=]+=\s*([^;]+);")


def homes(root: pathlib.Path) -> dict:
    found = collections.defaultdict(list)
    read = 0
    for path in sorted(root.rglob("*.rs")):
        if "target" in path.parts:
            continue
        read += 1
        for n, line in enumerate(path.read_text(errors="replace").splitlines(), 1):
            m = DECL.match(line)
            if not m:
                continue
            name, value = m.group(1), m.group(2).strip()
            if "::" in value:
                continue
            found[name].append((f"{path.relative_to(root)}:{n}", value))
    # A gate that reports clean over a directory it found nothing in reads like
    # a pass and is not one.
    if not read:
        raise SystemExit(f"no Rust files under {root}: nothing was checked")
    return found


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--root", default=".")
    args = p.parse_args()
    root = pathlib.Path(args.root).resolve()

    hard, soft, spelled = [], [], []
    for name, places in sorted(homes(root).items()):
        if len(places) < 2:
            continue
        values = {v for _, v in places}
        if len(values) > 1:
            spelled.append((name, places))
        elif name in PUBLISHED:
            hard.append((name, places))
        else:
            soft.append((name, places))

    def show(tag, rows):
        for name, places in rows:
            print(f"{tag}  {name}: {len(places)} homes")
            for where, value in places:
                print(f"        {where} = {value}")

    show("name ", spelled)
    show("soft ", soft)
    show("HARD ", hard)
    print(
        f"\n{len(hard)} published with more than one home, "
        f"{len(soft)} internal, {len(spelled)} names meaning two things"
    )
    return 1 if hard else 0


if __name__ == "__main__":
    sys.exit(main())
