#!/usr/bin/env python3
# NONOS Operating System (AGPL-3.0-or-later)
"""Every file in an emit directory describes the same circuit.

Three times in one day an emitter wrote a file whose name implied a shape it
did not have. A reduced recursion under the settlement name because a flag was
not passed. A transfer proof at the development point because a constant was
read from the wrong module. A boundary list over the packed wiring, 922 columns
at degree 14, sitting beside a structure file at 704 and 10, because one binary
assembled through `assemble_real` while the deployment assembles through the
point.

None of the three was a wrong value. Each was a correct value of a different
quantity, and every one of them read as the right file on inspection. What they
have in common is that nobody compared the directory against itself, because
the directory was the thing being produced.

So this is the gate that reads a finished emit and refuses to hand it over if
its files disagree. It compares by field name across files: a field two files
both carry has to hold one value. It is deliberately dumb about what the fields
mean, because a tool that understood them would be a second opinion about the
circuit and that is the failure it exists to catch.

    python3 ci/emit_agree.py --dir <emit directory>
"""

import argparse
import collections
import json
import pathlib
import sys

# Fields that name the circuit rather than the artifact. A file that carries one
# is making a claim about which circuit it is for.
SHAPE = [
    "point",
    "wiring",
    "trace_width",
    "log_trace_len",
    "num_transition",
    "num_boundary",
    "constraint_degree",
    "window_size",
    "trace_generator",
    "exempt_point",
    "region_width",
    "n_queries",
    "grind_bits",
    "extra_blowup_bits",
    "coset_shift",
    "rounds",
    "product_columns",
    "group_column_base",
    "group_constraint_base",
    "n_wired_columns",
    "max_group_width",
    "outer_n_periodic",
    "n_deep_terms",
]


# Identities across fields that do not share a name.
#
# Same-name comparison misses a quantity spelled two ways:
# `group_constraint_base` and `num_transition` are one quantity, so a base
# emitted 57 too high would sit beside its own refutation.
#
# Each entry is a claim written as arithmetic so it fires instead of being
# read. `left` and `right` are Python
# expressions over the union of every shape field in the directory.
RELATIONS = [
    (
        "a wired column costs two frame terms and one sigma",
        "n_deep_terms",
        "2 * trace_width + outer_n_periodic + 1",
    ),
    (
        "the product columns sit above the regions",
        "trace_width",
        "region_width + product_columns",
    ),
    (
        "the group lanes are the last product_columns of the constraint vector",
        "group_constraint_base + product_columns",
        "num_transition",
    ),
    (
        "the product columns are the last of the trace",
        "group_column_base + product_columns",
        "trace_width",
    ),
    (
        "one accumulator per BLOCK of wired columns",
        "product_columns",
        "-(-n_wired_columns // 8)",
    ),
    (
        "the wiring emitter and the layout count the same wired columns",
        "n_wired_columns",
        "max_group_width",
    ),
]


def relate(known: dict) -> list:
    """Check each identity whose inputs the directory actually carries.

    A relation over fields nobody emitted is not a pass and is not a failure; it
    is reported as unchecked, because a gate that stays silent about what it
    could not evaluate is the gate that reported clean over zero files.
    """
    rows = []
    for why, left, right in RELATIONS:
        try:
            a, b = eval(left, {"__builtins__": {}}, known), eval(right, {"__builtins__": {}}, known)
        except (NameError, TypeError, ZeroDivisionError):
            rows.append(("unchecked", why, left, right, None, None))
            continue
        rows.append(("HOLDS" if a == b else "BROKEN", why, left, right, a, b))
    return rows


def claims(path: pathlib.Path) -> dict:
    try:
        doc = json.loads(path.read_text())
    except (ValueError, OSError):
        return {}
    if not isinstance(doc, dict):
        return {}
    return {k: doc[k] for k in SHAPE if k in doc and not isinstance(doc[k], (list, dict))}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dir", required=True)
    a = ap.parse_args()
    root = pathlib.Path(a.dir).expanduser()

    files = sorted(p for p in root.rglob("*.json") if p.name != "manifest.json")
    if not files:
        print(f"no json under {root}: nothing was checked")
        return 1

    seen = collections.defaultdict(list)
    for p in files:
        for field, value in claims(p).items():
            seen[field].append((p.relative_to(root), value))

    disagree = {f: rows for f, rows in seen.items() if len({str(v) for _, v in rows}) > 1}

    print(f"{len(files)} files, {len(seen)} shape fields claimed")
    for field, rows in sorted(seen.items()):
        mark = "DISAGREE" if field in disagree else "        "
        for where, value in rows:
            print(f"{mark}  {field:<20} {str(value):<24} {where}")

    if disagree:
        print(f"\n{len(disagree)} fields disagree: this directory is not one circuit")
        return 1
    print("\nevery file describes one circuit")

    known = {f: rows[0][1] for f, rows in seen.items()}
    rows = relate(known)
    broken = [r for r in rows if r[0] == "BROKEN"]
    unchecked = [r for r in rows if r[0] == "unchecked"]
    print(f"\n{len(rows)} relations, {len(broken)} broken, {len(unchecked)} unchecked")
    for state, why, left, right, a, b in rows:
        if state == "unchecked":
            print(f"unchecked  {why}\n           {left} == {right}")
        else:
            print(f"{state:<9}  {why}\n           {left} = {a}, {right} = {b}")
    if broken:
        print(f"\n{len(broken)} identities do not hold over this directory")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
