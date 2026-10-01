# 14. Shared paths, format 6

Format 6 is the launch proof of 13-launch.md with its Merkle paths shared: the same
statement, the same parameter identity and the same verifier, and fewer bytes. Format 5 stays the
format the live pool verifies. A pool that takes format 6 is a new deployment.

## What changes

A launch proof opens nine trees at the query positions:
- the four FRI layers;
- the trace regions, the permutation columns, the composition and the periodic columns.

Format 5 carries a full path per query per tree. Two queries whose paths meet share every node
above the meeting point, and a sibling that is itself an ancestor of an opened leaf can be
computed rather than carried. Format 6 carries, per tree, only the siblings that cannot be
computed, in one order both sides derive from the positions.

## The walk

For one tree of depth $d$, given the opened leaves as (index, leaf digest) pairs:

1. **Known set.** The indices, sorted ascending, duplicates removed. Two leaves at one index must
   carry one digest, or the proof is refused.
2. **Each level, for $\ell = 0$ to $d - 1$:** walk the known set in ascending order. For each index
   $i$ whose sibling $i \oplus 1$ is not in the set, read the next digest of the stream: that is the
   sibling's value. Then, for each pair $(2j, 2j + 1)$ with a member in the set, compute
   $\text{node}(2j, 2j + 1)$, the Merkle node hash over the two children. The parents $\{i \gg 1\}$
   are the next level's known set.
3. **The end.** The stream must be consumed exactly, not a digest short and not one over, and the
   last known set is $\{0\}$ with the root as its value. That root must equal the committed root.

The positions are never on the wire. The verifier draws them from the transcript after the query
grind, as in format 5. The index a query opens in each tree:

| tree | leaf | index | depth |
|---|---|---|---|
| FRI layer $m$ | `hash_leaf_quad` of the fold group's four values | $q \bmod 2^{d_m}$ | $d_m = \log_2 N - 2(m + 1)$ |
| trace regions | `hash_leaf_wide` of the row's region columns | $q$ | $\log_2 N$ |
| permutation | `hash_leaf_wide` of the row's permutation columns | $q$ | $\log_2 N$ |
| composition | `hash_leaf_ext` of the value | $q$ | $\log_2 N$ |
| periodic | `hash_leaf_wide_periodic` of the periodic row | $q$ | $\log_2 N$ |

At the launch point $N = 2^{23}$, so the FRI trees have depths 21, 19, 17 and 15.

## Why it is as sound as format 5

- **Binding.** The Rust verifier rebuilds every query's full path from the stream
  (`merkle::multi::expand`) and then walks each one against its root, exactly as in format 5. An
  accepted format 6 proof therefore authenticates every opened value under the same roots as the
  format 5 proof with those paths. A changed stream digest is a changed sibling on some path, and
  that path no longer reaches its root.
- **One encoding.** The order is a function of the positions, the stream must be consumed exactly,
  and trailing bytes are refused. So a proof has one format 6 encoding, and its hash names it.
- **The walk is complete and minimal, proved.** `Shield.Multiproof` proves for every opened set:
  - a carried sibling is never one the walk already knows;
  - both children of every parent the walk reaches are known or carried;
  - the stream is never longer than one path per opened leaf.
  It also decides the pinned transfer's stream lengths from its positions, and they equal the
  Rust's.
- **The counts on the wire are not trusted.** Each stream carries its length so the body parses
  without the transcript. The verifier knows how many siblings the positions need and refuses any
  other count.

## The bytes

```text
header                      40   magic, format 6, protocol 1, params id
perm_root                   24
region_width                4
trace_root, comp_root       48
n_ood, ood_frame            4 + 16 n_ood
n_layers, fri roots         4 + 24 n_layers
n_final, final layer        4 + 16 n_final
n_q                         4
per query, per layer        64            the fold group's four F_p^2 values
pow_nonce, pow_chain        8 + 8 (chunks - 1)
fold_nonces                 8 n_layers    when the commit rounds are ground
row_width                   4
per query                   8 row_width + 16    the row, then the composition value
n_periodic, claims at z     4 + 16 n_periodic
per query                   8 n_periodic        the periodic row
streams                     4 + 24 count each, in order: FRI layers 0 to 3, trace,
                                          permutation, composition, periodic
```

Little endian throughout. A field element at or above the modulus is refused, and so is any byte
after the last stream. Against format 5, format 6 drops every path and its length word, the per
query layer count, the per query row length and the second query count. It adds one row width and
nine stream counts.

## Measured

The pinned transfer converted to format 6 by `shared_paths_test`:

| | format 5 | format 6 |
|---|---|---|
| package | 112,956 bytes | **93,796 bytes**, 19,160 fewer (17.0%) |
| path digests | 3,116, one path per query per tree | 2,348 in nine streams |

The digests per stream: FRI layers 306, 269, 222 and 187; trace, permutation, composition and
periodic 341 each. (The transfer pinned before hedged randomness measured 93,844 bytes and 2,350
digests: stream lengths move with the query positions.) The four base trees open at the same positions and so have streams of one
length.

## Code

- `nonos_stark::merkle::multi`: `compress`, `expand` and `stream_len`, with unit tests.
- `nonos_stark::air::shared_paths`: which leaf, index and depth each tree uses; `share` and `fill`.
- `stark_verify_ext_rounds_shared_why`: the format 5 verifier with the rebuild in front, one code
  path.
- `proof_wire::shared`: the format 6 codec.
- `shared_paths_test`: round trip, byte count against this layout, every stream digest bound,
  single-bit flips, cut, padded and regrown streams, and no crossing between formats 5 and 6.
