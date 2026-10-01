# 04. Trees

A spend proves that each note it retires is in the pool and in the association set. Both are
Merkle trees of depth 32 over the compression of [02-poseidon.md](02-poseidon.md). This document
defines the tree, the frontier the pool keeps instead of the tree, the root window that proofs are
checked against, and the membership argument in the circuit. It closes with the nullifier set: the
pool records spent nullifiers in a mapping, and an indexed Merkle tree for them exists in the code
but is not deployed.

Code references: the pool's tree is `GoldilocksIncrementalTree.sol` in the contracts repository,
the prover's copy is `stark_proofs/src/shield/member/tree.rs`, and the client's is

## 1. The tree

**Definition 1.1 (zeros).** $`Z_0 = (0, 0, 0, 0)`$ and
$`Z_{\ell+1} = \mathrm{compress}(Z_\ell, Z_\ell)`$ for $0 \le \ell < 32$.

$`Z_\ell`$ is the root of an empty subtree of height $\ell$. The pool computes the chain once at
deployment, and the prover and the client compute it at start (`member/tree.rs:28`,
`with_depth`).

**Definition 1.2 (tree).** For leaves $`c_0, \dots, c_{m-1}`$ with $m < 2^{32}$, set
$`N_0(i) = c_i`$ for $i < m$ and $`N_0(i) = Z_0`$ otherwise, and

```math
N_{\ell+1}(i) = \mathrm{compress}\big(N_\ell(2i),\ N_\ell(2i+1)\big).
```

The root is $`N_{32}(0)`$. Leaves are note commitments ([03-keys-notes-nullifiers.md](03-keys-notes-nullifiers.md)),
appended left to right and never removed.

A node whose subtree holds no leaf equals the zero of its height:
$`N_\ell(i) = Z_\ell`$ when $i \cdot 2^\ell \ge m$. `PoolTree::node` returns $`Z_\ell`$ in that case
without hashing (`member/tree.rs:47`).

**Capacity.** The pool admits at most $2^{32} - 1$ leaves (`MAX_LEAVES`). The index of leaf
$2^{32} - 1$ has all 32 bits set, so a carry-driven insert of it would write one frontier entry past
the array. The bound is one below the tree's size so that the last insertion reverts with
`TreeIsFull` before it can do that.

## 2. The frontier

The pool does not store the tree. It stores one node per level.

**Definition 2.1 (frontier).** After $m$ insertions, $`F_\ell`$ is the last value the insertion
algorithm below wrote at level $\ell$.

Insertion of leaf $c$ at index $m$ (`_insertLeafDeferred`): set $v = c$ and $\ell = 0$. While bit
$\ell$ of $m$ is 1, set $`v = \mathrm{compress}(F_\ell, v)`$ and $\ell = \ell + 1$. Then set
$`F_\ell = v`$.

**Lemma 2.2.** After $m$ insertions, for every level $\ell$ with bit $\ell$ of $m$ set,
$`F_\ell = N_\ell(\lfloor m / 2^\ell \rfloor - 1)`$: the frontier holds the complete left subtree at
every level where the count has a one.

*Proof.* By induction on $m$. Inserting at index $m$ climbs the levels where $m$ has
trailing ones. At each of them $`F_\ell`$ is the complete left sibling of the node being built, by the
hypothesis, so the value carried to level $\ell + 1$ is the complete node above. The climb stops at
the lowest zero bit $`\ell^*`$ of $m$, which is the lowest set bit of $m + 1$, and writes the complete
node there. Bits of $m + 1$ above $`\ell^*`$ equal those of $m$, and their frontier entries are
untouched. $\square$

**Proposition 2.3 (fold).** The root of the tree with $m$ leaves is

```math
v_0 = Z_0, \qquad v_{\ell+1} = \begin{cases} \mathrm{compress}(F_\ell, v_\ell) & \text{bit } \ell \text{ of } m = 1 \\ \mathrm{compress}(v_\ell, Z_\ell) & \text{bit } \ell \text{ of } m = 0 \end{cases}, \qquad \mathrm{root} = v_{32}
```

(`_foldFrontier`).

*Proof.* The invariant is $`v_\ell = N_\ell(\lfloor m / 2^\ell \rfloor)`$, the node at level $\ell$
on the path of index $m$, the first empty slot. At $\ell = 0$ that node is the empty leaf $`Z_0`$. If bit $\ell$
of $m$ is 1, the node is a right child and its left sibling is complete, which is $`F_\ell`$ by
Lemma 2.2. If bit $\ell$ is 0, the node is a left child and its right sibling holds no leaf, so it
is $`Z_\ell`$. Either way $`v_{\ell+1}`$ is the parent. At $\ell = 32$ the node is the root. $\square$

The contract tests the fold against sequential insertion bit for bit (`BatchInsert.t.sol`), and
the prover's `PoolTree` computes the same root from stored leaves. Both are checked against the
live pool: the relay rebuilds the published root from the leaf list before proving
("4 pool leaves and 4 association leaves rebuild to the published roots", `prove_inner`).

**Cost.** An insertion hashes once per trailing one of the index, one hash on average. A root is
32 hashes. The pool defers the root to `commitRoot`, so deposits pay the insertion and the root
walk is paid once per publication. Every note appended between two publications shares that root.

## 3. The root window

**Definition 3.1.** The pool keeps the last 128 published roots (`ROOT_WINDOW`) in a ring, with a
mapping for constant-time lookup. `isKnownRoot(r)` holds when $r \neq 0$ and $r$ is in the ring.

A settlement refuses an intent whose note root is not known (`UnknownOrStaleRoot`). The window
lets a proof built against one root settle after other deposits have moved the root.

**Proposition 3.2.** Every root the pool publishes differs from every earlier one, unless
Poseidon has a collision.

*Proof.* The leaf count strictly increases between two publications, and `commitRoot` returns
without publishing when the root did not move. Two trees with different leaf counts differ in at
least one leaf position that is a commitment in one and $`Z_0`$ in the other. Equal roots over
different leaf vectors give a collision at some level. $\square$

The ring evicts by deleting the evicted root from the mapping. That is correct only because roots
do not repeat: a repeated root still inside the window would be deleted by its older copy's
eviction. The same property keeps `commitRoot`, which anyone may call, from flushing the window:
a call that does not move the root does not advance the ring.

## 4. Membership in the circuit

The circuit proves that a spent note's commitment is a leaf of the tree under the published root.

**Definition 4.1 (opening).** An opening of leaf $c$ at index $i$ is the sibling list
$`s_0, \dots, s_{31}`$ with $`s_\ell = N_\ell(\lfloor i / 2^\ell \rfloor \oplus 1)`$ and the direction
bits $`d_\ell = \lfloor i / 2^\ell \rfloor \bmod 2`$ (`member/tree.rs:63`, `path`). The walk is
$`w_0 = c`$ and

```math
w_{\ell+1} = \begin{cases} \mathrm{compress}(w_\ell, s_\ell) & d_\ell = 0 \\ \mathrm{compress}(s_\ell, w_\ell) & d_\ell = 1 \end{cases}
```

and the opening is valid when $`w_{32}`$ equals the root.

The membership region (`nonos-stark/src/air/multi_membership/rules.rs`) runs one Poseidon
permutation per level. Each level's first row places the running digest and the sibling in the two
halves of the state by the direction bit,

```math
\mathrm{state}_j = (1 - d)\, w_j + d\, s_j, \qquad \mathrm{state}_{4+j} = (1 - d)\, s_j + d\, w_j, \qquad 0 \le j < 4,
```

and constrains $d(1 - d) = 0$ so that a direction cannot blend the two children
(`rules.rs:65`, `rules.rs:79`). The terminal digest $`w_{32}`$ is wired into the input's live gate,
which requires it to equal the published root when the input is live
([03-values.md](03-values.md), Section 4.6). A dummy input's walk is
not bound to anything.

**The index.** The direction bits are the leaf index, and the nullifier hashes the index as a
scalar. The circuit recomputes the scalar from the bits and wires both ends
(`shield/join/bind_index.rs:16`). Bit 0 is not otherwise on the trace: the bottom direction lives
only in which half of the first state the leaf occupies. The region witnesses it as a bit at the
opening's first row and selects the leaf from the two halves with it (`pin0`,
`multi_membership.rs`), so bit 0 is bound like the others. Without that, a note would retire under
its sibling position with every other constraint satisfied (`Break::ForeignIndex0`,
`test/double_spend.rs`).

**The association set.** The same region proves the spent commitment is a leaf of a second tree,
the association set, under the association root the intent publishes (`ASSOC_ROOT`, words 4 to 7).
The pool checks that root against its registry. The live gate conditions this walk on the same bit.

## 5. The nullifier set

**As deployed.** The pool records nullifiers in `mapping(bytes32 => bool) nullifierSpent`. A
settlement reverts with `NullifierAlreadySpent` if either nullifier of an intent is already
recorded, and records both otherwise. The mapping is exact: a nullifier is spent or it is not, and
the check costs one storage read.

**Indexed Merkle tree (built, not deployed).** A set whose non-membership a circuit could prove
needs more than a mapping. `stark_proofs/src/shield/imt` implements an indexed Merkle tree for
that purpose. It is described here because it is in the
repository, and nothing in the deployed flow uses it.

**Definition 5.1 (leaf).** A leaf is $(v, v', k, e)$: a key $`v \in \mathbb{F}_p^4`$, the next key
$v'$, the next leaf's index $k$, and a flag $e$ set on the leaf with the largest key, where $v'$ must
be zero (`imt/leaf.rs`). The leaf hash is

```math
\mathrm{compress}\big(\mathrm{compress}(v, v'),\ \mathrm{compress}((k, e, \mathtt{IMT\_LEAF\_DOMAIN}, 0),\ 0^4)\big)
```

with $`\mathtt{IMT\_LEAF\_DOMAIN} = \mathtt{0x494D544C}`$ (`imt/hash.rs`, `leaf_hash`). The empty set
is one sentinel leaf with key zero and $e = 1$.

**Definition 5.2 (order).** Keys compare as the 256-bit integer $`\sum_j v_j\, 2^{64 j}`$, which is
the `uint256` order of the `bytes32` encoding of [03-keys-notes-nullifiers.md](03-keys-notes-nullifiers.md),
Section 7 (`imt/order.rs`, `cmp`). Every limb is canonical, so the two orders agree.

**Proposition 5.3 (non-membership).** If the leaves form a chain sorted by key, then a key $u$ is
absent if and only if some leaf $L$ satisfies $L.v < u$ and either $L.e = 1$ or $u < L.v'$.

*Proof.* In a sorted chain each key other than the largest is followed by the next larger key.
If $u$ is absent, let $L$ be the leaf with the largest key below $u$, which exists because the
sentinel's key is zero and $u$ is not. Either $L$ is last, or its successor's key is above $u$
because it is not below and not equal. Conversely, a leaf with $L.v < u < L.v'$ leaves no room for
$u$ between two consecutive keys, and a last leaf with $L.v < u$ has no key above it. $\square$

Both bounds are strict (`imt/order.rs`, `excludes`): $u = L.v$ and $u = L.v'$ are keys in the set,
and each has its own test.

**Insertion.** A batch of keys is sorted first, so that each key's low leaf is either a leaf
already in the tree or the key inserted just before it (`imt/insert.rs`, `chain`). Strict sorting
excludes duplicates. The fold then checks that no two keys update the same leaf
(`writes_are_distinct`), because two keys in one gap validated against the pre-batch tree would
both write the same low leaf, and the fold would lose one of the writes.

## 6. Tests

| property | test |
|---|---|
| the zeros chain | `test/tree_zeros.rs` |
| batch insertion equals sequential insertion (contract) | `BatchInsert.t.sol` |
| the published roots rebuild from the leaves | `prove_inner` against the live pool, `test/live_pool.rs` |
| a note not in the tree is refused | `test/membership.rs`, `test/published_root.rs` |
| a note outside the association set is refused | `test/unlisted.rs`, `test/membership_scope.rs` |
| the index in the nullifier is the walked index, bit 0 included | `test/double_spend.rs` |
| indexed-tree bounds, last leaf and batch insertion | `imt/test/bounds.rs`, `last.rs`, `insert.rs`, `merge.rs`, `kat.rs` |

## 7. Open items

- The indexed Merkle tree is not deployed, and no circuit proves non-membership in it. The pool's
  mapping is the nullifier set.
- `imt/mod.rs` names `spec/nullifier-imt.md` as its specification, and that file is not in the
  repository.
