# Parameters

Every constant, the file that holds it, and who reads it. A number that lives in two places
drifts; each of these lives in one file and is repeated here with that file named.
`ci/one_home.py` fails the build if a quantity gains a second home.

## 1. Field and hash

| constant | value | held in | read by |
|---|---|---|---|
| p | 2^64 - 2^32 + 1 = 0xFFFFFFFF00000001 | `nonos-stark/src/field/element.rs` | everything |
| EPSILON | 2^32 - 1 | `element.rs` | add, sub, the 128-bit reduction |
| extension | F_p², X² - 7 | `field/ext.rs` | every challenge, composition, DEEP, FRI |
| Poseidon width / rate | 8 / 4 | `air/poseidon.rs` | the circuits, the pool's Solidity hasher |
| rounds | 32, LOG_ROUNDS 5 | `shield/note/limbs.rs::POOL_LOG_ROUNDS` | `PoseidonGoldilocks.sol::FULL_ROUNDS` |
| S-box | x^7 | `poseidon.rs` | all |
| MDS | Cauchy over i and 8 + j | `poseidon.rs` | all |
| round constants | BLAKE3("NONOS-POSEIDON-GOLDILOCKS-RC" r j) | `poseidon.rs` | all |
| NOTE_DOMAIN | 0x4E4F5445 "NOTE" | `poseidon.rs` | cm |
| SPEND_DOMAIN | 0x53504E44 "SPND" | `shield/key/domain.rs` | spend_pk |
| NULL_DOMAIN | 0x4E554C4C "NULL" | `shield/key/domain.rs` | nk |
| DEAD_DOMAIN | 0x44454144 "DEAD" | `shield/key/domain.rs` | a dummy input's position word |
| attestation leaf domain | 0x4E4F4E4F534C5633 "NONOSLV3" | `attest/mod.rs::LEAF_DOMAIN` | the attestation leaf |
| activity tag domain | 0x4E4F584143545631 "NOXACTV1" | `activity/mod.rs::ACTIVITY_DOMAIN` | the weekly tag T |
| activity key domain | 0x4E4F584143544B31 "NOXACTK1" | `activity/mod.rs::KEY_DOMAIN` | the key commitment K |
| transcript and Merkle hash | Keccak-256 | `nonos-stark/src/hash/` | provers and verifiers |
| Merkle digest | 32 bytes (`fri8`) | `merkle::DIGEST_BYTES` | every root and path |

The 128-bit reduction: with `x = lo + hi 2^64` and `hi = hh 2^32 + hl`, `2^64 = EPSILON` and
`2^96 = -1` modulo p, so `x = lo - hh + hl EPSILON`, corrected once at each borrow or carry and
reduced once at the end. Test `field_test.mul_agrees_with_u128_modulo_on_edges_and_random_inputs`.

## 2. Trees

| tree | depth | held in | used by |
|---|---|---|---|
| note tree | 32 | `shield/member/tree.rs::TREE_DEPTH` | the pool, the transfer circuits, the wallet |
| a week's nullifier tree Λ_e | 16 | `activity/mod.rs::DEPTH` | the activity statement, the weekly leaf list |
| attestation policy tree | 8 (256 slots) | `attest/mod.rs::DEPTH` | the attestation statement, boot and spawn gates |

Every tree is built the same way: zero leaves, `zeros[l + 1] = compress(zeros[l], zeros[l])`, each
node `compress(left, right)` (`PoolTree`).

## 3. Points

| point | queries | rate | query grind (8 chunks) | DEEP grind | fold grind | conjectured | provable |
|---|---:|---|---:|---:|---:|---:|---:|
| A | 19 | 2^-6 | 28 | 19 | 21 | 142 | 80.1 (query phase 80.8) |
| A′ | 18 | 2^-6 | 31 | 19 | 21 | 139 | see docs/16 |
| B | 17 | 2^-6 | 33 | 19 | 21 | 135 | see docs/16 |
| attestation | 26 | 2^-6 | 28 | 19 | 21 | 184 | 80 (query phase about 100) |

Held in `nonos-stark/src/fri_ext/grind.rs` (`QUERY_SHAPES`, `ATTEST_SHAPE`, `DEEP_GRIND_BITS`,
`COMMIT_GRIND_BITS`, `GRIND_CHUNKS`). Every point uses extra blowup 5, so rate 2^-6, and a radix-8
FRI fold. The argument for each figure is [docs/12-soundness.md](docs/12-soundness.md).

## 4. Statements

| statement | words | rows | width | region | degree | mask | periodic | held in |
|---|---:|---:|---:|---:|---:|---|---:|---|
| transfer | 36 | 2^13 | 44 | 34 | 11 | (42, 43) | 59 | `shield/join` |
| transfer with not-before | 37 | 2^13 | 44 | 34 | 11 | (42, 43) | 59 | `shield/join`, `not_before` |
| claim | 38 | 2^13 | 44 | 34 | 11 | (42, 43) | | `shield/join`, `claim` |
| attestation | 9 | 2^14 | 33 | 29 | 8 | (31, 32) | 22 | `attest/` |
| activity | 18 | 2^13 | 46 | 32 | 11 | (44, 45) | 92 | `activity/` |

Every statement's FRI domain is 2^23. `nox_verify/src/statements.rs` pins each statement's shape,
program, periodic root and accepted parameter identities.

## 5. Prover cost, measured

The 37-word transfer, as a wallet proves it from the bundled periodic cache (`nox_prover`,
`profile_test`), on a server pinned to a given number of cores:

| cores | total | of which FRI and the query grind | peak memory |
|---:|---:|---:|---:|
| 6 | 35.8 s | 18.9 s | 939 MB |
| 4 | 50.9 s | 28.1 s | 811 MB |

The activity statement proves in about 26 s with every core of a large server, peaking at 1.7 GB. Phones differ:
the wallet reports each phase's time through `nox_prove_ex`'s progress callback.
