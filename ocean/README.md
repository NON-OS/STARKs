Ocean

Claim

Ocean is the shielded note set. This directory is its client side in Zig:
keys, notes, the pool tree mirror, sealed memos, and the two-in two-out
intent a prover turns into a STARK. It does not prove and it does not talk
to L1. `sk` and every blinding live in RAM, reach the prover as a witness,
and never reach calldata. Byte for byte it agrees with the Rust circuit and
the Solidity pool, pinned to three real vectors: the published key
hierarchy, note A of the Sepolia pool, and the pool's root after leaf 2, and
to every pinned wallet vector: the 36-word and 37-word transfers and the
activity claim. The proof system uses no elliptic curve; the sealed notes use
X-Wing, whose ML-KEM-768 half keeps them sealed if X25519 falls.

Build

    zig build            Zig 0.14, 64-bit host
    zig build test       every vector and every refusal below

No allocator is hidden: `Tree` and `Wallet` take one and reserve before they
write, so a failed allocation leaves them as they were. No panic on input:
every check returns a named error. Secrets are wiped with volatile stores.

Modules, one invariant each

    field.zig     Goldilocks, canonical in [0, p); mul by the 128 bit reduction
    poseidon.zig  width 8, rate 4, 32 rounds, Cauchy MDS, BLAKE3 constants
    digest.zig    four limbs; bytes32 big endian with limb 0 low; hex
    note.zig      (value, asset, spend_pk, blinding); limbs; cm; 80 bytes
    key.zig       sk from seed; spend_pk, nk; nf; the activity tag and key commitment
    tree.zig      depth 32, every level stored; witness; rootOf
    spend.zig     two in, two out; dummy inputs; the 36 and 37 word intents; check
    memo.zig      client data 0x01: X-Wing, ChaCha20-Poly1305, view tag
    wallet.zig    sk in RAM; absorb; receive; maturity; pay; unshield; merge

Invariant

O1. spend_pk = compress(sk, tag(0x53504E44)); nk = compress(sk, tag(0x4E554C4C));
    nf = compress(compress(nk, cm), [leaf_index, live ? 0 : DEAD, 0, 0]). key.zig;
    key_test the_published_key_hierarchy_vector_derives, three cases.
O2. cm = commit_note(value lo, value hi, asset, spend_pk, blinding), NOTE at 11.
    note.zig; key_test the_live_sepolia_note_derives_from_its_secret_and_commits_to_its_leaf.
O3. Depth 32 over zeros[l+1] = compress(zeros[l], zeros[l]); bit l set puts the
    node on the right. tree.zig; tree_test the_live_pool_root_after_three_leaves_at_depth_32.
O4. Two inputs, two outputs; inputs = outputs + amount + fee in one asset; a
    transfer carries fee 0, price 0, recipient 0; both openings fold to their
    roots; nullifiers distinct. spend.zig; spend_test, eight refusals.
O5. A dummy input has value 0 and no leaf; its nullifier still enters the set.
    spend.zig Input; spend_test a_dummy_that_carries_value_is_refused_even_when_balanced.
    Its position word carries the dead marker, so its nullifier never equals a
    live note's.
O6. The note opening travels only sealed to the payee's X-Wing key (ML-KEM-768
    and X25519), bound to its leaf by the associated data. Every failure is
    NotForUs. The bytes are note_seal's, checked against its pinned vector.
    memo.zig; memo_test the_note_seal_vector_is_reproduced, nine bent bytes
    each refused.
O7. The second output is always the payer's own note; input and output order
    are shuffled; inputs are marked spent only after every check passes and
    are released if the payment does not settle. wallet.zig; wallet_test.
O8. A limb from bytes is refused when not canonical, never reduced.
    digest.zig; digest_test a_non_canonical_limb_is_refused_not_reduced.
O9. A note is spent only MIN_AGE = 32 blocks after its leaf lands, so an
    absorb and its spend never sit beside each other on chain. wallet.zig;
    wallet_test a_note_is_not_spent_before_it_is_old_enough.
O10. A payment above any two notes is refused with NeedsChain; merge pays the
    two largest to self first. wallet.zig; wallet_test
    two_notes_merge_and_a_payment_above_them_needs_a_chain.
O11. The production pool settles 37 words: the 36, then not_before, a positive
    multiple of 600 seconds, else NotBeforeOffGrid. spend.zig intentNotBefore;
    wallet_vectors_test, the four 37-word vectors.
O12. The activity tag T = compress([NOXACTV1, nk0..2], [nk3, week, 0, 0]) and
    the key commitment K = compress([NOXACTK1, nk0..2], [nk3, 0, 0, 0]), the
    words a holder publishes and declares. key.zig; activity_test, against the
    pinned activity vector, with the week's leaves folded to its root.

Bytes

    digest    32   big endian u256, limb 0 in bytes 24..32
    note      80   value 8 be | asset_id 8 be | spend_pk 32 | blinding 32
    address 1249   version 1 | spend_pk 4 x u64 le | X-Wing key 1216
    memo    1186   version 1 | view tag 1 | X-Wing ct 1120 | opening 48 | tag 16
    opening   48   value u64 le | asset_id u64 le | blinding 4 x u64 le
    witness  32 x 32   siblings, level 0 first
    intent    36 words: root 4 | assoc 4 | nf0 4 | nf1 4 | cm0 4 | cm1 4 |
              amount | fee | asset | price | recipient 4 | fee recipient 4
              (an address as limbs of 48, 48, 48 and 16 bits, low first);
              37 with not_before as word 36

Flow

    seed -> Secret.fromSeed -> derive -> Keys; ViewKey.fromSecret -> Address
    L1 NoteCommitted(cm, i)  -> wallet.absorb(cm) = i
    memo, i, block           -> wallet.receive: open under spend_pk, cm matches leaf i
    registry opening         -> wallet.attest(i, witness)
    pay(to, value, now)      -> mature notes, select, dummies, shuffle, check, seal, mark spent
    NeedsChain               -> merge(now) first, settle, then pay
    settle failed            -> release(payment)

Failure

NonCanonical, ZeroInverse, IndexOutOfRange, TreeFull, Unbalanced,
ValueOverflow, AssetMismatch, DummyCarriesValue, DoubleSpend, NotInPool,
NotInAssoc, SettleFieldsOnTransfer, NoRecipient, NotForUs, MalformedAddress,
MemoLeafMismatch, NotAttested, Insufficient, Immature,
NeedsChain, UnknownNote, NoFeeRecipient, FeeRecipientWithoutFee,
NotBeforeOffGrid. Nothing on this path panics on input.

Built and tested with Zig 0.14.0: 123 tests. The prover behind the witness is
`nox_prover`, which a wallet links.

License: AGPL-3.0-or-later
