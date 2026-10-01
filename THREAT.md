# Threat model

What is claimed, against whom, and what is not. This describes the system as deployed on the Sepolia
test network; it has had no external audit.

## 1. Adversaries

| | adversary | what it can do |
|---|---|---|
| A | the chain observer | reads every block, event and calldata byte, forever, and correlates across time |
| B | a lander (relayer) | sees each proof before it is on chain; can delay, withhold or reorder what it lands |
| C | a payer or payee | sends a wrong note, reuses one, tries to spend what is not theirs, publishes what it received |
| D | a malicious prover | chooses any witness and any proof bytes, with unbounded compute short of breaking the hash |
| E | the owner of the contracts | the Safe that can pause the pool and change its policy contracts |
| F | a quantum adversary | breaks discrete logarithms and pairings; keeps only hash and lattice assumptions |

## 2. What is claimed

**Against A.** A payment shows a root, two nullifiers, two note commitments, sealed note data and a
proof. Amounts, sender, payee and keys are not on chain. A commitment hides its note under a fresh
blinding. A nullifier is `compress(compress(nk, cm), [index, live, 0, 0])`, so linking it to its
commitment needs the spender's `nk`. Every payment has two inputs and two outputs, so a one-note
payment looks like a two-note one. Held by `stark_proofs/src/shield` (`key`, `join`, `live_test`).

**Against B.** A lander can land a proof or not; it cannot change one. Every public word is bound by
the transcript, so a changed recipient, fee, root or amount fails verification. It cannot learn who
pays whom. A wallet that is refused, or delayed past its patience, can settle the same proof itself
or through another lander.

**Against C.** A note is spendable with its secret alone, and only once: the nullifier set refuses a
repeat, and the position is bound into the nullifier. A dummy input carries a dead marker, so it
never counts as a live note. A payee who publishes the note they received publishes that note and
nothing else.

**Against D.** Each statement is a circuit with a pinned program image. The verifier rebuilds every
check from the image, the periodic root and the accepted parameter identities, and refuses any
other parameter set before reading a proof. The copy constraint's challenges are drawn after the
region columns are committed. Each circuit has three guards:
- a cell-by-cell audit: every witness cell no constraint reads is named by a rule, and the counts are pinned;
- tamper tests that change a public word, a lane, a path or a position and require the circuit itself to refuse;
- a Lean model whose constants and wiring a test holds equal to the code.

The figures are in [docs/12-soundness.md](docs/12-soundness.md): 80.8 bits on the query phase at
point A, and 80.1 bits provable round by round.

**Against F.** The notes sealed to a payee use X-Wing (ML-KEM-768 combined with X25519) and
ChaCha20-Poly1305, so a recorded note stays sealed while either ML-KEM or X25519 holds. That is
what "post-quantum" means in this repository: the privacy of sealed notes, nothing more.

## 3. What is not claimed

- **That nothing is visible.** The pool, the existence and time of each payment, the landing
  address and the fee rung are public.
- **Timing privacy beyond the protocol's rules.** A lander delays each proof by a random interval
  with a cap, and roots are committed on a fixed clock, but an observer still sees when payments
  land.
- **Network privacy on its own.** A wallet reaches a lander over Tor or a mixnet; without one, the
  wallet's IP address reaches the lander.
- **A large anonymity set at launch.** The set is the notes real users hold. Early on it is small,
  and the system does not pretend otherwise.
- **Soundness beyond the stated bounds.** Fiat-Shamir is analysed in the random-oracle model with
  Keccak-256 and Poseidon. The provable figures rest on the published proximity-gap theorems cited
  in docs/12.
- **Side channels on the proving device.** The prover holds the spending secret and the blindings in
  memory for the length of a proof.
- **The owner (E).** A change made through the Safe is a governance matter, not a cryptographic one.
  The owner cannot move shielded value: notes leave the pool only through valid proofs.

## 4. Reporting

Report a vulnerability privately through this repository's **Security** tab, not in a public issue.
