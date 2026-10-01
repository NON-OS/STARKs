# Verifying a proof

How to check a proof of any statement in this repository: natively, in a browser, and against what
is deployed. Every command runs from the repository root.

## 1. What a verifier holds

A verifier never takes the circuit from the prover. For each statement it holds four things, all
in `nox_verify/src/statements.rs` and in the statement's `spec/<statement>/MANIFEST.md`:

| | what it is |
|---|---|
| **program image** | the statement's constraints compiled to a program (`spec/<statement>/program.bin`), pinned by its keccak256 |
| **periodic root** | the commitment to the circuit's fixed columns, rebuilt by the verifier rather than read from the proof |
| **accepted parameter identities** | one 32-byte id per accepted point (queries, rate, grinds, fold, shape); any other is refused before the proof is read |
| **shape** | trace width, region width, window, constraint degree, mask columns, challenge lanes |

## 2. What a proof carries

A proof is format 7. It opens with a 40-byte header:

| bytes | field |
|---|---|
| 0..4 | `NOXP` |
| 4..6 | format, 7, little-endian |
| 6..8 | protocol, 1 |
| 8..40 | the parameter identity |

What follows is the proof at that point: the commitment roots, the out-of-domain frame, the DEEP
and FRI data, the grind nonces, and one shared set of Merkle paths for the queried rows. The public
words are not in the proof; the verifier is given them, and the transcript absorbs them.

## 3. Natively

```sh
cargo test --release -p nox_verify
```

This verifies every proof under `spec/` and requires each to be refused when a public word moves
or a byte flips. In code:

```rust
use nox_verify::{statements::NOT_BEFORE, verify, Refusal};

match verify(&NOT_BEFORE, &proof, &words) {
    Ok(()) => { /* the statement holds */ }
    Err(r) => eprintln!("refused: {}", r.reason()),
}
```

The checks run in this order, and a refusal names the first that failed:

| refusal | meaning |
|---|---|
| `Image` | the pinned image does not hash to its pin, or does not parse |
| `Length` | the proof is longer than the statement allows, or shorter than a header |
| `Header` | not format 7 of this protocol, or a parameter identity the statement does not accept |
| `Publics` | the wrong number of public words, or one not below p |
| `Shape` | the statement's numbers and the proof's parameter identity disagree |
| `Encoding` | the bytes after the header do not parse as a proof at that point |
| `Proof` | the proof does not verify |

`nox_verify` is `no_std` with `alloc`, so the same crate runs in a kernel gate.

## 4. In a browser

```sh
rustup target add wasm32-unknown-unknown
cargo build --profile wallet -p nox_verify_wasm --target wasm32-unknown-unknown
node nox_verify_wasm/js/check.mjs target/wasm32-unknown-unknown/wallet/nox_verify_wasm.wasm spec
```

`check.mjs` verifies every pinned proof through the module, and requires a moved word and a flipped
byte to be refused. A page uses `nox_verify_wasm/js/nox-verify.mjs`:

```js
import { load, STATEMENT, wordsFromJson } from "./nox-verify.mjs";

const v = await load(wasmBytes);
const words = wordsFromJson(publicsJsonText); // BigInt words; a JSON number keeps only 53 bits
const r = v.verify(STATEMENT.transferNotBefore, proofBytes, words);
// r.ok; on a refusal r.code and r.reason
```

Statement ids: 1 transfer, 2 transfer with not-before, 3 claim, 4 attestation, 5 activity.

## 5. Against the chain

The production pool's verifier pins the same image hash as the transfer with not-before
(`0x4364151e…2429`). To check a landed payment without trusting anyone's log:
1. Read the settlement transaction's calldata.
2. Take its proof bytes and public words.
3. Run them through `nox_verify` with `NOT_BEFORE`.

A proof the chain accepted verifies here, and the same bytes with any word changed are refused here
as on chain.

## 6. Reproducing the verifier

The browser module is built reproducibly: the same commit, built twice from two directories with
the build paths remapped, gives the same bytes. The commands are in the [README](../README.md#5-reproduce-a-release-build).
