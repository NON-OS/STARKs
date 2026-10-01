// NONOS Operating System (AGPL-3.0-or-later)
// The built module against every pinned proof, under Node:
//   node js/check.mjs <nox_verify_wasm.wasm> <spec dir>
// Exits nonzero on any pinned proof refused or any tampered one accepted.

import { readFileSync, readdirSync, existsSync } from "node:fs";
import { join } from "node:path";
import { load, STATEMENT, wordsFromJson } from "./nox-verify.mjs";

const [wasm, spec] = process.argv.slice(2);
const v = await load(readFileSync(wasm));
const sets = [
  [STATEMENT.attestation, "attest", "proof.bin"],
  [STATEMENT.activity, "activity", "proof.bin"],
  [STATEMENT.activity, "wallet-vectors-activity", "proof.bin"],
  [STATEMENT.transfer, "fri8", "proof.bin"],
  [STATEMENT.transferNotBefore, "not-before", "proof.bin"],
  [STATEMENT.claim, "claim", "proof.bin"],
  [STATEMENT.transferNotBefore, "wallet-vectors-not-before", "proof-format7.bin"],
];
const P = 0xffffffff00000001n;
let bad = 0, n = 0;
for (const [st, set, file] of sets) {
  for (const d of readdirSync(join(spec, set)).sort()) {
    const f = join(spec, set, d, file);
    if (!existsSync(f)) continue;
    const proof = new Uint8Array(readFileSync(f));
    const words = wordsFromJson(readFileSync(join(spec, set, d, "publics.json"), "utf8"));
    const t0 = performance.now();
    const honest = v.verify(st, proof, words);
    if (!honest.ok) console.log("   reason:", v.lastReason());
    const ms = (performance.now() - t0).toFixed(1);
    const moved = words.slice(); const at = Math.min(25, words.length - 1); moved[at] = (moved[at] + 1n) % P;
    const flipped = proof.slice(); flipped[proof.length >> 1] ^= 1;
    const r1 = v.verify(st, proof, moved), r2 = v.verify(st, flipped, words);
    const ok = honest.ok && !r1.ok && !r2.ok;
    n++; if (!ok) bad++;
    console.log(`${ok ? "ok  " : "FAIL"} ${set}/${d} honest=${honest.reason} (${ms} ms) moved=${r1.code} flipped=${r2.code}`);
  }
}
// The context digest, against the b3sum answer over the kernel's exact bytes.
{
  const want = "6fc7bcf4f4b46314afe0d2e71f58776d0dfdcdf9fc4c96dad1a91a8ba23b61c6";
  const b = Uint8Array.from(want.match(/../g).map((h) => parseInt(h, 16)));
  const dv = new DataView(b.buffer);
  const expect = [0, 1, 2, 3].map((i) => { const v = dv.getBigUint64(8 * i, true); return v >= P ? v - P : v; });
  const w = v.attestWords([1n, 2n, 3n, 4n], new TextEncoder().encode("nonos capsule context, fixture"), 1);
  const ok = w.length === 9 && w.slice(4, 8).every((x, i) => x === expect[i]) && w[8] === 1n;
  let refused = false;
  try { v.attestWords([1n, 2n, 3n, 4n], new Uint8Array(0), 2); } catch { refused = true; }
  console.log(`${ok && refused ? "ok  " : "FAIL"} attestation words: context digest ${ok ? "matches b3sum" : "DIFFERS"}, padding ${refused ? "refused" : "ACCEPTED"}`);
  if (!(ok && refused)) bad++;
}
// The published fixture tree refolds to the root the attestation proofs carry,
// and BLAKE3 matches the reference vector, whole and streamed.
{
  const tree = readFileSync(join(spec, "attest", "tree.json"), "utf8");
  const w = [...tree.matchAll(/"([0-9]+)"/g)].map((m) => BigInt(m[1]));
  const root = w.slice(0, 4);
  const leaves = [];
  for (let i = 4; i < w.length; i += 4) leaves.push(w.slice(i, i + 4));
  const folded = v.foldTree(leaves);
  const words = wordsFromJson(readFileSync(join(spec, "attest", "kernel", "publics.json"), "utf8"));
  const st = JSON.parse(readFileSync(join(spec, "attest", "kernel", "statement.json"), "utf8"));
  const d = Uint8Array.from(st.digest.match(/../g).map((h) => parseInt(h, 16)));
  const leafOk = v.leaf(st.kind, d).every((x, i) => x === leaves[st.slot][i]);
  const rootOk = folded.every((x, i) => x === root[i] && x === words[i]);
  const abc = new TextEncoder().encode("abc");
  const want = "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85";
  const hex = (b) => Array.from(b, (x) => x.toString(16).padStart(2, "0")).join("");
  const whole = hex(await v.blake3(abc));
  const streamed = hex(await v.blake3((async function* () { yield abc.subarray(0, 1); yield abc.subarray(1); })()));
  const ok = rootOk && leafOk && whole === want && streamed === want;
  console.log(`${ok ? "ok  " : "FAIL"} tree refolds to the proofs' root: ${rootOk}, leaf: ${leafOk}, blake3: ${whole === want && streamed === want}`);
  if (!ok) bad++;
}
console.log(`${n - bad} of ${n} pinned proofs: verified, and refused when changed`);
process.exit(bad ? 1 : 0);
