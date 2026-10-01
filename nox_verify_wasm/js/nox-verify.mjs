// NONOS Operating System (AGPL-3.0-or-later)
// nox_verify in a page or in Node: instantiate the module, hand it a proof and
// the public words you computed, get a verdict. Nothing is fetched but the
// module itself, and nothing leaves the page.
//
//   import { load, STATEMENT } from "./nox-verify.mjs";
//   const v = await load("nox_verify_wasm.wasm");
//   const r = v.verify(STATEMENT.transferNotBefore, proofBytes, words);
//   // r = { ok, code, reason }
//
// Also: attestWords (a slot's nine words), leaf and foldTree (refold a
// published tree), blake3 (measure a download a chunk at a time).

export const STATEMENT = Object.freeze({ transfer: 1, transferNotBefore: 2, claim: 3, attestation: 4, activity: 5 });

export const REASON = Object.freeze({
  0: "verified",
  1: "the pinned image does not match",
  2: "the proof's length is out of bounds",
  3: "not a format 7 proof at an accepted parameter id",
  4: "the public words are not the statement's",
  5: "the statement's shape does not match the proof's",
  6: "the proof does not parse",
  7: "the proof does not verify",
  100: "unknown statement",
});

/**
 * The `"publics": [...]` array of a JSON file as exact bigints. Public words
 * run to 2^64 and `JSON.parse` turns them into doubles, which keep 53 bits:
 * a word read that way is a different word, and the proof is refused for it.
 */
export function wordsFromJson(text) {
  const m = /"publics"\s*:\s*\[([^\]]*)\]/.exec(text);
  if (!m) throw new Error("no publics array");
  return m[1].split(",").map((w) => w.trim()).filter((w) => w.length).map((w) => {
    if (!/^[0-9]+$/.test(w)) throw new Error(`not a word: ${w}`);
    return BigInt(w);
  });
}

async function instantiate(source) {
  if (typeof source === "string" || source instanceof URL) {
    const res = await fetch(source);
    if (WebAssembly.instantiateStreaming && res.headers.get("content-type") === "application/wasm") {
      return (await WebAssembly.instantiateStreaming(res, {})).instance;
    }
    source = await res.arrayBuffer();
  }
  return (await WebAssembly.instantiate(source, {})).instance;
}

/** Load the module from a URL, a Response body's bytes, or an ArrayBuffer. */
export async function load(source) {
  const x = (await instantiate(source)).exports;
  return {
    /**
     * The attestation's nine public words for a slot of `root` (four bigint
     * words, as enrollment publishes the tree's root) holding `ctx` (the
     * context bytes the gate rebuilds: measurement, capability word, epoch)
     * as `kind` (0 kernel, 1 capsule, 3 bootloader). Throws on a kind never
     * proven or a root word not below p.
     */
    attestWords(root, ctx, kind) {
      const rp = x.nv_alloc(32), op = x.nv_alloc(72), cp = x.nv_alloc(ctx.length);
      try {
        const r = new BigUint64Array(x.memory.buffer, rp, 4);
        for (let i = 0; i < 4; i++) {
          if (typeof root[i] !== "bigint") throw new TypeError("root words must be bigint");
          r[i] = root[i];
        }
        if (ctx.length) new Uint8Array(x.memory.buffer, cp, ctx.length).set(ctx);
        const code = x.nv_attest_words(rp, cp, ctx.length, kind, op);
        if (code !== 0) throw new RangeError("not an attestation statement: kind or root out of range");
        return Array.from(new BigUint64Array(x.memory.buffer, op, 9));
      } finally {
        x.nv_free(rp, 32);
        x.nv_free(op, 72);
        x.nv_free(cp, ctx.length);
      }
    },
    /** A slot's leaf (four bigint words) from its kind and 32-byte digest. */
    leaf(kind, digest) {
      if (digest.length !== 32) throw new RangeError("a digest is 32 bytes");
      const dp = x.nv_alloc(32), op = x.nv_alloc(32);
      try {
        new Uint8Array(x.memory.buffer, dp, 32).set(digest);
        if (x.nv_leaf(kind, dp, op) !== 0) throw new RangeError("leaf refused");
        return Array.from(new BigUint64Array(x.memory.buffer, op, 4));
      } finally {
        x.nv_free(dp, 32);
        x.nv_free(op, 32);
      }
    },
    /**
     * The root (four bigint words) of a complete tree over `leaves`, each four
     * bigint words; the count a power of two up to 65,536.
     */
    foldTree(leaves) {
      const n = leaves.length, bytes = n * 32;
      const lp = x.nv_alloc(bytes), op = x.nv_alloc(32);
      try {
        const w = new BigUint64Array(x.memory.buffer, lp, 4 * n);
        leaves.forEach((q, i) => q.forEach((v, j) => {
          if (typeof v !== "bigint") throw new TypeError("leaf words must be bigint");
          w[4 * i + j] = v;
        }));
        if (x.nv_fold_tree(lp, n, op) !== 0) throw new RangeError("not a complete tree of words below p");
        return Array.from(new BigUint64Array(x.memory.buffer, op, 4));
      } finally {
        x.nv_free(lp, bytes);
        x.nv_free(op, 32);
      }
    },
    /**
     * BLAKE3 of a byte stream: a Uint8Array, or an async iterable of them
     * (a fetch body's reader, a File's stream), hashed a chunk at a time so a
     * 90 MiB image never sits in the module's memory whole.
     */
    async blake3(source) {
      const CHUNK = 1 << 20;
      const cp = x.nv_alloc(CHUNK), op = x.nv_alloc(32);
      try {
        x.nv_b3_reset();
        const feed = (u8) => {
          for (let at = 0; at < u8.length; at += CHUNK) {
            const part = u8.subarray(at, Math.min(at + CHUNK, u8.length));
            new Uint8Array(x.memory.buffer, cp, part.length).set(part);
            if (x.nv_b3_update(cp, part.length) !== 0) throw new Error("hash stream refused");
          }
        };
        if (source instanceof Uint8Array) feed(source);
        else for await (const chunk of source) feed(chunk);
        if (x.nv_b3_finish(op) !== 0) throw new Error("hash stream not begun");
        return new Uint8Array(x.memory.buffer, op, 32).slice();
      } finally {
        x.nv_free(cp, CHUNK);
        x.nv_free(op, 32);
      }
    },
    /** Why the last verify refused, as the verifier names it. */
    lastReason() {
      const len = x.nv_reason(0, 0);
      if (!len) return "";
      const p = x.nv_alloc(len);
      try {
        x.nv_reason(p, len);
        return new TextDecoder().decode(new Uint8Array(x.memory.buffer, p, len).slice());
      } finally {
        x.nv_free(p, len);
      }
    },
    /** The public word count of a statement, 0 if unknown. */
    words(statement) {
      return x.nv_statement_words(statement);
    },
    /**
     * Verify `proof` (Uint8Array, format 7) under `statement` against `words`,
     * an array of bigint, each below p. Compute the words yourself from what
     * you are checking; never take them from the proof's sender. Read them
     * from text with `wordsFromJson`, never through `JSON.parse`.
     */
    verify(statement, proof, words) {
      const n = words.length;
      const pp = x.nv_alloc(proof.length);
      const wp = x.nv_alloc(n * 8);
      let code = 100;
      try {
        // views after both allocations: a growing memory detaches older ones
        new Uint8Array(x.memory.buffer, pp, proof.length).set(proof);
        const w = new BigUint64Array(x.memory.buffer, wp, n);
        for (let i = 0; i < n; i++) {
          // a number above 2^53 has already lost bits; take only exact words
          if (typeof words[i] !== "bigint") throw new TypeError("public words must be bigint");
          w[i] = words[i];
        }
        code = x.nv_verify(statement, pp, proof.length, wp, n);
      } catch (e) {
        if (e instanceof TypeError) throw e;
        code = 7; // a trap is a refusal, never a pass
      } finally {
        x.nv_free(pp, proof.length);
        x.nv_free(wp, n * 8);
      }
      return { ok: code === 0, code, reason: REASON[code] ?? "refused" };
    },
  };
}
