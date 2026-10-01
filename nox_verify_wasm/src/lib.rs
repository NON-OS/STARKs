// NONOS Operating System (AGPL-3.0-or-later)
//! `nox_verify` as a WebAssembly module a page instantiates with nothing but
//! `WebAssembly.instantiate`: no bindings generator, no imports, four exports.
//!
//!     nv_alloc(len) -> ptr              a buffer the page fills
//!     nv_free(ptr, len)                 give it back
//!     nv_verify(statement, proof_ptr, proof_len, words_ptr, n_words) -> code
//!     nv_statement_words(statement) -> words, 0 for an unknown statement
//!     nv_reason(buf_ptr, buf_len) -> len   why the last nv_verify refused, UTF-8
//!     nv_attest_words(root_ptr, ctx_ptr, ctx_len, kind, out_ptr) -> code
//!                                       the attestation's nine words from a
//!                                       root (four u64) and the context bytes
//!     nv_leaf(kind, digest_ptr, out_ptr) -> code      a slot's leaf, four u64
//!     nv_fold_tree(leaves_ptr, n, out_ptr) -> code     a complete tree's root
//!     nv_b3_reset() / nv_b3_update(ptr, len) / nv_b3_finish(out_ptr)
//!                                       BLAKE3 over a stream, one at a time
//!
//! Statements: 1 the 36-word transfer, 2 the 37-word transfer with
//! `not_before`, 3 the 38-word claim, 4 the attestation (a kernel, capsule
//! or bootloader slot, nine words), 5 the 18-word activity claim. The code is 0 for a proof that
//! verifies, `Refusal::code` for one that does not, and 100 for an unknown
//! statement or a null buffer. Words are little-endian u64, one per public
//! word, the way a `BigUint64Array` lays them out.

use nox_verify::statements::{ACTIVITY, ATTEST, CLAIM, NOT_BEFORE, TRANSFER};
use nox_verify::{verify_why, Statement};
use std::sync::Mutex;

const UNKNOWN: u32 = 100;

/// The last refusal's reason. A page runs one verification at a time.
static REASON: Mutex<&'static str> = Mutex::new("");

fn record(r: &'static str) {
    if let Ok(mut g) = REASON.lock() {
        *g = r;
    }
}

/// # Safety
/// `buf` is null or points to `len` writable bytes. Copies at most `len` bytes
/// of the last reason and returns its full length.
#[no_mangle]
pub unsafe extern "C" fn nv_reason(buf: *mut u8, len: usize) -> usize {
    let r = REASON.lock().map(|g| *g).unwrap_or("");
    if !buf.is_null() {
        let n = r.len().min(len);
        // SAFETY: the caller's contract gives `len` writable bytes at `buf`.
        unsafe { core::ptr::copy_nonoverlapping(r.as_ptr(), buf, n) };
    }
    r.len()
}

fn statement(id: u32) -> Option<&'static Statement> {
    match id {
        1 => Some(&TRANSFER),
        2 => Some(&NOT_BEFORE),
        3 => Some(&CLAIM),
        4 => Some(&ATTEST),
        5 => Some(&ACTIVITY),
        _ => None,
    }
}

/// Every buffer is 8-byte aligned, so the same call serves the proof bytes
/// and the u64 words.
fn layout(len: usize) -> Option<std::alloc::Layout> {
    std::alloc::Layout::from_size_align(len, 8).ok()
}

/// A buffer of `len` bytes for the page to fill, or null when `len` is 0 or
/// too large to lay out.
#[no_mangle]
pub extern "C" fn nv_alloc(len: usize) -> *mut u8 {
    match layout(len) {
        // SAFETY: a nonzero size and a valid layout.
        Some(l) if len != 0 => unsafe { std::alloc::alloc(l) },
        _ => core::ptr::null_mut(),
    }
}

/// # Safety
/// `ptr` came from `nv_alloc(len)` with this `len` and is not used after.
#[no_mangle]
pub unsafe extern "C" fn nv_free(ptr: *mut u8, len: usize) {
    if let (false, Some(l)) = (ptr.is_null() || len == 0, layout(len)) {
        // SAFETY: the caller's contract: `ptr` is `nv_alloc(len)`'s, with this layout.
        unsafe { std::alloc::dealloc(ptr, l) }
    }
}

#[no_mangle]
pub extern "C" fn nv_statement_words(id: u32) -> u32 {
    statement(id).map_or(0, |s| s.words as u32)
}

/// # Safety
/// `proof` points to `proof_len` readable bytes and `words` to `n_words`
/// readable u64s, both from `nv_alloc`, which aligns them to 8.
#[no_mangle]
pub unsafe extern "C" fn nv_verify(
    id: u32,
    proof: *const u8,
    proof_len: usize,
    words: *const u64,
    n_words: usize,
) -> u32 {
    let Some(st) = statement(id) else {
        record("unknown statement");
        return UNKNOWN;
    };
    if proof.is_null() || words.is_null() || (words as usize) % 8 != 0 {
        record("a null or misaligned buffer");
        return UNKNOWN;
    }
    // SAFETY: non-null, and the caller's contract gives the lengths.
    let (p, w) = unsafe {
        (
            core::slice::from_raw_parts(proof, proof_len),
            core::slice::from_raw_parts(words, n_words),
        )
    };
    match verify_why(st, p, w) {
        Ok(()) => {
            record("");
            0
        }
        Err((r, why)) => {
            record(why);
            r.code()
        }
    }
}

/// # Safety
/// `root` points to 4 readable u64s, `ctx` to `ctx_len` readable bytes (or is
/// null with `ctx_len` 0), `out` to 9 writable u64s; the u64 buffers from
/// `nv_alloc`. Returns 0 and fills `out`, or 100 for a kind never proven, a
/// root word not below p, or a null or misaligned buffer.
#[no_mangle]
pub unsafe extern "C" fn nv_attest_words(
    root: *const u64,
    ctx: *const u8,
    ctx_len: usize,
    kind: u32,
    out: *mut u64,
) -> u32 {
    if root.is_null() || out.is_null() || (root as usize) % 8 != 0 || (out as usize) % 8 != 0 {
        return UNKNOWN;
    }
    if ctx.is_null() && ctx_len != 0 {
        return UNKNOWN;
    }
    // SAFETY: non-null and aligned, and the caller's contract gives the lengths.
    let (r, c) = unsafe {
        (
            core::slice::from_raw_parts(root, 4),
            if ctx_len == 0 {
                &[][..]
            } else {
                core::slice::from_raw_parts(ctx, ctx_len)
            },
        )
    };
    let Some(w) = nox_verify::attest::words([r[0], r[1], r[2], r[3]], c, kind as u64) else {
        return UNKNOWN;
    };
    // SAFETY: `out` holds 9 writable u64s by the caller's contract.
    unsafe { core::ptr::copy_nonoverlapping(w.as_ptr(), out, 9) };
    0
}

/// # Safety
/// `digest` points to 32 readable bytes, `out` to 4 writable, aligned u64s.
#[no_mangle]
pub unsafe extern "C" fn nv_leaf(kind: u32, digest: *const u8, out: *mut u64) -> u32 {
    if digest.is_null() || out.is_null() || (out as usize) % 8 != 0 {
        return UNKNOWN;
    }
    // SAFETY: 32 readable bytes by the caller's contract.
    let d: [u8; 32] = unsafe { core::ptr::read_unaligned(digest as *const [u8; 32]) };
    let l = nox_verify::attest::leaf(kind as u64, &d);
    // SAFETY: 4 writable u64s by the caller's contract.
    unsafe { core::ptr::copy_nonoverlapping(l.as_ptr(), out, 4) };
    0
}

/// # Safety
/// `leaves` points to `4 * n` readable, aligned u64s, `out` to 4 writable,
/// aligned u64s. Returns 0, or 100 for a count that is not a power of two up
/// to 2^16, a word not below p, or a bad buffer.
#[no_mangle]
pub unsafe extern "C" fn nv_fold_tree(leaves: *const u64, n: usize, out: *mut u64) -> u32 {
    if leaves.is_null() || out.is_null() || (leaves as usize) % 8 != 0 || (out as usize) % 8 != 0 {
        return UNKNOWN;
    }
    if n == 0 || n > 1 << 16 {
        return UNKNOWN;
    }
    // SAFETY: `4 * n` readable u64s by the caller's contract; n is bounded above.
    let flat = unsafe { core::slice::from_raw_parts(leaves, 4 * n) };
    let quads: Vec<[u64; 4]> = flat
        .chunks_exact(4)
        .map(|c| [c[0], c[1], c[2], c[3]])
        .collect();
    let Some(root) = nox_verify::attest::fold_tree(&quads) else {
        return UNKNOWN;
    };
    // SAFETY: 4 writable u64s by the caller's contract.
    unsafe { core::ptr::copy_nonoverlapping(root.as_ptr(), out, 4) };
    0
}

/// The page's one BLAKE3 stream: reset, update chunk by chunk, finish.
static B3: Mutex<Option<blake3::Hasher>> = Mutex::new(None);

#[no_mangle]
pub extern "C" fn nv_b3_reset() {
    if let Ok(mut g) = B3.lock() {
        *g = Some(blake3::Hasher::new());
    }
}

/// # Safety
/// `ptr` points to `len` readable bytes, or is null with `len` 0.
#[no_mangle]
pub unsafe extern "C" fn nv_b3_update(ptr: *const u8, len: usize) -> u32 {
    if ptr.is_null() && len != 0 {
        return UNKNOWN;
    }
    let Ok(mut g) = B3.lock() else {
        return UNKNOWN;
    };
    let Some(h) = g.as_mut() else {
        return UNKNOWN;
    };
    if len != 0 {
        // SAFETY: `len` readable bytes by the caller's contract.
        h.update(unsafe { core::slice::from_raw_parts(ptr, len) });
    }
    0
}

/// # Safety
/// `out` points to 32 writable bytes. Ends the stream; 100 if none was begun.
#[no_mangle]
pub unsafe extern "C" fn nv_b3_finish(out: *mut u8) -> u32 {
    if out.is_null() {
        return UNKNOWN;
    }
    let Ok(mut g) = B3.lock() else {
        return UNKNOWN;
    };
    let Some(h) = g.take() else {
        return UNKNOWN;
    };
    // SAFETY: 32 writable bytes by the caller's contract.
    unsafe { core::ptr::copy_nonoverlapping(h.finalize().as_bytes().as_ptr(), out, 32) };
    0
}
