# Attestation pinned proofs

One slot per kind of a fixture 256-slot tree, at 26 queries and a 28-bit grind, from the fixed entropy `(7 i + 3) mod 256`. Each proof was verified from its format 7 bytes and carries its rank certificate.

| slot | kind | index | bytes | keccak256 |
|---|---|---|---|---|
| kernel | 0 | 3 | 115024 | `c9dd904d7b5b73bf2cb74598a1839d47a37f7ae1e3b3cccb8db76dd8fb1e47f6` |
| capsule | 1 | 77 | 114576 | `1cb0a2cb60ec50d2ccfe2071a2d11d3e2da43ea4f371ac3dddd82a0e9778ec60` |
| bootloader | 3 | 200 | 115280 | `d61d18245d842ce8f0011aa3996ce4de6246577e5da0918c349781e10a87010b` |

Root: `0xaf60eb1eda76145a5112c50de08c423734196e159d50230aa950a0fa4ed59607`

Parameter id: `ca819110ed337eeeb9dfa3282d9c0a6c37e5e6eabb45170c2158be0c12117f89`

Periodic root: `aeb47d73baf1404fa29b4b5d0a9f31e659465ae90717ae141679c77a000a55fb`
