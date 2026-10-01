# What this wallet does for your anonymity, and what it cannot do

The proof hides which note you spend and, once the zero-knowledge argument ships, what the notes
are worth. The rest of anonymity is behaviour: who sends the transaction, when, in what amounts, to
which address, and what your network connection reveals. The wallet does the anonymous thing by
default. Turning any of it off is a named setting (`anon.Policy`), and `Policy.warnings` lists every
setting you weakened before anything is signed.

## Defaults

| default | what it prevents | code |
|---|---|---|
| Every spend is submitted by someone else, paid by the relay fee the proof binds to them | your address appearing as the sender of your spends | `Wallet.pay`, `withdraw`, `Policy.submitter` |
| Payee amounts and withdrawals come in standard sizes, 1, 2 and 5 times powers of ten of 0.001 | a public amount that names you | `anon/denom.zig` |
| Each payment waits a random 25 to 300 blocks before it may be submitted | deposit, transfer and withdrawal sitting next to each other on chain | `anon/timing.zig` |
| A withdrawal goes to a fresh address derived for it and never reused; the relay fee pays the gas | the two ends of the pool linked through one address | `anon/fresh.zig`, `Wallet.withdraw` |
| The wallet fetches every note event and opens memos locally | the RPC learning which notes are yours | `anon/scan.zig` |
| You are shown how many notes your spend hides among, with a warning below 100 | spending into a set too small to hide in | `anon/set.zig`, `Wallet.anonymitySet` |
| A note is spent only 32 blocks after it lands | a deposit spent in the next block | `wallet.MIN_AGE` |

## What it cannot do

- **The network.** The wallet opens no connections. The RPC you use sees your IP address and when
  you ask. Use your own node, or reach one over Tor. A submitter sees the payment it relays, but not
  who you are, unless your connection to it tells them.
- **A small pool.** Early on, few notes exist and every spend hides among few. The set display is
  honest about this. No wallet setting fixes it; only more users do.
- **Amounts inside the pool** are hidden by the proof, not by this wallet. Until the
  zero-knowledge argument is written, checked and deployed, do not rely on them being hidden.
- **Your own patterns.** Spending at the same hour every day, or withdrawing the exact sum you
  deposited, can still be matched by someone watching. Standard sizes and delays make that harder,
  not impossible.
- **The endpoints.** A payee knows they were paid. An exchange that receives a withdrawal knows
  that address.
