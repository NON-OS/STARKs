// NONOS Operating System (AGPL-3.0-or-later)
//! What the wallet does to stay anonymous, and what the user turned off.
//!
//! Every field defaults to the anonymous choice. Weakening one is a field the
//! caller sets by name, never an argument slipped into a payment call, and
//! `warnings` lists everything that was weakened, so a front end can show it
//! before anything is signed.

/// Blocks, at about 12 s each: a submission waits a uniform draw from
/// [DELAY_MIN, DELAY_MAX] after the payment is built, so deposit, transfer
/// and withdrawal do not sit next to each other on chain.
pub const DELAY_MIN: u64 = 25;
pub const DELAY_MAX: u64 = 300;

/// Below this many leaves since a note landed, the wallet says the set its
/// spend hides among is small.
pub const MIN_SET: usize = 100;

/// The smallest standard note, in the asset's base units: 0.001 of an 18
/// decimal token.
pub const UNIT: u64 = 1_000_000_000_000_000;

pub const Policy = struct {
    /// Who submits: the address the relay fee pays. A payment with no
    /// submitter is refused unless `self_submit` is set.
    submitter: ?[20]u8 = null,
    /// What the submitter is paid, in base units: covers its gas, so neither
    /// the sender nor a fresh withdrawal address needs to hold any.
    relay_fee: u64 = 0,
    /// Submit from the address that owns the notes. It links that address
    /// to every spend it sends.
    self_submit: bool = false,
    /// Payee notes and public amounts in standard sizes (`denom`).
    standard_notes: bool = true,
    /// The smallest standard note in note units. Null takes it from the
    /// launch pool's asset table (`denom.unitFor`).
    unit: ?u64 = null,
    /// The submission window after a payment is built, in blocks.
    delay_min: u64 = DELAY_MIN,
    delay_max: u64 = DELAY_MAX,
    /// Withdraw only to a fresh address this wallet derived and never used.
    fresh_withdrawals: bool = true,
    min_set: usize = MIN_SET,

    pub const Warning = enum {
        self_submit,
        nonstandard_amounts,
        short_delay,
        reused_or_foreign_recipient,
        small_anonymity_set,
    };

    /// Everything this policy weakened, in a fixed order. Empty for the
    /// defaults.
    pub fn warnings(self: *const Policy, buf: *[5]Warning) []const Warning {
        var n: usize = 0;
        if (self.self_submit) {
            buf[n] = .self_submit;
            n += 1;
        }
        if (!self.standard_notes) {
            buf[n] = .nonstandard_amounts;
            n += 1;
        }
        if (self.delay_max < DELAY_MIN or self.delay_min > self.delay_max) {
            buf[n] = .short_delay;
            n += 1;
        }
        if (!self.fresh_withdrawals) {
            buf[n] = .reused_or_foreign_recipient;
            n += 1;
        }
        if (self.min_set < MIN_SET) {
            buf[n] = .small_anonymity_set;
            n += 1;
        }
        return buf[0..n];
    }

    /// The policy tests and tools use to drive the protocol directly: every
    /// protection off. Named, so no caller ends up here by leaving a field
    /// out.
    pub fn unprotected() Policy {
        return .{
            .self_submit = true,
            .standard_notes = false,
            .delay_min = 0,
            .delay_max = 0,
            .fresh_withdrawals = false,
            .min_set = 0,
        };
    }
};
