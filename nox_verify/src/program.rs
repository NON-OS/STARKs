// NONOS Operating System (AGPL-3.0-or-later)
//! A circuit read from its program image: the constraint tape and boundary
//! list `gen_program_air.py` encodes, the same bytes the on-chain evaluator is
//! compiled from.
//!
//! The image says what the constraints are. The few numbers it does not carry
//! (width, the region split, degree, mask pair) come from the pinned
//! statement, and the parameter identity computed from both has to equal the
//! proof's, so a statement whose numbers disagree with its image verifies
//! nothing.

use crate::crypto::stark::air::{Air, AirExt, Permuted};
use crate::crypto::stark::field::{Fp, Fp2};
use crate::crypto::stark::fri::root_of_unity;
use alloc::vec::Vec;

/// The numbers a program image does not carry.
#[derive(Clone, Copy)]
pub struct Shape {
    pub trace_width: usize,
    pub region_width: usize,
    pub window: usize,
    pub constraint_degree: usize,
    pub mask_pair: Option<(usize, usize)>,
    pub challenge_lanes: usize,
}

#[derive(Clone, Copy)]
enum Op {
    Const(Fp2),
    Input(u16),
    Add(u16, u16),
    Sub(u16, u16),
    Mul(u16, u16),
}

#[derive(Clone, Copy)]
enum Source {
    Value(Fp),
    Public(usize),
}

/// A parsed image, before any statement's public words are applied.
pub struct Program {
    log_t: u32,
    n_frame: usize,
    n_periodic: usize,
    ops: Vec<Op>,
    outputs: Vec<u16>,
    /// `(column, row, source)`, in the image's order, which is the order the
    /// composition coefficients are drawn for.
    boundaries: Vec<(usize, usize, Source)>,
}

struct Cursor<'a> {
    b: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(n)?;
        let s = self.b.get(self.at..end)?;
        self.at = end;
        Some(s)
    }
    fn u8(&mut self) -> Option<u8> {
        self.take(1).map(|s| s[0])
    }
    fn u16(&mut self) -> Option<u16> {
        self.take(2).map(|s| u16::from_be_bytes([s[0], s[1]]))
    }
    fn u64(&mut self) -> Option<u64> {
        let s = self.take(8)?;
        let mut a = [0u8; 8];
        a.copy_from_slice(s);
        Some(u64::from_be_bytes(a))
    }
    fn fp(&mut self) -> Option<Fp> {
        let v = self.u64()?;
        (v < crate::crypto::stark::field::P).then(|| Fp::from_u64(v))
    }
}

impl Program {
    /// Parse an image, or `None` for anything malformed: a truncated or
    /// trailing byte, an operand naming a later result, a non-canonical
    /// constant, an inversion (no shipped circuit has one, and refusing them
    /// keeps every evaluation total), or a boundary row off the trace domain.
    pub fn parse(bytes: &[u8], window: usize) -> Option<Program> {
        let mut c = Cursor { b: bytes, at: 0 };
        let n_ops = c.u16()? as usize;
        let n_out = c.u16()? as usize;
        let n_bnd = c.u16()? as usize;
        let n_rows = c.u16()? as usize;
        let n_frame = c.u16()? as usize;
        let n_periodic = c.u16()? as usize;
        let log_t = c.u8()? as u32;
        let n_exempt = c.u8()? as usize;
        if log_t == 0 || log_t > 24 {
            return None;
        }
        let t = 1usize << log_t;
        let g = root_of_unity(log_t);

        /*
         * The engine exempts the transition on the last `window - 1` rows and
         * nothing else. An image claiming any other exemption describes a
         * circuit this engine does not evaluate, so it is refused rather than
         * reinterpreted.
         */
        if n_exempt != window.checked_sub(1)? {
            return None;
        }
        for k in 0..n_exempt {
            if c.fp()? != g.pow((t - 1 - k) as u64) {
                return None;
            }
        }

        let n_inputs = n_frame + n_periodic + 4;
        let mut ops = Vec::with_capacity(n_ops);
        for i in 0..n_ops {
            let earlier = |a: u16| (a as usize) < i;
            let op = match c.u8()? {
                0 => Op::Const(Fp2 { c0: c.fp()?, c1: c.fp()? }),
                1 => {
                    let k = c.u16()?;
                    if k as usize >= n_inputs {
                        return None;
                    }
                    Op::Input(k)
                }
                k @ 2..=4 => {
                    let (a, b) = (c.u16()?, c.u16()?);
                    if !earlier(a) || !earlier(b) {
                        return None;
                    }
                    match k {
                        2 => Op::Add(a, b),
                        3 => Op::Sub(a, b),
                        _ => Op::Mul(a, b),
                    }
                }
                _ => return None,
            };
            ops.push(op);
        }
        let mut outputs = Vec::with_capacity(n_out);
        for _ in 0..n_out {
            let o = c.u16()?;
            if o as usize >= n_ops {
                return None;
            }
            outputs.push(o);
        }

        /*
         * Rows travel as g^row. The trace domain is small enough to index once,
         * and a value that is no power of g below t is no row.
         */
        let mut row_of = Vec::with_capacity(n_rows);
        let mut powers = Vec::with_capacity(t);
        let mut x = Fp::ONE;
        for _ in 0..t {
            powers.push(x);
            x = x * g;
        }
        for _ in 0..n_rows {
            let v = c.fp()?;
            row_of.push(powers.iter().position(|p| *p == v)?);
        }

        let mut boundaries = Vec::with_capacity(n_bnd);
        for _ in 0..n_bnd {
            let col = c.u8()? as usize;
            let row = *row_of.get(c.u16()? as usize)?;
            let src = match c.u8()? {
                0 => Source::Value(c.fp()?),
                1 => Source::Public(c.u8()? as usize),
                _ => return None,
            };
            boundaries.push((col, row, src));
        }
        if c.at != bytes.len() {
            return None;
        }
        Some(Program {
            log_t,
            n_frame,
            n_periodic,
            ops,
            outputs,
            boundaries,
        })
    }

    /// The highest public word a boundary reads, plus one: the fewest words a
    /// statement over this image can have.
    pub fn public_words(&self) -> usize {
        self.boundaries
            .iter()
            .filter_map(|(_, _, s)| match s {
                Source::Public(k) => Some(k + 1),
                Source::Value(_) => None,
            })
            .max()
            .unwrap_or(0)
    }
}

/// A program image bound to one statement's public words: the AIR the engine
/// verifies against.
pub struct ProgramAir<'a> {
    program: &'a Program,
    shape: Shape,
    boundaries: Vec<(usize, usize, Fp)>,
    challenges: [Fp2; 4],
}

impl<'a> ProgramAir<'a> {
    /// `None` when the words are fewer than the image reads, a boundary names
    /// a column off the trace, or the frame the image reads is not the
    /// statement's window over its width.
    pub fn new(program: &'a Program, shape: Shape, publics: &[Fp]) -> Option<ProgramAir<'a>> {
        if program.n_frame != shape.window * shape.trace_width
            || shape.region_width >= shape.trace_width
        {
            return None;
        }
        let mut boundaries = Vec::with_capacity(program.boundaries.len());
        for &(col, row, src) in &program.boundaries {
            if col >= shape.trace_width {
                return None;
            }
            let v = match src {
                Source::Value(v) => v,
                Source::Public(k) => *publics.get(k)?,
            };
            boundaries.push((col, row, v));
        }
        Some(ProgramAir {
            program,
            shape,
            boundaries,
            challenges: [Fp2::ZERO; 4],
        })
    }

    fn eval(&self, window: &[Fp2], periodic: &[Fp2]) -> Vec<Fp2> {
        let p = self.program;
        let mut vals: Vec<Fp2> = Vec::with_capacity(p.ops.len());
        let input = |k: u16| -> Fp2 {
            let k = k as usize;
            if k < p.n_frame {
                window.get(k).copied().unwrap_or(Fp2::ZERO)
            } else if k < p.n_frame + p.n_periodic {
                periodic.get(k - p.n_frame).copied().unwrap_or(Fp2::ZERO)
            } else {
                self.challenges[k - p.n_frame - p.n_periodic]
            }
        };
        for op in &p.ops {
            let v = match *op {
                Op::Const(c) => c,
                Op::Input(k) => input(k),
                Op::Add(a, b) => vals[a as usize] + vals[b as usize],
                Op::Sub(a, b) => vals[a as usize] - vals[b as usize],
                Op::Mul(a, b) => vals[a as usize] * vals[b as usize],
            };
            vals.push(v);
        }
        p.outputs.iter().map(|&o| vals[o as usize]).collect()
    }
}

impl Air for ProgramAir<'_> {
    fn log_trace_len(&self) -> u32 {
        self.program.log_t
    }
    fn trace_width(&self) -> usize {
        self.shape.trace_width
    }
    fn window_size(&self) -> usize {
        self.shape.window
    }
    fn constraint_degree(&self) -> usize {
        self.shape.constraint_degree
    }
    fn num_transition(&self) -> usize {
        self.program.outputs.len()
    }
    fn transition(&self, window: &[Fp], periodic: &[Fp]) -> Vec<Fp> {
        let w: Vec<Fp2> = window.iter().map(|v| Fp2::from_base(*v)).collect();
        let p: Vec<Fp2> = periodic.iter().map(|v| Fp2::from_base(*v)).collect();
        self.eval(&w, &p).iter().map(|v| v.c0).collect()
    }
    fn boundary(&self) -> Vec<(usize, usize, Fp)> {
        self.boundaries.clone()
    }
}

impl AirExt for ProgramAir<'_> {
    fn transition_ext(&self, window: &[Fp2], periodic: &[Fp2]) -> Vec<Fp2> {
        self.eval(window, periodic)
    }
    fn challenge_lanes(&self) -> usize {
        self.shape.challenge_lanes
    }
    fn mask_pair(&self) -> Option<(usize, usize)> {
        self.shape.mask_pair
    }
    fn periodic_count(&self) -> usize {
        self.program.n_periodic
    }
    fn periodic_at(&self, _g: Fp, _t: usize, _z: Fp2) -> Option<Vec<Fp2>> {
        None
    }
}

impl Permuted for ProgramAir<'_> {
    fn region_width(&self) -> usize {
        self.shape.region_width
    }
    fn set_challenges(&mut self, beta: Fp, gamma: Fp) {
        self.set_challenges_ext(Fp2::from_base(beta), Fp2::from_base(gamma));
    }
    /// The image reads the challenges as four base-field inputs, each
    /// component its own input: beta's two, then gamma's two.
    fn set_challenges_ext(&mut self, beta: Fp2, gamma: Fp2) {
        self.challenges = [
            Fp2::from_base(beta.c0),
            Fp2::from_base(beta.c1),
            Fp2::from_base(gamma.c0),
            Fp2::from_base(gamma.c1),
        ];
    }
    /// A verifier fills nothing: there is no trace here.
    fn fill_products(&self, _trace: &mut [Fp]) {}
}
