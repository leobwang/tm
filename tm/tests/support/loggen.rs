//! **A seeded, synthetic `.tm/log.jsonl`**: a Rust port of the D9/D10 design
//! pass's `genlog.py` (about 40 events a day) and `genlog80.py` (about 61 a day,
//! the same generator with four to seven replans a block instead of one to
//! three).  Design `kernel/design/stage5/stage5-D9-D10-design.md` §14.1 row A3
//! and §18; the event shapes are the inventory's (`inventory.md` §4.2) and spec
//! §10.1's.
//!
//! The port is exact, not "in the spirit of": it carries CPython's Mersenne
//! Twister (`random.seed(7)`, `random()`, `randint`, `choice`, `getrandbits`)
//! and draws in the scripts' order, so [`design_logs`] reproduces the design
//! pass's eight files **byte for byte** (`tm/tests/loggen.rs` pins their line
//! counts, byte counts and FNV-1a-64 digests).  Every figure in design §1.1 and
//! §18 was taken on those files, so a measurement over this generator is a
//! measurement over the same logs.
//!
//! Dependency-free on purpose: `kernel/tm-kernel-ffi/examples/logbench.rs`
//! includes this file with `#[path]`, and that crate may depend on nothing.
//!
//! Quirks kept from the scripts, because the byte identity is the point: the
//! zone offset is `-05:00` from March to October and `-06:00` otherwise (not
//! the real DST rule); a pause's `unpause` and an interrupt's `resume` clamp
//! the minute at 59 without carrying the hour; `idle` clamps at `23*59`
//! minutes; every week close names `2026-W37`; ids are `1..=900`.

/// The two event rates of the design pass.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rate {
    /// `genlog.py`: one to three `plan` events a block, about 40 events a day.
    Forty,
    /// `genlog80.py`: four to seven `plan` events a block, about 61 a day.
    SixtyOne,
}

impl Rate {
    pub fn label(self) -> &'static str {
        match self {
            Rate::Forty => "40/day",
            Rate::SixtyOne => "61/day",
        }
    }
    /// The file stem the scripts wrote (`log-3y.jsonl`, `log80-3y.jsonl`).
    pub fn stem(self) -> &'static str {
        match self {
            Rate::Forty => "log",
            Rate::SixtyOne => "log80",
        }
    }
}

/// The scripts' four ages, in the order they generated them from one seed.
pub const AGES: [(&str, u32); 4] = [("1mo", 30), ("6mo", 182), ("1y", 365), ("3y", 1095)];

/// The scripts' seed.
pub const SEED: u32 = 7;

/// The scripts' id range, `1..=N_IDS`.
pub const N_IDS: u32 = 900;

// ---------------------------------------------------------------------------
// CPython's `random` module: MT19937 seeded by `init_by_array`, as
// `random.seed(int)` does.

struct PyRandom {
    mt: [u32; 624],
    i: usize,
}

impl PyRandom {
    fn new(seed: u32) -> PyRandom {
        let mut r = PyRandom { mt: [0; 624], i: 624 };
        r.init_genrand(19_650_218);
        // `random.seed(n)` splits |n| into 32-bit words; a u32 seed is one word.
        let key = [seed];
        let (mut i, mut j) = (1usize, 0usize);
        for _ in 0..624.max(key.len()) {
            let prev = r.mt[i - 1] ^ (r.mt[i - 1] >> 30);
            r.mt[i] = (r.mt[i] ^ prev.wrapping_mul(1_664_525))
                .wrapping_add(key[j])
                .wrapping_add(j as u32);
            i += 1;
            j += 1;
            if i >= 624 {
                r.mt[0] = r.mt[623];
                i = 1;
            }
            if j >= key.len() {
                j = 0;
            }
        }
        for _ in 0..623 {
            let prev = r.mt[i - 1] ^ (r.mt[i - 1] >> 30);
            r.mt[i] = (r.mt[i] ^ prev.wrapping_mul(1_566_083_941)).wrapping_sub(i as u32);
            i += 1;
            if i >= 624 {
                r.mt[0] = r.mt[623];
                i = 1;
            }
        }
        r.mt[0] = 0x8000_0000;
        r
    }

    fn init_genrand(&mut self, s: u32) {
        self.mt[0] = s;
        for i in 1..624 {
            self.mt[i] = 1_812_433_253u32
                .wrapping_mul(self.mt[i - 1] ^ (self.mt[i - 1] >> 30))
                .wrapping_add(i as u32);
        }
        self.i = 624;
    }

    fn next_u32(&mut self) -> u32 {
        if self.i >= 624 {
            for k in 0..624 {
                let y = (self.mt[k] & 0x8000_0000) | (self.mt[(k + 1) % 624] & 0x7fff_ffff);
                let mut v = self.mt[(k + 397) % 624] ^ (y >> 1);
                if y & 1 == 1 {
                    v ^= 0x9908_b0df;
                }
                self.mt[k] = v;
            }
            self.i = 0;
        }
        let mut y = self.mt[self.i];
        self.i += 1;
        y ^= y >> 11;
        y ^= (y << 7) & 0x9d2c_5680;
        y ^= (y << 15) & 0xefc6_0000;
        y ^ (y >> 18)
    }

    /// `random.random()`: 53 bits from two words.
    fn random(&mut self) -> f64 {
        let a = (self.next_u32() >> 5) as u64;
        let b = (self.next_u32() >> 6) as u64;
        (a * 67_108_864 + b) as f64 / 9_007_199_254_740_992.0
    }

    /// `random.getrandbits(k)` for `1 <= k <= 64`; words fill from the low end.
    fn getrandbits(&mut self, k: u32) -> u64 {
        if k <= 32 {
            return (self.next_u32() >> (32 - k)) as u64;
        }
        let lo = self.next_u32() as u64;
        let hi = (self.next_u32() >> (64 - k)) as u64;
        lo | (hi << 32)
    }

    /// `Random._randbelow_with_getrandbits(n)`, `n >= 1`.
    fn below(&mut self, n: u32) -> u32 {
        let k = 32 - n.leading_zeros();
        loop {
            let r = self.getrandbits(k) as u32;
            if r < n {
                return r;
            }
        }
    }

    /// `random.randint(a, b)`, inclusive.
    fn randint(&mut self, a: u32, b: u32) -> u32 {
        a + self.below(b - a + 1)
    }

    fn choice<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len() as u32) as usize]
    }
}

// ---------------------------------------------------------------------------
// The calendar, just enough of it: a civil date that steps by one day.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Date {
    pub y: i32,
    pub m: u32,
    pub d: u32,
    /// Monday = 0, as Python's `date.weekday()`.
    pub weekday: u32,
}

impl Date {
    /// 2026-01-01, a Thursday: the scripts' first day.
    pub const START: Date = Date { y: 2026, m: 1, d: 1, weekday: 3 };

    fn month_len(y: i32, m: u32) -> u32 {
        match m {
            2 if (y % 4 == 0 && y % 100 != 0) || y % 400 == 0 => 29,
            2 => 28,
            4 | 6 | 9 | 11 => 30,
            _ => 31,
        }
    }

    pub fn succ(self) -> Date {
        let weekday = (self.weekday + 1) % 7;
        if self.d < Date::month_len(self.y, self.m) {
            Date { d: self.d + 1, weekday, ..self }
        } else if self.m < 12 {
            Date { m: self.m + 1, d: 1, weekday, ..self }
        } else {
            Date { y: self.y + 1, m: 1, d: 1, weekday }
        }
    }

    pub fn iso(self) -> String {
        format!("{:04}-{:02}-{:02}", self.y, self.m, self.d)
    }
}

// ---------------------------------------------------------------------------
// The generator.

/// A generator carrying the scripts' random state across calls, as their
/// module-level `random.seed(7)` does across the four ages.
pub struct LogGen {
    rng: PyRandom,
    rate: Rate,
}

const TAGS: [&str; 5] = [r#"["lean"]"#, r#"["soundcode"]"#, r#"["admin"]"#, "[]", r#"["lean","proof"]"#];

/// Python's `repr(round(m / 60, 2))` for a nonnegative minute count: the
/// nearest hundredth (5m/3 is never a half), with at least one fraction digit.
fn hours_2dp(m: u32) -> String {
    let c = (10 * m + 3) / 6;
    let (whole, frac) = (c / 100, c % 100);
    if frac == 0 {
        format!("{whole}.0")
    } else if frac % 10 == 0 {
        format!("{whole}.{}", frac / 10)
    } else {
        format!("{whole}.{frac:02}")
    }
}

impl LogGen {
    pub fn new(rate: Rate, seed: u32) -> LogGen {
        LogGen { rng: PyRandom::new(seed), rate }
    }

    /// `gen(days)`: `days` consecutive days from 2026-01-01, one compact JSON
    /// line per event, without newlines.
    pub fn days(&mut self, days: u32) -> Vec<String> {
        let mut out = Vec::new();
        let mut d = Date::START;
        for _ in 0..days {
            self.day(d, &mut out);
            d = d.succ();
        }
        out
    }

    /// `day_events(d, 900)`, appended to `out`.
    fn day(&mut self, d: Date, out: &mut Vec<String>) {
        let r = &mut self.rng;
        let off = if (3..=10).contains(&d.m) { "-05:00" } else { "-06:00" };
        let iso = d.iso();
        let t = |h: u32, m: u32| format!("{iso}T{h:02}:{m:02}:00{off}");
        let hm = |mins: u32| (mins / 60, mins % 60);
        let wk = d.weekday < 5;
        let (wh, wm) = if wk { (6, 5) } else { (8, 30) };
        let wake = wh * 60 + wm;

        out.push(format!(r#"{{"t":"{}","ev":"wake","slept_min":{}}}"#, t(wh, wm), r.randint(380, 560)));
        let ah = wh + 1;
        let loc = if r.random() < if wk { 0.85 } else { 0.4 } { "lounge" } else { "home" };
        out.push(format!(
            r#"{{"t":"{}","ev":"arrive","loc":"{loc}","window":["{ah:02}:00","{:02}:00"],"budget":6}}"#,
            t(ah, 0),
            ah + 8
        ));
        let mut mins = ah * 60 + 2;
        let blocks = if wk { r.randint(5, 8) } else { r.randint(2, 4) };
        for b in 0..blocks {
            let iid = r.randint(1, N_IDS);
            let (h, m) = hm(mins);
            let pred = r.randint(2, 5);
            let rep = r.randint(2, 5);
            out.push(format!(
                r#"{{"t":"{}","ev":"start","id":"{iid}","pred":{pred},"rep":{rep},"hsw":{},"slept_min":480,"loc":"{loc}","blocks_done":{b},"since_break_min":{}}}"#,
                t(h, m),
                hours_2dp(mins - wake),
                if b % 2 == 0 { 0 } else { 60 }
            ));
            let dur = r.randint(40, 75);
            if r.random() < 0.25 {
                let (ph, pmm) = hm(mins + r.randint(10, 30));
                out.push(format!(r#"{{"t":"{}","ev":"pause","id":"{iid}"}}"#, t(ph, pmm)));
                out.push(format!(r#"{{"t":"{}","ev":"unpause","id":"{iid}"}}"#, t(ph, 59.min(pmm + 5))));
            }
            if r.random() < 0.15 {
                let (ih, imm) = hm(mins + 20);
                out.push(format!(r#"{{"t":"{}","ev":"interrupt","id":"{iid}"}}"#, t(ih, imm)));
                out.push(format!(
                    r#"{{"t":"{}","ev":"resume","lost_min":15,"dropped":[]}}"#,
                    t(ih, 59.min(imm + 15))
                ));
            }
            if r.random() < 0.1 {
                let (eh, em) = hm(mins + dur - 5);
                out.push(format!(r#"{{"t":"{}","ev":"extend","id":"{iid}","by_min":30}}"#, t(eh, em)));
            }
            mins += dur;
            let (h, m) = hm(mins);
            if r.random() < 0.12 {
                out.push(format!(
                    r#"{{"t":"{}","ev":"stop","id":"{iid}","remaining_min":{}}}"#,
                    t(h, m),
                    r.randint(15, 120)
                ));
            } else {
                let went = r.choice(&[1, 1, 1, 2, 3]);
                let tags = r.choice(&TAGS);
                let ci = r.randint(1, 5);
                let partial = if r.random() < 0.4 { r#","partial":true"# } else { "" };
                out.push(format!(
                    r#"{{"t":"{}","ev":"done","id":"{iid}","est_min":60,"actual_min":{dur},"went":{went},"tags":{tags},"ci":{ci}{partial}}}"#,
                    t(h, m)
                ));
            }
            if b % 2 == 1 {
                let actual = r.randint(15, 35);
                let place = r.choice(&["walk", "seat", "phone"]);
                out.push(format!(
                    r#"{{"t":"{}","ev":"break","planned_min":20,"actual_min":{actual},"where":"{place}"}}"#,
                    t(h, m)
                ));
                mins += 22;
            }
            if r.random() < 0.3 {
                let (eh, em) = hm(mins);
                out.push(format!(
                    r#"{{"t":"{}","ev":"energy","pred":4,"rep":{},"hsw":{},"loc":"{loc}"}}"#,
                    t(eh, em),
                    r.randint(1, 5),
                    hours_2dp(mins - wake)
                ));
            }
            let replans = match self.rate {
                Rate::Forty => r.randint(1, 3),
                Rate::SixtyOne => r.randint(4, 7),
            };
            for _ in 0..replans {
                let (ph, pm) = hm(mins);
                let hash = r.getrandbits(64);
                let drift = r.choice(&[0, 0, 15, 30]);
                out.push(format!(
                    r#"{{"t":"{}","ev":"plan","hash":"{hash:016x}","replans_today":{},"drift_min":{drift}}}"#,
                    t(ph, pm),
                    b + 1
                ));
            }
            mins += r.randint(0, 10);
        }
        for item in ["lunch", "package", "meds"] {
            let (rh, rm) = hm(mins.min(23 * 60));
            if r.random() < 0.8 {
                out.push(format!(
                    r#"{{"t":"{}","ev":"routine","item":"{item}","inst":"{iso}","status":"done","actual_min":{}}}"#,
                    t(rh, rm),
                    r.randint(5, 40)
                ));
            } else if r.random() < 0.5 {
                out.push(format!(r#"{{"t":"{}","ev":"skip","item":"{item}","inst":"{iso}"}}"#, t(rh, rm)));
            }
        }
        for _ in 0..r.randint(0, 3) {
            let (ih, im) = hm(mins.min(23 * 59));
            let attributed = r.choice(&["leak", "work", "break"]);
            out.push(format!(
                r#"{{"t":"{}","ev":"idle","attributed":"{attributed}","min":{}}}"#,
                t(ih, im),
                r.randint(12, 40)
            ));
        }
        if r.random() < 0.2 {
            out.push(format!(r#"{{"t":"{}","ev":"note","text":"felt slow after lunch, try a walk"}}"#, t(21, 0)));
        }
        if r.random() < 0.1 {
            out.push(format!(r#"{{"t":"{}","ev":"event","name":"reply","id":"{}"}}"#, t(20, 0), r.randint(1, N_IDS)));
        }
        if r.random() < 0.3 {
            out.push(format!(
                r#"{{"t":"{}","ev":"edit","id":"{}","field":"est","from":"2b","to":"3b"}}"#,
                t(20, 5),
                r.randint(1, N_IDS)
            ));
        }
        if r.random() < 0.2 {
            out.push(format!(
                r#"{{"t":"{}","ev":"move","id":"{}","from":"backlog","to":"week/2026-W38"}}"#,
                t(20, 6),
                r.randint(1, N_IDS)
            ));
        }
        if r.random() < 0.1 {
            out.push(format!(r#"{{"t":"{}","ev":"drop","id":"{}"}}"#, t(20, 7), r.randint(1, N_IDS)));
        }
        if r.random() < 0.15 {
            out.push(format!(r#"{{"t":"{}","ev":"undo","of":"done"}}"#, t(20, 8)));
        }
        out.push(format!(r#"{{"t":"{}","ev":"close","period":"day","key":"{iso}"}}"#, t(23, 30)));
        for _ in 0..r.randint(0, 2) {
            out.push(format!(
                r#"{{"t":"{}","ev":"demote","id":"{}","from":"{iso}","to":"2026-W38","est_min":120}}"#,
                t(23, 31),
                r.randint(1, N_IDS)
            ));
        }
        if d.weekday == 6 {
            out.push(format!(r#"{{"t":"{}","ev":"close","period":"week","key":"2026-W37"}}"#, t(23, 32)));
            for _ in 0..r.randint(0, 6) {
                out.push(format!(
                    r#"{{"t":"{}","ev":"demote","id":"{}","from":"2026-W37","to":"2026-09","est_min":180}}"#,
                    t(23, 33),
                    r.randint(1, N_IDS)
                ));
            }
        }
    }
}

/// `days` days of log at `rate`, from a fresh seed-7 generator.  For `1mo` this
/// is the design pass's file; the longer ages differ from theirs (the scripts
/// did not reseed between ages; see [`design_logs`]) but have the same shape.
pub fn log(rate: Rate, days: u32) -> Vec<String> {
    LogGen::new(rate, SEED).days(days)
}

/// The design pass's four files at `rate`, generated in the scripts' order
/// from one generator: `[(age, days, lines)]` for 1mo, 6mo, 1y, 3y.
pub fn design_logs(rate: Rate) -> Vec<(&'static str, u32, Vec<String>)> {
    let mut g = LogGen::new(rate, SEED);
    AGES.iter().map(|&(age, days)| (age, days, g.days(days))).collect()
}

/// The lines as file text: one line and one `\n` each, as the scripts wrote.
pub fn text(lines: &[String]) -> String {
    let mut s = String::with_capacity(lines.iter().map(|l| l.len() + 1).sum());
    for l in lines {
        s.push_str(l);
        s.push('\n');
    }
    s
}

/// FNV-1a-64, the digest design §9.8 names for `prefixFnv`.
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}
