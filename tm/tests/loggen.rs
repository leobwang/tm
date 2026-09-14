//! `support/loggen.rs` is the design pass's generator, not a look-alike (stage 5
//! step A3, design §14.1).  Every latency and memory figure in design §1.1 and
//! §18 was taken on the eight files `genlog.py` and `genlog80.py` wrote; these
//! pins are those files' line counts, byte counts and FNV-1a-64 digests, read
//! off the files themselves, so a benchmark over the port measures the same logs.

#[allow(dead_code)]
#[path = "support/loggen.rs"]
mod loggen;

use loggen::{design_logs, fnv1a64, log, text, Rate};

/// `(age, lines, bytes, FNV-1a-64)` of `log-<age>.jsonl` and `log80-<age>.jsonl`.
const FORTY: [(&str, usize, usize, u64); 4] = [
    ("1mo", 1_191, 123_939, 0xf9f8_14c3_d6b4_87b4),
    ("6mo", 7_422, 772_210, 0x3651_ac70_ebf5_8bc6),
    ("1y", 14_941, 1_555_376, 0xdeea_624d_2204_c6bd),
    ("3y", 45_172, 4_702_828, 0x93b6_4b18_ebe2_791c),
];
const SIXTY_ONE: [(&str, usize, usize, u64); 4] = [
    ("1mo", 1_845, 191_478, 0x6db6_afb7_bc75_9e4b),
    ("6mo", 11_172, 1_165_920, 0x70bc_c6a4_3bd0_38f5),
    ("1y", 22_055, 2_293_587, 0xc4e9_276e_02a2_7e4c),
    ("3y", 65_771, 6_857_648, 0x6546_dea4_ad25_b185),
];

#[test]
fn the_generator_reproduces_the_design_passs_eight_logs_byte_for_byte() {
    for (rate, pins) in [(Rate::Forty, FORTY), (Rate::SixtyOne, SIXTY_ONE)] {
        for ((age, _, lines), (pin_age, n, bytes, digest)) in design_logs(rate).into_iter().zip(pins) {
            assert_eq!(age, pin_age);
            let t = text(&lines);
            assert_eq!(
                (lines.len(), t.len(), fnv1a64(t.as_bytes())),
                (n, bytes, digest),
                "{}-{age}.jsonl",
                rate.stem()
            );
        }
    }
}

#[test]
fn every_generated_line_is_one_json_object_naming_its_event() {
    for rate in [Rate::Forty, Rate::SixtyOne] {
        let lines = log(rate, 30);
        // A fresh generator's first month is the first file exactly.
        assert_eq!(lines, design_logs(rate).swap_remove(0).2);
        for l in &lines {
            let v: serde_json::Value = serde_json::from_str(l).unwrap();
            assert!(v["t"].is_string() && v["ev"].is_string(), "{l}");
        }
    }
}
