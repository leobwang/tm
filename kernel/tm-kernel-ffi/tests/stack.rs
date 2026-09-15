//! **T0, design §14.1 and D9-21: every recursion over a list the wire can make
//! large runs in constant stack per element.**  Its own test binary, not
//! `tests/kernel.rs`: `check.sh` check 5 runs only that one, and these requests
//! are megabytes each, so keeping them out keeps `check.sh`'s wall time inside
//! design §14.0 item 4's 10% budget.  `cargo test` in this crate runs both.
//!
//! Stage 5 step A1 (gap 44 closed).  T0 (c) joined at L6 (gap 105 closed); T0 (b) joins at W3.
//! Stage 5 D9 B4 adds the `log` op at the line bound (`readLine`, `renderLine`).

use tm_kernel_ffi::call;

/// Runs `f` on a thread whose stack is exactly 2 MiB, so a test does not lean
/// on the harness's default (`RUST_MIN_STACK` can raise it).
fn on_a_2mib_thread<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// **T0 (a), design §14.1: gap 44 is closed.**  `jarr`/`jtail`, `jobj`/`jotail`,
/// `jemitTail`/`jemitOTail` and `splitDoc` recursed once per element, so before
/// A1 an array of 22,000 strings aborted a 2 MiB thread.  They now run as proved
/// `@[csimp]` accumulator twins (`jtail_eq_jtailAcc`, `jotail_eq_jotailAcc`,
/// `jemitTail_eq_jemitTailAcc`, `jemitOTail_eq_jemitOTailAcc`,
/// `splitDoc_eq_splitDocAcc`).  Arrays of strings: a 200,000-line document is
/// read, split, loaded, written and emitted back byte for byte.  Arrays of
/// objects: 200,000 objects are parsed to the end (the refusal is `run`'s, not
/// the parser's, and the same bytes with the closing `]` removed are refused by
/// the parser at the last element).  The objects sit in a key `run` never reads
/// because `run` appends each document with `++`, quadratic in the document
/// count (README "Stage 5 A1", gap 100).
#[test]
fn a_200000_element_array_reads_on_a_2mib_thread() {
    on_a_2mib_thread(|| {
        let lines: Vec<String> = (0..200_000).map(|i| format!("\"x{i}\"")).collect();
        let lines = lines.join(",");
        let out = call(&format!(r#"{{"docs":[{{"path":"w.md","lines":[{lines}]}}],"cmds":[]}}"#))
            .unwrap();
        assert_eq!(
            out,
            format!(r#"{{"ok":{{"docs":[{{"path":"w.md","lines":[{lines}]}}],"report":{{"closes":[]}}}}}}"#)
        );
    });
    on_a_2mib_thread(|| {
        let objs: Vec<String> =
            (0..200_000).map(|i| format!(r#"{{"path":"d{i}.md","lines":["x"]}}"#)).collect();
        let objs = objs.join(",");
        let out = call(&format!(r#"{{"docs":7,"pad":[{objs}]}}"#)).unwrap();
        assert_eq!(out, r#"{"err":"array expected"}"#);
        let out = call(&format!(r#"{{"docs":7,"pad":[{objs}}}"#)).unwrap();
        assert_eq!(out, r#"{"err":"bad json: expectedCommaOrBracket }"}"#);
    });
}

/// **T0 (a), the object half at scale (W-1 audit repair).**  The test above
/// sends 200,000 two-key objects, so `jotail` never runs past its second key.
/// Here the per-key twin `jotail_eq_jotailAcc` runs at scale: one object of
/// 200,000 keys, then 200,000 one-key objects, each on a 2 MiB thread, each in a
/// key `run` never reads, so the whole request is parsed and an empty `ok`
/// answers.  The same bytes with the object's closing `}` turned into `]` are
/// refused by the parser at the last key, so the parse did reach the end.
///
/// The emit twin `jemitOTail_eq_jemitOTailAcc` is not run at scale here, and
/// no wire request can run it: every object the kernel emits has a key list
/// written out in the source (`runPlanFast`, `reportJson`, `regionJson`,
/// `lerrJson`, `jone`), at most five keys, so `jemitOTail` never recurses more
/// than five times from `call`.  Large *arrays* are what a response carries,
/// and those are `jemitTail`, run by the test above.
#[test]
fn a_200000_key_object_reads_on_a_2mib_thread() {
    const EMPTY_OK: &str = r#"{"ok":{"docs":[],"report":{"closes":[]}}}"#;
    on_a_2mib_thread(|| {
        let keys: Vec<String> = (0..200_000).map(|i| format!(r#""k{i}":{i}"#)).collect();
        let keys = keys.join(",");
        let out = call(&format!(r#"{{"docs":[],"cmds":[],"pad":{{{keys}}}}}"#)).unwrap();
        assert_eq!(out, EMPTY_OK);
        let out = call(&format!(r#"{{"docs":[],"cmds":[],"pad":{{{keys}]}}"#)).unwrap();
        assert_eq!(out, r#"{"err":"bad json: expectedCommaOrBrace ]"}"#);
    });
    on_a_2mib_thread(|| {
        let objs: Vec<String> = (0..200_000).map(|i| format!(r#"{{"k":{i}}}"#)).collect();
        let objs = objs.join(",");
        let out = call(&format!(r#"{{"docs":[],"cmds":[],"pad":[{objs}]}}"#)).unwrap();
        assert_eq!(out, EMPTY_OK);
    });
}

/// A request of `lines` for the `log` op (stage 5 D9 B4), every line asked for a
/// header and, up to 4,096, a rendering; the zone is UTC with no transitions.
fn log_request(lines: &[String], render: usize) -> String {
    let render: Vec<String> = (1..=render.min(lines.len())).map(|n| n.to_string()).collect();
    format!(
        r#"{{"docs":[],"tz":{{"key":"UTC","base":"+00:00:00","then":[]}},"log":{{"ckpt":null,"from":1,"lines":[{}],"terminated":true,"want":{{"headersFrom":1,"render":[{}]}}}}}}"#,
        lines.join(","),
        render.join(",")
    )
}

/// **T0 for the `log` op (stage 5 D9 B4; README gap 101's note).**  `readLine`
/// and `renderLine` end to end on a 2 MiB thread, at the line bound: a string of
/// 65,000 characters, an unknown event's array of 21,000 numerals, an unknown
/// event of 5,000 keys (`restOf`'s merge sort, and `jemitOTail` at scale: the
/// rendering is an object of 5,002 keys, which the A1 test above could not reach
/// from `call`), 64 levels of nesting, an `hsw` of 65,000 fraction digits
/// (`finiteF64` and `JDec.render`), a line one character past the bound
/// (`lineTooLong`), and one nested 65 deep (`lineTooDeep`).  Then 32,768 lines,
/// the per-call bound, each with a header, 4,096 of them rendered.
#[test]
fn the_log_op_reads_and_renders_at_the_line_bound_on_a_2mib_thread() {
    const T: &str = r#"\"t\":\"2026-09-07T06:05:00-05:00\""#;
    on_a_2mib_thread(|| {
        let nums = vec!["1"; 21_000].join(",");
        let keys: Vec<String> = (0..5_000).map(|i| format!(r#"\"k{i}\":{i}"#)).collect();
        let deep = format!("{}1{}", "[".repeat(63), "]".repeat(63));
        let lines = vec![
            format!(r#""{{{T},\"ev\":\"note\",\"text\":\"{}\"}}""#, "y".repeat(65_000)),
            format!(r#""{{{T},\"ev\":\"mood\",\"xs\":[{nums}]}}""#),
            format!(r#""{{{T},\"ev\":\"mood\",{}}}""#, keys.join(",")),
            format!(r#""{{{T},\"ev\":\"mood\",\"x\":{deep}}}""#),
            format!(r#""{{{T},\"ev\":\"energy\",\"pred\":1,\"rep\":1,\"hsw\":0.{}1,\"loc\":\"h\"}}""#, "0".repeat(65_000)),
            format!(r#""{{{T},\"ev\":\"note\",\"text\":\"{}\"}}""#, "y".repeat(65_537)),
            format!(r#""{{{T},\"ev\":\"mood\",\"x\":[{deep}]}}""#),
        ];
        let out = call(&log_request(&lines, 7)).unwrap();
        assert!(out.starts_with(r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":7,"warnings":[{"line":6,"w":"lineTooLong"},{"line":7,"w":"lineTooDeep"}],"facts":null,"headers":[[1,"note",null],[2,"mood",null],[3,"mood",null],[4,"mood",null],[5,"energy",null]],"render":[[1,"{\"t\":\"2026-09-07T06:05:00-05:00\",\"ev\":\"note\",\"text\":\"yyy"#), "{}", &out[..out.len().min(400)]);
        assert!(out.contains(&format!(r#"\"hsw\":0.{}1,"#, "0".repeat(65_000))));
        assert!(out.contains(r#"\"k999\":999}"#), "the last key in serde's order");
        assert!(out.ends_with(r#""2026-09-07 06:05"],[6,null,null],[7,null,null]]}}}"#), "{}", &out[out.len().saturating_sub(200)..]);
    });
    on_a_2mib_thread(|| {
        let lines: Vec<String> = (0..32_768)
            .map(|i| format!(r#""{{{T},\"ev\":\"drop\",\"id\":\"x{i}\"}}""#))
            .collect();
        let out = call(&log_request(&lines, 4096)).unwrap();
        assert!(out.starts_with(r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":32768,"warnings":[],"facts":null,"headers":[[1,"drop","x0"],"#));
        assert!(out.contains(r#"[32768,"drop","x32767"]],"render":[[1,"#));
        assert!(out.ends_with(r#"[4096,"{\"t\":\"2026-09-07T06:05:00-05:00\",\"ev\":\"drop\",\"id\":\"x4095\"}","2026-09-07 06:05"]]}}}"#));
        let mut one_more = lines.clone();
        one_more.push(r#""""#.to_string());
        assert_eq!(call(&log_request(&one_more, 0)).unwrap(), r#"{"err":{"log":"tooManyLines"}}"#);
    });
    // Stage 5 D9 C1: the undo mask at the line bound (`Replay.maskFast`, a `foldl`; the
    // `@[csimp]` twins `survivors_eq_survivorsFast` and `cancelledLines_eq_cancelledLinesFast`).
    // 16,384 drops, each followed by its undo: every line is cancelled.
    on_a_2mib_thread(|| {
        let lines: Vec<String> = (0..32_768)
            .map(|i| {
                if i % 2 == 0 {
                    format!(r#""{{{T},\"ev\":\"drop\",\"id\":\"x{i}\"}}""#)
                } else {
                    format!(r#""{{{T},\"ev\":\"undo\",\"of\":\"drop\",\"id\":\"x{}\"}}""#, i - 1)
                }
            })
            .collect();
        let req = format!(
            r#"{{"docs":[],"tz":{{"key":"UTC","base":"+00:00:00","then":[]}},"log":{{"ckpt":null,"from":1,"lines":[{}],"terminated":true,"want":{{"facts":true}}}}}}"#,
            lines.join(",")
        );
        let start = std::time::Instant::now();
        let out = call(&req).unwrap();
        let all: Vec<String> = (1..=32_768).map(|n| n.to_string()).collect();
        assert_eq!(
            out,
            format!(
                r#"{{"ok":{{"docs":[],"report":{{"closes":[]}},"log":{{"lines":32768,"warnings":[],"facts":{{"cancelled":[{}]}},"headers":[],"render":[]}}}}}}"#,
                all.join(",")
            )
        );
        eprintln!("the mask at the line bound: {:.0} ms", start.elapsed().as_secs_f64() * 1000.0);
    });
}

/// `YYYY-MM-DD` of day `n` after 2026-09-07 (Howard Hinnant's `civil_from_days`,
/// over days since 1970-01-01; 2026-09-07 is day 20,703).
fn date_after_spec_monday(n: i64) -> String {
    let z = 20_703 + n + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + if m <= 2 { 1 } else { 0 };
    format!("{y:04}-{m:02}-{d:02}")
}

/// **T0 (c), design §14.8's L5 row, committed at L6 (gap 105 closed).**  The
/// lookahead of 3,660 days (`Look.maxLookaheadDays`) runs on a 2 MiB thread,
/// through the wire: a zone table of 600 transitions (a Chicago-shaped pair every
/// year over [1900, 2200)), and a calendar wall 12:50–13:50 on every one of the
/// 3,660 days, each indexed once by `wallIndex` and filtered per day by
/// `wallsOn`.  The day range is a `foldl` over core's `List.range`, each day held
/// once (`dayOf_eq_dayOfFast`), and every day is computed before the first seven
/// are emitted (Lean is strict).  The first seven days equal a seven-day request's.
#[test]
fn a_3660_day_lookahead_runs_on_a_2mib_thread() {
    let mut then = Vec::new();
    for y in 1900..2200 {
        then.push(format!(r#"["{y}-03-08T08:00:00Z","-05:00:00"]"#));
        then.push(format!(r#"["{y}-11-01T07:00:00Z","-06:00:00"]"#));
    }
    assert_eq!(then.len(), 600);
    let tz = format!(r#""tz":{{"key":"Chicago-shaped|1900-2200","base":"-06:00:00","then":[{}]}}"#, then.join(","));
    let walls: Vec<String> = (0..3660)
        .map(|i| format!(r#""- [ ] 3 Meeting      at:{d}T12:50/13:50 ^w{i}""#, d = date_after_spec_monday(i)))
        .collect();
    let docs = format!(r#"{{"path":"calendar/walls.md","lines":[{}]}}"#, walls.join(","));
    let capacity = |days: u32| {
        format!(
            concat!(
                r#""capacity":{{"pLounge":{{"config":{{"Mon":{{"num":"9","den":"10"}},"Tue":{{"num":"9","den":"10"}},"Wed":{{"num":"9","den":"10"}},"Thu":{{"num":"9","den":"10"}},"Fri":{{"num":"8","den":"10"}},"Sat":{{"num":"5","den":"10"}},"Sun":{{"num":"4","den":"10"}}}}}},"#,
                r#""arrival":{{"config":{{"Mon":"07:00","Tue":"07:00","Wed":"07:00","Thu":"07:00","Fri":"07:00","Sat":"10:00","Sun":"10:00"}}}},"#,
                r#""wake":{{"sec":21940,"ns":250000000}},"#,
                r#""prior":{{"lounge":[{{"from":{{"num":0,"den":1}},"to":{{"num":1,"den":1}},"level":4}},{{"from":{{"num":1,"den":1}},"to":{{"num":5,"den":1}},"level":5}},{{"from":{{"num":5,"den":1}},"to":{{"num":8,"den":1}},"level":4}},{{"from":{{"num":8,"den":1}},"to":{{"num":10,"den":1}},"level":3}},{{"from":{{"num":10,"den":1}},"level":2}}],"#,
                r#""home":[{{"from":{{"num":0,"den":1}},"to":{{"num":1,"den":1}},"level":3}},{{"from":{{"num":1,"den":1}},"to":{{"num":4,"den":1}},"level":4}},{{"from":{{"num":4,"den":1}},"to":{{"num":8,"den":1}},"level":3}},{{"from":{{"num":8,"den":1}},"level":2}}]}},"#,
                r#""homeMaxCi":3,"day":{{"breakMin":20,"breakAfterBlocks":2,"minLastBlockMin":30,"windowHours":{{"num":8,"den":1}},"windowCap":"19:00","budgetRatio":{{"num":75,"den":100}}}},"#,
                r#""priority":{{"bins":[{{"num":5,"den":10}},{{"num":25,"den":100}},{{"num":1,"den":10}}],"safety":{{"num":13,"den":10}},"defaultPriority":3}},"#,
                r#""days":{days},"day0":[0,0,0,60,170,180]}}"#
            ),
            days = days
        )
    };
    let request = |days: u32| format!(r#"{{"docs":[{docs}],"now":"2026-09-07","blockMin":60,{tz},{}}}"#, capacity(days));
    let long = request(3660);
    let week = request(7);
    on_a_2mib_thread(move || {
        let t = std::time::Instant::now();
        let out = call(&long).unwrap();
        let ms = t.elapsed().as_millis();
        assert!(out.starts_with(r#"{"ok":{"docs":[{"path":"calendar/walls.md""#), "{}", &out[..200.min(out.len())]);
        let look = &out[out.find(r#""lookahead":"#).expect("lookahead key")..];
        assert_eq!(look.matches(r#""day":"#).count(), 7, "{look}");
        let t = std::time::Instant::now();
        let short = call(&week).unwrap();
        let short_ms = t.elapsed().as_millis();
        let short_look = &short[short.find(r#""lookahead":"#).unwrap()..];
        assert_eq!(look, short_look);
        eprintln!("T0 (c): 3,660 days, 600 transitions, 3,660 walls: {ms} ms; the same request for 7 days: {short_ms} ms (2 MiB thread)");
    });
}

/// The T0 (c) request's capacity section (no calendar), with `candidates` when
/// `cands` is non-empty.
fn grants_request(days: u32, cands: &[String]) -> String {
    let mut then = Vec::new();
    for y in 1900..2200 {
        then.push(format!(r#"["{y}-03-08T08:00:00Z","-05:00:00"]"#));
        then.push(format!(r#"["{y}-11-01T07:00:00Z","-06:00:00"]"#));
    }
    let tz = format!(r#""tz":{{"key":"Chicago-shaped|1900-2200","base":"-06:00:00","then":[{}]}}"#, then.join(","));
    let candidates = if cands.is_empty() {
        String::new()
    } else {
        format!(r#","candidates":{{"hysteresis":true,"items":[{}]}}"#, cands.join(","))
    };
    format!(
        concat!(
            r#"{{"docs":[],"now":"2026-09-07","blockMin":60,{tz},"#,
            r#""capacity":{{"pLounge":{{"config":{{"Mon":{{"num":"9","den":"10"}},"Tue":{{"num":"9","den":"10"}},"Wed":{{"num":"9","den":"10"}},"Thu":{{"num":"9","den":"10"}},"Fri":{{"num":"8","den":"10"}},"Sat":{{"num":"5","den":"10"}},"Sun":{{"num":"4","den":"10"}}}}}},"#,
            r#""arrival":{{"config":{{"Mon":"07:00","Tue":"07:00","Wed":"07:00","Thu":"07:00","Fri":"07:00","Sat":"10:00","Sun":"10:00"}}}},"#,
            r#""wake":{{"sec":21940,"ns":250000000}},"#,
            r#""prior":{{"lounge":[{{"from":{{"num":0,"den":1}},"to":{{"num":1,"den":1}},"level":4}},{{"from":{{"num":1,"den":1}},"to":{{"num":5,"den":1}},"level":5}},{{"from":{{"num":5,"den":1}},"to":{{"num":8,"den":1}},"level":4}},{{"from":{{"num":8,"den":1}},"to":{{"num":10,"den":1}},"level":3}},{{"from":{{"num":10,"den":1}},"level":2}}],"#,
            r#""home":[{{"from":{{"num":0,"den":1}},"to":{{"num":1,"den":1}},"level":3}},{{"from":{{"num":1,"den":1}},"to":{{"num":4,"den":1}},"level":4}},{{"from":{{"num":4,"den":1}},"to":{{"num":8,"den":1}},"level":3}},{{"from":{{"num":8,"den":1}},"level":2}}]}},"#,
            r#""homeMaxCi":3,"day":{{"breakMin":20,"breakAfterBlocks":2,"minLastBlockMin":30,"windowHours":{{"num":8,"den":1}},"windowCap":"19:00","budgetRatio":{{"num":75,"den":100}}}},"#,
            r#""priority":{{"bins":[{{"num":5,"den":10}},{{"num":25,"den":100}},{{"num":1,"den":10}}],"safety":{{"num":13,"den":10}},"defaultPriority":3}},"#,
            r#""days":{days},"day0":[0,0,0,60,170,180]{candidates}}}}}"#
        ),
        tz = tz,
        days = days,
        candidates = candidates
    )
}

/// `n` dated candidates at `ci` 3, 600 minutes each, due dates spread evenly
/// over `days` (the shape README gap 106 was measured with).
fn spread_deadlines(n: usize, days: i64) -> Vec<String> {
    (0..n)
        .map(|i| {
            let due = date_after_spec_monday(((i as i64 + 1) * days) / n as i64 - 1);
            format!(
                r#"{{"id":"d{i}","ci":3,"remaining":600,"due":"{due}","window":false,"wall":false,"optional":false,"overdue":false,"mandatory":false,"hot":false}}"#
            )
        })
        .collect()
}

/// **Gap 106, T0 for the EDF pass (stage 5 D10 L8).**  Step 3's `reserveRest`
/// read each day through one closure per earlier reservation, and its day
/// recursions were not tail calls; the pass now runs as a proved `@[csimp]`
/// `foldl` holding each reserved day's six numerators once
/// (`edfGrantsGo_eq_edfGrantsGoFast`).  Through the wire, on a 2 MiB thread:
/// 1, 10, 20, 30 and 40 deadlines over the 3,660-day lookahead (the gap's
/// shape), then 1,024 (`maxCandidates`, the wire's bound).  Each answer carries
/// one grant per candidate, and a deadline's grant does not depend on the
/// deadlines due after it (`edf_a_later_deadline_takes_nothing_from_an_earlier_one`).
///
/// **The time is asserted** (W-3's audit: the test only printed it, and with the
/// seven `@[csimp]` attributes removed 40 deadlines took 18,102 ms and it still
/// passed).  Each call must finish within `GAP_106_MS` for up to 40 deadlines
/// and `GAP_106_MAX_MS` for 1,024; measured 121 ms and 825 ms with the twins,
/// so the bounds leave a loaded machine 40x and 18x, and the bound for 40 is 3.6x
/// under the regression it guards (which grows as the fourth power of the count).
#[test]
fn grants_over_a_3660_day_lookahead_run_on_a_2mib_thread() {
    const GAP_106_MS: u128 = 5_000;
    const GAP_106_MAX_MS: u128 = 15_000;
    on_a_2mib_thread(|| {
        let base = grants_request(3660, &[]);
        let t = std::time::Instant::now();
        let out = call(&base).unwrap();
        let base_ms = t.elapsed().as_millis();
        assert!(!out.contains(r#""grants""#), "{}", &out[..200.min(out.len())]);
        let mut line = format!("gap 106: no candidates {base_ms} ms");
        let grant_of = |out: &str, id: &str| -> String {
            let grants = &out[out.find(r#""grants":"#).unwrap_or_else(|| panic!("{}", &out[..300.min(out.len())]))..];
            let at = grants.find(&format!(r#"{{"id":"{id}""#)).unwrap_or_else(|| panic!("{id}"));
            grants[at..].split('}').next().unwrap().to_string()
        };
        for n in [1usize, 10, 20, 30, 40, 1024] {
            let cands = spread_deadlines(n, 3660);
            let req = grants_request(3660, &cands);
            let t = std::time::Instant::now();
            let out = call(&req).unwrap();
            let ms = t.elapsed().as_millis();
            let bound = if n <= 40 { GAP_106_MS } else { GAP_106_MAX_MS };
            assert!(ms <= bound, "gap 106 regressed: {n} deadlines over 3,660 days took {ms} ms (bound {bound} ms)");
            let grants = &out[out.find(r#""grants":"#).unwrap_or_else(|| panic!("{}", &out[..300.min(out.len())]))..];
            assert_eq!(grants.matches(r#"{"id":"#).count(), n, "{}", &grants[..300.min(grants.len())]);
            // The first-due deadline is served first: its grant is the one it gets alone.
            let alone = call(&grants_request(3660, &cands[..1])).unwrap();
            assert_eq!(grant_of(&out, "d0"), grant_of(&alone, "d0"));
            line.push_str(&format!("; {n} deadlines {ms} ms"));
        }
        eprintln!("{line} (3,660 days, 2 MiB thread)");
    });
}

/// **The floor pass forces the capacity the pass left once per request** (stage 5
/// D10 L8, host half; gap 79).  `withFloor` takes that capacity as a `Thunk`: a
/// strict argument evaluated per candidate ran step 3's pass once per candidate,
/// and 1,024 of them over 3,660 days took 705 s of this suite.  Through the wire,
/// on a 2 MiB thread: 512 dated deadlines and 512 undated candidates with a floor
/// to the lookahead's last day, against the same 1,024 without the floors.  Every
/// floor candidate is answered at its floor, and the dated grants are the same
/// bytes either way (a floor reserves nothing).
#[test]
fn floors_over_a_3660_day_lookahead_force_the_pass_once() {
    on_a_2mib_thread(|| {
        let last = date_after_spec_monday(3659);
        let dated = spread_deadlines(512, 3660);
        let floors: Vec<String> = (0..512)
            .map(|i| {
                format!(
                    r#"{{"id":"f{i}","ci":{},"remaining":60,"due":null,"window":false,"wall":false,"optional":false,"overdue":false,"mandatory":false,"hot":false,"floor":{{"left":{},"until":"{last}"}}}}"#,
                    i % 6,
                    30 + i
                )
            })
            .collect();
        let bare: Vec<String> = floors.iter().map(|f| f.replace(&format!(r#","floor":{{"left":"#), r#","nofloor":{"left":"#)).collect();
        let with = [dated.clone(), floors].concat();
        let without = [dated, bare].concat();
        let t = std::time::Instant::now();
        let a = call(&grants_request(3660, &with)).unwrap();
        let with_ms = t.elapsed().as_millis();
        let t = std::time::Instant::now();
        let b = call(&grants_request(3660, &without)).unwrap();
        let without_ms = t.elapsed().as_millis();
        // Asserted, as gap 106's test is (W-3): 1,076 and 381 ms measured; forcing the
        // pass once per candidate took 705 s.
        assert!(with_ms <= 20_000 && without_ms <= 20_000, "floors {with_ms} ms, without {without_ms} ms (bound 20,000 ms)");
        let grants = |out: &str| out[out.find(r#""grants":"#).expect("grants")..].to_string();
        let (ga, gb) = (grants(&a), grants(&b));
        assert_eq!(ga.matches(r#""class":"#).count(), 1024);
        assert_eq!(ga.matches(&format!(r#""until":"{last}""#)).count() >= 512, true, "{}", &ga[..300]);
        let dated_part = |g: &str| g[..g.find(r#"{"id":"f0""#).expect("f0")].to_string();
        assert_eq!(dated_part(&ga), dated_part(&gb), "a floor reserves nothing");
        assert!(!gb.contains(r#""class":"floor""#));
        eprintln!("floors: 512 deadlines + 512 floors {with_ms} ms; the same without floors {without_ms} ms (3,660 days, 2 MiB thread)");
    });
}
