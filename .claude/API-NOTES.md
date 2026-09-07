# model.rs / grammar.rs / config.rs
## tm_core::model
- `Id(pub String)`: `new`, `as_str`, `token()->"^id"`, `is_empty` (empty = no id yet), `is_valid(&str)`; Display = bare id. `Ref(pub String)`: `token()->"@x"`, `to_id()`.
- `Dur { minutes: u32, unit: DurUnit }`, `DurUnit { Blocks(u32), Minutes, Hours, HoursMinutes, Days }`; ctors `from_minutes`, `hours`, `hours_minutes`, `days`, `blocks(n, block_min)`, `canonical(min)`; `parse(s, block_min)`, `parse_no_days`; `as_minutes`, `as_blocks(block_min)`, `to_chrono`; Display prints the remembered unit. Equality is structural.
- `Moment { Date(NaiveDate), DateTime(NaiveDateTime) }`: `date()`, `to_datetime(default_time)`, `end_of_day()` (23:59), `parse`, Display. Helpers `parse_date/parse_time/parse_datetime`, `fmt_time/fmt_datetime`, `parse_interval(s)->(start,end)` (time-only end = same day, rolls to next day if earlier), `fmt_interval`, `parse_weekday`.
- `YearMonth { year, month }`: `parse("2026-09")`, `from_date`, `first_day/last_day/range/contains/next/prev`, Display. `IsoWeek { year, week }`: `parse("2026-W37")`, `from_date`, `monday/sunday/range/dates/contains/next/prev/short("W37")`, Display.
- `State { Todo, Active, Done, Demoted, Dropped, Waiting }`: `as_str()->"[ ]"`, `glyph`, `parse`, `from_glyph`, `is_open` (Todo|Active), `is_closed` (Done|Dropped).
- `Scope { Finite, Open }`; `Shape { None, Point{due: Moment}, Interval{start,end: NaiveDateTime}, Window{range: WindowRange, dur: Dur} }` + `default_on_miss()`; `WindowRange { Daily{from,to: NaiveTime}, Absolute{from,to} }` + `is_overnight`, `parse`, Display; `Pref { WakePlus(Dur), At(NaiveTime) }`.
- `Recur { None, Calendar(Rule), AfterDone{offset, window: Option<Dur>}, OnEvent{name, timeout: Option<Dur>} }` + `parse_after_done`, `parse_on_event`, `token()`; `Rule { Daily, Weekdays, Weekly(Vec<Weekday>), EveryNDays(u32), EveryNWeeks(u32, Weekday), Monthly(u8), Weeks(u32) }` + `parse`, Display.
- `OnMiss { Expire, Persist, Next }`; `Period { Day, Week, Month }`; `Rate { amount: Dur, per: Period }` (`parse("6b/w", block_min)`); `Budget { floor, cap: Option<Rate> }`; `Dep { Item(Id), Event(String) }` (`parse_list`); `Loc { Any, Lounge, Home, Out, Named(String) }`; `Stamp { Week(u32), Day(u32) }`; `Stamps { demoted: Vec<Stamp>, waiting_since: Option<NaiveDate> }` + `demoted_value()`.
- `Horizon { Backlog, Month(YearMonth), Week(IsoWeek), Day(NaiveDate), Routine, Optional, Calendar(IsoWeek), Inbox }`: `from_path(&str)->Option`, `path()`, `default_ci()` (1/0/3), `is_open_file()`, `allows_missing_state()`.
- `SourceLoc { file: String, line: usize (1-based), section: Option<String>, tokens: grammar::ItemLine }`.
- `Item { id, title, state, ci, ci_explicit, est, est_original, dur, priority, parent: Option<Ref>, horizon, scope, shape, pref, recur, on_miss, budget, splittable, after: Vec<Dep>, loc, buffer, tags, flags, series: Option<(String,u32 /*0-based*/)>, stamps, extra: Vec<(String,String)>, problems: Vec<String>, src }` + `has_id`, `has_flag`, `is_manual`, `is_travel_day`, `is_hot`, `own_remaining()` (est else est_original), `line()->&ItemLine`, `line_text()`.
- `Instance { item: Id, key: InstanceKey, due, window, status }`, `InstanceKey { Date(NaiveDate), Nth(u32) }`, `InstanceStatus { Pending, Done, Missed, Expired, Skipped }`.
- All types: Clone, Debug, PartialEq, Serialize, Deserialize. `ModelError::Invalid{what, value}`.

## tm_core::grammar
- `parse_file(path: &str, text: &str, cfg: &Config) -> ParsedFile`; `serialize_file(&ParsedFile) -> String` (byte-identical when unmodified).
- `ParsedFile { path, horizon, front_matter: Vec<(String,String)>, lines: Vec<Line>, generated: Vec<GeneratedRange>, problems: Vec<Problem> }` + `items()`, `items_mut()`, `find(&Id)`, `line_of(&Id)`, `front(key)`, `generated(name)`, `all_problems()`, `in_generated(line)`, `to_text()`.
- `Line { number, content: LineContent, eol: String }` + `text()`, `item()`; `LineContent { Item(Item), Verbatim(String) }`; `GeneratedRange { name, info, start_line, end_line: Option<usize> }`; `Problem { line (0 = file), message }`.
- `ParseCtx<'a> { file, horizon, block_min, line, section, series }` + `ParseCtx::new(file, block_min)`; `parse_line(text, &ctx) -> Result<Item, ParseError>` (`ParseError::NotAnItemLine`).
- `ItemLine { tokens: Vec<Token>, trailing: String }` (Display = original line); `Token { lead, text, kind: TokenKind }`; `TokenKind { Bullet, State, Ci, Est, Title, Parent, Tag, Priority, Id, Key(String), Flag, Word, Unparsed }`. Methods: `parse(text)`, `index_of`, `key_index` (max/cap alias), `get(key)`, `id()`, `has_flag`, `has_tag`, `set_token(key, value)` (replace in place else insert before ^id else append), `remove_token`, `set_state`, `set_ci`, `remove_ci`, `set_leading_est(Option<Dur>) -> Result<(), EditError>`, `set_title`, `set_priority(Option<u8>)`, `set_parent(Option<&Ref>)`, `add_tag`, `remove_tag`, `add_flag`, `remove_flag`, `append_id(&Id)`. Also `append_id_to_text(text, &Id)`.
- `format_item_line(&Item) -> String` canonical builder (state ci est title @parent #tags !k keys-in-table-order extra flags [ci:N for stateless files] ^id).
- `IdGen::new(seed)` / `from_entropy()`, `candidate()`, `next_id(&mut HashSet<String>) -> Id`; consts `ID_ALPHABET`, `ID_LEN`, `KEYS`, `FLAGS`.

## tm_core::config
- `Config { tz: chrono_tz::Tz, day: DayConfig, week: WeekConfig, priority: PriorityConfig, location: LocationConfig, energy: EnergyConfig, expected: ExpectedConfig, calendar: CalendarConfig, tui: TuiConfig }` — all `#[serde(default)]`, `Default` = §16.
- `Config::parse(&str)`, `load(path)`, `load_or_default(path)`, `to_toml()`, `default_toml() -> &'static str` (also `DEFAULT_TOML`), `block_min()`, `prior_energy(loc, hours_since_wake) -> u8`.
- `DayConfig { block_min, break_after_blocks, break_min, window_hours: f64, window_cap: NaiveTime, budget_ratio, wind_down: NaiveTime, bed: NaiveTime, overtime_reprompt_min, idle_min, min_last_block_min }`; `PriorityConfig { default_priority, bins: Vec<f64>, safety, hysteresis, batch_max_min }`; `LocationConfig { home_max_ci }`; `EnergyConfig { prior_weight, decay_days, duration_prior_weight, posterior_full_hours, posterior_zero_hours, prior: BTreeMap<String, StepFn>, sleep_debt: SleepDebt { under_hours, shift } }`; `ExpectedConfig { arrival: PerWeekday<NaiveTime>, p_lounge: PerWeekday<f64> }`; `CalendarConfig { ics_urls, sync_on_arrive, flight_regex }`; `TuiConfig { palette, min_width, editor }`.
- `StepFn(Vec<Step{from, to: Option<f64>, level}>)` + `from_pairs`, `parse_key`, `key`, `at(hours)`; `PerWeekday<T>` + `from_fn`, `get(Weekday)`, `map`, `try_map`; `hhmm` serde module; `ConfigError { Io, Parse, Serialize }`.

## Deviations (model/grammar/config)
1. `Rule::Weeks(u32)` added to the spec's `Rule` enum: the §4.3 routines example uses `every:week` (laundry, groceries), which no spec variant expresses; `every:week`/`every:Nw` map to it.
2. Three fields added to `Item` beyond §3.1 because the §4.1 grammar has keys with no home in the struct: `dur: Option<Dur>` (bare `dur:` on optional items; also mirrored inside `Shape::Window`), `pref: Option<Pref>`, `buffer: Option<Dur>`. Plus the requested `ci_explicit`, `flags`, `problems`.
3. `Stamps.readopted` (mentioned only in a §3.1 comment, with no grammar key) is omitted; horizon.rs can add a key later.
4. `Shape::Point { due: Moment }` instead of a bare DateTime, so a date-only `due:2026-11-20` is stored as written (`Moment::end_of_day()` gives 23:59 when a datetime is needed).
5. `Id` is a plain newtype and an item without `^id` has an empty `Id` (checked via `has_id()`), rather than `Option<Id>` — keeps the spec's `id: Id` and lets tree/planner index by id after `--fix-ids`.
6. Interval `at:` with a time-only end earlier than the start rolls to the next day (spec says "same-day end"; a red-eye would otherwise be an error). Documented on `parse_interval`.
7. `CalendarConfig::default().ics_urls` contains the §16 placeholder URL so that `default_toml()` parses to exactly `Config::default()` as required; ics.rs should treat a fetch failure of that placeholder gracefully.
8. `series` index is 0-based.

# tree.rs
Module tm_core::tree (all pure; no I/O).

Construction
- Tree::build(files: &[grammar::ParsedFile], cfg: &Config) -> Tree — files keep the order given (that order is the file index used for rank); items keep line order.
- Tree::from_texts(files: &[(&str /*path*/, &str /*text*/)], cfg: &Config) -> Tree — parses with grammar::parse_file then builds.
- Tree::key_of(item: &Item) -> Id — the key an item is addressed by: its ^id; for id-less lines (routines/optional/inbox) the TITLE (Id("lunch"), matching `tm skip lunch`); empty title → "file:line". The stored Item.id stays what the line says (has_id() stays truthful).

Types
- pub struct FileInfo { path: String, horizon: Horizon }
- pub struct Node { key: Id, item: Item /* ci resolved */, file: usize, parent: Option<Id> /* resolved */, root: Id, primary: bool }
- pub enum TreeProblem (thiserror): DuplicateId{id, locations: Vec<(String,usize)>} | DanglingParent{id, parent: Ref, file, line} | DanglingDep{id, dep: Id, file, line} | ParentCycle{ids: Vec<Id>} | DepCycle{ids: Vec<Id>} | MissingId{file, line, title}

Lookup
- files() -> &[FileInfo]; nodes() -> &[Node] (all, incl. shadowed duplicates, in (file,line) order); iter() -> impl Iterator<&Item> (primaries); ids() -> impl Iterator<&Id>; len(); is_empty(); contains(&Id) -> bool
- get(&Id) -> Option<&Item> (primary, ci resolved); node(&Id) -> Option<&Node>; all(&Id) -> Vec<&Item> (every copy, primary first)
- order(&Id) -> Option<(usize /*file idx*/, usize /*line*/)> — the §7.4 rank key; file_of(&Id) -> Option<&FileInfo>

Duplicate rule: same key on several lines → TreeProblem::DuplicateId, EXCEPT the §6.3 case of a week line copied into month/…"# Demoted": the copy outside "# Demoted" is the primary; the archived copies are listed by demoted_copies() -> Vec<&Item>. Children/series only attach to primaries.

Hierarchy (§6.1)
- parent(&Id) -> Option<&Id>; children(&Id) -> &[Id] (ordered by file,line); has_children(&Id) -> bool
- ancestors(&Id) -> Vec<Id> (nearest first; stops before a repeat); descendants(&Id) -> Vec<Id> (DFS pre-order; cycle-safe)
- root(&Id) -> Id (self for a root/unknown; on a parent cycle stops at first repeated node); is_root(&Id); roots() -> &[Id] (dangling-parent items count as roots; cycle members do not); depth(&Id) -> usize
- own_priority(&Id) -> Option<u8> (the line's !k); root_priority(&Id) -> u8 (ROOT's !k else cfg.priority.default_priority; !k on non-roots ignored)
- tags_effective(&Id) -> Vec<String> (own then ancestors', deduped)
- Resolved at build: item.ci = nearest ancestor with ci_explicit, else file default (ci_explicit stays false).

Derived shape (§3.2, §6.4)
- effective_shape(&Id) -> Shape — as written; a shape-None item walks up through shape-None ancestors: if the first ancestor with a written shape is an Interval → Point{due: Moment::DateTime(interval.start)} (any depth below the interval). A Point or Window ancestor derives nothing (stays None).
- effective_due(&Id) -> Option<NaiveDateTime> — Point due (bare date → 23:59 via Moment::end_of_day), Interval start, else None (windows, undated).
- is_prep(&Id) -> bool; prep_children(interval: &Id) -> Vec<Id> (direct shape-None children); prep_need(interval: &Id) -> u32 minutes (Σ remaining of prep children).

Rollups (§6.4) — minutes as u32
- remaining(&Id) -> Option<u32>: est → est_original → dur (Item::own_remaining) → Σ children (recursive); Some(0) for Done/Dropped; None when no estimate anywhere (unknown id → None).
- planned_minutes(&Id) -> Option<u32>: est_original (or dur) else Σ children; ignores state and est: (progress denominator).
- done_minutes(&Id, done_by_item: &HashMap<Id,u32>) -> u32 (own + all descendants).
- progress(&Id, done_by_item) -> Option<f64> = done_minutes / planned_minutes.

Series (§5.4)
- series_names() -> impl Iterator<&str> (sorted); series_members(name) -> &[Id]; series_of(&Id) -> Option<(&str, u32)>
- series_head(name) -> Option<Id> (first member not Done/Dropped); series_heads() -> Vec<Id> (name order)
- is_series_active(&Id) -> bool (true ONLY for the head; false for other members and for items outside any series); series_suppressed(&Id) -> bool (member and not head); implied_dep(&Id) -> Option<Id> (previous line of the section).

Dependencies (§5.5)
- deps(&Id) -> &[Dep] (as written); all_deps(&Id) -> Vec<Dep> (plus implied series dep)
- deps_satisfied(&Id, done: &HashSet<Id>, events: &HashSet<String>) -> bool; blocked_by(&Id, done, events) -> Vec<Dep> (unsatisfied, line order, implied last). Dep::Item satisfied when done contains it OR the tree has it State::Done (the implied series dep also when the previous line is Dropped); Dep::Event satisfied when events contains the name. Unknown ids have no deps.
- dep_cycles() -> Vec<Vec<Id>>; parent_cycles() -> Vec<Vec<Id>> — each cycle once, rotated to start at the smallest id; edges point child→parent / item→dependency.

Checks (for check.rs)
- dangling_parents() -> &[(Id, Ref)]; dangling_deps() -> Vec<(Id, Id)>; duplicate_ids() -> Vec<(Id, Vec<(String,usize)>)>; demoted_copies() -> Vec<&Item>; missing_ids() -> Vec<&Item> (no ^id outside routines/optional/inbox); problems() -> Vec<TreeProblem> (all of the above + cycles).

Candidate sources (§6.2)
- day_candidate_ids(today: NaiveDate, this_week: IsoWeek) -> Vec<Id>: items in week/<this_week> + day/<today> "# Pinned" section + backlog.md + every series head anywhere; state ∈ {Todo, Active}; non-head series members removed; (file,line) order. Eligibility (deps/waiting/loc/caps) is the caller's filter. For plan-basic on 2026-09-07/W37: m1 m2 m3 m4 d1 x1 x2 t1 t3 t4 t5 a1 a3 d2 c2 p1.
- routine_ids() / optional_ids() -> Vec<Id> (title keys, open state); calendar_ids(week: IsoWeek) -> Vec<Id> (open state)
- week_items(IsoWeek) -> Vec<&Item>; month_items(YearMonth) -> Vec<&Item> (any state, # Demoted copies included); items_in(path: &str) -> Vec<&Item> (exact path, else same horizon)
- waiting_ids() -> Vec<Id> ([?] anywhere)
- overdue(now: NaiveDateTime) -> Vec<Id>: Todo/Active, recur == None, on_miss == Persist, effective Point due (end_of_day) < now or Interval end < now; calendar/ walls excluded.
- month_items_with_est_and_no_children() -> Vec<Id> (month items outside # Demoted / not Demoted with est_original or est and no children — the §6.2 check warning input).

## Deviations (tree)
1. Id-less lines (routines.md, optional.md, inbox.md) are keyed by their TITLE (Id("lunch")) so routine_ids()/optional_ids() can return Ids and match the CLI's `tm skip <name>` / `tm routine done <name>`; Item.id itself stays empty. A title that equals a real id elsewhere is reported as a duplicate.
2. Derived prep shape: chosen the "nearest Interval ancestor through a chain of shape-None items" rule (any depth), documented; an explicit Point or Window ancestor derives nothing for its shape-less children (spec §3.2 only names Interval).
3. The §6.3 duplicate (^m2 in week/ and month/#Demoted in the plan-basic fixture) is treated as sanctioned: the non-#Demoted copy is primary, the archive copy is exposed via demoted_copies() and is NOT a DuplicateId problem.
4. remaining() returns Some(0) for Done/Dropped items (so parent sums exclude finished children) and Option<u32> minutes rather than a Dur (a sum has no natural unit; callers use Dur::blocks/canonical when writing est:).
5. overdue() excludes calendar/ intervals (synced walls simply pass) and recurring items (their instances expire/persist per §5.3), and uses the effective (derived) due so a prep child is overdue once its exam has started.
6. Dep satisfaction also consults the tree's own state (a dep on a line that is [x] in the file is satisfied without the done set); a dep on a Dropped line is NOT satisfied except for the implied series dep (the head skips dropped lines).
7. is_series_active(id) is true only for the head (false for items outside any series); series_suppressed(id) is the planner-facing "hide this" predicate.
8. Added planned_minutes(), is_prep(), prep_children(), all_deps(), implied_dep(), series_suppressed(), missing_ids(), demoted_copies(), problems()/TreeProblem beyond the listed scope, as small helpers check.rs/priority.rs will need.

NOTE: tree.rs was later revised: the duplicate-id primary-copy rule now follows the §6.3 lifecycle (live line wins over [-] archive copies) and ci inheritance uses the parent's RESOLVED ci. Read the file for current behavior.

# store.rs
Module `tm_core::store` (paths are relative to the plan root, `/`-separated, e.g. `week/2026-W37.md`, `.tm/state.json`).

CONSTANTS: `CONFIG_PATH = "config.toml"`, `STATE_PATH = ".tm/state.json"`, `MODEL_PATH = ".tm/model.json"`, `LOG_PATH = ".tm/log.jsonl"`, `MAX_FILE_ATTEMPTS: usize = 3`.

ERRORS: `enum StoreError { Io{path,source}, Parse{path,line,message}, NotFound(Id), Conflict{id: Id, file: String, ours: String, theirs: String}, Json{path,source}, Toml(ConfigError) }` + `is_conflict()`, `is_not_found()`. `Conflict.id` is empty for a whole-file edit, and `ours`/`theirs` are then whole file texts (CLI exit code 3).

TRAIT (object-safe; `&dyn Store` works):
```rust
pub trait Store {
    // primitives implementors supply
    fn list_files(&self) -> Result<Vec<String>, StoreError>;   // *.md in tree order
    fn read_text(&self, rel: &str) -> Result<String, StoreError>;
    fn write_file(&self, rel: &str, text: &str) -> Result<(), StoreError>;
    fn exists(&self, rel: &str) -> bool;
    fn abs_path(&self, rel: &str) -> Option<PathBuf>;
    // provided
    fn append_text(&self, rel: &str, text: &str) -> Result<(), StoreError>;      // .tm/log.jsonl
    fn read_config(&self) -> Result<Config, StoreError>;                          // defaults when missing
    fn modify_line(&self, rel: Option<&str>, id: &Id, ours: &str, edit: &mut LineEdit<'_>) -> Result<(), StoreError>;
    fn modify_file(&self, rel: &str, edit: &mut FileEdit<'_>) -> Result<(), StoreError>;
    fn read_tree(&self) -> Result<PlanFiles, StoreError>;
    fn read_file(&self, rel: &str) -> Result<ParsedFile, StoreError>;
    fn write_line(&self, id: &Id, new_text: &str) -> Result<(), StoreError>;      // §1.3
    fn write_line_in(&self, rel: Option<&str>, id: &Id, new_text: &str) -> Result<(), StoreError>;
    fn remove_line(&self, id: &Id) -> Result<String, StoreError>;                 // returns the removed text
    fn remove_line_in(&self, rel: Option<&str>, id: &Id) -> Result<String, StoreError>;
    fn reorder_line(&self, id: &Id, delta: i32) -> Result<bool, StoreError>;      // TUI J/K, within the section
    fn move_line(&self, id: &Id, to_rel: &str, section: Option<&str>) -> Result<(), StoreError>;
    fn move_line_from(&self, from: Option<&str>, id: &Id, to_rel: &str, section: Option<&str>) -> Result<(), StoreError>;
    fn append_to_section(&self, rel: &str, heading: &str, line: &str) -> Result<(), StoreError>;   // "## Log" or "Log"
    fn insert_line(&self, rel: &str, section: Option<&str>, text: &str) -> Result<(), StoreError>;
    fn replace_generated(&self, rel: &str, name: &str, body: &str) -> Result<(), StoreError>;
    fn replace_generated_stamped(&self, rel: &str, name: &str, info: Option<&str>, body: &str) -> Result<(), StoreError>;
    fn ensure_file(&self, rel: &str, initial: &str) -> Result<bool, StoreError>;  // true = created
    fn ensure_horizon_file(&self, h: &Horizon) -> Result<bool, StoreError>;
    fn load_state(&self) -> Result<RuntimeState, StoreError>;                     // missing → default
    fn save_state(&self, state: &RuntimeState) -> Result<(), StoreError>;
}
pub trait StoreExt: Store {   // blanket impl for every Store, dyn Store included
    fn read_json<T: DeserializeOwned>(&self, rel: &str) -> Result<Option<T>, StoreError>;
    fn write_json<T: Serialize>(&self, rel: &str, value: &T) -> Result<(), StoreError>;
}
pub type LineEdit<'a> = dyn FnMut(&ParsedFile, usize) -> Result<Option<String>, StoreError> + 'a;
pub type FileEdit<'a> = dyn FnMut(&ParsedFile) -> Result<Option<String>, StoreError> + 'a;
```
Semantics worth knowing: `write_line` requires one item line with the same `^id` (an id-less line may gain one) — anything else is `Parse`; writing identical text is a no-op; a missing horizon file is created with its front matter by `insert_line`/`append_to_section`/`replace_generated`; `move_line` writes the destination first, then removes the source (never loses a line); `reorder_line` moves only among the item lines of the line's own section and returns false when clamped.

STORES:
```rust
pub struct FsStore;  FsStore::new(root: impl Into<PathBuf>) -> FsStore; .root() -> &Path; .abs(rel) -> PathBuf;
                     .with_before_write_hook(BeforeWriteHook) -> FsStore;   // Box<dyn Fn(&Path, usize /*attempt*/) + Send + Sync>
pub struct MemStore;  MemStore::new(); ::from_dir(dir) -> Result<MemStore, StoreError>;
                      .with_file(rel, text) -> MemStore (builder); .insert/.remove/.text/.paths/.snapshot(); Clone + Debug
```
`FsStore` writes atomically (temp file in the same dir + rename) and guards every mutation: `modify_line` re-reads, matches the line by id, checks mtime **and** content hash, retries once, then `Conflict`; `modify_file` re-applies the edit to a racing writer's version up to 3 times.

READING:
```rust
pub struct PlanFiles { pub config: Config, pub files: Vec<ParsedFile> }   // tree order: month, week, backlog, routines, optional, calendar, day, inbox, other
impl PlanFiles { fn file(&self, rel) -> Option<&ParsedFile>; fn items(&self) -> impl Iterator<Item=&Item>;
                 fn locate(&self, id: &Id) -> Option<Location>; fn find(&self, id: &Id) -> Option<&Item>;
                 fn file_of(&self, id: &Id) -> Option<&str>; fn ids(&self) -> HashSet<String>; fn tree(&self) -> Tree }
pub struct Location { pub file: usize, pub line: usize }   // 0-based line index = line number - 1
```
Ids: an id-less line (routines/optional/inbox) is addressed by the title key `Tree::key_of` gives it (`Id("lunch")`); when an id is on several lines, the copy **outside** a `# Demoted` section is the one edited (use the `_in`/`_from` variants to target the other).

PURE TEXT TRANSFORMS (`store::edit`, usable for previews without writing): `front_matter_len`, `headings -> Vec<Heading{index,level,text}>`, `section_range(parsed, idx) -> (usize, usize)`, `is_demoted`, `find_line(parsed, &Id) -> Option<usize>`, `replace_line`, `remove_line -> (String, String)`, `reorder_line -> Option<String>`, `append_to_section`, `append_to_end`, `replace_generated(parsed, name, info, body)`, `start_marker`/`end_marker`, `validate_replacement`.

PATHS: `horizon_path(&Horizon) -> String`, `initial_text(&Horizon) -> String` (month `---\nmonth: …\n---\n`; week adds `window: a..b`; day adds `![day](YYYY-MM-DD.svg)`), `file_rank(rel) -> u8`, `sort_files(&mut Vec<String>)`, `is_plan_file(rel) -> bool` (`*.md`, no dot-directories, not `CLAUDE.md`).

RUNTIME STATE (§10.2, serde-exact, field order as in the spec, every field defaulted, unknown fields ignored):
```rust
pub struct RuntimeState { pub date: Option<NaiveDate>, pub wake: Option<NaiveTime>, pub arrival: Option<NaiveTime>,
    pub loc: Option<String>, pub window: Option<(NaiveTime, NaiveTime)>, pub budget: Option<u32>,
    pub active: Option<ActiveBlock>, pub break_: Option<BreakState> /*"break"*/, pub interrupt: Option<InterruptState>,
    pub last_plan_hash: Option<String>, pub priorities_yesterday: BTreeMap<Id, u8>, pub closed: Closed }
pub struct ActiveBlock { pub id: Id, pub started: NaiveTime, pub est_min: u32, pub paused: bool }
pub struct BreakState { pub started: Option<NaiveTime>, pub planned_min: u32, pub place: Option<String> /*"where"*/ }
pub struct InterruptState { pub started: Option<NaiveTime>, pub id: Option<Id> }
pub struct Closed { pub day: Option<NaiveDate>, pub week: Option<IsoWeek>, pub month: Option<YearMonth> }
```
Times serialize as `"HH:MM"`, the window as `["07:00","16:00"]`, week/month as `2026-W36`/`2026-08`; serde helper modules `opt_hhmm`, `opt_window`, `opt_str` are public for reuse.

## Deviations (store)
1. Whole-file edits are guarded too (new `Store::modify_file` + `MAX_FILE_ATTEMPTS`). §1.3 only mandates the guard for `write_line`; extending it to `append_to_section`/`insert_line`/`replace_generated` prevents tm from clobbering a concurrent save of the same file, and the retry is a clean merge (the edit is re-applied to the other writer's text). `MemStore` keeps the plain read-edit-write default, so the planner's purity tests are unaffected.
2. Two additions beyond the listed scope, both small and documented: `write_line_in`/`remove_line_in`/`move_line_from` (address one file's copy of a duplicated id — horizon.rs needs this for `# Demoted` copies and `tm readopt`) and `append_text` (O_APPEND on FsStore) so log.rs can extend `.tm/log.jsonl` through the trait and use MemStore in tests.
3. The race hook is `FsStore::with_before_write_hook(Box<dyn Fn(&Path, usize) + Send + Sync>)`, always compiled (not behind cfg(test)) — integration tests in tests/ link the normal lib, so a cfg(test) hook would be invisible to them. The scope suggested `with_test_hook`; the name differs, the mechanism is the one asked for.
4. Duplicate ids: the store's own rule is "prefer the copy outside a `# Demoted` section, else the first match in tree order", implemented locally in `store::edit::find_line`/`choose`. It deliberately does not depend on `tree.rs`'s primary-copy rule (which is being revised upstream); if tree.rs settles on a different rule, this one line of policy is the place to align it.
5. `CLAUDE.md` is excluded from `read_tree` (it is documentation, not a plan file), as are all dot-directories (`.tm/`, `.claude/`, `.git/`). `MemStore::from_dir` deliberately loads `.tm/` files too, so fixture trees with a state/log can be tested in memory.
6. `Conflict` doc/field meanings were widened (`ours`/`theirs` are the line texts for an id edit, whole file texts with an empty `id` for a file edit); the Display message changed accordingly.
7. `FsStore::list_files` returns an `Io` error when the plan root does not exist (rather than an empty tree); the CLI/`tm init` decides what to do about a missing `plan/`.

# log.rs
Module `tm_core::log` (all items documented; file opens with an "API overview" doc comment).

EVENTS
- `pub enum Event` — `#[serde(tag = "ev")]`, one variant per §10.1 kind with the spec's exact JSON field names: `Wake{slept_min: u32, onset_min: Option<u32>}`, `Arrive{loc: String, window: [String;2], budget: u32}`, `Start{id, pred: u8, rep: Option<u8>, hsw: f64, slept_min: u32, loc: String, blocks_done: u32, since_break_min: u32}`, `Done{id, est_min, actual_min, went: Option<u8>, tags: Vec<String>, ci: u8, partial: bool}`, `Extend{id, by_min}`, `Stop{id, remaining_min}`, `Break{planned_min, actual_min: Option<u32>, r#where: Option<String>}` (JSON key `where`), `Energy{pred, rep, hsw, loc}`, `Interrupt{id: Option<String>}`, `Resume{lost_min, dropped: Vec<String>}`, `Pause{id}`, `Unpause{id}`, `Idle{attributed: String, min}`, `Routine{item, inst, status, actual_min: Option<u32>}`, `Skip{item, inst}`, `Plan{hash, replans_today, drift_min}`, `Named{name, id: Option<String>}` (tag `event`), `Demote{id, from, to, est_min}`, `Readopt{id}`, `Move{id, from, to}`, `Drop{id}`, `Edit{id, field, from, to}`, `Note{text}`, `Loc{loc}`, `Close{period, key}`, `Undo{of, id: Option<String>}`, plus `Unknown{ev: String, rest: serde_json::Map}` (lossless round-trip; a KNOWN name with a bad payload is a parse error naming the event and field, never `Unknown`).
- `pub const EVENT_NAMES: &[&str]` (26 tags, §10.1 order). `Event::name() -> &str`, `Event::primary_id() -> Option<&str>` (what `undo{id}` matches), `Event::is_state_change() -> bool` (false for plan/note/undo/unknown), `Event::is_leak()`.
- `pub struct LogEntry { pub t: DateTime<FixedOffset>, #[serde(flatten)] pub ev: Event }` with `new`, `to_json() -> Result<String, serde_json::Error>`, `parse(&str)`, `local(tz)`, `calendar_date(tz)`.
- `pub fn fmt_timestamp(&DateTime<FixedOffset>) -> String` (RFC 3339, whole seconds, offset), `pub fn parse_timestamp(&str)` (RFC 3339 or `…THH:MM±HH:MM`).
- `pub enum LogError { Read{path, source}, Write{path, source}, Json(serde_json::Error) }` (thiserror).

LOG
- `pub struct Log { pub entries: Vec<LogEntry>, pub warnings: Vec<LogWarning> }`, `LogWarning{line, text, error}` (Display).
- `Log::new/from_entries/parse(text)/read(path)` (missing file → empty, malformed lines → warnings, only I/O is an error), `Log::append(path, &LogEntry)` / `append_all` (creates `.tm/`, one object per line), `push/len/is_empty/to_jsonl/iter`.
- Undo: `Log::undo_mask() -> UndoMask{cancelled: Vec<bool>, dangling: Vec<usize>}` (+`pairs()`), free fn `undo_mask(&[LogEntry])`, `Log::effective()`, `Log::undo_target() -> Option<&LogEntry>`, `Log::compensating_undo() -> Option<Event>`.
- Iteration (undo applied): `iter_day(date, tz)`, `iter_range(from, to, tz)`, `iter_item(id)`, `day_index(tz)`, `replay(range: Option<RangeInclusive<NaiveDate>>, tz) -> Replay`.

DAYS
- `pub fn hours_since_wake(&DateTime<A>, &DateTime<B>) -> f64` (rounded to 0.01, the `hsw` field), `pub fn local_midnight(date, tz)`.
- `pub struct DayIndex` — `new(tz, wakes)`, `tz/wakes/calendar_date/last_wake_before/day_of(t)/wake_of(date)/bounds(date) -> (start, end)`. Day = wake to next wake; a wake ≥ 24 h old is stale and the instant falls back to its calendar date in `tz`.

REPLAY
- `pub fn replay(entries: &[LogEntry], range: Option<RangeInclusive<NaiveDate>>, tz: Tz) -> Replay` (applies the undo mask first; the block machine runs over every surviving entry, only in-range results are kept).
- `pub struct Replay { tz, range, days: BTreeMap<NaiveDate, DayReplay>, items: BTreeMap<String, ItemReplay>, instances: BTreeMap<String, BTreeMap<String, InstanceRecord>>, energy: Vec<EnergyObs>, durations: Vec<DurationObs>, interrupts: Vec<Interruption>, events: BTreeMap<String, Vec<NamedEvent>>, demotions: BTreeMap<String, Vec<Demotion>>, closes: Vec<CloseRecord>, dropped_items, done_items, last_done, done_dates, longest_leak: Option<LeakRecord>, open_block: Option<OpenBlock>, open_interrupt, unknown: u32, warnings: Vec<String> }` — Serialize/Deserialize for `--json`.
- Accessors: `day(date)`, `block_minutes(id)`, `block_minutes_on(id, date)`, `blocks_done(date)`, `block_minutes_on_day(date)`, `leak_min(date)`, `lost_min(date)`, `is_done(id)`, `last_done(id) -> Option<DateTime<FixedOffset>>` (after-done recurrence), `done_dates(id) -> Vec<NaiveDate>` (calendar instances), `instance(item, inst)`, `instance_status(item, inst) -> InstanceStatus` (Pending when unlogged), `instances_of(item)`, `events_named(name)`, `events_for(id)`, `event_occurred(name, since, id)`, `stamps(id) -> Vec<Stamp>`, `energy_on(date)`, `durations_on(date)`, `interrupts_on(date)`, `breaks()`, `total_block_min()`, `done_minutes_map() -> HashMap<Id, u32>` (feeds `tree::done_minutes`, §6.4).
- `DayReplay { date, wake, slept_min, onset_min, arrival, loc, window, budget, loc_changes, first_start, starts: Vec<StartRecord>, block_min, blocks_done, load, minutes_by_ci: [u32;6], done: Vec<String>, lost_min, dropped, leak_min, longest_leak, idle: Vec<IdleRecord>, breaks: Vec<BreakRecord>, routine_min, plans, replans_today, drift_min, last_plan_hash, segments: Vec<LogSegment> }` with `wake_to_arrive_min()`, `arrive_to_start_min()`, `break_min()`, `high_ci_min()`, `gaps(min_min) -> Vec<(DateTime, DateTime)>`, `gap_min(min_min)`.
- `ItemReplay { id, minutes, blocks, minutes_by_day, done_at, partial_done_at, stops, extended_min }`.
- Records: `LogSegment{start, end, kind: SegmentKind}` (+`minutes()`), `SegmentKind::{Block, Pause, Interrupt, Break, Routine, Idle}`, `EnergyObs{t, day, pred, rep, hsw, loc, slept_min, went, id, from_start}` (+`delta()`, `weight()` — went 3 → 2.0, went 2 → 1.5), `DurationObs{t, day, id, ci, tags, est_min, actual_min, went, partial}` (+`ratio()`), `BreakRecord` (+`actual_or_planned()`), `IdleRecord`, `Interruption`, `NamedEvent`, `Demotion{…, stamp: Option<Stamp>}`, `CloseRecord`, `InstanceRecord{t, status, raw_status, actual_min}`, `LeakRecord`, `OpenBlock{id, started, worked_min, since, paused}` (+`worked_min_at(now)`), `StartRecord`.
- Helpers: `pub fn parse_instance_status(&str) -> Option<InstanceStatus>`, `pub fn stamp_from_key(&str) -> Option<Stamp>` (`2026-W37` → `W37`, `2026-09-07` → `D07`).

Block-minute conventions: `done.actual_min` is authoritative; a block cut by `stop` or by another `start` gets partial credit for worked minutes (elapsed minus paused and interrupted time); a block still open at the end of the log gets none and appears as `open_block`; a retro `done` with `actual_min: 0` marks the item done without a block or duration observation.

## Deviations (log)
1. `DayIndex` caps the wake-to-wake day at 24 h: past that the wake is stale and an entry falls back to its calendar date in `tz`. The spec only says "one row per 24h from wake to wake" (§12.1); the cap is what stops a missing `wake` from merging two calendar days into one 48 h day. `bounds()` is defined to agree with `day_of()` exactly, so days tile; the fixture test's contrary expectation was the failure I fixed.
2. `load` and `minutes_by_ci` (§11 energy mix) are summed over `done` events only, because `stop` carries no `ci`. So on a day with a stopped block they are less than `block_min` (fixture day 1: 323 vs 368). Documented on the fields.
3. `Replay` counts a `done` as a block when `actual_min > 0`, so a retro `tm done ^id` (`actual_min: 0`) marks the item done but adds no block, minutes or duration observation. Spec-implied (§13 "retro, no timing"), not spelled out.
4. §11's leak ledger also wants "unattributed gaps > idle_min", which needs `config.day.idle_min` and belongs to `review.rs`; `log.rs` supplies the raw material as `DayReplay::gaps(min_min)`/`gap_min` rather than folding it into `leak_min` (which stays exactly the `idle{attributed:"leak"}` minutes the scope asked for).
5. Unknown *extra* keys on a KNOWN event are dropped (serde default), so such a line does not round-trip byte-identically; only wholly unknown `ev` names are preserved verbatim via `Event::Unknown`.
6. Kept the previous agent's two WIP commits and added one commit on top rather than rewriting history (no rebase/reset).

# ics.rs
All in `tm_core::ics`.

Types:
- `struct CalEvent { uid: String, summary: String, start: NaiveDateTime, end: NaiveDateTime, location: Option<String>, all_day: bool, recurring: bool }` (Clone/Debug/PartialEq/Eq/Serialize/Deserialize). Times are naive wall-clock in `config.tz`. Methods: `id() -> Id`, `minutes() -> i64`, `overlaps(from, to) -> bool`, `week() -> IsoWeek` (the calendar file it belongs in = ISO week of `start`).
- `struct IcsFeed { events: Vec<CalEvent>, warnings: Vec<String> }`
- `struct ParseOptions { tz: Tz, window: Option<(NaiveDateTime, NaiveDateTime)> }` with `ParseOptions::new(tz)`, `.window(from, to)`, `ParseOptions::for_week(tz, week)`; `Default` = UTC + no window.
- `enum EventKind { Flight, Lecture, Other }` with `.ci() -> u8` (1/2/3).
- `struct SyncResult { files: Vec<(IsoWeek, String)>, events: Vec<CalEvent>, warnings: Vec<String> }`
- `enum IcsError { Fetch{url,source}, Body{url,source}, Parse(String), NotFound(String) }` (thiserror).
- consts: `MAX_UNWINDOWED_OCCURRENCES: u32 = 1000`, `CAL_ID_LEN: usize = 6`, `FLIGHT_BUFFER: &str = "2h"`, `FETCH_TIMEOUT_SECS: u64 = 20`.

Functions:
- `parse_ics(text: &str) -> Result<Vec<CalEvent>, IcsError>` (UTC, no window — convenience only)
- `parse_ics_with(text: &str, opts: &ParseOptions) -> Result<Vec<CalEvent>, IcsError>`
- `parse_ics_report(text: &str, opts: &ParseOptions) -> Result<IcsFeed, IcsError>`
- `window_for_week(week: IsoWeek) -> (NaiveDateTime, NaiveDateTime)` — `[Monday(week-1) 00:00, Monday(week+2) 00:00)`
- `sync_weeks(week: IsoWeek) -> [IsoWeek; 3]`
- `events_in_window(events: Vec<CalEvent>, from: NaiveDateTime, to: NaiveDateTime) -> Vec<CalEvent>`
- `stable_id(uid: &str, occurrence_start: Option<NaiveDateTime>) -> Id`
- `classify_event(summary: &str, flight_re: Option<&Regex>) -> EventKind`
- `render_calendar_lines(events: &[CalEvent], cfg: &Config, week: IsoWeek) -> Vec<String>`
- `merge_calendar_file(existing_text: Option<&str>, new_lines: &[String]) -> String`
- `fetch(url: &str) -> Result<String, IcsError>` (ureq, 20s timeout)
- `trait Fetcher { fn fetch(&self, url: &str) -> Result<String, IcsError>; }`; `struct HttpFetcher`; `struct StaticFetcher` (`::new().with(url, text)`)
- `sync<F: Fetcher + ?Sized>(fetcher: &F, cfg: &Config, today: NaiveDate, existing: &[(IsoWeek, String)]) -> Result<Vec<(IsoWeek, String)>, IcsError>`
- `sync_report<F: Fetcher + ?Sized>(...) -> Result<SyncResult, IcsError>`

Typical CLI use (`tm sync-cal`, `tm arrive` when `cfg.sync_on_arrive_possible()`): read the three existing `calendar/<week>.md` texts, call `sync(&HttpFetcher, &cfg, today, &existing)`, write each returned `(week, text)` to `calendar/<week>.md` (`ics.rs` does no file I/O; a returned empty string means an empty file). Re-running with the files just written reproduces them byte for byte.

## Deviations (ics)
1. `parse_ics(text)` is kept with the scope's signature but needs a target zone and an expansion window to be useful, so the real entry points are `parse_ics_with`/`parse_ics_report` taking `ParseOptions { tz, window }`; bare `parse_ics` = UTC, no window (capped at `MAX_UNWINDOWED_OCCURRENCES` per rule).
2. Flight detection order: §15/the scope say "flight_regex OR ✈", but the §16 default regex `\b[A-Z]{2} ?\d{2,4}\b` matches course codes — `CS 234 lecture` (the §4.3 example that must be ci 2, no buffer) is a literal match. So `classify_event` checks the lecture words first (lecture/lectures/class/seminar/recitation/colloquium/tutorial/webinar, whole-word, case-insensitive) and only then the flight test. This is the ci rule: flight 1, lecture 2, everything else 3. An unparseable `flight_regex` degrades to ✈-only instead of failing the sync.
3. Summaries are made safe for the §4.1 title rule rather than emitted raw: a word that would parse as a token (`@lab`, `#ops`, `!2`, `^x`, `key:value`) — or, in first position, as the leading estimate (`2h`) — is wrapped in parentheses (`(@lab)`), because no token starts with `(`. An empty SUMMARY becomes `untitled`. A flight without a `✈` gets one prefixed, matching §4.3.
4. `sync` takes `today: NaiveDate` (the date in `cfg.tz`) rather than an instant, and `existing` as `&[(IsoWeek, String)]` of file texts — `ics.rs` stays I/O-free apart from `fetch`.
5. Ids are 6 chars (per scope) while tree ids are 4; a recurring event's id mixes in the occurrence start, so re-timing a *series* renumbers its lines while moving a one-off keeps its id. `render_calendar_lines` re-hashes with a counter on a within-file collision so a file never has duplicate ids.
6. All-day (`VALUE=DATE`) events keep the ICS half-open convention: `at:2026-09-16T00:00/2026-09-17T00:00`. That is faithful but means the planner sees a 24h wall for an all-day event — flagged here in case §8.2 wants to treat `all_day` walls specially later (the flag is on `CalEvent`, but the rendered line carries nothing to distinguish it).
7. `merge_calendar_file` places the generated block where the file's first generated line was (after front matter/headings), keeping `manual` lines, prose and blank lines in their original order; output always ends with `\n`. It is idempotent from the second run onwards.
8. Unsupported ICS constructs produce warnings (returned in `IcsFeed`/`SyncResult`), not errors; only an unreadable feed or a failed fetch aborts a sync.
9. `sync` fails the whole sync if any configured feed fails, so no file is half-written.