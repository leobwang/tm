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

# check (layer 2)
Module `tm_core::check` (the file opens with an "API overview" doc comment and a table of every code, severity and meaning).

TYPES
- `pub enum Severity { Error, Warning }` — `Serialize` as `"error"`/`"warning"`; `as_str()`, `is_error()`, `Display`. Copy/Ord/Hash.
- `pub struct CheckProblem { pub severity: Severity, pub code: &'static str, pub file: String, pub line: usize /*1-based, 0 = whole file*/, pub id: Option<Id>, pub message: String }` — Clone/Debug/PartialEq/Eq/**Serialize** (no Deserialize: `code` is `&'static str`). `Display` = `file:line: error[code]: message` (`file: …` when line is 0, no prefix when file is empty). Ctors `CheckProblem::error(code, file, line, id, msg)` / `::warning(...)`, plus `is_error()`. `id` is the item's key (`^id`, or the title for an id-less routine/optional/inbox line), `None` for file-level problems and for `missing-id`.
- `pub enum CheckError { Store(#[from] StoreError) }` (thiserror) — only `fix_ids` can fail; `check` is infallible.

CODES (each a `pub const &str`, all listed in `pub const CODES: &[&str]`)
errors: `DUP_ID "dup-id"`, `DANGLING_PARENT "dangling-parent"`, `PARENT_CYCLE "parent-cycle"`, `DEP_CYCLE "dep-cycle"`, `DANGLING_DEP "dangling-dep"`, `BAD_VALUE "bad-value"` (also used for a few warnings), `BAD_CI "bad-ci"`, `ROUTINE_SHAPE "routine-shape"`, `CALENDAR_SHAPE "calendar-shape"`.
warnings: `UNKNOWN_KEY "unknown-key"`, `UNCLASSIFIED_TOKEN "unclassified-token"`, `MISSING_ID "missing-id"`, `OUTCOME_WITH_EST "outcome-with-est"`, `OPTIONAL_SHAPE "optional-shape"`, `PRIORITY_ON_CHILD "priority-on-child"`, `SERIES_ORDER "series-order"`, `WALL_CONFLICT "wall-conflict"`, `DAY_SECTION "day-section"`, `WAITING_STATE "waiting-state"`.

FUNCTIONS
- `pub fn check(files: &[ParsedFile], tree: &Tree, cfg: &Config) -> Vec<CheckProblem>` — `tree` must be `Tree::build(files, cfg)` (the structural half reads the tree, the per-line half the files). Deterministic, sorted by `(file, line, code, message)`.
- `pub fn has_errors(&[CheckProblem]) -> bool`
- `pub fn exit_code(&[CheckProblem]) -> i32` — 2 when any error, else 0 (§13).
- `pub fn summary(&[CheckProblem]) -> String` — `"no problems"` or `"2 errors, 3 warnings"` (singular/plural handled).
- `pub fn needs_id(item: &Item) -> bool` — `!item.has_id() && !item.horizon.allows_missing_state()`; the predicate `missing-id` and `fix_ids` share.
- `pub fn fix_ids(store: &dyn Store, files: &mut [ParsedFile], gen: &mut IdGen) -> Result<Vec<(String /*file*/, usize /*1-based line*/, Id)>, CheckError>` — pass the whole tree (`store.read_tree()?.files`): the ids already in it are the uniqueness set. Each changed file goes through `Store::modify_file` (§1.3 guard: a racing save is merged, ids are re-assigned against the merged text) and the corresponding entry in `files` is replaced by the re-read version, so the caller's tree is up to date afterwards. Files needing no id are not written at all; changed lines differ only by an appended ` ^id`.
- `pub fn assign_ids_in_text(text: &str, ctx: &ParseCtx<'_>, gen: &mut IdGen, existing: &mut HashSet<String>) -> (String, Vec<Id>)` — the pure single-buffer version for the TUI's first load / previews. Returns `text` unchanged when `ctx.horizon.allows_missing_state()` (routines/optional/inbox) or when nothing was assigned; `existing` absorbs both the ids already in `text` and the new ones. Lines inside `<!-- tm:… -->` generated ranges are never touched.

TYPICAL CLI USE (`tm check [--fix-ids]`):
```rust
let plan = store.read_tree()?;                       // PlanFiles { config, files }
let mut files = plan.files;
if fix { check::fix_ids(&store, &mut files, &mut IdGen::from_entropy())?; }
let tree = Tree::build(&files, &plan.config);
let problems = check::check(&files, &tree, &plan.config);
for p in &problems { println!("{p}"); }              // or serde_json for --json
println!("{}", check::summary(&problems));
std::process::exit(check::exit_code(&problems));
```

## Deviations (check)
1. Two codes beyond the scope's "e.g." list, because the scope named the checks but gave no code for them: `day-section` (an item in a `day/` file outside `# Pinned`) and `waiting-state` (`waiting:` without `[?]` and vice versa). Every code is a `pub const` and `CODES` is exhaustive, so the CLI never has to hard-code a string.
2. `bad-ci` covers both halves of the scope's one bullet: `ci:` outside `0..=5` **and** a `!k` outside `1..=4` (the grammar leaves `!9` as an `Unparsed` token, which check re-labels as `bad-ci` instead of `unclassified-token`, so it is reported once).
3. Parse problems are split by kind: a value that failed to parse and a missing state are `bad-value` **errors**; a problem the parser resolved by rule (duplicate key/parent/priority/id, conflicting shape or recurrence keys, `ci` given twice, `win:` without `dur:`, a flag absorbed into the title) is a `bad-value` **warning**; an "unknown file kind" file-level problem is a warning so a stray note in `plan/` does not fail a commit hook.
4. `wall-conflict` sweeps **every** open `Interval` in the tree (sorted by start, pairwise while they overlap), not only `calendar/` lines — the planner treats an exam in `week/` as a wall too (§8.2 step 1) — and reports each overlapping pair once, at the later line, naming both ids. `buffer:` is deliberately not counted (it is placement, not a booking). Only primary nodes are considered, so a §6.3 archive copy never "overlaps itself".
5. `dup-id` is reported once per line carrying the id (each naming the other locations) rather than once per id, so every offending line shows up in the file-ordered output.
6. `fix_ids` writes through `Store::modify_file` rather than `Store::write_file`, to get the §1.3 race guard; a test with `FsStore::with_before_write_hook` shows a racing save being merged and its new line also getting an id. After a successful write the entry in `files` is refreshed with `store.read_file`, so `files` is never left stale.
7. `assign_ids_in_text` takes `existing: &mut HashSet<String>` (rather than an immutable set) so the caller's id set stays correct across successive buffers, and it parses through `grammar::parse_file` with a default `Config` whose only changed field is `ctx.block_min` — that is all `parse_file` reads, and it gives generated-range and section handling for free.
8. `check` uses `cfg` only for `cfg.block_min()`, to state the `outcome-with-est` estimate in blocks (the unit the month conversation uses).

# recur (layer 2)
Module `tm_core::recur` — all pure, `today`/`now`/`Replay` injected, no I/O.

```rust
pub type DateRange = (NaiveDate, NaiveDate);          // inclusive (from, to)
pub const CARRY_LOOKBACK_DAYS: i64 = 60;

pub fn instances(item: &Item, range: DateRange, today: NaiveDate, replay: &Replay, cfg: &Config) -> Vec<Instance>;
pub fn instances_with_info(item: &Item, range: DateRange, today: NaiveDate, now: NaiveDateTime, replay: &Replay, cfg: &Config) -> Vec<(Instance, InstanceInfo)>;
pub fn instance_info(item: &Item, inst: &Instance, today: NaiveDate, now: NaiveDateTime) -> InstanceInfo;
pub fn is_mandatory(item: &Item, inst: &Instance, today: NaiveDate, now: NaiveDateTime) -> bool;
pub fn today_instances<'a, I: IntoIterator<Item=&'a Item>>(items: I, today: NaiveDate, now: NaiveDateTime, replay: &Replay, cfg: &Config) -> Vec<(Instance, InstanceInfo)>;
pub fn week_instances<'a, I: IntoIterator<Item=&'a Item>>(items: I, week: IsoWeek, today: NaiveDate, now: NaiveDateTime, replay: &Replay, cfg: &Config) -> Vec<(Instance, InstanceInfo)>;

pub struct InstanceInfo { pub mandatory: bool, pub last_chance: bool, pub overdue: bool,
    pub carried_from: Option<NaiveDate>, pub deferred_from_yesterday: bool, pub not_yet: bool,
    pub dur_min: Option<u32> }                        // Copy + Default + Serialize/Deserialize

pub fn after_done_state(item: &Item, replay: &Replay, today: NaiveDate, cfg: &Config) -> Option<AfterDoneState>;
pub struct AfterDoneState { pub last_done: Option<DateTime<FixedOffset>>, pub last_done_date: Option<NaiveDate>,
    pub count: u32, pub due: NaiveDate, pub due_at: NaiveDateTime,
    pub valid_until: Option<NaiveDate>, pub valid_until_at: Option<NaiveDateTime>, pub missed: bool }

pub fn waiting_state(item: &Item, replay: &Replay, today: NaiveDate, cfg: &Config) -> Option<WaitingState>;
pub struct WaitingState { pub since: Option<NaiveDate>, pub days_waiting: i64,
    pub timeout_at: Option<NaiveDate>, pub expired: bool, pub arrived: Option<DateTime<FixedOffset>> }
pub fn event_resolves(item: &Item, name: &str) -> bool;   // on-event: name, or after:event:name

pub enum Edit { State(State), Set { key: String, value: String }, Unset { key: String } }
pub struct Edits { pub edits: Vec<Edit> }
impl Edits { fn is_empty(&self)->bool; fn len(&self)->usize; fn iter(&self)->impl Iterator<Item=&Edit>;
             fn apply(&self, line: &mut ItemLine) -> Result<(), grammar::EditError>; }
pub fn on_done_waiting(item: &Item, today: NaiveDate) -> Edits;   // [?] + waiting:<today>
pub fn on_event_arrived(item: &Item) -> Edits;                    // [ ] − est: − waiting:

pub fn skip_instance(item: &Item, inst: &Instance, now: DateTime<FixedOffset>) -> LogEntry;             // Event::Skip
pub fn done_instance(item: &Item, inst: &Instance, now: DateTime<FixedOffset>, actual_min: Option<u32>) -> LogEntry; // Event::Routine status "done"
```

Conventions callers must know: instances are keyed by `Tree::key_of(item)` (title for id-less routine lines); the log `inst` string is `InstanceKey`'s Display (`2026-09-07` / `#6`); an instance's `window` is the whole placeable span (overnight windows run into the next morning, `every:week` spans Mon..Sun, after-done spans due..valid_until) and `due` is the end of the on-time chance; `is_mandatory` requires a `win:` item whose span closes today or earlier, with a persist instance staying mandatory once closed and expire/next losing it once `now` passes the close.

## Deviations (recur)
All documented at the top of recur.rs under "Deviations from the scope":
1. Signatures take `today` (and `cfg`, for `cfg.tz`) because statuses are relative to today and log timestamps are `DateTime<FixedOffset>` that only `cfg.tz` turns into local dates; `today_instances`/`week_instances`/`is_mandatory` also take `now` (the scope's `is_mandatory` already did).
2. `after_done_state` returns `Option<AfterDoneState>` (None when the item is not an `after-done:` item) rather than an unconditional value.
3. The extra-flags struct is named `InstanceInfo` (the name the planner part of the scope uses), not `InstanceExt`.
4. `WaitingState` has a fifth field `arrived: Option<DateTime<FixedOffset>>` (the `tm event` that already resolved the wait) so the Necessities screen can tell "still waiting" from "arrived, flip the line"; it is also what lets `instances()` produce a pending instance for a resolved-but-not-yet-rewritten `[?]` line.
5. Added `done_instance()` beside `skip_instance()` (`tm routine done` needs the symmetric constructor).
6. Two rules the spec left to me, both documented in the module docs: (a) `Rule::Weeks(n)` (`every:week`, not in the spec's `Rule` enum but added by model.rs) yields one instance per qualifying ISO week keyed by its Monday with a window spanning the whole week — that is what makes "laundry any day, mandatory Sunday, persists into next week" work; (b) `is_mandatory` refines §5.2's "on_miss ≠ expire" with "once the window has closed, only a `persist` instance stays mandatory" (an expire or next window whose close `now` has passed is over), and an `after-done:` item with no `~validity` never counts as a last chance since no day is its last.
7. `today_instances` bounds the persist carry at `CARRY_LOOKBACK_DAYS = 60` and collapses carried instances to the most recent one per item, so a long-neglected daily persist routine cannot flood the planner.

# energy (layer 2)
## tm_core::energy

CONSTS: `HSW_BUCKETS: usize = 12`, `DEFAULT_TAG = "_default"`, `WEEKDAY_KEYS: [&str;7]` (Mon..Sun), `WEEKDAYS: [Weekday;7]`.
ERRORS: `EnergyError { Io{path,source}, Json{path,source} }` (thiserror).

MODEL (`.tm/model.json`, §8.5, field order = spec order, `#[serde(default)]`, unknown keys ignored):
```rust
pub struct Model { pub energy: BTreeMap<String, Vec<u8>>,   // curve name -> 12 levels, index = floor(hsw)
                   pub sleep_debt_shift: f64,
                   pub duration: BTreeMap<String, f64>,      // tag (or "_default", or "<ci>:<tag>") -> multiplier
                   pub p_lounge: WeekdayMap<f64>,
                   pub expected_arrival: WeekdayMap<Hhmm>,
                   pub fitted: Option<NaiveDate>, pub n_obs: u32 }
```
- `Model::default()` (empty = fall back to config priors), `is_empty()`, `is_fitted()`, `from_config(&Config)`.
- `energy_at(curve, hsw) -> Option<u8>`, `sleep_shift(&Config) -> f64`, `p_lounge_on(Weekday,&Config) -> f64`, `expected_arrival_on(Weekday,&Config) -> NaiveTime`.
- `from_json(&str)`, `to_json() -> String` (pretty, arrays inline, trailing newline), `load(&Path) -> Result<Option<Model>>`, `load_or_default(&Path)`, `save(&Path)`. `Model` is plain serde, so `store.read_json::<Model>(store::MODEL_PATH)` / `write_json` also work.
- `WeekdayMap<T>`: `new/get(Weekday)/set/iter()/len/is_empty`, `FromIterator<(Weekday,T)>`; serializes as a Mon..Sun object with missing days omitted. `Hhmm(pub NaiveTime)` serializes as "HH:MM". `weekday_key(Weekday)`, `parse_weekday_key(&str)`.

PREDICT:
```rust
pub struct Features { pub loc: Loc, pub hsw: f64, pub hod: f64, pub slept_min: Option<u32>,
                      pub weekday: Weekday, pub blocks_done: u32, pub since_break_min: u32 }
Features::new(loc, hsw) | Features::at(t: DateTime<Tz>, wake: DateTime<Tz>, loc) | .with_slept(Option<u32>) | .with_progress(blocks_done, since_break_min) | .under_slept(&Config)
pub fn predict(&Model, &Config, &Features) -> u8            // learned curve else prior, minus sleep-debt shift, clamped 0..=5
pub fn bucket(hsw) -> usize                                  // floor, clamped 0..=11
pub fn curve_key(&Loc, &Config, &Model) -> String            // Lounge->"lounge", Home/Out/Any/unknown->"home", named keeps its name when a curve exists
pub fn prior_level(&Config, curve, hsw) -> u8
```

POSTERIOR (today's reports):
```rust
pub struct Report { pub t: DateTime<Tz>, pub pred: u8, pub rep: u8 }  // .delta()
Posterior::none(&Config) | ::from_reports(&[(DateTime<Tz>, pred, rep)], &Config) | ::from_observations(&[EnergyObs], tz, &Config)
posterior.reports() / is_empty() / latest_before(t) / adjustment(t) -> f64 / correct(t, pred) -> u8
pub fn posterior_weight(hours_since, full_hours, zero_hours) -> f64   // 1 up to full, linear to 0 at zero
```

FIT + MONITORS:
```rust
pub struct ArrivalObs { pub date: NaiveDate, pub time: NaiveTime, pub loc: String }
pub struct FitInput<'a> { pub energy: &'a [log::EnergyObs], pub durations: &'a [log::DurationObs],
                          pub arrivals: &'a [ArrivalObs], pub base: Option<&'a Model> }   // ::new(e,d,a), .with_base(m)
pub fn fit(&Config, &FitInput, today: NaiveDate) -> Model
pub fn fit_replay(&Config, &log::Replay, today) -> Model            // `tm model --fit`
pub fn arrivals_from_replay(&Config, &Replay) -> Vec<ArrivalObs>
pub fn observation_weight(day, went, today, &Config) -> f64          // exp(-age/decay) * went (3->2.0, 2->1.5)
pub fn shrunken_mean(prior, n0, &[(w, x)]) -> f64
pub struct Comparison { n, mae_a, mae_b, bias_a, bias_b, by_hour: Vec<(u32,f64,f64)> }  // .b_is_better()
pub fn compare(&Config, a: &Model, b: &Model, &[EnergyObs]) -> Comparison       // re-predicts both models
pub struct Calibration { n, mae, bias, by_hour: Vec<(hour, n, mae, bias)> }
pub fn calibration(&Config, &[EnergyObs]) -> Calibration                        // §11, uses the LOGGED pred
pub struct TagStats { tag, n, mean_ratio, multiplier, recent_ratio: Option<f64> }
pub fn estimate_calibration(&Config, &[DurationObs], today) -> Vec<TagStats>    // §11 "lean ×1.6 (n=9)"
pub fn features_of(&EnergyObs) -> Features
pub fn show(&Model) -> String                                                   // `tm model --show`
```

DURATIONS: `duration_multiplier(&Model, ci, &[String]) -> f64` ("<ci>:<tag>", then "<tag>", then "_default", then 1.0); `planned_minutes(est_min, multiplier) -> u32`; `fmt_multiplier(f64) -> String`; `fmt_planned(&Dur, f64) -> String` ("2b×1.6", plain "2b" at 1.0).

## tm_core::capacity

```rust
pub type Wall = (DateTime<Tz>, DateTime<Tz>);
pub type WallsByDate = BTreeMap<NaiveDate, Vec<Wall>>;
pub enum SlotKind { Block, ShortBlock }
pub struct Slot { pub start: DateTime<Tz>, pub end: DateTime<Tz>, pub energy: u8, pub kind: SlotKind }  // .minutes(), .fits(ci)
pub struct Break { pub start, pub end }                                       // .minutes()
pub enum SlotOrBreak { Slot(Slot), Break(Break) }                             // .start(), .end()
pub struct Cut { pub slots: Vec<Slot>, pub breaks: Vec<Break> }               // .timeline() interleaved, .slot_minutes(), .break_minutes()
pub fn local_dt(tz, NaiveDate, NaiveTime) -> DateTime<Tz>                     // DST-safe
pub fn window_and_budget(arrival: DateTime<Tz>, walls_today: &[Wall], &Config) -> (DateTime<Tz>, u32)
pub fn budget_blocks(&Config) -> u32          // floor(window_hours*60/block_min*budget_ratio) = 6
pub fn remaining_budget(budget, blocks_done) -> u32
pub fn free_intervals(from, to, &[Wall]) -> Vec<Wall>
pub fn cut_slots(from, end, &[Wall], &Config) -> Cut                          // §8.2 step 3; slots come back with energy 0
pub fn cut_slots_from(from, end, &[Wall], &Config, blocks_since_break: u32) -> Cut
pub struct EnergyCtx<'a> { model, cfg, posterior, wake: DateTime<Tz>, loc: Loc, slept_min: Option<u32>, blocks_done: u32, allow_home: bool }
   EnergyCtx::new(model,cfg,posterior,wake,loc).with_slept(..).with_blocks_done(..).with_allow_home(..)
   .energy_at(t, blocks_done, since_break_min) -> u8 ; .cap_for_location(u8) -> u8
pub fn energize(&[Slot], &EnergyCtx) -> Vec<Slot>                             // predict + posterior + home cap
pub struct DayCapacity { pub date: NaiveDate, pub minutes_at_level: [u32; 6] }
   ::empty(date), ::from_slots(date, &[Slot]), .total(), .at_least(min_ci)
pub fn lookahead(&WallsByDate, &Config, &Model, today_slots: &[Slot], from: NaiveDate, days: u32, wake_default: NaiveTime) -> Vec<DayCapacity>
pub fn available_until(&[DayCapacity], due: NaiveDate, min_ci: u8) -> u32
pub fn reserve(&mut [DayCapacity], minutes: u32, min_ci: u8) -> u32           // earliest day first, highest level first; returns what it took
pub fn upto(&[DayCapacity], due: NaiveDate) -> usize                          // slice length for `reserve(&mut caps[..n], ..)`
pub fn week_grid(&[DayCapacity]) -> String                                    // `tm plan --week`
```
Typical planner use: `let (end, budget) = window_and_budget(arrival, walls, cfg); let cut = cut_slots(now, end, walls, cfg); let slots = energize(&cut.slots, &EnergyCtx::new(&model, cfg, &posterior, wake, loc).with_slept(s)); let caps = lookahead(&walls_by_date, cfg, &model, &slots, today, 7, wake_time);` then priority.rs does `reserve(&mut caps[..upto(&caps, due)], need, ci)`.

## Deviations (energy)
1. **Sleep-debt sign (spec bug).** §8.5 writes `sleep_debt_shift = shrunken mean of (rep − energy[b])`, but the same section *subtracts* the shift and the example value is `+0.8`. Both cannot hold, so `fit` learns the deficit `mean(energy[b] − rep)` (positive under short sleep) and `predict` subtracts it. Documented in the module header.
2. **`compare` takes `&Config` first**: `compare(cfg, a, b, obs)`. A model falls back to the config priors for buckets it has not learned, so re-predicting needs the config. Also added `calibration(cfg, obs)` (MAE/bias of the *logged* pred, which is what the §11 monitor and §12.4 review row actually show) and `estimate_calibration(cfg, durations, today)` for the §11 estimate-calibration monitor.
3. **`fit` takes a `FitInput` with an optional `base: Option<&Model>`** rather than three loose slices, and `fit_replay(cfg, &Replay, today)` is the `tm model --fit` entry point. `base` implements §8.5's "hand edits become the new prior": when given, the current model.json is the shrinkage prior instead of the config priors.
4. **`duration[(ci, tag)]`**: v1 *learns* by first tag plus `_default` (as §8.5's own example is keyed), but the *lookup* tries `"<ci>:<tag>"` first so a hand-edited model can carry the fully-keyed value the formula names.
5. **Location curves**: `Out`, `Any` and unknown named locations use the **home** curve (conservative), not `Config::prior_energy`'s own lounge fallback; a named location keeps its own curve when the model or config has one.
6. **Multiple posterior reports**: the most recent report at or before the slot wins (superseded, not summed) — §8.5 only defines one report.
7. **`cut_slots` returns a `Cut { slots, breaks }`** (plus `timeline()`), not `Vec<Slot>`: the planner needs the breaks too. Added `cut_slots_from(..., blocks_since_break)` for mid-day replans. The "last block may be short or dropped" rule is applied at the end of *every* free stretch (a wall ends a stretch like the window end does), and the break counter is **not** reset by a wall or a placed routine — a caller that wants a routine to count as a break can cut each stretch separately with `cut_slots_from`.
8. **`energize(slots, &EnergyCtx)`** bundles the model/cfg/posterior/wake/loc/slept/blocks_done/allow_home arguments the scope listed positionally (9 arguments otherwise), and `allow_home` was added because §8.2 step 3 needs `--allow-home`.
9. **`window_and_budget`** solves `end = base + Σ walls inside [arrival, end]` as a fixed point (an extension can pull in a further wall) and clamps `end ≥ arrival` so arriving after `window_cap` gives an empty window, not a negative one. Walls are clipped and merged, so overlapping walls count once.
10. **Lookahead budget trim**: future days keep only `budget × block_min` minutes, highest-energy slots first (ties by start time); *today* is taken exactly as handed in, since the planner knows whether its slots are already budget-limited.
11. **The §4.3 printed timeline cannot be reproduced by `cut_slots` alone** (step 2 has already placed routines there — lunch at 11:20). With only the 12:50–13:50 wall the cut is 07:00, 08:00, break 09:00–09:20, 09:20, 10:20, break 11:20–11:40, 11:40 (12:40→12:50 = 10 min dropped), wall, 13:50, break 14:50–15:10, 15:10–16:00 short. A second test passes lunch in as an occupied interval and reproduces the day file's 11:50/12:50 boundaries. Both layouts are asserted and the interpretation is documented in the module header.
12. **`model.json` formatting**: `Model::to_json` uses a custom `serde_json` formatter so objects are indented but arrays stay on one line (a 12-level curve reads as a curve). Key order is BTreeMap/Mon..Sun order, so the fixture (written in the spec's key order) round-trips modulo key order — the snapshot pins the canonical output.
13. `n_obs` is defined as the number of *energy* observations behind the fit (the spec does not say); `fitted` is the injected `today`.

# horizon (layer 2)
Module `tm_core::horizon` (file opens with an "API overview" doc comment plus a "Choices the spec leaves open" section).

CONSTANTS: `MIN_REMAINING_MIN: u32 = 5` (floor for a computed `est:`), `DEMOTED_SECTION = "Demoted"`, `PINNED_SECTION = "Pinned"`, `OVERDUE_SECTION = "Overdue"`, `REVIEW_BLOCK = "review"`, `REVIEW_PLACEHOLDER = "review pending"`.

ERRORS: `enum HorizonError { Store(#[from] StoreError), NotFound(Id), MissingFile(String), Edit{id, message}, Horizon{id, horizon, message}, Log(#[from] serde_json::Error) }` (thiserror).

CONTEXT:
```rust
pub struct Ctx<'a> { pub store: &'a dyn Store, pub files: &'a PlanFiles, pub tree: &'a Tree,
                     pub replay: Option<&'a Replay>, pub now: DateTime<FixedOffset> }
impl<'a> Ctx<'a> {
    pub fn new(store: &'a dyn Store, files: &'a PlanFiles, tree: &'a Tree, now: DateTime<FixedOffset>) -> Ctx<'a>;
    pub fn with_replay(self, replay: &'a Replay) -> Ctx<'a>;   // builder
    pub fn cfg(&self) -> &Config;  pub fn block_min(&self) -> u32;
    pub fn local(&self) -> DateTime<Tz>;  pub fn today(&self) -> NaiveDate;  pub fn now_naive(&self) -> NaiveDateTime;
}
```
Typical caller: `let files = store.read_tree()?; let tree = files.tree(); let cx = Ctx::new(&store, &files, &tree, now);` — after any operation the snapshot is stale, so re-read before the next one.

VERBS (§13):
```rust
pub fn move_item(cx: &Ctx, id: &Id, to: &Horizon, section: Option<&str>) -> Result<Moved, HorizonError>;
pub fn demote(cx: &Ctx, id: &Id) -> Result<Demoted, HorizonError>;          // week items only
pub fn readopt(cx: &Ctx, id: &Id, to: Option<&Horizon>) -> Result<Moved, HorizonError>;  // None = current week
pub fn drop_item(cx: &Ctx, id: &Id) -> Result<String, HorizonError>;        // returns the new line text
pub fn rank(cx: &Ctx, id: &Id, n: usize) -> Result<bool, HorizonError>;     // 1-based, clamped; false = no move
```
CLOSES (§6.3):
```rust
pub fn close_day(cx: &Ctx, date: NaiveDate) -> Result<CloseReport, HorizonError>;
pub fn close_week(cx: &Ctx, week: IsoWeek) -> Result<CloseReport, HorizonError>;
pub fn close_month(cx: &Ctx, month: YearMonth, drops: &[Id]) -> Result<CloseReport, HorizonError>;
pub fn auto_close(store: &dyn Store, state: &mut RuntimeState, today: NaiveDate,
                  now: DateTime<FixedOffset>, replay: Option<&Replay>) -> Result<Vec<ClosedPeriod>, HorizonError>;
pub fn pending_closes(store: &dyn Store, state: &RuntimeState, today: NaiveDate) -> Vec<(Period, String)>;
pub const AUTO_CLOSE_CATCHUP: usize = 16;   // periods of each kind one sweep will catch up on
pub fn churn(tree: &Tree, min: usize) -> Vec<(Id, Vec<Stamp>)>;   // >= min stamps, most stamped first
pub fn period_name(p: Period) -> &'static str;                    // "day" | "week" | "month"
```
REPORTS (all Clone/Debug/PartialEq/Eq/Serialize/Deserialize):
```rust
pub struct Moved { pub id: Id, pub from: String, pub to: String }              // paths, e.g. "week/2026-W37.md"
pub struct Demoted { pub id: Id, pub est_min: u32, pub stamps: Vec<Stamp> }
pub struct Reopened { pub id: Id, pub est_min: u32 }
pub struct CloseReport { pub period: Option<Period> /*json "week"*/, pub key: String,
    pub moved: Vec<Moved>, pub demoted: Vec<Demoted>, pub reopened: Vec<Reopened>,
    pub dropped_children: Vec<Id>, pub dropped: Vec<Id>, pub overdue_to_backlog: Vec<Id>,
    pub notes: Vec<String> }   // + is_empty()
pub struct ClosedPeriod { pub period: Period, pub key: String, pub report: CloseReport }
```
Log events written (through `store.append_text(store::LOG_PATH, …)`, one JSON object per line, timestamped `cx.now`): `demote{id,from,to,est_min}` per demoted/pinned item, `move{id,from,to}` (move_item, overdue→backlog, month carry-over), `readopt{id}`, `drop{id}`, `close{period,key}` at the end of every close.

## Deviations (horizon)
1. **`est:` at day close (differs from the DoD's literal expectation).** The scope's formula — `remaining = own_remaining − done minutes today, floored` — and the DoD's expected value ("60 done minutes on ^t3 → est:1b") contradict each other on the plan-basic fixture: ^t3 is `- [>] 4 2b … est:1b ^t3`, so own_remaining is 60, minus 60 done = 0 → the floor. I implemented the formula (est: is the running remainder — `tm stop` / partial `tm done` maintain it, so subtracting est_original instead would throw away every earlier day's work), and the test asserts `est:5m` (MIN_REMAINING_MIN). `est:1b` would only follow from `est_original − done_today`, which double-counts across days. If you want the DoD's literal number, change `day_remaining()` in horizon.rs (~line 900) to start from `item.est_original`.
2. **Signatures.** Free functions take a `Ctx` (store + files + tree + replay + now) instead of long parameter lists; the log path is not injected — events go through `Store::append_text(LOG_PATH, …)` so MemStore-based tests see them. `auto_close` takes the store (not a Ctx) because it re-reads the tree between closes, and it *saves* `.tm/state.json` when anything ran (that is what makes it idempotent across processes).
3. **`Closed` renamed.** The scope's `auto_close -> Vec<Closed>` would collide with `store::Closed` (the state.json struct); the returned type is `ClosedPeriod { period, key, report }`.
4. **CloseReport fields.** The scope's tuples became named structs (`Moved`, `Demoted`, `Reopened`) for a usable `--json` shape, and three fields were added: `period`/`key` (which close this was), `reopened` (`[>]`→`[ ]` rewrites at day close) and `dropped` (`tm close month --drop`). `period` serializes as "day"/"week"/"month" to match §10.1.
5. **Folding children** = the §6.4 rollup (`Tree::remaining`), not a sum on top of the parent's own estimate: a `6b` milestone with 1b subtasks carries `est:6b`. Only a parent with no estimate of its own inherits its children's sum. (Documented in the module header.)
6. **Week close and intervals.** §6.3's "recurring items and calendar intervals are never touched" is read as: recurring lines (`recur != None`) anywhere, and the synced `calendar/` files (which are never week files). A dated interval written *in a week file* (^x1, the Midterm) is demoted like any other unfinished line — otherwise the clause would exempt nothing at all in a week close. Easy to flip if you disagree: add a `Shape::Interval` guard next to the `Recur::None` filter in `close_week`.
7. **A second demotion rewrites the existing `# Demoted` copy** (accumulating stamps, deduped) instead of appending a second line, so the id never becomes a `tm check` duplicate. When the target month file already holds a *live* line with the same id, the copy is appended anyway and a note is added to the report.
8. **Review placeholder placement.** `Store::replace_generated` inserts a missing block right after the front matter / `![day]` line, i.e. *above* the generated plan; the placeholder is instead appended at the end of the day file (below `## Notes`), which is where a review belongs. A day with no file gets no file created (a note says so). An existing `tm:review` block is **left alone when it already holds a review** — §6.3 gives the close the review *section*, §13's `tm review day --write` gives it the *text*, and the auto-close routinely runs after the review was written, so replacing the body would destroy the only copy of it. Only an absent, empty or still-placeholder block is (re)written (in place, via `edit::replace_generated`), which is what keeps a second close a byte-for-byte no-op. `close_week` / `close_month` touch no generated block at all, so a written week or month review is never at risk.
9. **Overdue → backlog is a pure move**: the line keeps its bytes (no `est:` rewrite, no stamp), per "moved to backlog.md#Overdue *instead*".
10. **auto_close catches up, oldest first, bounded.** §6.3's close "runs automatically on the first command after the period ends", so *every* unclosed period of each kind is closed (finest-first: day, week, month, so a pinned item demoted into the week is demoted on into the month in the same sweep), not just the last one — skipping a week would otherwise strand its unfinished milestones as `[ ]` lines in a file the planner no longer reads, and `state.closed` only moves forward, so nothing would ever pick them up. The sweep is capped at `AUTO_CLOSE_CATCHUP` (16) periods per kind, ending at the last complete one; anything older is stamped closed without running. A tree with **no** close history — every tree between `tm init` and its first command, since `tm init` writes week and day files and no `state.json` — gets the same bounded catch-up. Periods whose file does not exist are recorded as closed without running. `pending_closes` reports exactly what the sweep would run.
11. **`demote()` refuses non-week items** with `HorizonError::Horizon` (a pinned day item is *moved* by `close_day`; a month outcome has no enclosing horizon). Note this also means demoting an already-demoted item fails once the tree resolves it to the month archive copy — readopt it first (covered by a test).
12. **`close_month` resolves every id in `drops` or fails.** The close auto-runs with an empty drop list (`auto_close` from `Ctx::load`), so a `--drop` usually arrives after the carry: an id no longer in the month file is looked for in the *next* month's file and, when found there, brought back and dropped — the close is idempotent under a growing drop list, and the tree lands where a one-shot `close_month(m, drops)` would have left it (extra log events: `move{id, from: next, to: month}` then `drop{id}`). An id in neither file is `HorizonError::NotFound`, or `HorizonError::Horizon` when it lives somewhere else in the tree; both are raised before the first write, so a bad drop list leaves the tree untouched. `CloseReport::absorb` folds the undone carry out of the earlier report's `moved`/`demoted` so the merged counts describe the tree. The CLI rejects `--drop` on `tm close day` / `tm close week` (§6.3 gives the flag to the month row alone) rather than ignoring it.
13. **`readopt()` never leaves an id on two live lines** (§4.1/§17.2: ids are global). It refuses an id with no demoted line anywhere (`HorizonError::Horizon`, "not demoted … use `tm move`") so a `readopt` log event always records a real demotion undone; and when the id *still* has a live line — anything `tree::is_archive_copy` rejects, the shape the §4.3 example tree ships — that line is the item, so the archive copy is absorbed into it (stamps merged, copy deleted) and the live line is what moves into `to`. Only when the id is archive copies only does the copy itself travel.

# priority.rs + planner.rs types (layer 3)
tm_core::priority

```rust
// §6.2 candidates
pub enum Ineligible { Closed(State), Waiting, Blocked(Vec<Dep>), CapReached{cap: Rate, done_min: u32} }  // thiserror Display
pub struct Candidate { id, title, ci, k, remaining_min, planned_min, need_min, multiplier: f64,
    effective_due: Option<DateTime<Tz>>, window: Option<(DateTime<Tz>, DateTime<Tz>)>, scope: Scope,
    floor: Option<Rate>, floor_done_min, cap: Option<Rate>, cap_done_min, state: State,
    blocked_by: Vec<Dep>, waiting: bool, loc: Loc, splittable: bool, hot: bool, overdue: bool,
    mandatory: bool, is_optional: bool, is_wall: bool, instance: Option<InstanceKey>,
    root_order: (usize, usize), own_order: (usize, usize), tags: Vec<String> }   // Clone+Debug+PartialEq+Default+Serialize
impl Candidate { fn new(id, ci, k, remaining_min, &Config) -> Candidate;   // bare, for tests/fixtures
                 fn eligible() -> bool; fn ineligible_reason() -> Option<Ineligible>;
                 fn cap_left_min() -> Option<u32>; fn floor_need_min(&Config) -> Option<u32> }
pub fn collect_candidates(&Tree, &Replay, &Config, &Model, today: NaiveDate, now: DateTime<Tz>) -> Vec<Candidate>;
pub fn done_this_period(&Replay, &Tree, &Id, Period, today) -> u32;   // item + descendants, period start..today
pub fn period_range(Period, today) -> (NaiveDate, NaiveDate);
pub fn lookahead_days(&[Candidate], today) -> u32;                    // size capacity::lookahead so EDF is honest

// §7.2–§7.4
pub enum PrioClass { Wall, Hot, Impossible, Overdue, Mandatory, HotFlag, Dated, Floor, Rank, Optional }
   impl { fn label() -> &'static str; fn is_urgent() -> bool }
pub struct Prio { id, p: u8, class: PrioClass, k: u8, u: Option<f64>, bin: Option<u8>, need_min, avail_min,
                  allocation_min, shortfall_min, until: Option<NaiveDate>, hysteresis_applied: bool, raw_p: u8 }
   impl { fn is_hot() -> bool }                                        // Clone+Debug+PartialEq+Serialize
pub fn compute(&[Candidate], &[DayCapacity], &BTreeMap<Id,u8>, &Config, today) -> Vec<Prio>;  // 1:1, same order
pub fn utilization(need_min, avail_min) -> f64;                        // need 0 -> 0.0, avail 0 -> INFINITY
pub fn bin_of(u: f64, bins: &[f64]) -> Option<u8>;                     // None = HOT
pub fn priorities_for_state(&[Prio]) -> BTreeMap<Id, u8>;              // state.priorities_yesterday, walls excluded

// §7.4 sorting, §7.5 batching
pub type SortKey = (u8, (usize, usize), (usize, usize));
pub fn sort_key(&Prio, &Candidate) -> SortKey;
pub fn sorted(&[Prio], &[Candidate]) -> Vec<Id>;                       // walls first, then by key; ineligible excluded
pub fn sorted_candidates<'a>(&[Prio], &'a [Candidate]) -> Vec<&'a Candidate>;
pub fn blocked(&[Candidate]) -> Vec<(Id, Ineligible)>;
pub struct Batch { ids: Vec<Id>, ci: u8, total_min: u32, total_remaining_min: u32 }  impl { fn is_batch() -> bool }
pub fn batches(sorted: &[&Candidate], &Config) -> Vec<Batch>;          // ALL groups, assignment order, singles included

// §13 explain, §11 monitor
pub struct Explanation { id, priority_part: String, need_part: Option<String>, slot_part: Option<String>,
                         deps_part: String, cap_part: Option<String>, extra: Vec<String> }   // Display joins with "; "
pub fn explain(&Id, &[Candidate], &[Prio], &Config) -> String;
pub fn explanation(&Id, &[Candidate], &[Prio], &Config) -> Option<Explanation>;
pub fn fmt_blocks(minutes: u32, block_min: u32) -> String;             // "6b" | "2.6b" | "20m"
pub struct DeadlineHealth { min_slack_days: Option<f64>, hot: usize, impossible: usize, overdue: usize }
pub fn deadline_health(&[Prio], &[Candidate], today) -> DeadlineHealth;
```

tm_core::planner (types only; §8.2 is M4)

```rust
pub struct PlanInput<'a> { tree: &Tree, log: &Log, replay: &Replay, cfg: &Config, model: &Model,
    runtime: &RuntimeState, now: DateTime<Tz>, caps: Option<&[DayCapacity]>, candidates: Option<&[Candidate]> }
   impl { fn new(tree, log, replay, cfg, model, runtime, now); fn with_caps(..); fn with_candidates(..); fn date() }
pub enum SegKind { Block, Batch(Vec<Id>), Break, Routine, Wall, Rest, Optional, WindDown, Sleep, Lost }
pub struct SegFlags { done, current, underused, hot, mandatory, deferred, ghost, planned_min: Option<u32>,
                      multiplier: Option<f64>, note: Option<String> }   // Default
pub struct Segment { start, end: DateTime<Tz>, kind: SegKind, energy: Option<u8>, item: Option<Id>,
                     instance: Option<InstanceKey>, flags: SegFlags }   impl { fn minutes() }
pub struct Diagnostics { underused: Vec<(Id,u8,u8)>, a_capacity_lost: u32, hot: Vec<Id>,
    impossible: Vec<(Id,u32,NaiveDate)>, conflicts: Vec<(Id,Id)>, blocked: Vec<(Id,Vec<Dep>)>, deferred: Vec<Id>,
    waiting: Vec<Id>, dropped_tail: Vec<Id>, plan_honesty: Option<f64>, rest_debt_min: u32, notes: Vec<String> }
pub struct DayPlan { date, window: (DateTime<Tz>, DateTime<Tz>), budget_blocks: u32, segments: Vec<Segment>,
                     diagnostics: Diagnostics, priorities: Vec<(Id, Prio)> }
   impl { fn empty(date, window, budget); fn hash() -> String /* 16 hex, FNV-1a over serialized segments */;
          fn block_minutes() -> u32 }
pub fn plan(&PlanInput) -> DayPlan;
```

Typical caller: `let cands = priority::collect_candidates(&tree, &replay, &cfg, &model, today, now);` → size the lookahead with `priority::lookahead_days(&cands, today)` → `capacity::lookahead(...)` → `let prios = priority::compute(&cands, &caps, &state.priorities_yesterday, &cfg, today);` → `priority::batches(&priority::sorted_candidates(&prios, &cands), &cfg)` for step 5, `priority::blocked(&cands)` for the diagnostics, `priority::priorities_for_state(&prios)` back into `state.json`.

## Deviations
All ten are documented in priority.rs's module header under "Choices the spec leaves open (deviations)" / "How the rule is implemented".

1. **Floor `need` carries `safety`.** §7.2 writes `need = floor − done_this_period` while §7.1 defines `need = remaining × safety` for everything. I use `(floor − done) × safety`, which is what the M3 definition of done spells out ("min:6b/w with 2b done → need 4b × safety").
2. **Which candidates enter the EDF pass.** Only non-wall, non-optional candidates with a *tree* due (`due:` or the §3.2 derived prep due) — **not** instance candidates. A routine window instance also carries a `due` (its window close), but it is a placement window, not a deadline; letting it reserve lookahead capacity would double-count the day. Overdue items *do* take part: their window `[today, past due]` is empty, so they reserve nothing and score `u = ∞`.
3. **Class precedence.** §7.2's `p = 0` line lists four causes; when several apply the class reported is the first of Wall → Optional → Overdue → Mandatory → HotFlag → Impossible → Hot → Dated/Floor/Rank. So a candidate that is both overdue and (artefactually) impossible reads as `Overdue` while still carrying the EDF numbers — and `deadline_health.overdue` and `.impossible` stay disjoint.
4. **`u` when nothing is needed** is 0, not ∞ (§7.1 only defines the capacity-0 case), so a finished item is never reported HOT.
5. **Floors do not reserve.** The floor pass reads the capacity left *after* the EDF pass (§7.1: capacity is net of earlier deadlines' reservations) but subtracts nothing itself — two floors in one period are independent claims and the spec gives them no order.
6. **A floor whose `u_floor ≥ 1` is HOT/IMPOSSIBLE** like any other `u ≥ 1` (§7.2's HOT line is written over `u`, not over "dated").
7. **Open, undated, floorless candidates fall back to `p = k + 2`** (§7.2's pure-rank line, which is written for *finite* items). In practice these are non-mandatory routine instances, which the planner places by window rather than by rank.
8. **Hysteresis applies to every non-wall class**, not only the binned ones — §7.4 states it as a property of `p`. Classes with a constant `p` are unaffected in practice.
9. **`BTreeMap` instead of `HashMap`** for `compute`'s `yesterday` argument and `priorities_for_state`'s return, matching `store::RuntimeState::priorities_yesterday` exactly so the `state.json` round trip needs no conversion (the scope said `HashMap`).
10. **`min_slack_days`** (§11 gives no formula) is `days_until_due × (1 − u)` over deadlines that are still ahead (overdue has its own column); a non-finite `u` scores `−days`. **Batching gathers forward** rather than merging only adjacent runs: a batch starts at the first ungrouped small candidate and scans forward for same-`ci` candidates that still fit in a block, so scattered 20m items actually batch (§7.5's own example — "package · insurance · bank" — pairs items that are not adjacent). Walls and optionals are never batched (walls are placed as intervals, optionals only fill rest slots). **`batches` returns one `Vec<Batch>` covering every candidate** (singles as 1-element batches), which is what the scope's "return one Vec<Group> in assignment order" asked for, under the `Batch` name the scope also used.

Two additions beyond the listed scope, both small: `lookahead_days` (see "upstream bugs" — the caller must size the lookahead to the furthest deadline or §7.3 reports false shortfalls) and `Candidate::window` / `Candidate::instance` (the planner needs the placement span and instance key that `recur` computed; recomputing them would duplicate §5.1).

In `planner.rs`: `PlanInput` carries both `log` (as §8 names it) and `replay` (what the planner actually reads), plus the two optional `caps`/`candidates` shortcuts the scope allowed; `Diagnostics` gains the requested `notes: Vec<String>`.

# planner (layer 4)
`tm_core::planner` — everything below is new or extended; every pre-existing public name (PlanInput, DayPlan, Segment, SegKind, SegFlags, Diagnostics, plan, DayPlan::empty/hash/block_minutes) is unchanged in name and meaning.

```rust
pub struct PlanInput<'a> {            // Copy; 4 fields added, none removed
    pub tree: &'a Tree, pub log: &'a Log, pub replay: &'a Replay,
    pub cfg: &'a Config, pub model: &'a Model, pub runtime: &'a RuntimeState,
    pub now: DateTime<Tz>,
    pub caps: Option<&'a [DayCapacity]>, pub candidates: Option<&'a [Candidate]>,
    pub allow_home: bool,                       // NEW — `tm plan --allow-home`
    pub overrides: Option<&'a PlanOverrides>,   // NEW — §9.1 what-ifs
}
impl PlanInput<'a> {
    fn new(tree, log, replay, cfg, model, runtime, now) -> PlanInput<'a>;  // unchanged
    fn with_caps(self, &[DayCapacity]) -> Self;
    fn with_candidates(self, &[Candidate]) -> Self;
    fn with_allow_home(self, bool) -> Self;      // NEW
    fn with_overrides(self, &PlanOverrides) -> Self;  // NEW
    fn date(&self) -> NaiveDate;
}

pub fn plan(input: &PlanInput) -> DayPlan;              // §8.2, pure
pub fn week_plan(input: &PlanInput) -> WeekPlan;        // §13 `tm plan --week`
pub fn diff(old: &DayPlan, new: &DayPlan) -> PlanDiff;  // §13 `--diff`, §11 drift
pub fn explain(day: &DayPlan, id: &Id, cands: &[Candidate], cfg: &Config) -> String;  // §13
pub fn overtime_drops(input: &PlanInput, id: &Id, blocks: u32) -> Vec<Id>;           // §9.1
pub fn fmt_clock(t: DateTime<Tz>) -> String;            // "HH:MM"

pub struct PlanOverrides {  // Clone+Debug+Default+PartialEq+Eq
    pub est_min: BTreeMap<Id, u32>, pub extra_min: BTreeMap<Id, u32>, pub drop: BTreeSet<Id>,
}
impl PlanOverrides { fn new(); fn with_est(self,&Id,u32); fn extending(self,&Id,u32);
                     fn dropping(self,&Id); fn is_empty(&self) -> bool }

pub struct PlanDiff { pub moved: Vec<(Id, DateTime<Tz>, DateTime<Tz>)>,
                      pub added: Vec<Id>, pub removed: Vec<Id>, pub drift_min: u32 }
impl PlanDiff { fn is_empty(&self) -> bool }

pub struct WeekPlan { pub from: NaiveDate, pub days: Vec<WeekDay>,
                      pub capacity: Vec<DayCapacity>, pub grid: String,
                      pub priorities: Vec<(Id, Prio)>, pub unplaced: Vec<Id>,
                      pub notes: Vec<String> }
pub struct WeekDay { pub date: NaiveDate, pub capacity_min: u32, pub planned_min: u32,
                     pub blocks: u32, pub items: Vec<(Id, u32)> }

// added to existing types (nothing renamed or removed)
impl SegKind  { fn is_work(&self) -> bool }                    // Block | Batch
impl Segment  { fn items(&self) -> Vec<Id> }                   // one id, or a batch's
impl DayPlan  { fn planned_block_minutes(&self, from: DateTime<Tz>) -> u32;  // §8.3's LHS
                fn assigned(&self) -> Vec<Id>;                 // whole day, in time order
                fn assigned_from(&self, from: DateTime<Tz>) -> Vec<Id>;  // planned half
                fn segment_of(&self, id: &Id) -> Option<&Segment> }
```

Notes for callers:
- `DayPlan::block_minutes()` covers the whole day, the replayed morning included; use `planned_block_minutes(now)` for the budget check.
- `SegKind::Batch(ids)` segments have `item == None`; use `Segment::items()`.
- `diagnostics.blocked` holds only dep-blocked items (`Vec<(Id, Vec<Dep>)>`); waiting and cap-exhausted items are in `waiting` / `dropped_tail`, and `priority::blocked(&cands)` still has the full reason list.
- `plan()` builds its own candidates and lookahead unless `with_candidates` / `with_caps` are given; `DayPlan::priorities` is one `(Id, Prio)` per candidate, in candidate order (two entries can share an id — a carried persist instance and today's).
- Test helpers live in `tm-core/tests/planner_common/mod.rs` (`load`, `load_with_log`, `BASIC_LOG`, `basic_state`, `timeline`, `diagnostics`) and are reusable by emit.rs / CLI tests via `mod planner_common;`.

## Deviations (planner)
Documented in planner.rs's module header ("How §8.2 is implemented, and the choices the spec leaves open", 10 numbered points). The ones that matter:

1. **`travel-day` zeroes the remaining budget**, not the window: routines, walls and optionals still get placed. §8.2 only writes "travel-day zeroing".
2. **An open interruption does not extend the window.** §8.1 extends the window by walls inside it, but §9 says an interruption drops the tail; extending would contradict that. Calendar walls (and their `buffer:`) do extend it.
3. **`buffer:` is a separate Wall segment** in front of the event and counts as wall time for §8.1. Wall conflicts are computed on the un-buffered intervals (matching `check.rs`'s `wall-conflict` rule).
4. **No `loc:` filter on routines.** §8.2 lists it under step 5 (ASSIGN); a `loc:out` errand is a reason to go out, not to skip the day.
5. **Wind-down is blocked for slot cutting**, which is the strongest form of "no Block with `ci ≥ 4` after wind-down": no block of any `ci` is planned there. A mandatory routine with nowhere else to go may still reach into it.
6. **Sleep detection** is "the routine keyed `sleep`, or an overnight window of ≥ 6 h"; the Sleep segment is clipped at midnight so the DayPlan stays one day.
7. **The Active block holds one block, then re-competes.** `state.active` is reserved like a wall from `now` to the end of the block it is in (`started + block_min`, rolled forward while that instant is past; clipped by the next wall, the wind-down and `est_min − elapsed`), so nothing is planned on top of it and it survives an ineligible item or a spent budget. §8.2 step 5's exemption is for the item's current *slot*, one block: reserving the whole remaining estimate made a 6b item swallow 355 minutes in one segment, which deleted every routine window inside it (lunch, dinner) from the day and left step 3 no slots to count a break against. After its block the item takes its place in the key order again, its group already charged for the run's minutes; the run still costs exactly one block of the remaining budget however long it lasts.
8. **A carried (window-closed) instance** may be placed anywhere left in the day, but a `win:HH:MM-HH:MM` daily range still constrains the hours.
9. **A group takes another slot whenever it is still owed minutes**, so a 192-minute item consumes four 60-minute slots (the last one partly). Sub-block packing is out of scope.
10. **`plan_honesty`** = Σ minutes still owed by the groups the day *starts* ÷ (`remaining_budget × block_min`). Any reading based on scheduled block minutes can never exceed 1 (the fill is budget-capped) and so could never fire §11's "> 1.1" warning. `None` when the budget is zero. **`rest_debt_min`** = Σ (`planned_min − actual_min`) over today's logged breaks.
11. **`a_capacity_lost`** = Rest minutes at energy ≥ 4 on a day that had an unassigned `ci = 5` candidate. **`deferred`** is generalised from "ci-5 items" to any unassigned eligible candidate for which some slot's *raw* prediction was high enough and the posterior-corrected value was not.
12. **`dropped_tail`** lists every eligible candidate that got no slot, whatever the reason (budget, energy, contiguity) — §8.2 names no narrower rule. **`notes`** additionally names every window instance step 6 could not place ("lunch: no free 30m position in 11:30–13:30; not planned today"); an instance whose window has already closed is §5.3's expiry, not a placement failure, and is not reported.
13. **§8.3's tail-drop is tested as** "removing a block from the budget leaves every kept slot holding the same items and never adds an item". An *energy downgrade* can legitimately swap items (that is exactly what the `deferred` diagnostic reports), so it is not covered by the subset form. **"IMPOSSIBLE never dropped"** is tested as (a) always named in `diagnostics.impossible` with its shortfall and (b) never displaced by a `p > 0` candidate — with many `p = 0` items and few slots some must still be left out.
14. **`week_plan` is deliberately light** (documented on `WeekPlan`): today is the real `plan()`; later days are a greedy per-day allocation over the lookahead respecting `ci`, deadlines and `max:`, with no routines, breaks, batching, `atomic` contiguity, interruptions or posterior.
15. **Fixture placement**: `plan-basic` did **not** get a `.tm/` — see `upstream_bugs`. Its planner history lives in `planner_common::BASIC_LOG` / `basic_state()` instead. `plan-home-day/` and `plan-travel-day/` (both copies of `plan-basic` with a changed calendar/state) do carry their own `.tm/`.

# emit (layer 4)
module tm_core::emit — all pure, no I/O, no clock.

TIMELINE (§4.3)
- `pub fn render_plan_section(plan: &DayPlan, tree: &Tree, cfg: &Config, now: DateTime<Tz>) -> (String /*info: "10:42"*/, String /*body, rows newline-terminated*/)` — pass `info` to `Store::replace_generated_stamped(rel, "plan", Some(&info), &body)`.
- `pub fn render_plan_section_with(plan, tree, cfg, now, layout: &Layout) -> (String, String)`
- `pub struct Layout { pub title_w: usize }` + `Layout::new(w)` (min 4), `Default` = 27.
- `pub fn svg_link(date: NaiveDate) -> String` → `![day](2026-09-07.svg)`; `pub fn svg_file_name(date) -> String`.
- Column constants: `TIME_W=5, CI_W=2, P_W=2, MARK_W=1, PARENT_W=3, EST_W=2, ACTUAL_W=1, DEFAULT_TITLE_W=27, TITLE_COL=14`. Glyph/mark constants: `MARK_DONE ✓, MARK_CURRENT ▶, MARK_HOT ⚠, MARK_UNDERUSED ↓, GLYPH_ROUTINE ·, GLYPH_WALL ⏰, GLYPH_OPTIONAL ○, GLYPH_WIND_DOWN 🌙, DIVIDER "───"`.
- Row: `HH:MM  ci[↓] pN mark title(27) @parent(43) est(48) (actual)(52) note(55)`; character-counted fixed columns, trailing blanks trimmed. `p` is shown for Block/Batch only (a batch shows its first member's `p`). The `───  window ends HH:MM` row is generated where cumulative Block/Batch minutes reach `budget_blocks × block_min`, or at the window end, whichever is earlier.

DAY BAR (§12.1)
- `pub fn daybar_cells(plan: &DayPlan, ghost: Option<&DayPlan>, tree: &Tree, cfg: &Config, cols: usize, wake: DateTime<Tz>, now: DateTime<Tz>) -> DayBar`
- `pub struct DayBar { cells: Vec<Cell>, ghost: Vec<Cell>, cursor_col: usize, cols: usize, wake: DateTime<Tz>, now: DateTime<Tz>, span_min: u32 }` + `cell_minutes() -> f64`, `col_of(t) -> Option<usize>`, `x_of(t, width) -> f64`, `start_of(col) -> DateTime<Tz>`.
- `pub struct Cell { hue: Option<usize>, brightness: u8, style: CellStyle, tooltip: String, segment: Option<usize> }` + `Cell::empty()`, `Cell::rgb(&Config) -> (u8,u8,u8)` (palette hue × brightness/5 for Work; the style's fixed colour otherwise).
- `pub enum CellStyle { Work, Routine, Break, Lost, Interrupt, Optional, Wall, Rest, Sleep, Empty }` + `CellStyle::of(&Segment)`, `.colour()`, `.is_hatched()`.
- `pub fn hue_index(root: &Id, palette_len: usize) -> usize` (FNV-1a 32-bit); `pub fn palette_rgb(&Config, idx) -> (u8,u8,u8)`; `pub fn parse_hex_colour(&str) -> Result<(u8,u8,u8), EmitError>`.

SVG (§17.2)
- `pub fn render_svg(bar: &DayBar, plan: &DayPlan, cfg: &Config, width_px: u32, height_px: u32) -> String` — one `<rect>`+`<title>` per segment, `<pattern id="tm-lost"|"tm-interrupt">` hatching, `stroke-dasharray="2 2"` on optionals, hour ticks (labels every 3 h), `class="cursor"` line + time label, `class="ghost"` row beneath from `bar.ghost` runs.

TEXT
- `pub fn render_now(plan, tree, now) -> String` (uses `Config::default()`), `pub fn render_now_with(plan, tree, cfg, now) -> String`.
- `pub fn render_diagnostics(diag: &Diagnostics, tree: &Tree, cfg: &Config) -> Vec<String>` — first line is always `"1 underused (4→3) · 0 ci-5 lost"`.
- `pub fn render_banners(plan: &DayPlan, tree: &Tree, cfg: &Config) -> Vec<String>` — §7.3's `"d1 CS 234 pset 2: needs 8b, 5b available by Fri"` (reads `plan.priorities`).
- `pub fn legend(plan: &DayPlan, tree: &Tree) -> EnergyMix`; `pub struct EnergyMix { minutes_at_ci: [u32;6], total_min: u32, share_ci4_plus: f64, underused_count: usize, optional_min: u32 }` + `EnergyMix::line()`.
- `pub enum EmitError { BadColour(String) }` (thiserror).

CONVENTIONS emit assumes of a DayPlan (documented in the module header, relevant to planner.rs): a finished segment (`flags.done`) spans what actually happened (so `(actual)` = `seg.minutes()`), `flags.planned_min`/`flags.multiplier` are the `2b×1.6` display pair, and a `SegKind::Wall` with `item == None` is §9's ad-hoc interruption (hatched red).

## Deviations (emit)
1. **Three signatures take one extra argument**, each because the value cannot be derived from what the scope listed: `render_diagnostics(diag, tree, cfg)` and `render_banners(plan, tree, cfg)` need `cfg.block_min()` to print "needs 8b"; `legend(plan, tree)` needs the tree because a segment carries the *slot's* energy while §11's energy mix is about the *item's* ci (slot energy is the fallback). `render_now` keeps the scope's `(plan, tree, now)` and uses `Config::default()`; `render_now_with(plan, tree, cfg, now)` is the explicit-config twin.
2. **`render_banners` is a second function.** §7.3's exact banner ("needs 8b, 5b available by Fri") needs `Prio::need_min`/`avail_min`, which live on `DayPlan::priorities`, not in `Diagnostics`; `render_diagnostics` alone can only say "d1 impossible: 3b short by 2026-09-11".
3. **`DayBar` carries four fields beyond `{cells, ghost, cursor_col}`** (`cols`, `wake`, `now`, `span_min`) so the SVG, the TUI widget and the tooltip/hover code measure with the same geometry rather than recomputing it.
4. **Three documented divergences from the §4.3 example** (its own rows are mutually inconsistent; the module header and the test header list them): (a) rows with a blank mark or a narrow ci-column glyph (`·`, `○`, `───`) start the title at column 14, where the example uses 15 — the example itself uses 14 on marked rows and on the `⏰`/`🌙` rows; (b) when an item has no `@parent`, the estimate stays in the estimate column (48) instead of sliding to 43; (c) the break's `(24m)` sits in the actual column (52), not at 48. Four rows (`07:00`, `08:00`, `09:20`, `21:30`) reproduce byte for byte, as do `@parent` at 43, `est` at 48 and the note at 55.
5. **The window divider rule is mine** (the spec shows the row without saying where it goes): at the end of the Block/Batch segment whose *elapsed* minutes take the day to `budget_blocks × block_min`, else at the window end, inserted before the first segment starting at/after that instant. On the §4.3 example this lands exactly at 15:10 with "window ends 16:00".
6. **`Cell::rgb` scales only `Work`.** §12.1's "brightness = ci (0 black … 5 full)" applied to routines (ci 1) or optionals (ci 0) would render them black, so every non-work style has a fixed colour (routines grey, breaks light grey, Lost orange, Interrupt red, walls dark, sleep near-black, rest/empty near-white) and `brightness` stays on the cell for the TUI.
7. **Interrupt detection**: `SegKind::Wall` with `item == None` maps to `CellStyle::Interrupt` (§9's ad-hoc wall; a synced wall always has an id). `SegKind::WindDown` maps to `CellStyle::Sleep`, `Rest`/`Lost` to their own styles.
8. **Row kinds the spec does not show** get sensible text: `Rest` → "rest 40m", `Lost` → "lost 55m", `Sleep` → "sleep 8h30m", all with the `·` glyph.

# review (layer 4)
Module `tm_core::review` (file opens with an "API overview" doc comment plus a "Choices the spec leaves open (deviations)" section).

CONSTS: `ADHERENCE_TOLERANCE_MIN: i64 = 10`, `REST_DEBT_WARN_MIN: u32 = 40`, `BREAK_OVERRUN_FACTOR: u32 = 2`, `CUT_STAMPS: usize = 2`, `HEAT_HOURS: usize = 24`, `HEAT_STYLES: usize = 7`.
ERRORS: `enum ReviewError { Store(#[from] StoreError) }` (thiserror). Only `write_day_review` can fail; every computation is infallible.
FORMATTING: `fmt_hm(u32) -> String` (`490 -> "8h10m"`), `fmt_blocks_min(minutes, block_min) -> String` (`30 -> "0.5b"`, `155 -> "2.6b"`, `20 -> "20m"`).

STATUS LINE (§11, §12.1)
```rust
pub struct PlannedBlock { pub id: Id, pub start: DateTime<Tz> }   // ::new(id, start)
pub struct StatusLine { blocks_done: u32, budget: u32, leak_min: u32, adherence_pct: Option<u8>,
                        window_end: Option<NaiveTime>, lost_min: u32, rest_debt_min: u32, load: f64 }
pub struct StatusHead { date: NaiveDate, now: NaiveTime, loc: Option<String>, wake: Option<NaiveTime>,
                        slept_min: Option<u32>, pred: Option<u8>, rep: Option<u8> }
pub fn status_line(&Replay, &Config, &RuntimeState, plan_at_arrival: &[PlannedBlock]) -> StatusLine;
pub fn render_status(&StatusLine) -> String;          // "● 5/6 · leak 14m · adherence 83% · window → 16:00 · lost 55m"
pub fn render_status_full(&StatusHead, &StatusLine) -> String;   // the whole §12.1 first line
```
The day is `runtime.date`, else the last day in the replay. `budget` falls back to `runtime.budget` → the `arrive` event → `capacity::budget_blocks(cfg)`. Above `REST_DEBT_WARN_MIN`, `render_status` appends `· rest debt 60m`.

DAY REVIEW (§12.4)
```rust
pub struct DayExtras { plan_at_arrival: Vec<PlannedBlock>, underused: usize,
                       tomorrow_first: Vec<TomorrowCandidate>, optional: Option<OptionalQuota>,
                       lost_note: Option<String>, budget: Option<u32> }   // Default
pub struct DayReview { date, loc: Option<String>, blocks_done, budget, load: f64, load_blocks: f64,
    block_len_min: u32 /* cfg.day.block_min */, plan_honesty: Option<f64>, block_min: u32 /* Σ worked */,
    window: Option<(NaiveTime, NaiveTime)>, lost_min, lost_note, leak: LeakLedger, adherence: Adherence,
    wake_to_arrive_min: Option<i64>, arrive_to_start_min: Option<i64>, replans: u32, drift_min: u32,
    breaks: BreakIntegrity, rest_debt_min: u32, mix: EnergyMix, energy: EnergyReview,
    estimates: Vec<energy::TagStats>, slept_min, onset_min: Option<u32>, done: Vec<Id>,
    demoted: Vec<DemotedRow>, tomorrow: Vec<TomorrowCandidate>, optional: Option<OptionalQuota> }
pub fn day_review(&Tree, &Replay, &Config, &Model, date: NaiveDate, tz: Tz, &DayExtras) -> DayReview;
pub fn render_day(&DayReview) -> String;   // exactly §12.4's seven rows
```
Parts: `LeakLedger { attributed_min, gap_min, total_min, longest_min }`; `Adherence { planned, started_on_time, completed, started_pct, completed_pct, missed: Vec<Id> }`; `BreakRow { planned_min, actual_min, place, over }` + `BreakIntegrity { breaks, planned_min, actual_min, over_count, over_share, by_where: BTreeMap<String,(usize,u32)> }`; `EnergyMix { minutes_by_ci: [u32;6], total_min, high_min, high_share, underused }`; `EnergyHour { hour, pred, rep: Option<u8> }` + `EnergyReview { n, mae, bias, by_hour, flip_hour: Option<u32>, mae_prior, mae_learned, hours: Vec<EnergyHour> }`; `DemotedRow { id, est_min, to }`; `TomorrowCandidate { id, note: Option<String> }` (`::new(id, Option<&str>)`); `OptionalQuota { minutes, cap_min: Option<u32>, outside_rest_min }`.

WEEK REVIEW
```rust
pub enum Style { Block, Break, Routine, Interrupt, Pause, Leak, Idle }  // .index() .all() .label()
pub struct DayHeat { date, hours: Vec<[u32; HEAT_STYLES]> /* 24 */, blocks_done, block_min }  // .total(Style)
pub struct LoungeRate { by_wake_hour: Vec<(u32, usize, f64)>, overall: Option<f64>, streak: u32 }
pub struct SleepRow { date, slept_min, onset_min: Option<u32>, blocks_done: u32 }
pub struct CurveOverlay { curve: String, prior: Vec<u8>, learned: Option<Vec<u8>> }
pub struct ChurnRow { id: Id, stamps: Vec<Stamp> }
pub struct WeekExtras { budget_blocks: Option<u32>, planned_blocks: Option<f64>, deadline_health: Option<DeadlineHealth> }
pub struct WeekReview { week, hit: Vec<Id>, demoted: Vec<Id>, blocks_per_day: Vec<(NaiveDate,u32)>,
    blocks_done, block_min, load: f64, block_len_min, heat: Vec<DayHeat>, mix: EnergyMix,
    breaks: BreakIntegrity, latency: Vec<(NaiveDate, Option<i64>, Option<i64>)>, sleep: Vec<SleepRow>,
    lounge: LoungeRate, mae_per_day: Vec<(NaiveDate, usize, f64)>, estimates: Vec<TagStats>,
    curves: Vec<CurveOverlay>, planned_blocks: f64, budget_blocks: Option<u32>, plan_honesty: Option<f64>,
    deadline_health: Option<DeadlineHealth>, churn: Vec<ChurnRow>, carry_in_min, carry_out_min: u32 }
pub fn week_review(&Tree, &Replay, &Config, &Model, week: IsoWeek, tz: Tz, &WeekExtras) -> WeekReview;
pub fn render_week(&WeekReview) -> String;
```
Milestones = the week file's top-level items (a child of another week item is a task). `plan_honesty = planned_blocks / (budget_blocks × cfg.week.plan_ratio)`. Churn reuses `horizon::churn(tree, CUT_STAMPS)`.

MONTH REVIEW
```rust
pub struct OutcomeRow { id, title: String, k: u8, done: bool, progress: Option<f64> }
pub struct MonthExtras { cut_stamps: usize }   // Default = CUT_STAMPS
pub struct MonthReview { month, block_len_min, outcomes: Vec<OutcomeRow>, done_count: usize,
    demoted: Vec<Id>, churn: Vec<ChurnRow>, carry_over: Vec<(String /*"2026-W36"*/, u32)>, cuts: Vec<Id> }
pub fn month_review(&Tree, &Replay, &Config, month: YearMonth, tz: Tz, &MonthExtras) -> MonthReview;
pub fn render_month(&MonthReview) -> String;
```

WRITING
```rust
pub fn write_day_review(store: &dyn Store, date: NaiveDate, text: &str) -> Result<(), ReviewError>;
```
Replaces the body of the day file's `<!-- tm:review start --> … <!-- tm:review end -->` block (the one `horizon::close_day` leaves with `horizon::REVIEW_PLACEHOLDER`), appends the block at the end when it is missing, and creates the day file with its front matter when it does not exist. Goes through `Store::modify_file`, so §1.3's race guard applies.

Typical CLI use (`tm review day --write --json`): `let replay = log.replay(None, cfg.tz); let r = review::day_review(&tree, &replay, &cfg, &model, today, cfg.tz, &extras);` then `println!("{}", review::render_day(&r))` or `serde_json::to_string(&r)`, and `review::write_day_review(&store, today, &review::render_day(&r))` for `--write`. Every review type is `Serialize` + `Clone` + `Debug` + `PartialEq` (no `Deserialize`: `priority::DeadlineHealth` and `check`-style `&'static str` fields are serialize-only upstream).

## Deviations (review)
All are listed in review.rs's module header under "Choices the spec leaves open (deviations)":

1. `load` is §11's formula literally (`Σ block_min × ci / 5`, ci-weighted minutes — what `log::DayReplay::load` computes). §12.4's printed `load 18.4` is not reproducible from its own row (five blocks) under any reading of the formula, so the value is the formula's, not the example's (the fixture day prints `load 293.0`). `DayReview::load_blocks` gives the same quantity in blocks. Block minutes the log has no `ci` for (`DayReplay::ci_unknown`, a block cut by `stop`) are attributed from the tree, so load and the energy mix cover every logged minute.
2. Leak ledger = attributed `idle{leak}` + unattributed gaps ≥ `cfg.day.idle_min` (`DayReplay::gaps`); "longest single leak" is the longest of either kind.
3. Adherence: each `start` is matched to at most one planned block, closest first, within `ADHERENCE_TOLERANCE_MIN`; "completed" = the planned id has a non-partial `done` that day. `missed` lists the planned blocks that were not started on time.
4. Rest debt = `⌊blocks_done / break_after_blocks⌋ × break_min − Σ breaks taken`, floored at 0 (§11 gives no formula), so a cut break and a skipped break cost the same.
5. Energy calibration is scored on the LOGGED `pred` (via `energy::calibration`) — that is what §12.4's row shows; `mae_prior`/`mae_learned` additionally re-score the config prior and the learned model with `energy::compare`. `flip_hour` = the first hour whose bias sign is opposite the first non-zero hour's and after which that first sign never returns (`None` when it never flips or flips back).
6. Estimate calibration runs over the WHOLE replay's durations, not just the day's: §12.4's `lean ×1.6 (n=9)` is a running multiplier.
7. Event-to-day attribution: the replay's wake-to-wake day everywhere it already bucketed; demotions (kept globally by the replay) are attributed by their calendar date in `tz`.
8. Plan honesty: for the week `planned / (budget × cfg.week.plan_ratio)` with the budget a parameter (it lives in the week file's front matter, which the tree does not carry) and planned defaulting to Σ `remaining` over the week's top-level items; for the day `plan_at_arrival.len() / budget` (§8.1 has already applied `budget_ratio`, so the day budget IS the realistic one).
9. Signatures: `status_line` takes `cfg` in addition to the replay/runtime/plan (the leak ledger needs `idle_min`, rest debt needs `break_min`/`break_after_blocks`, and the budget falls back to §8.1's formula); the three review functions take their `*Extras` by reference. Otherwise the shapes are §11's and §13's.
10. `fmt_blocks_min` differs from `priority::fmt_blocks` only in printing a half block as `0.5b` rather than `30m`, matching §12.4's `t5 (0.5b → week)`.
11. Not implemented here: §11's "Waiting" row, whose surface is §12.3's Necessities screen and whose data is `Tree::waiting_ids` + the `waiting:` stamp (no log involved). `HEAT_STYLES = 7` splits idle into `Leak` and `Idle` so §12.1's hatched-orange leak can be drawn separately.

# cli (layer 4)
`tm` is a bin crate, so nothing is importable; what a downstream agent (the TUI) needs is the module tree and its seams. All items are documented and each file opens with an "API overview".

tm/src/main.rs — `mod cli;` + `fn main() { std::process::exit(cli::main()) }`.

cli/mod.rs
- `pub struct Cli { json: bool, dir: Option<PathBuf>, now: Option<String>, command: Command }` (clap derive; `--json`, `--dir`, hidden `--now <RFC3339>` are `global = true`).
- `pub enum Command { Init, Wake, Arrive, Plan, Now, Start, Done, Extend, Stop, Break, Interrupt, Resume, Pause, Energy, Idle, Add, Edit, MoveItem(name="move"), Rank, Demote, Readopt, Drop, Event, Skip, Routine, Close, SyncCal(name="sync-cal"), Review, Model, Log, Undo, Triage, Check, Tui }` with one Args struct per verb (`PlanArgs`, `StartArgs`, …) and `pub enum PeriodArg { Day, Week, Month } -> model::Period`.
- `pub fn main() -> i32`; `fn run(&Globals, Command) -> Result<i32, CliError>`.
- **TUI seam**: `Command::Tui => lifecycle::tui()`. The TUI agent adds `tm/src/tui/` and replaces that one arm (`lifecycle::tui()` currently prints "tm tui: not built yet" to stderr and returns 1).

cli/ctx.rs
- `pub struct Globals { dir: Option<PathBuf>, json: bool, now: Option<DateTime<FixedOffset>> }`
- `pub fn resolve_dir(Option<&Path>) -> Result<PathBuf, CliError>` (--dir, $TM_DIR, then walk up for a plan root or a `plan/` child).
- `pub struct Ctx { store: FsStore, cfg: Config, json: bool, now: DateTime<FixedOffset>, now_tz: DateTime<Tz>, today: NaiveDate, state: RuntimeState, files: PlanFiles, tree: Tree, log: Log, replay: Replay, model: Model, closed: Vec<ClosedPeriod>, timed_out: Vec<Id> }`
- `Ctx::load(&Globals, housekeeping: bool)`, `reload()`, `hz() -> horizon::Ctx`, `append_event(Event)`, `append_entry(&LogEntry)`, `save_state()`, `key(&str) -> Id`, `item(&Id)`, `line(&Id) -> ItemLine`, `write_line(&Id, &ItemLine)`, `block_min()`, `loc()`, `wake_time()`, `wake_dt()`, `slept_min()`, `at(NaiveTime) -> DateTime<Tz>`, `instant(NaiveDateTime)`, `walls_today()/walls_on(date)/walls_by_date(days)`, `window() -> (start, end, budget)`, `today_slots(allow_home) -> Vec<Slot>`, `priorities(allow_home) -> (Vec<Candidate>, Vec<Prio>, Vec<DayCapacity>)`, `hysteresis_input()`, `last_plan()/save_last_plan()`, `plans_today()`, `taken_ids()`.
- `pub const LAST_PLAN_PATH = ".tm/last_plan.json"`, `ARRIVAL_PLAN_PATH = ".tm/arrival_plan.json"`; `pub struct StoredPlan { date, hash, priorities: BTreeMap<Id,u8>, segments: Vec<StoredSegment{start,end,kind,item}> }`.

cli/out.rs — `pub enum CliError { Msg, NotFound(Id), Usage, Store, Horizon, Log, Ics, Model, Edit, Check, Energy, Io{path,source}, Json }` (thiserror, `#[from]` for each core error) + `msg()`, `io()`, `conflict() -> Option<&StoreError>`, `exit_code()`, `message()`, `document() -> ErrorOut`, `report(json: bool)`; `pub struct ErrorOut { ok: false, kind: &'static str, message, exit_code, detail: serde_json::Map }` with `report()` — §13's `--json` failure document, defined once here and printed on stderr by `CliError::report(true)`, so every verb's `Err` is machine-readable without a verb touching it (`kind` slugs: `not-found conflict invalid usage parse edit horizon io json config log model calendar error`); `pub fn emit<T: Serialize>(json: bool, human: impl FnOnce() -> String, &T)` (the success half, stdout); `fmt_dur`, `fmt_time`; `EXIT_ERROR = 1`, `EXIT_CONFLICT = 3`. `tm check`'s exit 2 is a *result*, not a failure: it keeps `emit` and stdout.

cli/undo.rs — `pub const UNDO_PATH = ".tm/undo.json"`, `MAX_ENTRIES = 50`; `pub struct Recorder` (`start(&Ctx, verb)`, `finish(&Ctx, summary)`), `pub struct UndoEntry { verb, t, summary, events: Vec<UndoneEvent{ev,id}>, files: Vec<FileBefore{path,before}>, state: RuntimeState }`, `pub struct UndoStack`, `pub fn undo(&mut Ctx) -> Result<Undone, CliError>`.

cli/planning.rs — `pub fn build(&Ctx, allow_home) -> (DayPlan, Vec<Prio>)`, `pub fn write_plan(&mut Ctx, &DayPlan, &[Prio]) -> Result<Vec<String>, CliError>` (day section + SVG + `plan` event + state/sidecar), `pub fn seg_out(&DayPlan, &Ctx) -> Vec<SegOut>`, `plan()`, `now()`; output structs `PlanOut`, `SegOut`, `PlanDiff`, `WeekOut`, `DayOut`, `NowOut`, `ActiveOut`.

cli/render.rs — the **adapter onto `tm_core::emit`**, not a renderer of its own: `pub fn rows(&DayPlan, &Tree, &Config) -> Vec<Row{time,energy,mark,text,item,kind}>` (one per segment, built from `emit::mark_of` + `emit::render_segment_row`), `pub fn timeline(&DayPlan, &Tree, &Config, now) -> String` (the `tm:plan` body — `emit::render_plan_section(..).1`), `pub fn diagnostics(&DayPlan, &Tree, &Config) -> Vec<String>` (`emit::render_diagnostics`), `pub fn svg(&DayPlan, ghost: Option<&DayPlan>, &Tree, &Config, wake, now) -> String` (`emit::daybar_cells` at `SVG_COLS = 96` then `emit::render_svg` at 960×64), `pub fn kind_name(&SegKind) -> &'static str` (the word `--json` and `.tm/last_plan.json` use). One text for one `DayPlan` across `tm plan`, `tm tui` and the M4 snapshots.

cli/ghost.rs — §12.1's ghost row, shared by both frontends. `pub use crate::tui::app::ArrivalBlock as Block` (the type lives under `tui/` so nothing there imports `crate::cli`), `pub fn blocks(&Ctx) -> Vec<Block>` (`.tm/arrival_plan.json` for *today*; empty when missing, unreadable or stale), `pub fn plan(&[Block], &Config, &Model, &Tree, &RuntimeState, fallback: &DayPlan) -> Option<DayPlan>` — the arrival record **rebuilt** into a `DayPlan` (blocks sized `est × multiplier` per §8.5, clipped at the next recorded start, gaps left empty), never re-planned, since a `plan()` at the arrival instant would see today's log and today's state. `tm plan` feeds it to `render::svg`; the TUI draws it under the day bar.

cli/day.rs, cli/items.rs, cli/lifecycle.rs, cli/init.rs — one `pub fn <verb>(&Globals, &Args) -> Result<i32, CliError>` per verb plus its `Serialize` output struct (`WakeOut`, `ArriveOut`, `StartOut`, `DoneOut`, `ExtendOut`, `StopOut`, `BreakOut`, `InterruptOut`, `PauseOut`, `EnergyOut`, `IdleOut`, `AddOut`, `EditOut`, `MoveOut`, `RankOut`, `DemoteOut`, `DropOut`, `EventOut`, `InstanceOut`, `TriageOut`, `CloseOut`, `SyncOut`, `ReviewOut`, `ModelOut`, `LogOut`, `CheckOut`, `InitOut`, `Undone`). Reusable by the TUI: `lifecycle::sync_calendar(&Ctx) -> Result<SyncOut, CliError>` (what `R` should call) and `items::id_gen(&Ctx, salt) -> IdGen` (deterministic id seeding).

## Deviations (cli)
1. **`cli/render.rs` is an adapter, not a second renderer.** It was written when `emit.rs` was a stub; every function now delegates to `tm_core::emit` (§1.2's home for the renderer) and the module keeps its own SVG geometry constants (`SVG_WIDTH/HEIGHT/COLS`) and the `Row`/`kind_name` shapes `--json` serialises. It stays because those two are CLI surface, not `emit` surface.
2. **`tm review` returns the real review document.** `lifecycle::review` calls `tm_core::review`'s `day_review`/`week_review`/`month_review` and prints `render_day`/`render_week`/`render_month`; `--json` is `ReviewOut { period, key, review: ReviewBody, wrote }` where `ReviewBody` is an untagged `Day(Box<DayReview>) | Week(Box<WeekReview>) | Month(Box<MonthReview>)` — the object §14's `/review-day` and `/review-week` skills read field by field (`tm/tests/init_skills.rs` checks every field name those skills quote against this output). The plan-dependent half of the day monitors comes from `lifecycle::day_extras` (adherence against `.tm/arrival_plan.json`, the under-used count, tomorrow's candidates, the optional quota, the budget), and only for *today*: an earlier day gets what the log alone knows.
3. **`tm plan --week` still does not call `planner::week_plan`**, though that function now exists: the verb only needs the §8.4 grid, so it stays `capacity::lookahead(7 days)` + `capacity::week_grid`. `planner::week_plan` (and `WeekPlan`) is what a caller wanting the *plan* per day would use.
4. **Sidecars, because `RuntimeState` has no field for them** (I may not edit store.rs, and unknown keys in state.json are dropped on save): `.tm/undo.json` (the undo stack the scope wanted in state.json), `.tm/arrival_plan.json` (the `plan_at_arrival` block starts for §12.1's ghost row), `.tm/last_plan.json` (`--diff` baseline + the §7.4 hysteresis roll, which needs to know which *day* the stored priorities belong to). All three are documented at their definitions.
5. **Events §10.1 does not define**: `tm add` logs `edit{id, field:"add", from:"", to:<line>}` (there is no `add` event, and undo needs a target); a §5.1 waiting *timeout* logs `edit{id, field:"state", from:"[?]", to:"[ ]"}` (there is no timeout event). `tm rank` logs nothing (§10.1 has no rank event) but is still undoable.
6. **`tm break` is a toggle**: the first call sets `state.break` only; the second (or the next `start`/`done`/`stop`) appends one complete `break{planned_min, actual_min, where}` stamped at the break's *start*. That gives §11's break integrity a real `actual_min` with exactly one event per break, at the cost of the start itself not being logged.
7. **Undo reverts whole-file bytes**: a `Recorder` snapshots every plan `*.md`, `state.json` and the log length before a verb; `tm undo` appends one `undo{of,id}` per event the verb wrote (newest first), restores the changed files' previous bytes (deleting files the verb created), and restores `state.json` except `closed` (so the auto-close does not re-run). Simpler and more robust than inverse line edits; `.tm/last_plan.json` and the SVG are caches and are not restored.
8. **Deterministic ids**: `tm add` and `tm check --fix-ids` seed `IdGen` from `now` + the line text instead of `IdGen::from_entropy()`, so `--now` pins them for snapshots and nothing in the binary reaches for entropy.
9. **`tm start` refuses to start a second block** (`tm done`/`tm stop`/`tm extend` first) rather than silently cutting the running one.
10. **`tm close <period>` closes the current period** by default (`--date` picks another); the *previous* period is what the auto-close handles, so the explicit verb is "I am finished with this one".
11. **`tm plan` logs a `plan` event only when the hash changed** (per `DayPlan::hash`'s contract) so a standing day is not counted as a replan; it always rewrites the section, the SVG and the sidecar. `--explain` writes nothing at all.
12. **Extra flags** (all optional, none replacing a spec flag): `done --went 1|2|3` (§10.1's `went`), `arrive --at HH:MM`, `close/review --date`, `idle --min`, `init --example|--force`, `readopt --to`, `move --section`.
13. **Usage errors exit 1**, not clap's default 2 (§13 reserves 2 for validation problems); `--help`/`--version` exit 0.
14. `est:` written by `stop`/`extend`/`done --partial` uses whole blocks when the minutes divide evenly, mirroring `horizon.rs`'s private `est_dur` so a stop and a day close write the same text.
15. The **exit-3 conflict path is unit-tested** in `cli/out.rs`, not integration-tested: the §1.3 race needs a writer between the store's read and its verified write (`FsStore::with_before_write_hook`), which cannot be provoked from outside the process — as the scope anticipated.

# tui-today (layer 5)
`tm` is a bin crate, so nothing is importable; what the queue agent (screens 2–5) needs is the module tree and the seams. Every file opens with an "API overview" doc comment.

crate::tui (tm/src/tui/mod.rs)
- `pub mod app; pub mod daybar; pub mod inbox; pub mod necessities; pub mod prompts; pub mod queue; pub mod review; pub mod theme; pub mod today;` — screens 2–5 are wired into the binary, not pending: `app` dispatches their §12.6 key rows and `today::draw` gives each of them the body area.
- `pub fn run(g: &cli::ctx::Globals) -> Result<i32, CliError>` — the whole frontend. Private helpers: `setup/restore/resume/install_panic_hook`, `load/reload/data_of/now_of`, `watch/is_watched`, `event_loop`, `mouse`, `perform`, `verb`, `editor`; `const DEBOUNCE = 200ms`, `POLL = 200ms`, `INTERACTIVE_VERBS = ["start"]`.

crate::tui::app — pure, no terminal/store/clock
```rust
pub enum Screen { Today, Queue, Necessities, Review, Inbox }   // Copy+Default(Today)+Eq+Hash
impl Screen { const ALL: [Screen;5]; fn from_digit(char)->Option<Screen>; fn number()->u8; fn title()->&'static str }
pub enum Mode { Normal, BreakWhere, Energy, Command, Input(InputKind), Help }   // Clone+Default+Eq
pub enum InputKind { Note, Location }              // + label()
pub enum BreakPlace { Walk, Seat, Bed, Phone }     // + as_str(), from_key(char)
pub enum Answer { Extend, Stop, Done, Later, Work, Break, Routine, Interrupt, Leak }
pub enum Action { None, Screen(Screen), Help, CommandLine, Quit, Edit, Replan, ReplanOrResume,
                  Sync, Done, Extend, Stop, Break, BreakWhere(BreakPlace), Interrupt,
                  EnergyPrompt, Energy(u8), Location, SkipRoutine, Note, Pause,
                  SelectNext, SelectPrev, Open, Cancel, Submit, Input(char), Backspace,
                  Answer(Answer) }                 // Clone+Debug+Eq
pub enum Effect { Verb(Vec<String>), Editor{file: String, line: usize}, Note(String),
                  SetLocation(String), Quit }      // Clone+Debug+Eq
pub struct Overtime { id, title, est: String, multiplier: Option<f64>, planned_min, elapsed_min,
                      drops: Vec<String>, stays: String, reprompt_min }
pub struct Idle { minutes: u32 }
pub enum Prompt { Overtime(Overtime), Idle(Idle) }  // + kind() -> PromptKind
pub enum PromptKind { Overtime, Idle }
pub struct TimelineRow { text: String, segment: Option<usize> }   // segment None = the ─── divider
pub struct Hover { col: usize, text: String }
pub struct Milestone { id, title, done_min, planned_min, done: bool, hot: bool }
pub struct HotRow { id, title, note }   pub struct WaitRow { id, title, note }
pub struct WeekPane { week: Option<IsoWeek>, done_blocks, planned_blocks, milestones, hot, waiting, diagnostics }
pub struct EnergyPane { hours: Vec<u32>, pred: Vec<u8>, rep: Vec<Option<u8>> }
pub struct AppData { cfg: Config, model: Model, state: RuntimeState, tree: Tree, log: Log,
                     replay: Replay, now: DateTime<Tz> }
pub struct App {
    // data
    pub cfg, model, state, tree, log, replay, posterior: Posterior, now: DateTime<Tz>, today: NaiveDate,
    pub plan: DayPlan, pub ghost: Option<DayPlan>,
    // digests refresh() recomputes
    pub rows: Vec<TimelineRow>, pub status: StatusLine, pub head: StatusHead,
    pub week: WeekPane, pub energy: EnergyPane,
    // UI
    pub screen: Screen, pub mode: Mode, pub selection: usize, pub selected_item: Option<Id>,
    pub input: String, pub message: Option<String>, pub hover: Option<Hover>,
    pub prompt: Option<Prompt>, pub prompt_at: Option<DateTime<Tz>>, pub quit: bool,
}
impl App {
    pub fn new(AppData) -> App;                       // plans from `now`
    pub fn with_plan(AppData, DayPlan, Option<DayPlan>) -> App;   // the tests' constructor
    pub fn adopt(&mut self, AppData);                 // after a write/file change; keeps the UI state
    pub fn replan(&mut self);  pub fn refresh(&mut self);
    pub fn tick(&mut self, now) -> bool;              // replans on a minute change, raises prompts
    pub fn timeline_rows(&self, title_w: usize) -> Vec<TimelineRow>;
    pub fn wake(&self) -> DateTime<Tz>;  pub fn loc(&self) -> Loc;
    pub fn predicted_energy(&self, at) -> u8;
    pub fn title_of(&Id) -> String;  pub fn priority_of(&Id) -> Option<u8>;
    pub fn selected_segment(&self) -> Option<usize>;  pub fn selected_location(&self) -> Option<(String, usize)>;
    pub fn select(&mut self, delta: isize);           // RELATIVE
    pub fn select_segment(&mut self, segment: usize);
    pub fn active_elapsed_min(&self) -> Option<u32>;
    pub fn overtime_due(&self) -> Option<Overtime>;  pub fn idle_due(&self) -> Option<Idle>;
    pub fn raise_prompt(&mut self) -> bool;
    pub fn action_for(&self, KeyEvent) -> Action;     // = resolve(screen, mode, prompt, key)
    pub fn apply(&mut self, Action) -> Vec<Effect>;
}
pub fn resolve(Screen, Mode, Option<PromptKind>, KeyEvent) -> Action;
pub fn split_args(&str) -> Result<Vec<String>, String>;   // quote-aware `:` splitting
```

crate::tui::today
```rust
pub fn draw(f: &mut Frame, app: &App);                       // the whole frame, all screens
pub fn is_wide(&App, Rect) -> bool;  pub fn bar_area(&App, Rect) -> Rect;   // mouse hit-testing
pub fn status_line(&App, width) -> Line;  pub fn week_fold(&App, width) -> Line;
pub fn timeline_lines(&App, width, height) -> Vec<Line>;
pub fn now_lines(&App, width) -> Vec<Line>;
pub fn energy_lines(&App, width) -> Vec<Line>;
pub fn week_lines(&App, width) -> Vec<Line>;  pub fn week_title(&App) -> String;
pub fn hint_line(&App, width) -> Line;
```

crate::tui::daybar
```rust
pub const LABEL_W: u16 = 14;                 // right-hand `▲ 10:42` / `plan @07:00` gutter
pub fn bar_width(Rect) -> usize;  pub fn bar(&App, cols) -> emit::DayBar;
pub fn draw(f, Rect, &App);  pub fn draw_tooltip(f, Rect, &Hover);
pub fn hit(Rect, column: u16, row: u16) -> Option<usize>;
pub fn tooltip(&DayBar, col) -> Option<String>;  pub fn segment_at(&DayBar, col) -> Option<usize>;
```

crate::tui::prompts
```rust
pub fn overtime_lines(&Overtime) -> Vec<Line>;  pub fn overtime_title(&Overtime) -> String;
pub fn idle_lines(&Idle) -> Vec<Line>;          pub fn idle_title(&Idle) -> String;
pub fn lines(&Prompt) -> (String, Vec<Line>);   pub fn help_lines() -> Vec<Line>;
pub fn centred(Rect, w, h) -> Rect;             pub fn draw(f, Rect, &Prompt);  pub fn draw_help(f, Rect);
```

crate::tui::theme
```rust
pub const STATUS, HINT, ACCENT, WARN, DIM, SELECTED, OVERLAY, CURSOR, TOOLTIP: Style;
pub fn pane(&str) -> Block;  pub fn pane_focused(&str) -> Block;
pub fn cell_glyph(&emit::Cell) -> char;  pub fn cell_style(&emit::Cell, &Config, ghost: bool) -> Style;
```

Those hooks are now taken. `App` carries the four screen states (`queue: queue::QueueState`, `necessities: necessities::NecessitiesState`, `review: review::ReviewState`, `capture: inbox::CaptureState`) and builds what they render from: `App::view(&self) -> queue::View<'_>` and `App::reviews(&self) -> review::Reviews`. A key the shell's own rows do not claim becomes `Action::ScreenKey(KeyEvent)`; `App::screen_key` hands it to the screen's `on_key` (Today ignores it), and `screen_action` turns the returned `queue::Action` into shell `Effect`s — `Ignored` falls back to the global row (with `r` = Replan), `Note`/`Edit`/`Prompt`/`Mutate` become a message, an editor or a verb. `today::draw` matches `Screen::{Queue, Necessities, Review, Inbox}` to `queue::render` / `necessities::render` / `review::render` / `inbox::render` over the body area.

Test harness reuse: `tm/tests/tui_common/mod.rs` pulls the nine pure modules in with `#[path = "../../src/tui/<file>.rs"]` (theme, app, daybar, prompts, today, queue, necessities, inbox, review — a bin crate has no lib target, so `use tm::…` is impossible) and offers `config()`, `tree(&cfg)`, `log(&cfg)`, `state()`, `day_plan(&cfg)`, `ghost_plan(&cfg)`, `app()`, `app_at(h, m)`, `overtime_app(h, m, est_min)`, `tight_overtime_app()`, `idle_app(h, m)`, `render(&App, w, h)`, `render_lines(&[Line], w)`, `lines(&[Line])`, `prio(id, p, class)`, `seg(...)`, `at(&cfg, h, m)`. It deliberately does NOT include `mod.rs`, so adding `pub mod queue;` there cannot break these tests.

# tui-queue (layer 5)
All four screen modules are self-contained: they depend only on tm-core, ratatui, crossterm and chrono. Shared plumbing lives in `queue.rs`; `necessities.rs`, `inbox.rs` and `review.rs` do `use super::queue::{...}`, which resolves identically whether they sit under `tui/` or at a test crate's root.

SHARED (tm::tui::queue)
```rust
pub struct View<'a> { tree: &Tree, files: &PlanFiles, cfg: &Config, replay: &Replay,
                      candidates: &[Candidate], prios: &[Prio], caps: &[DayCapacity],
                      today: NaiveDate, now: DateTime<Tz>, /* private done map */ }
impl View<'a> { fn new(tree, files, cfg, replay, candidates, prios, caps, today, now) -> View<'a>;
                fn week() -> IsoWeek; fn month() -> YearMonth; fn block_min() -> u32;
                fn prio(&Id) -> Option<&Prio>; fn candidate(&Id) -> Option<&Candidate>;
                fn done_minutes() -> &HashMap<Id,u32>; fn progress(&Id) -> Option<f64> }

pub enum Action { Ignored, Redraw, Note(String), Edit(Id), Prompt(Prompt), Mutate(Mutation) }
pub enum Prompt { Add{file: String, section: Option<String>}, Ci(Id), Estimate(Id), Priority(Id) }
pub enum Mutation { Reorder{id: Id, delta: i32}, Demote(Id), Readopt(Id), Drop(Id),
                    Skip{item: Id, instance: InstanceKey}, Event{name: String, id: Option<Id>},
                    Capture{text: String, file: String, section: Option<String>, from_inbox: Option<usize>},
                    DropInboxLine{line: usize} }

pub fn width(&str)->usize; pub fn truncate(&str, usize)->String; pub fn pad(&str, usize)->String;
pub fn fmt_u(Option<f64>)->String;                       // "u=0.6" | "u=∞" | ""
pub fn fmt_fits(&Prio, remaining_min: u32, block_min: u32)->String;   // "fits 6/6"; "" for pure-rank
pub fn bar(Option<f64>, cells: usize)->String;           // "▓▓▓░░░"
pub fn due_text(NaiveDate, today: NaiveDate)->String;    // "due today"|"due Fri"|"due Oct 20"
pub fn est_text(&View, &Id)->String;
pub fn edit_command(&Config, &Tree, &Id)->Option<String>;// "code -g week/2026-W37.md:8"
pub fn reorder(&dyn Store, &Id, delta: i32)->Result<bool, StoreError>;  // J/K, byte-faithful
```

SCREEN 2 (queue.rs)
```rust
pub enum Pane { Month, Week, Tasks }   // .left() .right()
pub struct QueueState { pane, month_sel, week_sel, task_sel, anchor: Pane, focus: Option<Id> }
impl QueueState { fn new(); fn parent(&View)->Option<Id>; fn selected(&View)->Option<Id> }
pub struct MonthRow { id, priority: Option<u8>, title, bar, demoted: bool, stamps }
pub struct WeekRow  { id, p: Option<u8>, hysteresis: bool, ci, est, title, parent, due, u, fits,
                      bar, done: bool, wall: bool }
pub struct TaskRow  { id, p: Option<u8>, ci, est, title, blocked: Option<String>, done: bool }
pub fn month_rows(&View)->Vec<MonthRow>;
pub fn week_rows(&View)->Vec<WeekRow>;
pub fn task_rows(&View, parent: Option<&Id>)->Vec<TaskRow>;
pub fn fits_footer(&View, &[TaskRow])->String;           // "fits this week: 6b of 6b"
pub const KEYMAP: &str; pub const KEYMAP_NARROW: &str;
pub fn render(&QueueState, &View, &mut Frame, Rect);
pub fn on_key(&mut QueueState, &View, KeyEvent) -> Action;
```

SCREEN 3 (necessities.rs)
```rust
pub enum Cell { Free, Window, Wall, Conflict }           // .glyph() .style()
pub const FIRST_HOUR: u32 = 6; LAST_HOUR: u32 = 24; MAX_WINDOW_HOURS: i64 = 12; GRID_WIDTH: u16 = 33;
pub struct Grid { days: [NaiveDate;7], cells: Vec<[Cell;7]>, conflicts: Vec<(Id,Id)> }
pub fn grid(&View) -> Grid;
pub enum Section { Impossible, Dated, Waiting, Necessary }   // .title(); Ord = display order
pub struct Row { section, id, title, p: Option<u8>, need, capacity, u, detail,
                 instance: Option<InstanceKey>, event: Option<String> }
pub fn rows(&View) -> Vec<Row>;
pub struct NecessitiesState { sel: usize }               // ::new(), .selected(&View)
pub const KEYMAP: &str;
pub fn render(&NecessitiesState, &View, &mut Frame, Rect);
pub fn on_key(&mut NecessitiesState, &View, KeyEvent) -> Action;
```

SCREEN 4 (review.rs) — §12.4, and the one screen that renders `tm_core::review` rather than a `View`
```rust
pub enum Period { Day, Week, Month }                     // Copy+Default(Day); .left() .right() .verb() .title()
pub struct Reviews { day: DayReview, week: WeekReview, month: MonthReview }   // + .text(Period) -> String
pub struct ReviewState { period: Period, scroll: usize } // ::new()
pub fn on_key(&mut ReviewState, &Reviews, KeyEvent) -> Action;
pub fn render(&ReviewState, &Reviews, &mut Frame, Rect);
```
`h`/`l` (or `[`/`]`) change the period, `j`/`k` scroll, `w` and `c` return `Action::Note` with the command to run (`review <period> --write`, `/review-<period>`) rather than writing or shelling out. Every number is `render_day`/`render_week`/`render_month`'s, so the screen, `tm review` and §17 M8's hand-computed values are one set.

SCREEN 5 (inbox.rs)
```rust
pub const CLAUDE_TRIAGE: &str;                           // the `C` command line
pub struct Target { file: String, section: Option<String> }  // ::new, .is_bare(), Display "f.md #Sec"
pub fn targets(&View) -> Vec<Target>;                    // the Tab ring, 5 entries
pub struct Normalized { ci: Option<u8>, est: Option<String>, title: String,
                        tokens: Vec<String>, problem: Option<String> }
pub fn normalize(&str, &Config, today: NaiveDate) -> Normalized;
pub struct Capture { raw, line: String, target: Target, target_index: usize, problem: Option<String> }
pub fn capture(input: &str, &View, target: Option<usize>) -> Capture;
pub fn preview_text(&Capture) -> String;                 // "parsed  <line>  → <target>"
pub struct InboxLine { line: usize, raw: String, parsed: String, problem: Option<String> }
pub fn inbox_lines(&View) -> Vec<InboxLine>;
pub struct CaptureState { buffer, editing: bool, target: Option<usize>, sel, triaging: Option<usize>,
                          note: Option<String> }         // ::new(), .capture(&View)
pub const KEYMAP_EDITING: &str; pub const KEYMAP_LIST: &str;
pub fn render(&CaptureState, &View, &mut Frame, Rect);
pub fn on_key(&mut CaptureState, &View, KeyEvent) -> Action;
```

MERGED (tui/mod.rs declares all four; `today::draw` and `App` dispatch them):
```rust
pub mod queue; pub mod necessities; pub mod inbox; pub mod review;
Screen::Queue       => queue::render(&app.queue, &app.view(), f, body),
Screen::Necessities => necessities::render(&app.necessities, &app.view(), f, body),
Screen::Review      => review::render(&app.review, &app.reviews(), f, body),
Screen::Inbox       => inbox::render(&app.capture, &app.view(), f, body),
// key dispatch: App::screen_key -> <screen>::on_key(&mut app.<state>, &view, key) -> queue::Action
```
`App` carries the four states (`queue`, `necessities`, `review`, `capture`), `fn view(&self) -> queue::View<'_>` built from its already-loaded tree/files/cfg/replay/candidates/prios/caps, and `fn reviews(&self) -> review::Reviews` built the way `tm review` builds them. Each `render` draws its own §12.6 keymap row on the last line of the area it is given; pass a one-line-shorter area to suppress it.

# init (layer 5)
`tm` is a bin crate, so this is the module seam, not an importable API. New private-to-the-binary module `tm::init` (declared as `mod init;` in tm/src/main.rs, sibling of `cli`):

Constants (all embedded from tm/templates/ with include_str!):
- `pub const CLAUDE_MD: &str` — §14's rules, verbatim.
- `pub const SETTINGS_JSON: &str` — .claude/settings.json.
- `pub const PRE_COMMIT: &str` — .githooks/pre-commit.
- `pub const GITIGNORE: &str` — the runtime-state ignore block.
- `pub const SKILLS: &[(&str, &str)]` — 8 (name, SKILL.md) pairs in §14 table order.
- `pub const DIRS: &[&str] = &["calendar", ".tm"]`, `pub const HOOKS_DIR: &str = ".githooks"`.

Types:
- `pub struct Options { pub today: NaiveDate, pub example: bool, pub force: bool }` + `Options::new(today) -> Options` (today is injected; no clock in the module).
- `pub enum Mode { Managed, Executable, Merge }` — how one file is written (Merge = user-owned, appended to, never rewritten).
- `pub struct InitFile { pub path: String, pub text: String, pub mode: Mode }`.
- `pub struct Written { pub created: Vec<String>, pub unchanged: Vec<String> }`.
- `pub enum InitError { NotEmpty { dir: String }, Io { path: String, source: io::Error } }` (thiserror).

Functions:
- `pub fn files(&Options) -> Vec<InitFile>` — the whole tree, pure, in write order (snapshot-friendly, no I/O).
- `pub fn write(root: &Path, &Options) -> Result<Written, InitError>` — creates root, DIRS and every file; refuses a non-empty root unless `force`; sets 0o755 on the hook (unix); merges an existing .gitignore.
- `pub fn hook_hint(root: &Path) -> String` — "git config core.hooksPath <root>/.githooks".

CLI seam (unchanged for callers): `cli::init::run(&Globals, &InitArgs) -> Result<i32, CliError>` and `cli::init::InitOut { dir, created, skipped, hook_hint }` keep their names, fields and JSON shape; the TUI or another verb can reuse `crate::init::files()` to preview or re-emit any generated file (e.g. to refresh CLAUDE.md or a SKILL.md after an upgrade) without re-running init.