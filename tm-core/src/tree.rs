//! Tree — tm-spec-v1.md §3.2 (derived fields), §5.4 (series), §5.5
//! (dependencies), §6.1 (hierarchy vs horizon), §6.2 (day candidates),
//! §6.4 (rollups), plus the id / parent / cycle checks that `check.rs` uses.
//!
//! # API overview
//!
//! * [`Tree::build`]`(&[ParsedFile], &Config) -> Tree` — index every item of
//!   every file. [`Tree::from_texts`]`(&[(path, text)], &Config)` parses
//!   first (tests, `tm add` previews). Pure: no I/O, no clock.
//! * **Keys.** Items are addressed by [`Id`]. A line without `^id`
//!   (routines, optional, inbox) is keyed by its title — `Id("lunch")` —
//!   which is how the CLI names routines (`tm skip lunch`); an id-less line
//!   with an empty title, or whose title is already taken (by a `^id` or an
//!   earlier id-less line — a repeated inbox capture), is keyed `file:line`,
//!   so no id-less line is ever shadowed. [`Tree::key_of`]`(&Item)` computes
//!   the preferred key, [`Node::key`] holds the actual one,
//!   [`Tree::duplicate_titles`] lists the title collisions; the stored
//!   `Item.id` stays what the line says.
//! * **Nodes.** [`Node`] = the cloned [`Item`] with resolved fields (`ci` =
//!   the parent's resolved ci per §3.1: the nearest ancestor with an explicit
//!   ci, else the root's file default, else the item's own file default), its
//!   key, file index, resolved parent key and root key. [`Tree::get`]
//!   returns the item, [`Tree::node`] the node, [`Tree::nodes`] all of them in
//!   (file order, line order) — the rank order §7.4 sorts by
//!   ([`Tree::order`] gives `(file index, line)`).
//! * **Duplicates.** The §6.3 lifecycle legitimately leaves one `^id` on
//!   several lines: `tm close week` turns the week line into `[-]` (the week
//!   file becomes an archive) *and* copies it into `month/…# Demoted` with
//!   `est:` = remaining and a `demoted:` stamp; `tm readopt` then moves that
//!   copy into the current week, leaving the older `[-]` archive line behind.
//!   Those `[-]` lines — in a `week/` file or under `month/…# Demoted`, by
//!   state and horizon, never by file order — are **archive copies**, and the
//!   tree resolves the id to one item: the primary is the live copy (the one
//!   that is not an archive copy), else the copy with the most `demoted:`
//!   stamps, which is the newest record and carries the folded `est:`.
//!   Shadowed archive copies are listed by [`Tree::demoted_copies`] and still
//!   appear in [`Tree::week_items`] / [`Tree::month_items`] /
//!   [`Tree::items_in`]. Anything beyond that — two copies in one file, or
//!   two live copies — is a [`TreeProblem::DuplicateId`].
//! * **Hierarchy** (§6.1): [`Tree::parent`], [`Tree::children`] (ordered by
//!   (file, line)), [`Tree::ancestors`], [`Tree::descendants`],
//!   [`Tree::root`], [`Tree::roots`], [`Tree::depth`],
//!   [`Tree::tags_effective`] (own ∪ ancestors'), [`Tree::own_priority`],
//!   [`Tree::root_priority`] (the *root's* `!k`, else
//!   `config.priority.default_priority`).
//! * **Derived shape** (§3.2): [`Tree::effective_shape`] — an item whose
//!   written shape is `None` walks up through shape-less ancestors; if the
//!   first ancestor with a written shape is an `Interval`, the item is
//!   `Point { due: interval.start }` (prep work, at any depth below the
//!   interval). A `Point` or `Window` ancestor derives nothing.
//!   [`Tree::effective_due`] is the `Point` due (a bare date counts as
//!   `23:59`), the `Interval` start, or `None`. [`Tree::prep_children`] /
//!   [`Tree::prep_need`] are the interval's side of the same relation.
//! * **Rollups** (§6.4): [`Tree::remaining`] (`est` → `est_original` →
//!   `dur` → Σ children; `Some(0)` for Done/Dropped), [`Tree::done_minutes`],
//!   [`Tree::planned_minutes`], [`Tree::progress`].
//! * **Series** (§5.4): [`Tree::series_head`], [`Tree::series_heads`],
//!   [`Tree::is_series_active`] (true only for the head),
//!   [`Tree::series_suppressed`], [`Tree::series_members`],
//!   [`Tree::implied_dep`] (the previous line of the section).
//! * **Dependencies** (§5.5): [`Tree::deps`] (as written),
//!   [`Tree::all_deps`] (plus the implied series dep),
//!   [`Tree::deps_satisfied`] / [`Tree::blocked_by`]`(id, done, events)` —
//!   an item dep is satisfied when the tree has it `Done` or `done` lists it
//!   (the implied series dep also when the previous line is `Dropped`); an
//!   event dep when `events` names it.
//! * **Candidates** (§6.2): [`Tree::day_candidate_ids`]`(today, week)` —
//!   `week/<week>` + `day/<today># Pinned` + `backlog.md` + series heads
//!   anywhere, state Todo/Active, non-head series members removed.
//!   Routines, optional and calendar lines come separately from
//!   [`Tree::routine_ids`], [`Tree::optional_ids`], [`Tree::calendar_ids`]
//!   (their instances are `recur.rs`'s job). Also [`Tree::week_items`],
//!   [`Tree::month_items`], [`Tree::items_in`], [`Tree::waiting_ids`],
//!   [`Tree::overdue`]`(now)`, [`Tree::month_items_with_est_and_no_children`].
//! * **Checks**: [`Tree::problems`] collects [`TreeProblem`]s
//!   ([`Tree::duplicate_ids`], [`Tree::dangling_parents`],
//!   [`Tree::dangling_deps`], [`Tree::parent_cycles`], [`Tree::dep_cycles`],
//!   [`Tree::missing_ids`]); [`Tree::duplicate_titles`] and
//!   [`Tree::month_items_with_est_and_no_children`] are warning inputs.
//!
//! Every walk over `parent` / `after:` is cycle-safe; on a parent cycle
//! `root` stops at the first repeated node (and the cycle is reported).

use std::collections::{BTreeMap, HashMap, HashSet};

use chrono::{NaiveDate, NaiveDateTime};
use thiserror::Error;

use crate::config::Config;
use crate::grammar::{parse_file, ParsedFile};
use crate::model::{Dep, Horizon, Id, IsoWeek, Item, OnMiss, Recur, Ref, Shape, State, YearMonth};

/// A structural problem found while building the tree; `check.rs` reports
/// these (§1.3, §17 M1).
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum TreeProblem {
    /// One `^id` on several lines beyond what the §6.3 lifecycle leaves
    /// behind: two copies in one file, or two live copies (an archive copy is
    /// a `[-]` line in a `week/` file or under `month/…# Demoted`).
    #[error("duplicate id ^{id} at {}", fmt_locations(.locations))]
    DuplicateId {
        /// The id.
        id: Id,
        /// Every `(file, line)` carrying it, in tree order.
        locations: Vec<(String, usize)>,
    },
    /// `@parent` names nothing in the tree.
    #[error("{file}:{line}: ^{id} has parent @{parent} which does not exist")]
    DanglingParent {
        /// The child.
        id: Id,
        /// The reference as written.
        parent: Ref,
        /// File of the child.
        file: String,
        /// Line of the child.
        line: usize,
    },
    /// `after:^x` names nothing in the tree.
    #[error("{file}:{line}: ^{id} depends on ^{dep} which does not exist")]
    DanglingDep {
        /// The dependent item.
        id: Id,
        /// The missing dependency.
        dep: Id,
        /// File of the dependent item.
        file: String,
        /// Line of the dependent item.
        line: usize,
    },
    /// `@parent` links form a cycle.
    #[error("parent cycle: {}", fmt_cycle(.ids))]
    ParentCycle {
        /// The cycle, each id once, starting at the smallest.
        ids: Vec<Id>,
    },
    /// `after:` links form a cycle (§5.5: a `tm check` error).
    #[error("dependency cycle: {}", fmt_cycle(.ids))]
    DepCycle {
        /// The cycle, each id once, starting at the smallest.
        ids: Vec<Id>,
    },
    /// A line in a horizon file has no `^id` (routines, optional and inbox
    /// lines may omit it).
    #[error("{file}:{line}: missing ^id on `{title}`")]
    MissingId {
        /// File.
        file: String,
        /// Line.
        line: usize,
        /// Title of the line.
        title: String,
    },
}

fn fmt_locations(locs: &[(String, usize)]) -> String {
    locs.iter()
        .map(|(f, l)| format!("{f}:{l}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn fmt_cycle(ids: &[Id]) -> String {
    let mut parts: Vec<String> = ids.iter().map(|i| i.token()).collect();
    if let Some(first) = ids.first() {
        parts.push(first.token());
    }
    parts.join(" -> ")
}

/// One file the tree was built from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileInfo {
    /// Path as given to the parser.
    pub path: String,
    /// Horizon derived from the path.
    pub horizon: Horizon,
}

/// An item with its resolved context.
#[derive(Debug, Clone, PartialEq)]
pub struct Node {
    /// The key this node is addressed by (see the module docs).
    pub key: Id,
    /// The item, with `ci` resolved from the hierarchy.
    pub item: Item,
    /// Index into [`Tree::files`].
    pub file: usize,
    /// Resolved parent key (`None` when there is no parent or it dangles).
    pub parent: Option<Id>,
    /// Key of the top of the parent chain (`key` itself for a root).
    pub root: Id,
    /// False for a shadowed copy of a duplicated key (the index points at
    /// another node with the same key).
    pub primary: bool,
}

/// The parent/child index over every parsed file, with the derived fields
/// of §3.2. See the module docs.
#[derive(Debug, Clone)]
pub struct Tree {
    files: Vec<FileInfo>,
    nodes: Vec<Node>,
    index: HashMap<Id, usize>,
    children: HashMap<Id, Vec<Id>>,
    roots: Vec<Id>,
    series: BTreeMap<String, Vec<Id>>,
    duplicates: Vec<(Id, Vec<usize>)>,
    duplicate_titles: Vec<(String, Vec<usize>)>,
    demoted_copies: Vec<usize>,
    dangling_parents: Vec<(Id, Ref)>,
    default_priority: u8,
}

impl Tree {
    // -----------------------------------------------------------------------
    // Construction
    // -----------------------------------------------------------------------

    /// Parse `(path, text)` pairs and build the tree.
    pub fn from_texts(files: &[(&str, &str)], cfg: &Config) -> Tree {
        let parsed: Vec<ParsedFile> = files
            .iter()
            .map(|(path, text)| parse_file(path, text, cfg))
            .collect();
        Tree::build(&parsed, cfg)
    }

    /// Build the tree. Files keep the order given; items keep line order.
    pub fn build(files: &[ParsedFile], cfg: &Config) -> Tree {
        let infos: Vec<FileInfo> = files
            .iter()
            .map(|f| FileInfo {
                path: f.path.clone(),
                horizon: f.horizon,
            })
            .collect();

        // 1. Nodes in (file, line) order, keyed by `^id` / title / `file:line`.
        let mut nodes: Vec<Node> = Vec::new();
        for (fi, f) in files.iter().enumerate() {
            for item in f.items() {
                let key = Tree::key_of(item);
                nodes.push(Node {
                    root: key.clone(),
                    key,
                    item: item.clone(),
                    file: fi,
                    parent: None,
                    primary: true,
                });
            }
        }

        // 2. Title keys. A title already taken — by a `^id`, or by an earlier
        //    id-less line — falls back to `file:line`, so every id-less line
        //    stays addressable and none is shadowed (§4.3: inbox, routines and
        //    optional lines carry no id, and a repeated capture is normal).
        let mut taken: HashSet<Id> = nodes
            .iter()
            .filter(|n| n.item.has_id())
            .map(|n| n.key.clone())
            .collect();
        let mut title_groups: Vec<(String, Vec<usize>)> = Vec::new();
        let mut title_pos: HashMap<String, usize> = HashMap::new();
        for i in 0..nodes.len() {
            let n = &mut nodes[i];
            if n.item.has_id() || n.item.title.is_empty() {
                continue;
            }
            match title_pos.get(&n.item.title) {
                Some(&g) => title_groups[g].1.push(i),
                None => {
                    title_pos.insert(n.item.title.clone(), title_groups.len());
                    title_groups.push((n.item.title.clone(), vec![i]));
                }
            }
            if !taken.insert(n.key.clone()) {
                n.key = line_key(&n.item);
                n.root = n.key.clone();
            }
        }
        let duplicate_titles: Vec<(String, Vec<usize>)> =
            title_groups.into_iter().filter(|(_, idxs)| idxs.len() > 1).collect();

        // 3. Index with the duplicate rule (§6.3 archive copies excepted).
        let mut groups: Vec<(Id, Vec<usize>)> = Vec::new();
        let mut group_pos: HashMap<Id, usize> = HashMap::new();
        for (i, n) in nodes.iter().enumerate() {
            match group_pos.get(&n.key) {
                Some(&g) => groups[g].1.push(i),
                None => {
                    group_pos.insert(n.key.clone(), groups.len());
                    groups.push((n.key.clone(), vec![i]));
                }
            }
        }
        let mut index: HashMap<Id, usize> = HashMap::new();
        let mut duplicates: Vec<(Id, Vec<usize>)> = Vec::new();
        let mut demoted_copies: Vec<usize> = Vec::new();
        for (key, members) in &groups {
            let primary = *members
                .iter()
                .min_by_key(|&&i| record_rank(&nodes[i].item))
                .expect("a group has at least one member");
            index.insert(key.clone(), primary);
            if members.len() == 1 {
                continue;
            }
            if is_real_duplicate(&nodes, members) {
                duplicates.push((key.clone(), members.clone()));
            } else {
                demoted_copies.extend(members.iter().copied().filter(|&i| i != primary));
            }
            for &i in members {
                if i != primary {
                    nodes[i].primary = false;
                }
            }
        }
        demoted_copies.sort_unstable();

        // 4. Parents.
        let mut dangling_parents: Vec<(Id, Ref)> = Vec::new();
        for n in nodes.iter_mut() {
            if let Some(r) = n.item.parent.clone() {
                let pk = r.to_id();
                if index.contains_key(&pk) {
                    n.parent = Some(pk);
                } else if n.primary {
                    dangling_parents.push((n.key.clone(), r));
                }
            }
        }

        // 5. Children (primary nodes only), roots.
        let mut children: HashMap<Id, Vec<Id>> = HashMap::new();
        let mut roots: Vec<Id> = Vec::new();
        for n in nodes.iter().filter(|n| n.primary) {
            match &n.parent {
                Some(p) => children.entry(p.clone()).or_default().push(n.key.clone()),
                None => roots.push(n.key.clone()),
            }
        }

        // 6. Resolved fields: root, ci. `ci` without an explicit value is the
        //    parent's resolved ci (§3.1): the nearest ancestor with an explicit
        //    ci, else the top ancestor's file default — which is what the
        //    parser left in its `ci` — else the item's own file default. Read
        //    the parsed values for every node first so the result does not
        //    depend on processing order.
        let resolved: Vec<(Id, u8)> = (0..nodes.len())
            .map(|i| {
                let chain = ancestor_chain(&nodes, &index, i);
                let root = chain
                    .last()
                    .map(|&a| nodes[a].key.clone())
                    .unwrap_or_else(|| nodes[i].key.clone());
                let ci = if nodes[i].item.ci_explicit {
                    nodes[i].item.ci
                } else {
                    match chain.iter().find(|&&a| nodes[a].item.ci_explicit) {
                        Some(&a) => nodes[a].item.ci,
                        None => chain.last().map(|&a| nodes[a].item.ci).unwrap_or(nodes[i].item.ci),
                    }
                };
                (root, ci)
            })
            .collect();
        for (n, (root, ci)) in nodes.iter_mut().zip(resolved) {
            n.root = root;
            n.item.ci = ci;
        }

        // 7. Series sections.
        let mut series: BTreeMap<String, Vec<Id>> = BTreeMap::new();
        for n in nodes.iter().filter(|n| n.primary) {
            if let Some((name, _)) = &n.item.series {
                series.entry(name.clone()).or_default().push(n.key.clone());
            }
        }

        Tree {
            files: infos,
            nodes,
            index,
            children,
            roots,
            series,
            duplicates,
            duplicate_titles,
            demoted_copies,
            dangling_parents,
            default_priority: cfg.priority.default_priority,
        }
    }

    /// The key an item is addressed by: its `^id`, else its title, else
    /// `file:line`. This is the key the tree *prefers*; when the title is
    /// already taken (by a `^id`, or by an earlier id-less line with the same
    /// title) the tree keys the line `file:line` instead — [`Node::key`] is
    /// authoritative, and [`Tree::duplicate_titles`] lists such collisions.
    pub fn key_of(item: &Item) -> Id {
        if item.has_id() {
            item.id.clone()
        } else if !item.title.is_empty() {
            Id::new(item.title.clone())
        } else {
            line_key(item)
        }
    }

    // -----------------------------------------------------------------------
    // Lookup
    // -----------------------------------------------------------------------

    /// The files the tree was built from, in build order.
    pub fn files(&self) -> &[FileInfo] {
        &self.files
    }

    /// Every node (including shadowed duplicates) in (file, line) order.
    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    /// Every primary item in (file, line) order.
    pub fn iter(&self) -> impl Iterator<Item = &Item> {
        self.nodes.iter().filter(|n| n.primary).map(|n| &n.item)
    }

    /// Every primary key in (file, line) order.
    pub fn ids(&self) -> impl Iterator<Item = &Id> {
        self.nodes.iter().filter(|n| n.primary).map(|n| &n.key)
    }

    /// Number of primary items.
    pub fn len(&self) -> usize {
        self.index.len()
    }

    /// True when the tree holds no items.
    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    /// True when `id` is a key in the tree.
    pub fn contains(&self, id: &Id) -> bool {
        self.index.contains_key(id)
    }

    /// The primary node for `id`.
    pub fn node(&self, id: &Id) -> Option<&Node> {
        self.index.get(id).map(|&i| &self.nodes[i])
    }

    /// The primary item for `id` (with resolved `ci`).
    pub fn get(&self, id: &Id) -> Option<&Item> {
        self.node(id).map(|n| &n.item)
    }

    /// Every item carrying `id`, primary first, then the others in tree order.
    pub fn all(&self, id: &Id) -> Vec<&Item> {
        let mut out = Vec::new();
        if let Some(p) = self.get(id) {
            out.push(p);
        }
        out.extend(
            self.nodes
                .iter()
                .filter(|n| !n.primary && &n.key == id)
                .map(|n| &n.item),
        );
        out
    }

    /// `(file index, line number)` of the primary item — the §7.4 rank key.
    pub fn order(&self, id: &Id) -> Option<(usize, usize)> {
        self.node(id).map(|n| (n.file, n.item.src.line))
    }

    /// The file the primary item lives in.
    pub fn file_of(&self, id: &Id) -> Option<&FileInfo> {
        self.node(id).map(|n| &self.files[n.file])
    }

    // -----------------------------------------------------------------------
    // Hierarchy (§6.1)
    // -----------------------------------------------------------------------

    /// Resolved parent key.
    pub fn parent(&self, id: &Id) -> Option<&Id> {
        self.node(id).and_then(|n| n.parent.as_ref())
    }

    /// Children in (file, line) order.
    pub fn children(&self, id: &Id) -> &[Id] {
        self.children.get(id).map(Vec::as_slice).unwrap_or(&[])
    }

    /// True when the item has at least one child.
    pub fn has_children(&self, id: &Id) -> bool {
        !self.children(id).is_empty()
    }

    /// Ancestors nearest first, stopping before any repeat.
    pub fn ancestors(&self, id: &Id) -> Vec<Id> {
        match self.index.get(id) {
            Some(&i) => ancestor_chain(&self.nodes, &self.index, i)
                .into_iter()
                .map(|a| self.nodes[a].key.clone())
                .collect(),
            None => Vec::new(),
        }
    }

    /// Descendants in depth-first pre-order (each node's subtree before its
    /// next sibling, children in (file, line) order); cycle-safe.
    pub fn descendants(&self, id: &Id) -> Vec<Id> {
        let mut out = Vec::new();
        let mut seen: HashSet<&Id> = HashSet::new();
        seen.insert(id);
        let mut stack: Vec<&Id> = self.children(id).iter().rev().collect();
        while let Some(k) = stack.pop() {
            if !seen.insert(k) {
                continue;
            }
            out.push(k.clone());
            stack.extend(self.children(k).iter().rev());
        }
        out
    }

    /// The top of the parent chain (`id` itself for a root or an unknown id).
    pub fn root(&self, id: &Id) -> Id {
        self.node(id).map(|n| n.root.clone()).unwrap_or_else(|| id.clone())
    }

    /// True when the item has no (resolved) parent.
    pub fn is_root(&self, id: &Id) -> bool {
        self.node(id).is_some_and(|n| n.parent.is_none())
    }

    /// Every root in (file, line) order (items with a dangling parent count
    /// as roots; members of a parent cycle are not roots).
    pub fn roots(&self) -> &[Id] {
        &self.roots
    }

    /// Number of resolved ancestors (0 for a root).
    pub fn depth(&self, id: &Id) -> usize {
        self.ancestors(id).len()
    }

    /// The item's own `!k`, as written.
    pub fn own_priority(&self, id: &Id) -> Option<u8> {
        self.get(id).and_then(|i| i.priority)
    }

    /// The root's `!k`, else `config.priority.default_priority` (§3.2, §7.1).
    /// A `!k` on a non-root is ignored here (see [`Tree::own_priority`]).
    pub fn root_priority(&self, id: &Id) -> u8 {
        self.get(&self.root(id))
            .and_then(|r| r.priority)
            .unwrap_or(self.default_priority)
    }

    /// Own tags followed by every ancestor's, nearest first, without
    /// repeats.
    pub fn tags_effective(&self, id: &Id) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut push = |item: &Item| {
            for t in &item.tags {
                if !out.contains(t) {
                    out.push(t.clone());
                }
            }
        };
        if let Some(it) = self.get(id) {
            push(it);
        }
        for a in self.ancestors(id) {
            if let Some(it) = self.get(&a) {
                push(it);
            }
        }
        out
    }

    // -----------------------------------------------------------------------
    // Derived shape (§3.2, §6.4)
    // -----------------------------------------------------------------------

    /// The shape the planner sees: as written, except that a shape-less item
    /// below an `Interval` (through any number of shape-less ancestors) is
    /// `Point { due: interval.start }`.
    pub fn effective_shape(&self, id: &Id) -> Shape {
        let Some(item) = self.get(id) else {
            return Shape::None;
        };
        if item.shape != Shape::None {
            return item.shape.clone();
        }
        for a in self.ancestors(id) {
            let Some(anc) = self.get(&a) else { break };
            match &anc.shape {
                Shape::None => continue,
                Shape::Interval { start, .. } => {
                    return Shape::Point {
                        due: crate::model::Moment::DateTime(*start),
                    }
                }
                _ => break,
            }
        }
        Shape::None
    }

    /// **The walls of one date** — every open `Interval` item that overlaps it,
    /// its start moved back by `buffer:` (§8.2 step 1), sorted by start: fork
    /// `Ctx::walls_on`, moved here at W-38 (the campaign's D69 call on README
    /// gap 3244) so that the week review's heat grid reads the walls the CLI
    /// reads without a `Ctx` — the TUI builds the week review from its own
    /// `Tree` — and `Ctx::walls_on` is now this, called. One definition, and it
    /// is the host's: README gap 3432 is its exit, at R3.
    pub fn walls_on(&self, tz: chrono_tz::Tz, date: NaiveDate) -> Vec<crate::capacity::Wall> {
        let mut out = Vec::new();
        for item in self.iter() {
            if item.state.is_closed() {
                continue;
            }
            let id = Tree::key_of(item);
            let Shape::Interval { start, end } = self.effective_shape(&id) else {
                continue;
            };
            let start = match item.buffer {
                Some(b) => start - chrono::Duration::minutes(i64::from(b.as_minutes())),
                None => start,
            };
            if start.date() > date || end.date() < date {
                continue;
            }
            out.push((
                crate::capacity::local_dt(tz, start.date(), start.time()),
                crate::capacity::local_dt(tz, end.date(), end.time()),
            ));
        }
        out.sort_by_key(|(a, _)| *a);
        out
    }

    /// True when the item's `Point` shape comes from an ancestor interval.
    pub fn is_prep(&self, id: &Id) -> bool {
        self.get(id).is_some_and(|i| i.shape == Shape::None)
            && matches!(self.effective_shape(id), Shape::Point { .. })
    }

    /// The deadline the EDF pass sorts by: a `Point` due (a bare date is
    /// `23:59` that day), an `Interval` start, or `None` (windows and
    /// shape-less items).
    pub fn effective_due(&self, id: &Id) -> Option<NaiveDateTime> {
        match self.effective_shape(id) {
            Shape::Point { due } => Some(due.end_of_day()),
            Shape::Interval { start, .. } => Some(start),
            _ => None,
        }
    }

    /// Direct children of an interval whose written shape is `None` — the
    /// ones whose due derives from it. Empty when `id` is not an interval.
    pub fn prep_children(&self, id: &Id) -> Vec<Id> {
        if !matches!(self.get(id).map(|i| &i.shape), Some(Shape::Interval { .. })) {
            return Vec::new();
        }
        self.children(id)
            .iter()
            .filter(|c| self.get(c).is_some_and(|i| i.shape == Shape::None))
            .cloned()
            .collect()
    }

    /// Σ `remaining` over the interval's prep children (minutes) — the need
    /// the §7 pressure uses. Done/Dropped children contribute nothing.
    pub fn prep_need(&self, id: &Id) -> u32 {
        self.prep_children(id)
            .iter()
            .filter_map(|c| self.remaining(c))
            .sum()
    }

    // -----------------------------------------------------------------------
    // Rollups (§6.4)
    // -----------------------------------------------------------------------

    /// Remaining minutes: `est` → `est_original` → `dur` → Σ over children
    /// (`None` when neither the item nor any descendant has an estimate).
    /// Done and Dropped items have `Some(0)` remaining.
    pub fn remaining(&self, id: &Id) -> Option<u32> {
        let mut seen = HashSet::new();
        self.remaining_inner(id, &mut seen)
    }

    fn remaining_inner(&self, id: &Id, seen: &mut HashSet<Id>) -> Option<u32> {
        let item = self.get(id)?;
        if !seen.insert(id.clone()) {
            return None;
        }
        if item.state.is_closed() {
            return Some(0);
        }
        if let Some(d) = item.own_remaining() {
            return Some(d.as_minutes());
        }
        let mut total: Option<u32> = None;
        for c in self.children(id) {
            if let Some(m) = self.remaining_inner(c, seen) {
                total = Some(total.unwrap_or(0).saturating_add(m));
            }
        }
        total
    }

    /// The estimate progress is measured against: `est_original`, else Σ
    /// over children (recursively), else `None`. Unlike [`Tree::remaining`]
    /// this ignores state and `est:`.
    pub fn planned_minutes(&self, id: &Id) -> Option<u32> {
        let mut seen = HashSet::new();
        self.planned_inner(id, &mut seen)
    }

    fn planned_inner(&self, id: &Id, seen: &mut HashSet<Id>) -> Option<u32> {
        let item = self.get(id)?;
        if !seen.insert(id.clone()) {
            return None;
        }
        if let Some(d) = item.est_original.or(item.dur) {
            return Some(d.as_minutes());
        }
        let mut total: Option<u32> = None;
        for c in self.children(id) {
            if let Some(m) = self.planned_inner(c, seen) {
                total = Some(total.unwrap_or(0).saturating_add(m));
            }
        }
        total
    }

    /// Σ logged block minutes of the item and all its descendants, given the
    /// per-item minutes from `log.rs` replay.
    pub fn done_minutes(&self, id: &Id, done_by_item: &HashMap<Id, u32>) -> u32 {
        let own = done_by_item.get(id).copied().unwrap_or(0);
        self.descendants(id)
            .iter()
            .filter_map(|d| done_by_item.get(d))
            .fold(own, |acc, m| acc.saturating_add(*m))
    }

    /// `done_minutes / planned_minutes`; `None` without a planned estimate.
    pub fn progress(&self, id: &Id, done_by_item: &HashMap<Id, u32>) -> Option<f64> {
        let planned = self.planned_minutes(id)?;
        if planned == 0 {
            return None;
        }
        Some(self.done_minutes(id, done_by_item) as f64 / planned as f64)
    }

    // -----------------------------------------------------------------------
    // Series (§5.4)
    // -----------------------------------------------------------------------

    /// Series names, sorted.
    pub fn series_names(&self) -> impl Iterator<Item = &str> {
        self.series.keys().map(String::as_str)
    }

    /// Members of a series in section order (across files in file order
    /// when the same section name appears in several).
    pub fn series_members(&self, name: &str) -> &[Id] {
        self.series.get(name).map(Vec::as_slice).unwrap_or(&[])
    }

    /// `(series name, 0-based index)` of a member.
    pub fn series_of(&self, id: &Id) -> Option<(&str, u32)> {
        self.get(id)
            .and_then(|i| i.series.as_ref())
            .map(|(n, i)| (n.as_str(), *i))
    }

    /// The first member with state ∉ {Done, Dropped}.
    pub fn series_head(&self, name: &str) -> Option<Id> {
        self.series_members(name)
            .iter()
            .find(|m| self.get(m).is_some_and(|i| !i.state.is_closed()))
            .cloned()
    }

    /// Every series head, in series-name order.
    pub fn series_heads(&self) -> Vec<Id> {
        self.series
            .keys()
            .filter_map(|n| self.series_head(n))
            .collect()
    }

    /// True when the item is the head of its series (false for other
    /// members and for items outside any series).
    pub fn is_series_active(&self, id: &Id) -> bool {
        self.series_of(id)
            .and_then(|(n, _)| self.series_head(n))
            .is_some_and(|h| &h == id)
    }

    /// True when the item is a series member that is not the head — invisible
    /// to the planner.
    pub fn series_suppressed(&self, id: &Id) -> bool {
        self.series_of(id).is_some() && !self.is_series_active(id)
    }

    /// The previous line of the item's series section (the section's implied
    /// `after:`), if any.
    pub fn implied_dep(&self, id: &Id) -> Option<Id> {
        let (name, _) = self.series_of(id)?;
        let members = self.series_members(name);
        let pos = members.iter().position(|m| m == id)?;
        pos.checked_sub(1).map(|p| members[p].clone())
    }

    // -----------------------------------------------------------------------
    // Dependencies (§5.5)
    // -----------------------------------------------------------------------

    /// `after:` as written.
    pub fn deps(&self, id: &Id) -> &[Dep] {
        self.get(id).map(|i| i.after.as_slice()).unwrap_or(&[])
    }

    /// `after:` as written plus the implied series dependency.
    pub fn all_deps(&self, id: &Id) -> Vec<Dep> {
        let mut out = self.deps(id).to_vec();
        if let Some(prev) = self.implied_dep(id) {
            let d = Dep::Item(prev);
            if !out.contains(&d) {
                out.push(d);
            }
        }
        out
    }

    fn dep_satisfied(&self, dep: &Dep, implied: bool, done: &HashSet<Id>, events: &HashSet<String>) -> bool {
        match dep {
            Dep::Event(name) => events.contains(name),
            Dep::Item(target) => {
                if done.contains(target) {
                    return true;
                }
                match self.get(target).map(|i| i.state) {
                    Some(State::Done) => true,
                    Some(State::Dropped) => implied,
                    _ => false,
                }
            }
        }
    }

    /// True when every dependency is satisfied: an item dep when the tree has
    /// it `Done` or `done` lists it (the implied series dep also when the
    /// previous line is `Dropped`); an event dep when `events` names it.
    /// Unknown ids have no dependencies.
    pub fn deps_satisfied(&self, id: &Id, done: &HashSet<Id>, events: &HashSet<String>) -> bool {
        self.blocked_by(id, done, events).is_empty()
    }

    /// The dependencies that are not satisfied, in line order (implied series
    /// dep last).
    pub fn blocked_by(&self, id: &Id, done: &HashSet<Id>, events: &HashSet<String>) -> Vec<Dep> {
        let implied = self.implied_dep(id).map(Dep::Item);
        let mut out: Vec<Dep> = self
            .deps(id)
            .iter()
            .filter(|d| !self.dep_satisfied(d, false, done, events))
            .cloned()
            .collect();
        if let Some(d) = implied {
            if !out.contains(&d) && !self.dep_satisfied(&d, true, done, events) {
                out.push(d);
            }
        }
        out
    }

    /// Cycles in the `after:` graph (explicit and implied deps), each id once
    /// starting at the smallest, in order of discovery.
    pub fn dep_cycles(&self) -> Vec<Vec<Id>> {
        let keys: Vec<&Id> = self.ids().collect();
        let edges = |k: &Id| -> Vec<Id> {
            self.all_deps(k)
                .into_iter()
                .filter_map(|d| match d {
                    Dep::Item(t) if self.contains(&t) => Some(t),
                    _ => None,
                })
                .collect()
        };
        find_cycles(&keys, edges)
    }

    /// Cycles in the `@parent` graph, each id once starting at the smallest.
    pub fn parent_cycles(&self) -> Vec<Vec<Id>> {
        let keys: Vec<&Id> = self.ids().collect();
        let edges = |k: &Id| -> Vec<Id> { self.parent(k).cloned().into_iter().collect() };
        find_cycles(&keys, edges)
    }

    // -----------------------------------------------------------------------
    // Checks
    // -----------------------------------------------------------------------

    /// `(child, parent ref)` for every `@parent` that resolves to nothing.
    pub fn dangling_parents(&self) -> &[(Id, Ref)] {
        &self.dangling_parents
    }

    /// `(item, dep)` for every `after:^x` that resolves to nothing.
    pub fn dangling_deps(&self) -> Vec<(Id, Id)> {
        let mut out = Vec::new();
        for n in self.nodes.iter().filter(|n| n.primary) {
            for d in &n.item.after {
                if let Dep::Item(t) = d {
                    if !self.contains(t) {
                        out.push((n.key.clone(), t.clone()));
                    }
                }
            }
        }
        out
    }

    /// `^id`s on more than one line beyond what the §6.3 lifecycle leaves
    /// behind — two copies in one file, or two live copies — with every
    /// `(file, line)` carrying the id.
    pub fn duplicate_ids(&self) -> Vec<(Id, Vec<(String, usize)>)> {
        self.duplicates
            .iter()
            .map(|(id, idxs)| (id.clone(), self.locations(idxs)))
            .collect()
    }

    /// Id-less lines sharing a title (two identical inbox captures, two
    /// routines called `lunch`), with every `(file, line)`. Not a
    /// [`TreeProblem`] — uniqueness is a rule about `^id`s (§17.2) — but a
    /// possible `tm check` warning for routines and optional, whose lines the
    /// CLI names by title. Only the first line keeps the title key.
    pub fn duplicate_titles(&self) -> Vec<(String, Vec<(String, usize)>)> {
        self.duplicate_titles
            .iter()
            .map(|(title, idxs)| (title.clone(), self.locations(idxs)))
            .collect()
    }

    /// **The placements an id-less title names, when it names more than one**
    /// (`None` when the key is unambiguous or is an `^id`).
    ///
    /// This is [`Tree::duplicate_titles`] asked about **one** key rather than
    /// listed whole, so there is no second answer to "is this title taken
    /// twice" (AGENTS §5.3). It exists because the answer has to be a
    /// *refusal* and not a pick: the tree keys the second such line
    /// `file:line`, so `Tree::get(title)` quietly returns the first, and a
    /// loader that picks between two readings is the defect AGENTS §5.6 is
    /// named after. D32 settled the same question for the kernel — a title-key
    /// collision keeps refusing — and this is the host side of it.
    pub fn ambiguous_title(&self, key: &Id) -> Option<Vec<(String, usize)>> {
        self.duplicate_titles
            .iter()
            .find(|(title, _)| Id::new(title.clone()) == *key)
            .map(|(_, idxs)| self.locations(idxs))
    }

    fn locations(&self, idxs: &[usize]) -> Vec<(String, usize)> {
        idxs.iter()
            .map(|&i| (self.files[self.nodes[i].file].path.clone(), self.nodes[i].item.src.line))
            .collect()
    }

    /// The archive copies shadowed by another line with the same id (§6.3):
    /// the `month/…# Demoted` copy of an open week line, the `[-]` archive
    /// line a closed week keeps once its item is readopted or recorded in the
    /// month, or the older of two archive lines. In (file, line) order.
    pub fn demoted_copies(&self) -> Vec<&Item> {
        self.demoted_copies.iter().map(|&i| &self.nodes[i].item).collect()
    }

    /// True for a primary node or a shadowed archive copy — the nodes a
    /// per-file listing shows.
    fn is_listed(&self, i: usize) -> bool {
        self.nodes[i].primary || self.demoted_copies.binary_search(&i).is_ok()
    }

    /// Lines without `^id` outside routines, optional and inbox.
    pub fn missing_ids(&self) -> Vec<&Item> {
        self.nodes
            .iter()
            .filter(|n| !n.item.has_id() && !n.item.horizon.allows_missing_state())
            .map(|n| &n.item)
            .collect()
    }

    /// Every structural problem, for `tm check`.
    pub fn problems(&self) -> Vec<TreeProblem> {
        let mut out = Vec::new();
        for (id, locations) in self.duplicate_ids() {
            out.push(TreeProblem::DuplicateId { id, locations });
        }
        for it in self.missing_ids() {
            out.push(TreeProblem::MissingId {
                file: it.src.file.clone(),
                line: it.src.line,
                title: it.title.clone(),
            });
        }
        for (id, parent) in &self.dangling_parents {
            let it = self.get(id);
            out.push(TreeProblem::DanglingParent {
                id: id.clone(),
                parent: parent.clone(),
                file: it.map(|i| i.src.file.clone()).unwrap_or_default(),
                line: it.map(|i| i.src.line).unwrap_or(0),
            });
        }
        for (id, dep) in self.dangling_deps() {
            let it = self.get(&id);
            out.push(TreeProblem::DanglingDep {
                file: it.map(|i| i.src.file.clone()).unwrap_or_default(),
                line: it.map(|i| i.src.line).unwrap_or(0),
                id,
                dep,
            });
        }
        for ids in self.parent_cycles() {
            out.push(TreeProblem::ParentCycle { ids });
        }
        for ids in self.dep_cycles() {
            out.push(TreeProblem::DepCycle { ids });
        }
        out
    }

    // -----------------------------------------------------------------------
    // Candidate sources (§6.2)
    // -----------------------------------------------------------------------

    /// Items the day planner competes (§6.2): `week/<this_week>` +
    /// `day/<today># Pinned` + `backlog.md` + every series head, with state
    /// Todo or Active and non-head series members removed, in (file, line)
    /// order. Eligibility (deps, `loc`, caps) is the caller's filter.
    pub fn day_candidate_ids(&self, today: NaiveDate, this_week: IsoWeek) -> Vec<Id> {
        self.nodes
            .iter()
            .filter(|n| n.primary && n.item.state.is_open() && !self.series_suppressed(&n.key))
            .filter(|n| {
                let it = &n.item;
                let in_source = match it.horizon {
                    Horizon::Week(w) => w == this_week,
                    Horizon::Day(d) => d == today && it.src.section.as_deref() == Some("Pinned"),
                    Horizon::Backlog => true,
                    _ => false,
                };
                in_source || self.is_series_active(&n.key)
            })
            .map(|n| n.key.clone())
            .collect()
    }

    fn keys_where(&self, pred: impl Fn(&Item) -> bool) -> Vec<Id> {
        self.nodes
            .iter()
            .filter(|n| n.primary && pred(&n.item))
            .map(|n| n.key.clone())
            .collect()
    }

    /// Open lines of `routines.md` (keys are titles).
    pub fn routine_ids(&self) -> Vec<Id> {
        self.keys_where(|i| i.horizon == Horizon::Routine && i.state.is_open())
    }

    /// Open lines of `optional.md` (keys are titles).
    pub fn optional_ids(&self) -> Vec<Id> {
        self.keys_where(|i| i.horizon == Horizon::Optional && i.state.is_open())
    }

    /// Open lines of `calendar/<week>.md`.
    pub fn calendar_ids(&self, week: IsoWeek) -> Vec<Id> {
        self.keys_where(|i| i.horizon == Horizon::Calendar(week) && i.state.is_open())
    }

    /// Every item of `week/<week>.md`, any state (a `[-]` archive line whose
    /// item was readopted elsewhere included — see [`Tree::demoted_copies`]).
    pub fn week_items(&self, week: IsoWeek) -> Vec<&Item> {
        self.listed_where(|i| i.horizon == Horizon::Week(week))
    }

    /// Every item of `month/<month>.md`, any state (the `# Demoted` copies
    /// included — see [`Tree::demoted_copies`]).
    pub fn month_items(&self, month: YearMonth) -> Vec<&Item> {
        self.listed_where(|i| i.horizon == Horizon::Month(month))
    }

    fn listed_where(&self, pred: impl Fn(&Item) -> bool) -> Vec<&Item> {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(i, n)| pred(&n.item) && self.is_listed(*i))
            .map(|(_, n)| &n.item)
            .collect()
    }

    /// Every item of the file at `path` (exact path, else the file with the
    /// same horizon), any state, shadowed copies included.
    pub fn items_in(&self, path: &str) -> Vec<&Item> {
        let fi = self
            .files
            .iter()
            .position(|f| f.path == path)
            .or_else(|| {
                let h = Horizon::from_path(path)?;
                self.files.iter().position(|f| f.horizon == h)
            });
        match fi {
            Some(fi) => self.nodes.iter().filter(|n| n.file == fi).map(|n| &n.item).collect(),
            None => Vec::new(),
        }
    }

    /// Items in state `[?]`, anywhere.
    pub fn waiting_ids(&self) -> Vec<Id> {
        self.keys_where(|i| i.state == State::Waiting)
    }

    /// Todo/Active, non-recurring items whose effective `Point` due or
    /// `Interval` end is before `now` and whose `on_miss` is `persist`
    /// (§5.3: overdue badge, priority 0). Synced `calendar/` walls are
    /// excluded — they pass, they are never overdue.
    pub fn overdue(&self, now: NaiveDateTime) -> Vec<Id> {
        self.nodes
            .iter()
            .filter(|n| n.primary)
            .filter(|n| {
                let it = &n.item;
                it.state.is_open()
                    && it.recur == Recur::None
                    && it.on_miss == OnMiss::Persist
                    && !matches!(it.horizon, Horizon::Calendar(_))
                    && match self.effective_shape(&n.key) {
                        Shape::Point { due } => due.end_of_day() < now,
                        Shape::Interval { end, .. } => end < now,
                        _ => false,
                    }
            })
            .map(|n| n.key.clone())
            .collect()
    }

    /// `month/` items (outside `# Demoted`, not themselves demoted) that
    /// carry an estimate but have no children — the §6.2 check warning
    /// "outcome with estimate — did you mean a milestone?".
    pub fn month_items_with_est_and_no_children(&self) -> Vec<Id> {
        self.nodes
            .iter()
            .filter(|n| n.primary)
            .filter(|n| {
                let it = &n.item;
                matches!(it.horizon, Horizon::Month(_))
                    && it.state != State::Demoted
                    && it.src.section.as_deref() != Some("Demoted")
                    && it.est_original.or(it.est).is_some()
                    && !self.has_children(&n.key)
            })
            .map(|n| n.key.clone())
            .collect()
    }
}

/// The `file:line` key of an id-less line.
fn line_key(item: &Item) -> Id {
    Id::new(format!("{}:{}", item.src.file, item.src.line))
}

/// A `month/…# Demoted` line: the copy `tm close week` writes (§6.3).
pub fn in_month_demoted(item: &Item) -> bool {
    matches!(item.horizon, Horizon::Month(_)) && item.src.section.as_deref() == Some("Demoted")
}

/// An **archive copy**: a line the §6.3 lifecycle leaves behind carrying an
/// id that lives elsewhere too. State *and* horizon, never file order —
/// `tm close week` turns the week line into `[-]` (the week file becomes an
/// archive) and copies it into `month/<current># Demoted`, so exactly two
/// shapes qualify: a `[-]` line in a `week/` file, and a `[-]` line under
/// `month/…# Demoted`. A `[-]` line anywhere else (backlog, day, a month
/// section that is not `# Demoted`) is not something a close produces, so it
/// still counts as a live copy and collides.
pub fn is_archive_copy(item: &Item) -> bool {
    item.state == State::Demoted
        && (matches!(item.horizon, Horizon::Week(_)) || in_month_demoted(item))
}

/// The sort key [`record_rank`] returns: `(is an archive copy, most stamps
/// first, is not the `month/…# Demoted` copy)`.
pub type RecordRank = (bool, std::cmp::Reverse<usize>, bool);

/// Which of several lines carrying one id is the record (smallest wins; ties
/// go to the earlier line): the live line — anything that is not an archive
/// copy — else the copy with the most `demoted:` stamps, since `tm close
/// week` appends a stamp to the copy it writes and never to the line it
/// archives, so the most-stamped copy is the newest record (the one carrying
/// the folded `est:`); else the `month/…# Demoted` copy.
///
/// `store::choose` ranks with this too, so the line a reader resolves an id
/// to (`Tree::get`) is the line a writer rewrites (`Store::write_line`): a
/// disagreement here means `tm edit ^id` reads one copy and overwrites the
/// other (§1.3 "writers address items by id").
pub fn record_rank(item: &Item) -> RecordRank {
    (
        is_archive_copy(item),
        std::cmp::Reverse(item.stamps.demoted.len()),
        !in_month_demoted(item),
    )
}

/// True when the lines carrying one id are more than the §6.3 lifecycle
/// leaves behind: two in one file (a close rewrites a line in place, it never
/// duplicates one within a file), or two live copies.
fn is_real_duplicate(nodes: &[Node], members: &[usize]) -> bool {
    let mut files: HashSet<usize> = HashSet::new();
    let mut live = 0;
    for &i in members {
        if !files.insert(nodes[i].file) {
            return true;
        }
        if !is_archive_copy(&nodes[i].item) {
            live += 1;
        }
    }
    live >= 2
}

/// Node indices of the ancestors of `i`, nearest first, stopping before a
/// repeat (parent cycle) or an unresolved parent.
fn ancestor_chain(nodes: &[Node], index: &HashMap<Id, usize>, i: usize) -> Vec<usize> {
    let mut chain = Vec::new();
    let mut seen: HashSet<usize> = HashSet::new();
    seen.insert(i);
    let mut cur = i;
    while let Some(p) = nodes[cur].item.parent.as_ref() {
        let Some(&pi) = index.get(&p.to_id()) else { break };
        if !seen.insert(pi) {
            break;
        }
        chain.push(pi);
        cur = pi;
    }
    chain
}

/// Elementary cycles reachable by DFS over `edges`, each reported once
/// (rotated to start at its smallest id), in order of discovery.
fn find_cycles(keys: &[&Id], edges: impl Fn(&Id) -> Vec<Id>) -> Vec<Vec<Id>> {
    #[derive(Clone, Copy, PartialEq)]
    enum Color {
        White,
        Gray,
        Black,
    }
    let mut color: HashMap<Id, Color> = keys.iter().map(|k| ((*k).clone(), Color::White)).collect();
    let mut found: Vec<Vec<Id>> = Vec::new();
    let mut seen: HashSet<Vec<Id>> = HashSet::new();

    for &start in keys {
        if color[start] != Color::White {
            continue;
        }
        // Iterative DFS; `path` and `pending` (remaining out-edges of each
        // node on the path, in reverse so `pop` gives line order) stay in step.
        let mut path: Vec<Id> = vec![start.clone()];
        let mut pending: Vec<Vec<Id>> = vec![reversed(edges(start))];
        color.insert(start.clone(), Color::Gray);
        while let Some(next) = pending.last_mut() {
            let Some(target) = next.pop() else {
                let done = path.pop().expect("path and pending stay in step");
                pending.pop();
                color.insert(done, Color::Black);
                continue;
            };
            match color.get(&target).copied() {
                Some(Color::Gray) => {
                    let pos = path.iter().position(|p| *p == target).unwrap_or(0);
                    let mut cycle: Vec<Id> = path[pos..].to_vec();
                    rotate_to_min(&mut cycle);
                    if seen.insert(cycle.clone()) {
                        found.push(cycle);
                    }
                }
                Some(Color::White) => {
                    color.insert(target.clone(), Color::Gray);
                    pending.push(reversed(edges(&target)));
                    path.push(target);
                }
                _ => {}
            }
        }
    }
    found
}

fn reversed(mut v: Vec<Id>) -> Vec<Id> {
    v.reverse();
    v
}

fn rotate_to_min(cycle: &mut [Id]) {
    if let Some(min_pos) = (0..cycle.len()).min_by_key(|&i| &cycle[i]) {
        cycle.rotate_left(min_pos);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tree(files: &[(&str, &str)]) -> Tree {
        Tree::from_texts(files, &Config::default())
    }

    fn id(s: &str) -> Id {
        Id::new(s)
    }

    #[test]
    fn keys_for_idless_lines_are_titles() {
        let t = tree(&[("routines.md", "- lunch win:11:30-13:30 dur:30m every:day\n- ^\n")]);
        assert!(t.contains(&id("lunch")));
        assert_eq!(t.get(&id("lunch")).unwrap().ci, 1);
        assert!(!t.get(&id("lunch")).unwrap().has_id());
        assert_eq!(t.routine_ids().len(), 2);
    }

    #[test]
    fn duplicate_rule_keeps_the_live_copy() {
        let t = tree(&[
            ("month/2026-09.md", "# Outcomes\n- [ ] 4 !2 Out ^O\n# Demoted\n- [-] 4 3b Copy @O est:3b demoted:W37 ^m\n"),
            ("week/2026-W37.md", "- [ ] 4 6b Copy @O ^m\n- [ ] 3 1b Child @m ^c\n"),
        ]);
        assert!(t.duplicate_ids().is_empty());
        assert_eq!(t.get(&id("m")).unwrap().horizon, Horizon::Week(IsoWeek::new(2026, 37)));
        assert_eq!(t.demoted_copies().len(), 1);
        assert_eq!(t.children(&id("m")), &[id("c")]);
        assert_eq!(t.all(&id("m")).len(), 2);
        assert_eq!(t.month_items(YearMonth::new(2026, 9)).len(), 2);
        assert_eq!(t.root_priority(&id("c")), 2);
    }

    #[test]
    fn real_duplicates_are_reported() {
        let t = tree(&[("week/2026-W37.md", "- [ ] 3 1b A ^x\n- [ ] 3 1b B ^x\n")]);
        let d = t.duplicate_ids();
        assert_eq!(d.len(), 1);
        assert_eq!(d[0].1.len(), 2);
        assert_eq!(t.get(&id("x")).unwrap().title, "A");
        assert!(matches!(t.problems()[0], TreeProblem::DuplicateId { .. }));
    }

    #[test]
    fn cycles_do_not_hang() {
        let t = tree(&[("week/2026-W37.md", "- [ ] 3 A @b ^a\n- [ ] 3 B @a ^b\n")]);
        assert_eq!(t.parent_cycles(), vec![vec![id("a"), id("b")]]);
        assert!(t.roots().is_empty());
        assert_eq!(t.ancestors(&id("a")), vec![id("b")]);
        assert_eq!(t.remaining(&id("a")), None);
        assert_eq!(t.descendants(&id("a")), vec![id("b")]);
        assert_eq!(t.tags_effective(&id("a")), Vec::<String>::new());
    }
}
