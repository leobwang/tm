import TmKernel
/-!
Axiom audit.  Every theorem this stage claims must depend only on Lean's three
standard axioms — never `sorryAx`.  Run with:

    LEAN_PATH=.lake/build/lib/lean lean Check.lean
-/
open Tm

-- the horizon order, derived
#print axioms Tm.coarsen_month
#print axioms Tm.coarsen_saturates_only_at_month
#print axioms Tm.demote_is_one_step
#print axioms Tm.closeTo_target_is_open
#print axioms Tm.impl_day_rule_disagrees
#print axioms Tm.containing_can_target_a_closed_region
#print axioms Tm.horizonPrecedes_asymm
#print axioms Tm.demotion_target_follows_the_closed_region

-- entity versus observation
#print axioms Tm.archive_elsewhere
#print axioms Tm.one_line_per_file
#print axioms Tm.exactly_one_live
#print axioms Tm.archive_line_is_demoted

-- the plan as one object
#print axioms Tm.no_two_lines_of_one_id_in_one_file
#print axioms Tm.lines_per_id_le_two
#print axioms Tm.no_two_lines_of_one_id_in_one_path
#print axioms Tm.no_line_is_lost
#print axioms Tm.the_tombstone_is_behind_the_live_line
#print axioms Tm.a_backwards_demotion_is_refused
#print axioms Tm.a_reopened_record_needs_no_horizon
#print axioms Tm.transform_closed

-- the grammar
#print axioms Tm.readNat_digitsOf
#print axioms Tm.tokenize_raw
#print axioms Tm.tokenize_toks
#print axioms Tm.serialize_parse
#print axioms Tm.parse_serialize
#print axioms Tm.renderSplit_splitDoc
#print axioms Tm.view_set_is_not_silent
#print axioms Tm.lead_edit_is_silent
#print axioms Tm.setEst_canonical
#print axioms Tm.setEst_line_reparses

-- the commands
#print axioms Tm.move_into_archive_file_is_rejected
#print axioms Tm.plan_move_into_archive_file_is_rejected
#print axioms Tm.move_idem
#print axioms Tm.move_last_wins
#print axioms Tm.move_last_wins_refuted_globally
#print axioms Tm.move_back_restores
#print axioms Tm.move_back_at_a_fresh_rank_is_not_the_inverse
#print axioms Tm.drop_idem
#print axioms Tm.drop_preserves_archive_glyph
#print axioms Tm.readopt_reopens
#print axioms Tm.set_is_not_silent
#print axioms Tm.set_last_wins
#print axioms Tm.stamps_accumulate_across_readopt
#print axioms Tm.demote_twice_is_not_a_thing
#print axioms Tm.demote_on_a_standing_tombstone_is_refused
#print axioms Tm.demote_roundtrips
#print axioms Tm.demote_archive_none
#print axioms Tm.readopt_demote_not_id
#print axioms Tm.readopt_demote_id_mod_stamps
#print axioms Tm.readopt_of_a_live_record_is_refused
#print axioms Tm.readopt_after_demote_succeeds
#print axioms Tm.floor_and_respect_are_incompatible
#print axioms Tm.demoteEst_conserves
#print axioms Tm.demoteEst_respects_user
#print axioms Tm.mapAt_ok_of_inRange
#print axioms Tm.mapAt_rejects_unoriented
#print axioms Tm.cmdMove_succeeds
#print axioms Tm.demote_into_a_horizon_that_does_not_follow_is_rejected
#print axioms Tm.resolveDest_rejects

-- the glyph is a function of placement, and the loader is its inverse
#print axioms Tm.glyphOfStatus_statusOfGlyph
#print axioms Tm.statusOfGlyph_glyphOfStatus
#print axioms Tm.glyphAt_live
#print axioms Tm.glyphAt_statusOfGlyph
#print axioms Tm.glyphAt_statusOfGlyph_paired
#print axioms Tm.every_glyph_has_a_state
#print axioms Tm.a_differing_demotion_pair_renders_back

-- the boundary
#print axioms Tm.grain_rejects_99
#print axioms Tm.lone_placement_renders_back
#print axioms Tm.orientPair_comm
#print axioms Tm.pairedEntity_order_independent
#print axioms Tm.unordered_horizons_are_rejected
#print axioms Tm.paired_placement_renders_back
#print axioms Tm.paired_renders_each_placement
#print axioms Tm.the_kernel_can_read_the_pairs_it_writes
#print axioms Tm.load_render_line
#print axioms Tm.freshRank_gt
#print axioms Tm.move_out_and_back_is_not_the_inverse
#print axioms Tm.move_to_a_document_that_does_not_exist_is_rejected
#print axioms Tm.dedupIds_nodup
#print axioms Tm.firstDupPath_none

-- §6.3's three close rows, generated from one rule at three grains
#eval (closeTo day 250, closeTo week 250, closeTo month 250)
-- the rule horizon.rs:1323 uses, versus the derived one, on a Sunday closed on Monday
#eval (targetContaining day 6, closeTo day 7)

-- ===========================================================================
-- APPENDED: §3.1's item fields and the rest of the plan-level tier.
-- ===========================================================================

-- the bounded types and their smart constructors
#print axioms Tm.clock_rejects_25h
#print axioms Tm.clock_rejects_minute_60
#print axioms Tm.weekday_rejects_7
#print axioms Tm.monthDay_rejects_0
#print axioms Tm.monthDay_rejects_32
#print axioms Tm.monthDay_roundtrips
#print axioms Tm.TagSet.no_duplicates
#print axioms Tm.TagSet.mem_ofList

-- widening the entity leaves the tier structure alone
#print axioms Tm.wf_ignores_the_item_fields

-- §5.3's default `on_miss`, derived
#print axioms Tm.onMiss_interval
#print axioms Tm.onMiss_point
#print axioms Tm.onMiss_window
#print axioms Tm.effectiveOnMiss_override
#print axioms Tm.effectiveOnMiss_default

-- `@parent`: the walk, sound and complete, and the check bites
#print axioms Tm.anc_add
#print axioms Tm.chain_dup_gives_cycle
#print axioms Tm.parentsAcyclic_sound
#print axioms Tm.parentsAcyclic_complete
#print axioms Tm.self_parent_is_rejected
#print axioms Tm.climb_reaches_a_root
#print axioms Tm.every_item_has_a_root
#print axioms Tm.no_item_is_its_own_ancestor
#print axioms Tm.parent_names_an_item

-- `after:`: the peel, sound and complete, and the check bites
#print axioms Tm.peelN_empty_or_fixed
#print axioms Tm.fixed_is_deadlocked
#print axioms Tm.afterAcyclic_sound
#print axioms Tm.afterAcyclic_complete
#print axioms Tm.self_dep_is_rejected
#print axioms Tm.no_deadlocked_set
#print axioms Tm.dep_names_an_item

-- `Normalized`: a site names one line
#print axioms Tm.site_names_one_line
#print axioms Tm.no_prose_line_shares_a_rank

-- §3.2's derived fields
#print axioms Tm.effectiveShape_as_written
#print axioms Tm.effectiveShape_prep
#print axioms Tm.effectiveShape_does_not_reach_the_grandparent
#print axioms Tm.effectiveCi_explicit
#print axioms Tm.effectiveCi_inherits
#print axioms Tm.effectiveCi_default
#print axioms Tm.rootPrio_of_a_root
#print axioms Tm.rootPrio_walks_past_the_child

-- §4.2's sections and §4.3's per-file-kind shapes
#print axioms Tm.a_day_file_holds_only_pinned_items
#print axioms Tm.calendar_lines_are_intervals
#print axioms Tm.routine_lines_are_open
#print axioms Tm.routine_lines_have_a_window_or_after_done
#print axioms Tm.optional_items_declare_a_duration
#print axioms Tm.a_shapeless_calendar_line_is_rejected
#print axioms Tm.an_unpinned_day_item_is_rejected

-- ==========================================================================
-- APPENDED at the stage-one merge: the modules three concurrent branches
-- each added, which none of them could extend without conflicting.
-- ==========================================================================

-- Arith.lean
#print axioms Tm.Arith.denPos
#print axioms Tm.Arith.mkPos_num
#print axioms Tm.Arith.mkPos_den
#print axioms Tm.Arith.le_agrees_with_exact_division
#print axioms Tm.Arith.utilGe_eq_le
#print axioms Tm.Arith.utilGe_capacity_zero
#print axioms Tm.Arith.utilDefined_iff
#print axioms Tm.Arith.util_zero_over_zero_is_undefined
#print axioms Tm.Arith.util_zero_over_zero_is_hot
#print axioms Tm.Arith.utilScaledGe_cross
#print axioms Tm.Arith.utilScaledGe_eq_le
#print axioms Tm.Arith.isHot_iff
#print axioms Tm.Arith.impossible_imp_hot
#print axioms Tm.Arith.hot_and_possible_iff_exact
#print axioms Tm.Arith.binOf_ix
#print axioms Tm.Arith.binOf_eq_hot_iff
#print axioms Tm.Arith.binOf_eq_plus_iff
#print axioms Tm.Arith.rungs_le
#print axioms Tm.Arith.default_bin_le_three
#print axioms Tm.Arith.rungs_capacity_zero
#print axioms Tm.Arith.binOf_capacity_zero
#print axioms Tm.Arith.utilGe_mono
#print axioms Tm.Arith.rungs_antitone
#print axioms Tm.Arith.binOf_antitone
#print axioms Tm.Arith.rungs_mono_need
#print axioms Tm.Arith.rungs_anti_avail
#print axioms Tm.Arith.countP_tail_zero
#print axioms Tm.Arith.ladder_eq_rungs
#print axioms Tm.Arith.default_ladder_eq_rungs
#print axioms Tm.Arith.defaultBins_match_the_spec
#print axioms Tm.Arith.utilGe_edge_mono
#print axioms Tm.Arith.defaultBins_are_the_intervals
#print axioms Tm.Arith.log2_ladder_disagrees_at_eleven_percent
#print axioms Tm.Arith.floorQ_spec
#print axioms Tm.Arith.floorQ_le_self
#print axioms Tm.Arith.self_lt_floorQ_succ
#print axioms Tm.Arith.floorQ_withinOne
#print axioms Tm.Arith.floorQ_mono
#print axioms Tm.Arith.ceilQ_ge
#print axioms Tm.Arith.ceilQ_lt
#print axioms Tm.Arith.ceilQ_spec
#print axioms Tm.Arith.self_le_ceilQ
#print axioms Tm.Arith.ceilQ_withinOne
#print axioms Tm.Arith.ceilQ_mono
#print axioms Tm.Arith.floorQ_le_ceilQ
#print axioms Tm.Arith.halfUpQ_eq_floor
#print axioms Tm.Arith.halfUpQ_spec
#print axioms Tm.Arith.halfUpQ_withinOne
#print axioms Tm.Arith.halfUpQ_mono
#print axioms Tm.Arith.floorQ_le_halfUpQ
#print axioms Tm.Arith.halfUpQ_le_ceilQ
#print axioms Tm.Arith.rounding_agrees_when_exact
#print axioms Tm.Arith.scale_num
#print axioms Tm.Arith.scale_den
#print axioms Tm.Arith.needMin_covers
#print axioms Tm.Arith.needMin_ge_remaining
#print axioms Tm.Arith.needMin_safety_ge_remaining
#print axioms Tm.Arith.needMin_safety_examples
#print axioms Tm.Arith.rounding_the_need_changes_the_bin
#print axioms Tm.Arith.budget_eight_hours
#print axioms Tm.Arith.budget_mono_window
#print axioms Tm.Arith.overRatio_eq_lt
#print axioms Tm.Arith.overRatio_example
#print axioms Tm.Arith.plannedMin_mono
#print axioms Tm.Arith.plannedMin_withinOne
#print axioms Tm.Arith.plannedMin_example
#print axioms Tm.Arith.ramp_le_one
#print axioms Tm.Arith.ramp_full
#print axioms Tm.Arith.ramp_zero
#print axioms Tm.Arith.ramp_antitone
#print axioms Tm.Arith.defaultRamp_examples
#print axioms Tm.Arith.posterior_can_go_negative
#print axioms Tm.Arith.energyAfter_nonpos
#print axioms Tm.Arith.energyAfter_no_report
#print axioms Tm.Arith.energyAfter_examples

-- Boundary.lean
#print axioms Tm.grain_rejects_out_of_range
#print axioms Tm.grain_accepts_month
#print axioms Tm.dedupIds_cons
#print axioms Tm.mem_dedupIds
#print axioms Tm.orientPair_cases
#print axioms Tm.pairEntity_renders_back
#print axioms Tm.foldl_max_ge
#print axioms Tm.le_foldl_max
#print axioms Tm.live_line_mem
#print axioms Tm.demote_to_a_document_that_does_not_exist_is_rejected
#print axioms Tm.applyAll_closed

-- Cal.lean
#print axioms Tm.Cal.ys_zero
#print axioms Tm.Cal.ys_one
#print axioms Tm.Cal.ys_era_len
#print axioms Tm.Cal.ys_era
#print axioms Tm.Cal.q4
#print axioms Tm.Cal.q100
#print axioms Tm.Cal.q400
#print axioms Tm.Cal.isLeap_arith
#print axioms Tm.Cal.yearLen_as_if
#print axioms Tm.Cal.ys_step
#print axioms Tm.Cal.yearLen_bounds
#print axioms Tm.Cal.ys_succ_bounds
#print axioms Tm.Cal.ys_mono
#print axioms Tm.Cal.ys_le
#print axioms Tm.Cal.ys_ge
#print axioms Tm.Cal.yoe_bracket
#print axioms Tm.Cal.yearOfZ_bracket
#print axioms Tm.Cal.yearOfZ_unique
#print axioms Tm.Cal.yearOfZ_mono
#print axioms Tm.Cal.md_of_doy_common
#print axioms Tm.Cal.md_of_doy_leap
#print axioms Tm.Cal.doy_of_md_common
#print axioms Tm.Cal.doy_of_md_leap
#print axioms Tm.Cal.cumBefore_mono_common
#print axioms Tm.Cal.cumBefore_mono_leap
#print axioms Tm.Cal.monthLen_le_31_common
#print axioms Tm.Cal.monthLen_le_31_leap
#print axioms Tm.Cal.cumBefore_mono
#print axioms Tm.Cal.monthLen_le_31
#print axioms Tm.Cal.md_of_doy
#print axioms Tm.Cal.doy_of_md
#print axioms Tm.Cal.month_bracket
#print axioms Tm.Cal.monthOfDoy_mono
#print axioms Tm.Cal.valid_iff
#print axioms Tm.Cal.ofDay_year
#print axioms Tm.Cal.ofDay_month
#print axioms Tm.Cal.doy_in_range
#print axioms Tm.Cal.yearOfZ_ge_one
#print axioms Tm.Cal.ofDay_valid
#print axioms Tm.Cal.toDay_ofDay
#print axioms Tm.Cal.zOf_bracket
#print axioms Tm.Cal.originShift_le_zOf
#print axioms Tm.Cal.ofDay_toDay
#print axioms Tm.Cal.dayOf_dateOf
#print axioms Tm.Cal.dateOf_dayOf
#print axioms Tm.Cal.toDay_lt_of_year_lt
#print axioms Tm.Cal.leap_2000
#print axioms Tm.Cal.leap_1900
#print axioms Tm.Cal.leap_2024
#print axioms Tm.Cal.leap_2026
#print axioms Tm.Cal.feb_2024_has_29
#print axioms Tm.Cal.feb_1900_has_28
#print axioms Tm.Cal.feb_30_is_not_a_date
#print axioms Tm.Cal.feb_29_2024_is_a_date
#print axioms Tm.Cal.feb_29_2023_is_not_a_date
#print axioms Tm.Cal.month_13_is_not_a_date
#print axioms Tm.Cal.month_0_is_not_a_date
#print axioms Tm.Cal.year_0_is_not_a_date
#print axioms Tm.Cal.unixEpoch_eq
#print axioms Tm.Cal.after_feb28_2024
#print axioms Tm.Cal.after_feb28_2023
#print axioms Tm.Cal.year_2024_is_366
#print axioms Tm.Cal.year_1900_is_365
#print axioms Tm.Cal.year_2000_is_366
#print axioms Tm.Cal.weekday_origin
#print axioms Tm.Cal.weekday_1970_01_01
#print axioms Tm.Cal.weekday_2000_01_01
#print axioms Tm.Cal.weekday_2026_09_07
#print axioms Tm.Cal.weekdayOf_thursday_iff
#print axioms Tm.Cal.weekdayOf_wednesday_iff
#print axioms Tm.Cal.thursdayOf_is_thursday
#print axioms Tm.Cal.thursdayOf_in_week
#print axioms Tm.Cal.weekOrdinal_mono
#print axioms Tm.Cal.weekOrdinal_eq_iff
#print axioms Tm.Cal.jan1_shift
#print axioms Tm.Cal.jan1_step
#print axioms Tm.Cal.jan1_toDay
#print axioms Tm.Cal.isoOf_year
#print axioms Tm.Cal.isoOf_week
#print axioms Tm.Cal.isoOf_weekday
#print axioms Tm.Cal.isoOf_year_bracket
#print axioms Tm.Cal.isoOf_weekday_range
#print axioms Tm.Cal.isoOf_week_range
#print axioms Tm.Cal.isoWeeksIn_52_or_53
#print axioms Tm.Cal.isoWeeksIn_53_iff
#print axioms Tm.Cal.isoWeek1Monday_bracket
#print axioms Tm.Cal.dayOfIso_isoOf
#print axioms Tm.Cal.isoOf_dayOfIso
#print axioms Tm.Cal.iso_2026_09_07
#print axioms Tm.Cal.iso_2026_has_53_weeks
#print axioms Tm.Cal.iso_2027_01_01
#print axioms Tm.Cal.iso_2025_12_29
#print axioms Tm.Cal.iso_2020_has_53_weeks
#print axioms Tm.Cal.iso_2019_has_52_weeks
#print axioms Tm.Cal.iso_2021_01_01
#print axioms Tm.Cal.iso_year_can_differ_from_civil_year
#print axioms Tm.Cal.monthOrdinal_origin
#print axioms Tm.Cal.monthOrdinal_mono
#print axioms Tm.Cal.monthOrdinal_2026_09
#print axioms Tm.Cal.a_week_can_straddle_two_civil_months
#print axioms Tm.Cal.monthOfWeekByToday_is_not_stable
#print axioms Tm.Cal.monthOfIsoWeek_is_met
#print axioms Tm.Cal.monthOfIsoWeek_mono
#print axioms Tm.Cal.monthOfIsoWeek_W36
#print axioms Tm.Cal.monthOfIsoWeek_W35

-- Cmd.lean
#print axioms Tm.lift_roundtrips
#print axioms Tm.resolveDest_ix
#print axioms Tm.mapAt_get
#print axioms Tm.entityInRange_of_mem
#print axioms Tm.sitesInRange_set
#print axioms Tm.demotionsOriented_set
#print axioms Tm.settled_absorbing
#print axioms Tm.readopt_clears_archive
#print axioms Tm.readopt_keeps_stamps
#print axioms Tm.demote_stamps
#print axioms Tm.transform_state_none

-- Grain.lean
#print axioms Tm.coarsen_day
#print axioms Tm.coarsen_week
#print axioms Tm.coarsen_is_up
#print axioms Tm.index_day
#print axioms Tm.index_week
#print axioms Tm.index_month
#print axioms Tm.index_mono
#print axioms Tm.regionOf_is_open
#print axioms Tm.closed_is_stable_in_time
#print axioms Tm.epoch_day_6_is_a_sunday
#print axioms Tm.epoch_day_7_is_a_monday
#print axioms Tm.impl_rule_disagrees_iff
#print axioms Tm.containing_targets_a_closed_region_iff
#print axioms Tm.impl_day_rule_disagrees_2026
#print axioms Tm.containing_can_target_a_closed_region_2026
#print axioms Tm.day_refines_week
#print axioms Tm.week_does_not_refine_month
#print axioms Tm.monthOfWeek_is_met
#print axioms Tm.monthOfWeek_mono
#print axioms Tm.closeTo_week_is_not_monthOfWeek
#print axioms Tm.horizonPrecedes_iff
#print axioms Tm.horizonPrecedes_irrefl

-- Line.lean
#print axioms Tm.ofChar_char
#print axioms Tm.head_cons_tail
#print axioms Tm.rawFor_eq_raw
#print axioms Tm.unitValue_estWord
#print axioms Tm.isEstKey_estWord
#print axioms Tm.find_setEstIn
#print axioms Tm.find_insertBeforeId
#print axioms Tm.tok_wf_iff
#print axioms Tm.digitsOf_no_space
#print axioms Tm.estWord_ne_nil
#print axioms Tm.estWord_no_space
#print axioms Tm.estWord_not_id
#print axioms Tm.est_tok_wf
#print axioms Tm.toksWf_head_sep
#print axioms Tm.insertBeforeId_head
#print axioms Tm.toksWf_insertBeforeId
#print axioms Tm.toksWf_setEstIn
#print axioms Tm.idWords_insertBeforeId
#print axioms Tm.estKey_not_id
#print axioms Tm.idWords_setEstIn
#print axioms Tm.canonical_iff

-- Plan.lean
#print axioms Tm.filter_flatMap
#print axioms Tm.render_filter_other
#print axioms Tm.render_filter_self
#print axioms Tm.flatMap_of_all_empty
#print axioms Tm.sum_over_nodup_one_key
#print axioms Tm.itemsWf_parts
#print axioms Tm.itemsWf_of_parts
#print axioms Tm.planWf_parts
#print axioms Tm.planWf_of_parts
#print axioms Tm.docsWf_store
#print axioms Tm.pathsDistinct_store
#print axioms Tm.render_site
#print axioms Tm.lines_mem
#print axioms Tm.weave_nil_right
#print axioms Tm.weave_item_first
#print axioms Tm.weave_prose_first
#print axioms Tm.splitDoc_prose_ge
#print axioms Tm.splitDoc_items_ge
#print axioms Tm.anc_zero
#print axioms Tm.anc_succ_none
#print axioms Tm.anc_succ_some
#print axioms Tm.anc_none_mono
#print axioms Tm.anc_none_add
#print axioms Tm.chainOf_succ_none
#print axioms Tm.chainOf_succ_some
#print axioms Tm.chainOf_length
#print axioms Tm.chainOf_mem_dom
#print axioms Tm.chainOf_mem_anc
#print axioms Tm.peelN_nil
#print axioms Tm.peel_eq_or_lt
#print axioms Tm.deadlocked_survives_peel
#print axioms Tm.deadlocked_survives_peelN
#print axioms Tm.nodup_map_inj
#print axioms Tm.WfPlan
#print axioms Tm.climb_succ_none
#print axioms Tm.climb_succ_some
#print axioms Tm.shapeWf_of_mem

-- State.lean
#print axioms Tm.clock_accepts_2330
#print axioms Tm.dedupTags_mem
#print axioms Tm.dedupTags_nodup
#print axioms Tm.wfPair_none
#print axioms Tm.wfPair_some
#print axioms Tm.wf_eq
#print axioms Tm.render_le_two
#print axioms Tm.render_all_same_id

-- Text.lean
#print axioms Tm.glyph_roundtrip
#print axioms Tm.digit_roundtrip
#print axioms Tm.digitsOf_ne_nil
#print axioms Tm.digitsOf_all_digits
#print axioms Tm.readNatAux_of_digits
#print axioms Tm.natStep_digitsOf
#print axioms Tm.toTok_raw
#print axioms Tm.chunk_flatten
#print axioms Tm.group_flatten
#print axioms Tm.takeWhile_append_all
#print axioms Tm.chunk_head
#print axioms Tm.chunk_merge
#print axioms Tm.group_head
#print axioms Tm.group_word
#print axioms Tm.group_sep
#print axioms Tm.toTok_of_wf
#print axioms Tm.group_tok

-- ==========================================================================
-- APPENDED after stage 2 and the field wiring.
-- ==========================================================================

-- Arith.lean

-- Boundary.lean
#print axioms Tm.sortByRank_nil
#print axioms Tm.sortByRank_cons
#print axioms Tm.insertByRank_mem
#print axioms Tm.sortByRank_mem
#print axioms Tm.insertByRank_sorted
#print axioms Tm.sortByRank_sorted
#print axioms Tm.insertByRank_distinct
#print axioms Tm.sortByRank_distinct
#print axioms Tm.sortByRank_id
#print axioms Tm.sortByRank_strict
#print axioms Tm.mem_placementsOfDoc
#print axioms Tm.mem_placementsOf
#print axioms Tm.buildEntities_fold
#print axioms Tm.buildEntities_spec
#print axioms Tm.loadStore_fold_not_mem
#print axioms Tm.loadStore_fold_mem
#print axioms Tm.loadStore_fold_some
#print axioms Tm.loadStore_get_of_mem
#print axioms Tm.loadStore_get_some
#print axioms Tm.mem_lines_of_render
#print axioms Tm.loneEntity_archive
#print axioms Tm.buildEntity_renders
#print axioms Tm.loadCore_docsWf
#print axioms Tm.loadCore_lines_mem
#print axioms Tm.placements_of_doc
#print axioms Tm.renderDocAt_loadCore
#print axioms Tm.loadPlan_spec
#print axioms Tm.loadPlan_docs
#print axioms Tm.the_kernel_reads_back_what_it_writes
#print axioms Tm.renderDocAt_untouched
#print axioms Tm.mapAt_ok_shape
#print axioms Tm.a_command_rewrites_only_the_files_it_touches
#print axioms Tm.foldl_max_ge_gen
#print axioms Tm.le_foldl_max_gen
#print axioms Tm.docProseMax_ge
#print axioms Tm.archive_line_mem
#print axioms Tm.live_line_site_mem
#print axioms Tm.normalized_of_fresh_or_old
#print axioms Tm.normalized_after_relocation
#print axioms Tm.normalized_after_edit
#print axioms Tm.move_at_freshRank_normalized
#print axioms Tm.moveTo_freshRank_normalized
#print axioms Tm.demote_at_freshRank_normalized
#print axioms Tm.readopt_at_freshRank_normalized
#print axioms Tm.drop_normalized
#print axioms Tm.setEst_normalized
#print axioms Tm.itemsWf_of_normalized
#print axioms Tm.applyCmd_move_succeeds
#print axioms Tm.runPlan_renders_the_input
#print axioms Tm.the_round_trip_is_not_vacuous
#print axioms Tm.the_round_trip_fires
#print axioms Tm.the_spec_demotion_pair_loads
#print axioms Tm.the_spec_pair_is_one_entity_with_a_tombstone
#print axioms Tm.the_spec_pair_puts_the_tombstone_in_the_month
#print axioms Tm.the_spec_demotion_pair_round_trips

-- Cmd.lean

-- Line.lean
#print axioms Tm.Field.isDigitC_cases
#print axioms Tm.Field.upper_not_lower
#print axioms Tm.Field.upper_not_digit
#print axioms Tm.Field.digit_not_lower
#print axioms Tm.Field.digit_not_upper
#print axioms Tm.Field.isName_all
#print axioms Tm.Field.isName_ne_nil
#print axioms Tm.Field.isNameC_ne
#print axioms Tm.Field.isName_avoids
#print axioms Tm.Field.isName_no_space
#print axioms Tm.Field.cap_is_an_alias_of_max
#print axioms Tm.Field.cap_writes_as_max
#print axioms Tm.Field.key_name_roundtrip
#print axioms Tm.Field.key_name_isKey
#print axioms Tm.Field.key_name_ne_nil
#print axioms Tm.Field.key_name_avoids
#print axioms Tm.Field.flag_name_roundtrip
#print axioms Tm.Field.flag_name_ne_nil
#print axioms Tm.Field.flag_name_no_space
#print axioms Tm.Field.flag_name_no_colon
#print axioms Tm.Field.digitsOf_isDigitC
#print axioms Tm.Field.hmOf_concat
#print axioms Tm.Field.parse_render_dur
#print axioms Tm.Field.parse_render_durND
#print axioms Tm.Field.renderDur_ne_nil
#print axioms Tm.Field.renderDur_chars
#print axioms Tm.Field.renderDur_head_digit
#print axioms Tm.Field.clock_rejects_2500
#print axioms Tm.Field.clock_rejects_minute_60
#print axioms Tm.Field.clock_rejects_unpadded
#print axioms Tm.Field.clock_reads_1130
#print axioms Tm.Field.padTo2_length
#print axioms Tm.Field.padTo_digits
#print axioms Tm.Field.padTo_no_colon
#print axioms Tm.Field.parse_render_clock
#print axioms Tm.Field.renderClock_length
#print axioms Tm.Field.renderClock_chars
#print axioms Tm.Field.renderClock_head_digit
#print axioms Tm.Field.ofDay_month_bounds
#print axioms Tm.Field.ofDay_day_bounds
#print axioms Tm.Field.padTo4_length
#print axioms Tm.Field.padTo_not_char
#print axioms Tm.Field.date_rejects_feb30
#print axioms Tm.Field.date_accepts_feb29_2024
#print axioms Tm.Field.date_rejects_unpadded
#print axioms Tm.Field.date_rejects_year_zero
#print axioms Tm.Field.parse_render_date
#print axioms Tm.Field.renderDate_chars
#print axioms Tm.Field.renderDate_avoid
#print axioms Tm.Field.renderDate_head_digit
#print axioms Tm.Field.renderDT_chars
#print axioms Tm.Field.renderDT_avoid
#print axioms Tm.Field.parse_render_DT
#print axioms Tm.Field.parseDT_clock_none
#print axioms Tm.Field.parse_render_moment
#print axioms Tm.Field.moment_date_form
#print axioms Tm.Field.moment_datetime_form
#print axioms Tm.Field.parse_render_interval
#print axioms Tm.Field.renderClock_no_slash
#print axioms Tm.Field.renderClock_no_dash
#print axioms Tm.Field.parse_render_window
#print axioms Tm.Field.overnight_window_roundtrips
#print axioms Tm.Field.pref_bare_wake
#print axioms Tm.Field.parse_render_pref
#print axioms Tm.Field.mapOpt_map
#print axioms Tm.Field.headSat_ne
#print axioms Tm.Field.headSat_cons
#print axioms Tm.Field.headSat_append
#print axioms Tm.Field.headSat_digitsOf
#print axioms Tm.Field.headSat_false_of
#print axioms Tm.Field.headSat_not
#print axioms Tm.Field.parse_render_weekday
#print axioms Tm.Field.renderWeekday_no_comma
#print axioms Tm.Field.headSat_renderWeekday
#print axioms Tm.Field.rule_day
#print axioms Tm.Field.rule_weekday
#print axioms Tm.Field.rule_mwf
#print axioms Tm.Field.rule_2w_sun
#print axioms Tm.Field.rule_3d
#print axioms Tm.Field.rule_month_15
#print axioms Tm.Field.rule_week
#print axioms Tm.Field.rule_month_0_rejected
#print axioms Tm.Field.rule_month_32_rejected
#print axioms Tm.Field.rule_0d_rejected
#print axioms Tm.Field.renderRule_not_literal
#print axioms Tm.Field.parse_render_rule
#print axioms Tm.Field.renderDur_no
#print axioms Tm.Field.parse_render_afterDone
#print axioms Tm.Field.parse_render_onEvent
#print axioms Tm.Field.parse_render_onMiss
#print axioms Tm.Field.parse_render_period
#print axioms Tm.Field.parse_render_rate
#print axioms Tm.Field.rate_6b_w
#print axioms Tm.Field.rate_4h_w
#print axioms Tm.Field.rate_2b_d
#print axioms Tm.Field.parse_render_dep
#print axioms Tm.Field.eventPrefix_no_comma
#print axioms Tm.Field.renderDep_no_comma
#print axioms Tm.Field.parse_render_deps
#print axioms Tm.Field.deps_mixed
#print axioms Tm.Field.parse_render_loc
#print axioms Tm.Field.parse_render_stamp
#print axioms Tm.Field.renderStamp_no_comma
#print axioms Tm.Field.parse_render_stamps
#print axioms Tm.Field.stamps_W36_W37
#print axioms Tm.Field.readNat_single
#print axioms Tm.Field.parse_render_ci
#print axioms Tm.Field.ci_rejects_6
#print axioms Tm.Field.ci_rejects_9
#print axioms Tm.Field.parse_render_prio
#print axioms Tm.Field.prio_rejects_5
#print axioms Tm.Field.prio_rejects_0
#print axioms Tm.Field.prio_reads_1
#print axioms Tm.Field.keyPrefix_head
#print axioms Tm.Field.sigilOf_head
#print axioms Tm.Field.sigil_not_key
#print axioms Tm.Field.sigil_not_digit
#print axioms Tm.Field.digit_not_key
#print axioms Tm.Field.keyPrefix_none_of
#print axioms Tm.Field.sigilOf_none_of
#print axioms Tm.Field.estSlot_head
#print axioms Tm.Field.ciSlot_head
#print axioms Tm.Field.startsToken_not_digit
#print axioms Tm.Field.estSlot_none_of_startsToken
#print axioms Tm.Field.ciSlot_none_of_startsToken
#print axioms Tm.Field.filterMap_cons_none'
#print axioms Tm.Field.filterMap_cons_some'
#print axioms Tm.Field.extract_phase3
#print axioms Tm.Field.extract_phase2
#print axioms Tm.Field.extract_phase1
#print axioms Tm.Field.extract_phase0
#print axioms Tm.Field.classifyPhase3_append
#print axioms Tm.Field.classifyPhase2_suffix
#print axioms Tm.Field.classifyPhase1_suffix
#print axioms Tm.Field.classifyPhase0_suffix
#print axioms Tm.Field.shape_at_wins
#print axioms Tm.Field.shape_win_needs_dur
#print axioms Tm.Field.shape_due_is_last
#print axioms Tm.Field.recur_every_wins
#print axioms Tm.Field.recur_afterDone_beats_onEvent
#print axioms Tm.Field.unparsed_sub_title
#print axioms Tm.Field.unclassified_token_stays_in_the_title
#print axioms Tm.Field.extra_sub_problems
#print axioms Tm.Field.unknown_key_is_reported
#print axioms Tm.Field.classifySigil_ne_extra
#print axioms Tm.Field.classifyPlain_ne_extra
#print axioms Tm.Field.kpOne_classifyBang
#print axioms Tm.Field.kpOne_classifySigil
#print axioms Tm.Field.kpOne_classifyPlain
#print axioms Tm.Field.keyValue_isSome
#print axioms Tm.Field.kpOne_classifyWord
#print axioms Tm.Field.extra_key_is_unknown
#print axioms Tm.Field.rawKeyPair_none_of_keyPrefix
#print axioms Tm.Field.rawKeyPair_none_of_digit
#print axioms Tm.Field.rawKeyPair_none_of_notStarts
#print axioms Tm.Field.keyPairs_raw
#print axioms Tm.Field.wordWf_iff
#print axioms Tm.Field.keyPrefix_keyWord
#print axioms Tm.Field.keyValue_keyWord
#print axioms Tm.Field.keyOf_keyWord
#print axioms Tm.Field.rawKeyPair_keyWord
#print axioms Tm.Field.keyWord_wordWf
#print axioms Tm.Field.keyWord_not_id
#print axioms Tm.Field.setKeyIn_cons_pos
#print axioms Tm.Field.setKeyIn_cons_neg
#print axioms Tm.Field.insertBeforeId_nil
#print axioms Tm.Field.insertBeforeId_id_nosep
#print axioms Tm.Field.insertBeforeId_id_sep
#print axioms Tm.Field.insertBeforeId_other
#print axioms Tm.Field.rawKeyPair_key
#print axioms Tm.Field.lookup_cons_ne
#print axioms Tm.Field.lookup_cons_self
#print axioms Tm.Field.lookup_cons_skip
#print axioms Tm.Field.lookup_setKeyIn
#print axioms Tm.Field.lookup_insertBeforeId
#print axioms Tm.Field.lookupKey_setKey
#print axioms Tm.Field.lookup_filter_none
#print axioms Tm.Field.lookupKey_unsetKey
#print axioms Tm.Field.view_set_due
#print axioms Tm.Field.view_set_at
#print axioms Tm.Field.view_set_win
#print axioms Tm.Field.view_set_dur
#print axioms Tm.Field.view_set_pref
#print axioms Tm.Field.view_set_every
#print axioms Tm.Field.view_set_afterDone
#print axioms Tm.Field.view_set_onEvent
#print axioms Tm.Field.view_set_onMiss
#print axioms Tm.Field.view_set_min
#print axioms Tm.Field.view_set_max
#print axioms Tm.Field.view_set_after
#print axioms Tm.Field.view_set_loc
#print axioms Tm.Field.view_set_estKey
#print axioms Tm.Field.view_set_demoted
#print axioms Tm.Field.view_set_waiting
#print axioms Tm.Field.view_set_buffer
#print axioms Tm.Field.view_set_ciKey
#print axioms Tm.Field.view_set_remaining
#print axioms Tm.Field.view_set_ci
#print axioms Tm.Field.est_key_beats_lead
#print axioms Tm.Field.ci_key_beats_positional
#print axioms Tm.Field.est_key_overrides_the_leading_estimate
#print axioms Tm.Field.unset_ci_key_leaves_the_positional_digit
#print axioms Tm.Field.set_max_writes_max
#print axioms Tm.Field.tok_wf_of_wordWf
#print axioms Tm.Field.toksWf_setKeyIn
#print axioms Tm.Field.toksWf_insertBeforeId_gen
#print axioms Tm.Field.idWords_setKeyIn
#print axioms Tm.Field.idWords_insertBeforeId_gen
#print axioms Tm.Field.setKey_canonical
#print axioms Tm.Field.setKey_line_reparses
#print axioms Tm.Field.isIdWord_startsToken
#print axioms Tm.Field.classifyWord_flag
#print axioms Tm.Field.insertAfterId_shape
#print axioms Tm.Field.view_set_flag
#print axioms Tm.Field.insertAfterId_none
#print axioms Tm.Field.setFlag_needs_a_boundary
#print axioms Tm.Field.filterMap_map_none'
#print axioms Tm.Field.filterMap_map_id'
#print axioms Tm.Field.filterMap_opt_none
#print axioms Tm.Field.rawKeyPair_tokOf_sigil
#print axioms Tm.Field.sigilOf_cons
#print axioms Tm.Field.rawKeyPair_at
#print axioms Tm.Field.rawKeyPair_hash
#print axioms Tm.Field.rawKeyPair_caret
#print axioms Tm.Field.rawKeyPair_prio
#print axioms Tm.Field.renderCi_head
#print axioms Tm.Field.rawKeyPair_ci
#print axioms Tm.Field.renderDur_headSat
#print axioms Tm.Field.rawKeyPair_estWordD
#print axioms Tm.Field.keyPrefix_flag
#print axioms Tm.Field.rawKeyPair_flag
#print axioms Tm.Field.keyPrefix_extra
#print axioms Tm.Field.rawKeyPair_extra
#print axioms Tm.Field.filterMap_map_none_mem
#print axioms Tm.Field.classifyWord_unparsed_sigil
#print axioms Tm.Field.rawKeyPair_unparsed
#print axioms Tm.Field.keyPairs_render
#print axioms Tm.Field.lookup_pair_self
#print axioms Tm.Field.lookup_pair_ne
#print axioms Tm.Field.lookup_filterMap_notMem
#print axioms Tm.Field.lookup_filterMap_pairs
#print axioms Tm.Field.kvList_keys
#print axioms Tm.Field.kvList_nodup
#print axioms Tm.Field.lookupKey_render
#print axioms Tm.Field.bind_map_render
#print axioms Tm.Field.optWf_some
#print axioms Tm.Field.kv_due
#print axioms Tm.Field.kv_interval
#print axioms Tm.Field.kv_window
#print axioms Tm.Field.kv_dur
#print axioms Tm.Field.kv_pref
#print axioms Tm.Field.kv_every
#print axioms Tm.Field.kv_afterDone
#print axioms Tm.Field.kv_onEvent
#print axioms Tm.Field.kv_onMiss
#print axioms Tm.Field.kv_floor
#print axioms Tm.Field.kv_cap
#print axioms Tm.Field.kv_after
#print axioms Tm.Field.kv_loc
#print axioms Tm.Field.kv_est
#print axioms Tm.Field.kv_demoted
#print axioms Tm.Field.kv_waiting
#print axioms Tm.Field.kv_buffer
#print axioms Tm.Field.kv_ci
#print axioms Tm.Field.view_render_due
#print axioms Tm.Field.view_render_interval
#print axioms Tm.Field.view_render_window
#print axioms Tm.Field.view_render_dur
#print axioms Tm.Field.view_render_pref
#print axioms Tm.Field.view_render_every
#print axioms Tm.Field.view_render_afterDone
#print axioms Tm.Field.view_render_onEvent
#print axioms Tm.Field.view_render_onMiss
#print axioms Tm.Field.view_render_floor
#print axioms Tm.Field.view_render_cap
#print axioms Tm.Field.view_render_after
#print axioms Tm.Field.view_render_loc
#print axioms Tm.Field.view_render_est
#print axioms Tm.Field.view_render_demoted
#print axioms Tm.Field.view_render_waiting
#print axioms Tm.Field.view_render_buffer
#print axioms Tm.Field.view_render_ci
#print axioms Tm.Field.filterMapMapNone
#print axioms Tm.Field.filterMapMapSome
#print axioms Tm.Field.filterMapOptNone
#print axioms Tm.Field.filterMapOptSome
#print axioms Tm.Field.findSome_append
#print axioms Tm.Field.findSomeMapNone
#print axioms Tm.Field.findSomeOptNone
#print axioms Tm.Field.findSomeOptSome
#print axioms Tm.Field.classifyPhase3_map
#print axioms Tm.Field.classifyPhase2_title
#print axioms Tm.Field.classifyPhase1_of_noEst
#print axioms Tm.Field.classifyPhase0_of_noCi
#print axioms Tm.Field.ciSlot_renderCi
#print axioms Tm.Field.estSlot_renderDur
#print axioms Tm.Field.ciSlot_none_of_len
#print axioms Tm.Field.renderDur_length
#print axioms Tm.Field.ciSlot_renderDur
#print axioms Tm.Field.ciSlot_caret
#print axioms Tm.Field.estSlot_caret
#print axioms Tm.Field.startsToken_caret
#print axioms Tm.Field.key_not_sigil
#print axioms Tm.Field.sigilOf_keyed
#print axioms Tm.Field.classifyWord_id
#print axioms Tm.Field.classifyWord_parent
#print axioms Tm.Field.classifyWord_tag
#print axioms Tm.Field.classifyWord_prio
#print axioms Tm.Field.classifyWord_key
#print axioms Tm.Field.classifyWord_extra
#print axioms Tm.Field.map_map'
#print axioms Tm.Field.map_congr'
#print axioms Tm.Field.mapOpt_toList
#print axioms Tm.Field.optMap_congr
#print axioms Tm.Field.midToks_kinds
#print axioms Tm.Field.slotGuard_est
#print axioms Tm.Field.slotGuard_ci
#print axioms Tm.Field.head_title_mid
#print axioms Tm.Field.kinds_render
#print axioms Tm.Field.findSome_cons_none
#print axioms Tm.Field.orElse_none
#print axioms Tm.Field.view_render_title
#print axioms Tm.Field.view_render_unparsed
#print axioms Tm.Field.view_render_tags
#print axioms Tm.Field.view_render_flags
#print axioms Tm.Field.view_render_extra
#print axioms Tm.Field.view_render_parent
#print axioms Tm.Field.view_render_prio
#print axioms Tm.Field.view_render_ciSlot
#print axioms Tm.Field.view_render_estLead
#print axioms Tm.Field.view_render_id
#print axioms Tm.Field.field_round_trip
#print axioms Tm.Field.title_absorbs_the_unclassified
#print axioms Tm.Field.spec_line_is_an_item
#print axioms Tm.Field.spec_line_ci
#print axioms Tm.Field.spec_line_leading_estimate
#print axioms Tm.Field.spec_line_remaining
#print axioms Tm.Field.spec_line_title
#print axioms Tm.Field.spec_line_parent
#print axioms Tm.Field.spec_line_tags
#print axioms Tm.Field.spec_line_due
#print axioms Tm.Field.spec_line_max
#print axioms Tm.Field.spec_line_id
#print axioms Tm.Field.spec_line_no_problems
#print axioms Tm.Field.spec_line_bytes
#print axioms Tm.Field.junk_extra_keys
#print axioms Tm.Field.junk_problems
#print axioms Tm.Field.junk_title
#print axioms Tm.Field.junk_bytes
#print axioms Tm.Field.flag_word_in_the_title_is_title_text
#print axioms Tm.Field.flag_word_after_the_id_is_a_flag
#print axioms Tm.Field.renderToks_words
#print axioms Tm.Field.toksWf_tokOf
#print axioms Tm.Field.wordWf_cons
#print axioms Tm.Field.wordWf_singleton
#print axioms Tm.Field.digitChar_not_space
#print axioms Tm.Field.wordWf_renderCi
#print axioms Tm.Field.wordWf_renderDur
#print axioms Tm.Field.wordWf_renderPrio
#print axioms Tm.Field.wordWf_flag
#print axioms Tm.Field.wordWf_isName
#print axioms Tm.Field.wordWf_caret
#print axioms Tm.Field.isIdWord_false_of_head
#print axioms Tm.Field.isIdWord_false_of_notStarts
#print axioms Tm.Field.isIdWord_false_cons
#print axioms Tm.Field.filter_map'
#print axioms Tm.Field.filterMapNoneList
#print axioms Tm.Field.filterOptNoneList
#print axioms Tm.Field.filter_map_gen
#print axioms Tm.Field.forall_mem_append'
#print axioms Tm.Field.forall_mem_cons'
#print axioms Tm.Field.forall_mem_map'
#print axioms Tm.Field.forall_mem_optToList'
#print axioms Tm.Field.filter_isIdWord_title
#print axioms Tm.Field.filter_isIdWord_words
#print axioms Tm.Field.headSat_keyWord
#print axioms Tm.Field.headSat_flag
#print axioms Tm.Field.renderWords_wordWf
#print axioms Tm.Field.filter_isIdWord_render
#print axioms Tm.Field.idToks_render
#print axioms Tm.Field.renderItem_canonical
#print axioms Tm.Field.render_round_trip
#print axioms Tm.Field.demo_wf
#print axioms Tm.Field.demo_round_trips
#print axioms Tm.Field.demo_line_reparses
#print axioms Tm.Field.demo_line_bytes
#print axioms Tm.Field.row_due_date
#print axioms Tm.Field.row_due_datetime
#print axioms Tm.Field.row_at_same_day
#print axioms Tm.Field.row_at_cross_day
#print axioms Tm.Field.row_at_rolls_past_midnight
#print axioms Tm.Field.row_win_daily
#print axioms Tm.Field.row_win_absolute
#print axioms Tm.Field.row_dur_30m
#print axioms Tm.Field.row_dur_1h
#print axioms Tm.Field.row_dur_hours_minutes
#print axioms Tm.Field.row_pref_wake_plus
#print axioms Tm.Field.row_pref_clock
#print axioms Tm.Field.row_every_day
#print axioms Tm.Field.row_every_weekday
#print axioms Tm.Field.row_every_mwf
#print axioms Tm.Field.row_every_2w_sun
#print axioms Tm.Field.row_every_3d
#print axioms Tm.Field.row_every_month_15
#print axioms Tm.Field.row_every_week
#print axioms Tm.Field.row_after_done_offset
#print axioms Tm.Field.row_after_done_window
#print axioms Tm.Field.row_on_event_bare
#print axioms Tm.Field.row_on_event_timeout
#print axioms Tm.Field.row_on_miss_expire
#print axioms Tm.Field.row_on_miss_persist
#print axioms Tm.Field.row_on_miss_next
#print axioms Tm.Field.row_min_6b_w
#print axioms Tm.Field.row_max_2b_d
#print axioms Tm.Field.row_cap_4h_w
#print axioms Tm.Field.row_after_ids
#print axioms Tm.Field.row_after_event
#print axioms Tm.Field.row_loc_lounge
#print axioms Tm.Field.row_loc_named
#print axioms Tm.Field.row_est_1b
#print axioms Tm.Field.row_demoted_stamps
#print axioms Tm.Field.row_waiting_date
#print axioms Tm.Field.row_buffer_2h
#print axioms Tm.Field.row_ci_key
#print axioms Tm.Field.row_flags
#print axioms Tm.Field.intervalWf_is_satisfiable
#print axioms Tm.Field.the_two_est_setters_write_the_same_token
#print axioms Tm.Field.toksWf_head_wf
#print axioms Tm.Field.toksWf_tail
#print axioms Tm.Field.toksWf_seps
#print axioms Tm.Field.toksWf_filter
#print axioms Tm.Field.isKeyTok_false_of_isIdWord
#print axioms Tm.Field.idWords_filter_notKey
#print axioms Tm.Field.unsetKey_canonical
#print axioms Tm.Field.unsetKey_line_reparses
#print axioms Tm.Field.setFlag_on_the_spec_line

-- Plan.lean
#print axioms Tm.splitDoc_nil
#print axioms Tm.splitDoc_cons_ok
#print axioms Tm.splitDoc_cons_error
#print axioms Tm.sorted_ext_by_key
#print axioms Tm.splitDoc_prose_sorted
#print axioms Tm.splitDoc_items_sorted
#print axioms Tm.pairwise_lt_of_le_ne
#print axioms Tm.pairwise_ne_of_nodup_keys
#print axioms Tm.flatMap_congr
#print axioms Tm.site_eq
#print axioms Tm.lines_set
#print axioms Tm.docRanks_eq
#print axioms Tm.ranksIn_append
#print axioms Tm.mem_ranksIn
#print axioms Tm.mem_proseRanks
#print axioms Tm.nodup_of_length_le_one
#print axioms Tm.render_filter_doc_len
#print axioms Tm.ranksIn_render_nodup
#print axioms Tm.nodup_swap_middle
#print axioms Tm.normalized_set

-- State.lean
#print axioms Tm.the_fields_are_the_line
#print axioms Tm.coreOfLine_fields
#print axioms Tm.coreOfLine_shape
#print axioms Tm.coreOfLine_recur
#print axioms Tm.coreOfLine_stamps
#print axioms Tm.the_spec_calendar_line_is_an_interval
#print axioms Tm.the_spec_calendar_line_has_a_loc
#print axioms Tm.the_spec_demoted_line_is_read_whole
#print axioms Tm.the_spec_item_line_is_read_whole
#print axioms Tm.core_fields_round_trip
#print axioms Tm.a_lone_demotion_renders_back

-- Text.lean
#print axioms Tm.digitsAux_fuel
#print axioms Tm.digitsOf_eq
#print axioms Tm.digitsOf_noSpace
#print axioms Tm.zeros_all_zero
#print axioms Tm.natStep_zeros
#print axioms Tm.zeros_are_digits
#print axioms Tm.readNat_padTo
#print axioms Tm.padTo_ne_nil
#print axioms Tm.padTo_no_space
#print axioms Tm.splitFirst_append
#print axioms Tm.splitFirst_sound
#print axioms Tm.splitOn_ne_nil
#print axioms Tm.splitOn_prepend
#print axioms Tm.splitOn_joinWith
#print axioms Tm.zeros_length
#print axioms Tm.digitsOf_length_le
#print axioms Tm.padTo_length
#print axioms Tm.splitFirst_none
#print axioms Tm.stripPre_append
#print axioms Tm.stripPre_head_ne

-- ==========================================================================
-- Dotted theorem names the earlier generator truncated (Q.le_refl became Q).
-- ==========================================================================
#print axioms Tm.Arith.Q.ok_defined
#print axioms Tm.Arith.Q.le_of
#print axioms Tm.Arith.Q.le_elim
#print axioms Tm.Arith.Q.lt_iff_not_le
#print axioms Tm.Arith.Q.le_refl
#print axioms Tm.Arith.Q.lt_irrefl
#print axioms Tm.Arith.Q.le_total
#print axioms Tm.Arith.Q.le_antisymm
#print axioms Tm.Arith.Q.le_trans
#print axioms Tm.Arith.Q.le_congr_left
#print axioms Tm.Arith.Q.le_congr_right
#print axioms Tm.Arith.Q.equiv_scale
#print axioms Tm.Arith.Q.le_scale_left
#print axioms Tm.Store.insert_get
#print axioms Tm.Store.get_set_self
#print axioms Tm.Store.get_set_other
#print axioms Tm.Store.dom_set
#print axioms Tm.WfPlan.items

-- the two `ofPair?` lemmas the earlier generator cut at the `?`
#print axioms Tm.Arith.ofPair?_zero
#print axioms Tm.Arith.ofPair?_some

-- added by the demotion-orientation revision
#print axioms Tm.demote_ok
#print axioms Tm.readopt_ok
#print axioms Tm.Core.archiveSite_none
#print axioms Tm.Core.archiveSite_some

-- APPENDED 2026-09-09 (stage-3 boundary session)
#print axioms Tm.the_char_edge_round_trips
-- APPENDED 2026-09-09 (stage-3 loader session: gap 16's loader pair)
#print axioms Tm.placement_doc_lt
#print axioms Tm.docRegion_loadCore_placement
#print axioms Tm.siteInRange_loadCore
#print axioms Tm.placement_bounds_pair
#print axioms Tm.entityInRange_loadEntity
#print axioms Tm.demotionOriented_loadEntity
#print axioms Tm.the_loader_builds_sites_in_range
#print axioms Tm.the_loader_builds_oriented_demotions

-- APPENDED 2026-09-09 (stage-3 loader session 2: the normalized third, gap 16 closed)
#print axioms Tm.render_nodup
#print axioms Tm.flatMap_nodup_store
#print axioms Tm.store_lines_nodup
#print axioms Tm.Store.insert_dom
#print axioms Tm.foldl_insert_dom_nodup
#print axioms Tm.slots_nodup_of_nodup
#print axioms Tm.placements_slot_nodup
#print axioms Tm.ranksIn_nodup_lines
#print axioms Tm.getElem?_eq_some_of_lt
#print axioms Tm.splitDoc_prose_nodup
#print axioms Tm.splitDoc_items_nodup
#print axioms Tm.splitDoc_slots_separated
#print axioms Tm.the_loader_builds_a_normalized_plan

-- APPENDED 2026-09-09 (stage-3 rank-verb session)
#print axioms Tm.lift_ok_of_wf
#print axioms Tm.wf_setRank
#print axioms Tm.setRankE_idem
#print axioms Tm.mapAt_at
#print axioms Tm.Store.set_same
#print axioms Tm.planCore_set_same
#print axioms Tm.rank_is_idempotent
#print axioms Tm.rank_preserves_the_order_of_the_others

-- APPENDED 2026-09-09 (stage-3 fresh-id session)
#print axioms Tm.digitsOf_injective
#print axioms Tm.candidates_nodup
#print axioms Tm.add_assigns_a_fresh_id

-- APPENDED 2026-09-10 (stage-3 gap-4 session: the est command path writes what Core.est reads)
#print axioms Tm.the_command_path_writes_what_the_field_path_reads

-- APPENDED 2026-09-10 (stage-3 add session: fresh id, insert, badItem)
#print axioms Tm.Store.get_insertFresh_self
#print axioms Tm.Store.get_insertFresh_other
#print axioms Tm.Store.dom_insertFresh
#print axioms Tm.WfPlan.insertFresh_get
#print axioms Tm.WfPlan.insertFresh_other
#print axioms Tm.WfPlan.insertFresh_rejects
#print axioms Tm.store_get_isNone_of_not_mem
#print axioms Tm.parseCmd_rejects_add_title_variants
#print axioms Tm.cmdAdd_inserts
#print axioms Tm.cmdAdd_rank
#print axioms Tm.cmdAdd_other_untouched

-- APPENDED 2026-09-12 (stage-3 continuation session)
#print axioms Tm.rank_onto_a_taken_rank_is_refused
#print axioms Tm.setRank_sitesFree
#print axioms Tm.cmdRank_succeeds
#print axioms Tm.applyCmd_rank_succeeds
#print axioms Tm.lines_insertFresh
#print axioms Tm.normalized_insertFresh_of_fresh
#print axioms Tm.add_at_freshRank_normalized
#print axioms Tm.sitesInRange_insertFresh
#print axioms Tm.demotionsOriented_insertFresh
#print axioms Tm.cmdAdd_succeeds
#print axioms Tm.the_undo_witness_loads
#print axioms Tm.move_has_no_inverse_command
#print axioms Tm.joinWith_splitOn
#print axioms Tm.a_file_splits_into_the_lines_it_was_joined_from_char
#print axioms Tm.joining_lines_is_not_injective_char

-- (same session, edit-widening block: the keyed edit, gap 32's guard, and
-- the est op routed through it)
#print axioms Tm.ndDur?_is_parseDurND
#print axioms Tm.setVal_writes_the_token_the_loader_reads
#print axioms Tm.editValOf_refuses_unwired_keys
#print axioms Tm.the_nine_wired_keys_accept_their_spec_values
#print axioms Tm.key_of_map
#print axioms Tm.editValOf_key
#print axioms Tm.editE_refuses_a_tabbed_line
#print axioms Tm.editE_ok_of_tabless
#print axioms Tm.the_edit_path_writes_what_the_field_path_reads
#print axioms Tm.unsetE_refuses_a_tabbed_line
#print axioms Tm.unset_of_a_key_the_line_does_not_carry_is_refused
#print axioms Tm.unsetE_ok_of_present
#print axioms Tm.the_unset_path_removes_what_the_field_path_reads
#print axioms Tm.the_est_op_is_the_keyed_est_edit
#print axioms Tm.edit_of_a_tabbed_line_is_refused
#print axioms Tm.est_of_a_tabbed_line_is_refused
#print axioms Tm.unset_of_a_tabbed_line_is_refused
#print axioms Tm.unset_of_an_absent_key_is_refused
#print axioms Tm.the_tab_guard_is_not_vacuous
#print axioms Tm.applyCmd_edit_succeeds
#print axioms Tm.applyCmd_est_succeeds
#print axioms Tm.applyCmd_unset_succeeds
#print axioms Tm.parseCmd_rejects_edit_variants
#print axioms Tm.parseCmd_reads_the_keyed_edit_forms

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3, J-route step 1: the JSON fragment's
-- foundations).  Every theorem of TmKernel/Json.lean, in declaration order.
-- Nothing here is on the wire yet -- Boundary.lean still builds Lean.Json --
-- so these audit the replacement, not the crossing.
-- ===========================================================================
#print axioms Tm.jbeq_sound
#print axioms Tm.jbeq_refl
#print axioms Tm.jbeq_iff
#print axioms Tm.jval_objects_keep_their_order
#print axioms Tm.demo_jval_is_decidable
#print axioms Tm.hexDigit_hexChar
#print axioms Tm.hexQuad_escOf
#print axioms Tm.junescape_escOf
#print axioms Tm.junescape_jescape
#print axioms Tm.demo_jescape_bytes
#print axioms Tm.demo_junescape_bytes
#print axioms Tm.the_escaping_is_not_vacuous
#print axioms Tm.the_emitted_escape_classes
#print axioms Tm.jescape_keeps_high_bytes_verbatim
#print axioms Tm.junescape_accepts_the_host_short_escapes
#print axioms Tm.the_accepted_escapes_exceed_the_emitted_ones
#print axioms Tm.junescape_refuses_a_truncated_escape
#print axioms Tm.junescape_refuses_a_truncated_hex_quad
#print axioms Tm.junescape_refuses_a_bad_hex_quad
#print axioms Tm.junescape_refuses_an_unknown_escape
#print axioms Tm.junescape_refuses_a_raw_quote
#print axioms Tm.junescape_refuses_a_raw_control
#print axioms Tm.junescape_refuses_a_lone_surrogate
#print axioms Tm.the_surrogate_guard_is_not_vacuous
#print axioms Tm.jrenderNat_is_digitsOf
#print axioms Tm.jdigits_append
#print axioms Tm.jparseNat_jrenderNat
#print axioms Tm.demo_jparseNat
#print axioms Tm.the_next_byte_guard_bites
#print axioms Tm.the_next_byte_guard_is_satisfiable
#print axioms Tm.jparseNat_refuses_a_non_numeral
#print axioms Tm.jparseNat_reads_a_bare_numeral

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3, J-route step 2: the emitter, the parser and
-- the round trip).  Every theorem TmKernel/Json.lean gained at J3-J4, in
-- declaration order: jemit, the fuel bound, the scanner, the parser's step
-- equations, jval_jemit / jparse_jemit, the fuel-sufficiency induction ending
-- in jparse_never_runs_out, and the witnesses.  Still not on the wire --
-- Boundary.lean builds Lean.Json until J5.
-- ===========================================================================
#print axioms Tm.one_le_jemitTail
#print axioms Tm.one_le_jemitOTail
#print axioms Tm.jemitTail_le_jemitArr
#print axioms Tm.jemitOTail_le_jemitObj
#print axioms Tm.jfuel_le_jemit
#print axioms Tm.skipWs_cons_of_not_ws
#print axioms Tm.jscan_cons_plain
#print axioms Tm.jscan_cons_esc
#print axioms Tm.hexChar_ne_quote_or_backslash
#print axioms Tm.jscan_escOf
#print axioms Tm.jscan_jescape
#print axioms Tm.jstring_jescape
#print axioms Tm.charDigit_cases
#print axioms Tm.charDigit_not_ws
#print axioms Tm.charDigit_ne_closers
#print axioms Tm.jemit_head
#print axioms Tm.notDigitStart_jemitTail
#print axioms Tm.notDigitStart_jemitOTail
#print axioms Tm.jval_null
#print axioms Tm.jval_true
#print axioms Tm.jval_false
#print axioms Tm.jval_string
#print axioms Tm.jval_lbracket
#print axioms Tm.jval_lbrace
#print axioms Tm.jval_digit
#print axioms Tm.jarr_empty
#print axioms Tm.jarr_value
#print axioms Tm.jarr_of_jemit
#print axioms Tm.jtail_end
#print axioms Tm.jtail_comma
#print axioms Tm.jobj_empty
#print axioms Tm.jobj_pair
#print axioms Tm.jobj_of_jemitPair
#print axioms Tm.jotail_end
#print axioms Tm.jotail_comma
#print axioms Tm.jpair_key
#print axioms Tm.jval_jemit
#print axioms Tm.jparse_jemit
#print axioms Tm.skipWs_length_le
#print axioms Tm.jscan_length
#print axioms Tm.jstring_length
#print axioms Tm.jstring_ne_outOfFuel
#print axioms Tm.jdigits_length
#print axioms Tm.jparseNat_length
#print axioms Tm.jdigits_fst_digits
#print axioms Tm.jparseNat_some_of_digit
#print axioms Tm.jval_consumes_step
#print axioms Tm.jarr_consumes_step
#print axioms Tm.jtail_consumes_step
#print axioms Tm.jobj_consumes_step
#print axioms Tm.jpair_consumes_step
#print axioms Tm.jotail_consumes_step
#print axioms Tm.jparser_consumes
#print axioms Tm.jval_fuel_step
#print axioms Tm.jarr_fuel_step
#print axioms Tm.jtail_fuel_step
#print axioms Tm.jobj_fuel_step
#print axioms Tm.jpair_fuel_step
#print axioms Tm.jotail_fuel_step
#print axioms Tm.jparser_fuel
#print axioms Tm.jparse_never_runs_out
#print axioms Tm.demo_jemit_bytes
#print axioms Tm.the_emitter_keeps_build_order
#print axioms Tm.the_emitter_is_compress_shaped
#print axioms Tm.the_json_round_trip_is_not_vacuous
#print axioms Tm.the_real_request_bytes_round_trip
#print axioms Tm.the_real_response_bytes_round_trip
#print axioms Tm.jparse_accepts_host_whitespace
#print axioms Tm.the_round_trip_survives_duplicate_keys
#print axioms Tm.jparse_refuses_a_leading_zero
#print axioms Tm.jparse_refuses_empty_input
#print axioms Tm.jparse_refuses_an_unterminated_string
#print axioms Tm.jparse_refuses_trailing_garbage
#print axioms Tm.jparse_refuses_a_bad_escape
#print axioms Tm.jparse_refuses_a_raw_control_byte
#print axioms Tm.jparse_refuses_a_trailing_comma
#print axioms Tm.jparse_refuses_an_unterminated_array
#print axioms Tm.jparse_refuses_a_missing_separator
#print axioms Tm.jparse_refuses_a_bare_key
#print axioms Tm.jparse_refuses_a_missing_colon
#print axioms Tm.jparse_refuses_an_unterminated_object
#print axioms Tm.jparse_reads_what_the_fragment_had_no_type_for
#print axioms Tm.jparseWith_refuses_when_the_fuel_runs_out
#print axioms Tm.the_jval_jemit_hypotheses_are_satisfiable
#print axioms Tm.the_jval_jemit_digit_guard_bites

-- ============================================================================
-- APPENDED 2026-09-12 (stage-3, J-route step 3: J5 -- the kernel's own JSON on
-- the wire).  Response side first: Boundary.lean builds every response as a
-- JVal and `call` emits it with `jemit` (key order is now build order).
-- `jescape_eq_jescapeTR` is the @[csimp] twin that keeps a long line off the
-- stack; the other two pin the new byte order at the builders the FFI calls.
-- ============================================================================
#print axioms Tm.jescape_eq_jescapeTR
#print axioms Tm.the_response_shapes_emit_in_build_order
#print axioms Tm.the_bad_line_diagnostic_keys_in_build_order
-- Request side (same banner, second commit): `call` reads with `jparse` and
-- every field through `jget`; no kernel module imports Lean.Data.Json.  The
-- @[csimp] twins keep a long string off the stack on the way in.
-- GOAL DISCHARGED: Goals.lean's `the_json_edge_round_trips` (stated over
-- Lean.Json, unprovable there) is renamed `the_response_call_emits_parses_back`
-- -- the round trip at the exported function -- and deleted from Goals.lean.
#print axioms Tm.junescapeTR_step
#print axioms Tm.junescapeTR_go
#print axioms Tm.junescape_eq_junescapeTR
#print axioms Tm.jscanTR_go
#print axioms Tm.jscan_eq_jscanTR
#print axioms Tm.jget_reads_the_one_pair
#print axioms Tm.jget_refuses_a_duplicate_key
#print axioms Tm.jget_ignores_a_duplicate_it_does_not_read
#print axioms Tm.parseCmd_refuses_a_duplicate_field
#print axioms Tm.run_refuses_cmds_that_are_not_an_array
#print axioms Tm.respond_names_a_parse_refusal
#print axioms Tm.the_response_call_emits_parses_back
#print axioms Tm.call_refuses_the_real_duplicate_id_request

-- ============================================================================
-- APPENDED 2026-09-12 (stage-3, step 4: a comment is prose).  An item line
-- inside <!-- --> is prose: splitDoc reads through commentAfter's state, the
-- scan skips commented lines and refuses an unterminated comment by name,
-- headings inside a comment are no sections, and placementSectionWf refuses a
-- placement inside a comment.  RENAMED (statements narrowed to lines outside a
-- comment; the unconditional forms are false of commented item lines), and
-- their old lines above removed: prose_is_never_an_item ->
-- prose_outside_a_comment_is_never_an_item; splitDoc_prose_not_item ->
-- splitDoc_prose_outside_a_comment_not_item; scanLines_prose ->
-- scanLines_prose_outside_a_comment.
-- ============================================================================
#print axioms Tm.item_lines_open_no_comment
#print axioms Tm.commentAfter_false_of_item
#print axioms Tm.ranksAscend_of_pairwise
#print axioms Tm.commentOpenFrom_cons_below
#print axioms Tm.commentOpenFrom_none_below
#print axioms Tm.prose_outside_a_comment_is_never_an_item
#print axioms Tm.prose_ranks_ascend
#print axioms Tm.splitDocC_cons
#print axioms Tm.splitDocC_prose_ge
#print axioms Tm.splitDocC_items_ge
#print axioms Tm.splitDocC_reads_comments
#print axioms Tm.splitDoc_prose_outside_a_comment_not_item
#print axioms Tm.splitDoc_items_outside_comments
#print axioms Tm.comment_free_prose_is_never_an_item
#print axioms Tm.renderSplit_splitDocC
#print axioms Tm.splitDocC_prose_strict
#print axioms Tm.splitDocC_items_strict
#print axioms Tm.splitDoc_prose_strict
#print axioms Tm.nodup_map_fst_of_strict
#print axioms Tm.splitDocC_slots_separated
#print axioms Tm.no_item_sits_in_a_comment
#print axioms Tm.an_item_in_a_comment_is_rejected
#print axioms Tm.scan_state_isSome
#print axioms Tm.scanLinesFrom_cons_ok
#print axioms Tm.scanLinesFrom_prose
#print axioms Tm.scanLines_prose_outside_a_comment
#print axioms Tm.scanLinesFrom_closes
#print axioms Tm.scanLines_accepts_only_closed_comments
#print axioms Tm.commentAt_loadCore_placement
#print axioms Tm.entityUncommented_loadEntity
#print axioms Tm.the_loader_places_no_item_in_a_comment
#print axioms Tm.a_commented_item_line_loads_as_prose
#print axioms Tm.the_commented_request_loads
#print axioms Tm.the_commented_request_round_trips
#print axioms Tm.a_commented_heading_is_no_section
#print axioms Tm.an_item_line_outside_a_comment_is_still_an_item
#print axioms Tm.an_unterminated_comment_is_refused

-- ============================================================================
-- APPENDED 2026-09-12 (stage-3, step 5: gap 40's bridges).  Line.lean's
-- parse => wf bridges (one shared readNat width bound under every date), the
-- edit table's guardWf and its no-second-grammar theorems for the eight keys
-- wired now (due at win every on-event loc waiting after), the year-9999
-- rollover where the at:/win: bridge is false, and after's plan-tier refusals
-- named danglingDep / depCycle with their success form.  Statements CHANGED in
-- place, names kept: the_edit_path_writes_what_the_field_path_reads (eight more
-- match arms), parseCmd_rejects_edit_variants (the keyNotWired witness is now
-- `demoted`), edit_of_a_tabbed_line_is_refused / applyCmd_edit_succeeds
-- (proofs only: applyCmd routes edits through nameEditFault).
-- ============================================================================
#print axioms Tm.Field.readNat_foldl_none
#print axioms Tm.Field.charDigit_lt
#print axioms Tm.Field.readNat_foldl_lt
#print axioms Tm.Field.readNat_lt_pow_length
#print axioms Tm.Field.mkDate?_some
#print axioms Tm.Field.parseDate_dayWf
#print axioms Tm.Field.parseDT_wf
#print axioms Tm.Field.parseMoment_wf
#print axioms Tm.Field.parseEnd_spec
#print axioms Tm.Field.parseInterval_spec
#print axioms Tm.Field.parseInterval_wf_unless_rollover
#print axioms Tm.Field.parseWindow_wf_unless_rollover
#print axioms Tm.Field.parseRule_wf
#print axioms Tm.Field.parseOnEvent_wf
#print axioms Tm.Field.parseDep_wf
#print axioms Tm.Field.mapOpt_all
#print axioms Tm.Field.parseDeps_wf
#print axioms Tm.Field.parseLoc_wf
#print axioms Tm.guardWf_isSome
#print axioms Tm.guardWf_none_iff
#print axioms Tm.editValOf_due_refuses_only_what_parseMoment_refuses
#print axioms Tm.editValOf_every_refuses_only_what_parseRule_refuses
#print axioms Tm.editValOf_onEvent_refuses_only_what_parseOnEvent_refuses
#print axioms Tm.editValOf_after_refuses_only_what_parseDeps_refuses
#print axioms Tm.editValOf_waiting_refuses_only_what_parseDate_refuses
#print axioms Tm.renderLoc_parseLoc
#print axioms Tm.editValOf_loc_refuses_only_a_bad_or_unworded_value
#print axioms Tm.editValOf_interval_refuses_only_a_bad_value_or_the_rollover
#print axioms Tm.editValOf_window_refuses_only_a_bad_value_or_the_rollover
#print axioms Tm.the_eight_bridged_keys_accept_their_spec_values
#print axioms Tm.the_year_9999_rollover_parses_but_the_edit_refuses_it
#print axioms Tm.wordLoc_renders_a_word
#print axioms Tm.nameEditFault_ok
#print axioms Tm.nameEditFault_ok_of
#print axioms Tm.parseCmd_refuses_the_bridged_keys_bad_values
#print axioms Tm.parseCmd_reads_the_bridged_keys
#print axioms Tm.applyCmd_edit_names_the_plan_tier_fault
#print axioms Tm.editFault_of_get
#print axioms Tm.edit_of_a_dangling_after_is_refused_by_name
#print axioms Tm.edit_of_a_cyclic_after_is_refused_by_name
#print axioms Tm.applyCmd_after_succeeds
#print axioms Tm.the_after_refusals_are_named_on_a_loaded_plan

-- APPENDED 2026-09-12 (stage-3, verification repair).  Two theorems narrowed
-- in a4ccd9c (they gained `inComment d.prose q.1 = false`) kept their old names;
-- renamed so the name matches the statement (AGENTS §7.4 item 3).  Old lines above
-- removed; statements and proofs unchanged.
#print axioms Tm.a_demoted_section_outside_a_comment_is_a_month_section
#print axioms Tm.a_pinned_section_outside_a_comment_is_a_day_section

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-4 session).  Stage 4 step 2: `close` is one fold at
-- three grains.  Close.lean (new module, imported by TmKernel.lean and by
-- Boundary.lean): the ClosePolicy table and its bridges, the fold, its
-- denotation `close_spec`, the discharged goal `close_day_stamps_a_day_stamp`,
-- the narrowed forms beside three goals left for step 3, D1 and the wall carry
-- as theorems, and the named refusals.  Boundary.lean: `endRank_is_freshRank`
-- and the loaded-plan witnesses of both directions.
-- ===========================================================================
#print axioms Tm.closeStamp_names_the_closed_grain
#print axioms Tm.closeStamp_month
#print axioms Tm.close_never_takes_a_settled_line
#print axioms Tm.closePolicy_takes_the_demoted_record_only_at_month
#print axioms Tm.closePolicy_demoted_landing_is_in_a_month_file
#print axioms Tm.closePolicy_copies_only_below_month
#print axioms Tm.closePolicy_copy_stamps
#print axioms Tm.closePolicy_move_is_unstamped
#print axioms Tm.closePolicy_exemptions
#print axioms Tm.Core.skel_stamps
#print axioms Tm.Frame.refl
#print axioms Tm.Frame.trans
#print axioms Tm.Site.shiftIn_doc
#print axioms Tm.wf_shiftIn
#print axioms Tm.skel_shiftIn
#print axioms Tm.WfPlan.mapAt_spec
#print axioms Tm.WfPlan.shiftAt_val
#print axioms Tm.frame_of_docs
#print axioms Tm.frame_shiftIn
#print axioms Tm.landAt_spec
#print axioms Tm.moveTo_skel
#print axioms Tm.moveTo_live
#print axioms Tm.fileE_skel
#print axioms Tm.closedRegionOf_frame
#print axioms Tm.closeAct_frame
#print axioms Tm.findDocIx_frame
#print axioms Tm.stepSkel_frame
#print axioms Tm.findDocIx_spec
#print axioms Tm.closeAct_of_open
#print axioms Tm.closeOne_spec
#print axioms Tm.foldlM_closeOne_spec
#print axioms Tm.closeCands_nodup
#print axioms Tm.closeAct_of_not_mem_closeCands
#print axioms Tm.close_spec
#print axioms Tm.close_skel
#print axioms Tm.exemptAct_cases
#print axioms Tm.stepSkel_of_exempt
#print axioms Tm.skelAfter_doc
#print axioms Tm.close_leaves_no_line_it_would_take
#print axioms Tm.close_leaves_no_unfinished_line_in_a_closed_region
#print axioms Tm.stepSkel_day_stamps
#print axioms Tm.close_day_stamps_a_day_stamp
#print axioms Tm.close_never_demotes_a_wall_but_may_carry_it
#print axioms Tm.close_day_files_into_the_week_of_now
#print axioms Tm.close_carries_a_wall_that_is_still_ahead
#print axioms Tm.closeOne_refuses_a_missing_target
#print axioms Tm.closeOne_refuses_a_carry_with_no_live_week
#print axioms Tm.closeOne_refuses_a_missing_section
#print axioms Tm.closeOne_refuses_an_ill_formed_post_state
#print axioms Tm.close_refuses_what_its_first_step_refuses
#print axioms Tm.close_without_candidates_is_the_identity
#print axioms Tm.foldl_max_from
#print axioms Tm.endRank_is_freshRank
#print axioms Tm.the_week_close_copies_carries_and_leaves_the_rest
#print axioms Tm.the_day_close_files_into_the_week_of_now
#print axioms Tm.the_month_close_moves_each_line_into_its_section
-- Stage 4 step 3 (same session, same banner): L16 discharged as stated in
-- Close.lean, with the skeleton half of L17 that does commute; L17 and L27
-- refuted and renamed to their negations in Boundary.lean, on loaded plans.
#print axioms Tm.closeCands_eq_nil_of_stay
#print axioms Tm.close_is_idempotent
#print axioms Tm.stepSkel_of_stay
#print axioms Tm.closeAct_of_closedRegionOf_none
#print axioms Tm.closedRegionOf_spec
#print axioms Tm.closeAct_of_another_grain
#print axioms Tm.stepSkel_lands_outside_every_closed_region
#print axioms Tm.stepSkel_comm
#print axioms Tm.close_bind_close_skel
#print axioms Tm.two_closes_at_one_instant_commute_on_skeletons
#print axioms Tm.the_close_commute_witness_loads
#print axioms Tm.the_week_then_month_close_lands_the_week_record_first
#print axioms Tm.the_month_then_week_close_lands_the_month_record_first
#print axioms Tm.close_week_month_orders_both_succeed_and_differ
#print axioms Tm.close_week_and_close_month_do_not_commute
#print axioms Tm.demote_then_readopt_succeeds_and_the_reverse_is_refused
#print axioms Tm.lifecycle_commands_do_not_commute
-- Stage 4 step 4 (same session, same banner): `autoClose` in Close.lean — L19a
-- and L19b discharged as stated, L19c's narrowing and the one-stamp theorem;
-- L19c refuted and renamed on a loaded three-month-stale plan in Boundary.lean.
#print axioms Tm.autoCloseOrder_is_the_chain
#print axioms Tm.autoCloseOrder_names_each_grain_once
#print axioms Tm.autoCloseOrder_is_coarsest_last
#print axioms Tm.autoClose_is_each_grain_once
#print axioms Tm.autoClose_ok
#print axioms Tm.autoClose_refuses_what_a_grain_refuses
#print axioms Tm.autoClose_refuses_a_refused_day_close
#print axioms Tm.close_keeps_nothing_to_close
#print axioms Tm.autoClose_leaves_nothing_to_close
#print axioms Tm.autoClose_catches_up_in_one_step
#print axioms Tm.autoClose_strands_no_unfinished_line
#print axioms Tm.close_skel_after
#print axioms Tm.autoClose_skel
#print axioms Tm.stepSkel_three_is_one
#print axioms Tm.autoClose_takes_each_line_at_most_once
#print axioms Tm.the_stale_witness_loads
#print axioms Tm.mem_closedLiveIds
#print axioms Tm.the_stale_catch_up_observed
#print axioms Tm.staleCaughtUp_map
#print axioms Tm.the_stale_tree_catches_up_in_one_call
#print axioms Tm.the_stale_ledger_before_catch_up
#print axioms Tm.the_stale_ledger_after_catch_up
#print axioms Tm.the_stale_tree_catches_up_losing_nothing
#print axioms Tm.the_stale_catch_up_leaves_only_settled_and_recurring_lines
#print axioms Tm.autoClose_leaves_lines_in_periods_it_passes
#print axioms Tm.the_stale_catch_up_refusals_are_named
-- Stage 4 step 5 (same session, same banner): what a close reports — the new
-- module Report.lean (D3's named per-item list, `closeR`/`autoCloseR`, and the
-- kind lemmas that widen L22 to the close commands); `now` and `blockMin` on
-- the wire, the close ops, and the report under `ok` in Boundary.lean.
#print axioms Tm.BlockMin.ofNat?_zero
#print axioms Tm.BlockMin.ofNat?_pos
#print axioms Tm.CloseDid.ofName?_name
#print axioms Tm.CloseDid.ofName?_refuses
#print axioms Tm.closeR_plan
#print axioms Tm.foldlM_closeStepR_plan
#print axioms Tm.autoCloseR_plan
#print axioms Tm.filterMap_ids
#print axioms Tm.closeReport_ids
#print axioms Tm.mem_closeReport
#print axioms Tm.close_found_the_target
#print axioms Tm.closeReport_stamp_names_its_grain
#print axioms Tm.autoCloseR_ok
#print axioms Tm.mem_closeCands
#print axioms Tm.not_mem_closeCands_of_stay
#print axioms Tm.close_takes_a_line_out_of_every_close
#print axioms Tm.close_keeps_a_line_untaken
#print axioms Tm.autoCloseR_names_each_line_at_most_once
#print axioms Tm.closeAct_carry_is_a_wall
#print axioms Tm.closedRegionOf_of_closeAct
#print axioms Tm.stepSkel_doc_kinds
#print axioms Tm.except_map_pair_fst
#print axioms Tm.applyCmdR_plan
#print axioms Tm.applyAllR_plan
#print axioms Tm.the_clock_reads_now_and_blockMin
#print axioms Tm.the_clock_refuses_a_malformed_value_by_name
#print axioms Tm.parseCmdAt_reads_the_close_ops_and_refuses_without_the_clock
#print axioms Tm.parseCmdAt_is_parseCmd
#print axioms Tm.run_names_the_clock_refusals
#print axioms Tm.runPlan_refusal_carries_no_report
#print axioms Tm.the_week_close_reports_each_line
#print axioms Tm.the_day_close_reports_each_line
#print axioms Tm.the_month_close_reports_each_line
#print axioms Tm.a_close_entry_emits_in_build_order
-- Stage 4 step 6 (same session, same banner): the three goals stated stronger
-- than §6.3 — L18 at plan level, F4 and B1–B3 — refuted and renamed on the loaded
-- week witness in Boundary.lean; the estimate half of narrowed B1–B3 in
-- Close.lean, on `remainingOf_setDemoted` in Line.lean.
#print axioms Tm.hasEst_setEst
#print axioms Tm.Field.viewRemaining_words
#print axioms Tm.Field.readNat_none_of_mem
#print axioms Tm.Field.unitValue_none_of_mem
#print axioms Tm.Field.neutral_of_mem
#print axioms Tm.Field.neutral_keyWord_demoted
#print axioms Tm.Field.neutral_of_demoted_tok
#print axioms Tm.Field.neutral_of_id_word
#print axioms Tm.Field.leadWords_append_neutral
#print axioms Tm.Field.remainingWords_append_neutral
#print axioms Tm.Field.setKeyIn_split
#print axioms Tm.Field.insertBeforeId_split
#print axioms Tm.Field.remainingOf_setDemoted
#print axioms Tm.the_close_week_witness_loads
#print axioms Tm.the_week_close_leaves_r1_and_t1_in_the_closed_week
#print axioms Tm.the_week_close_carries_the_wall_x1_to_another_file
#print axioms Tm.the_week_close_stamps_m2_and_writes_no_estimate
#print axioms Tm.mem_closedLiveIdsOfGrain
#print axioms Tm.close_leaves_live_lines_in_a_closed_region
#print axioms Tm.close_does_not_leave_every_wall_as_it_was
#print axioms Tm.close_writes_a_line_demoteEst_does_not
-- ===================================================================
-- APPENDED 2026-09-13 (stage-4 session, rebuild-on-lean).  Step 8: gap 59 —
-- closeCands in source order, and close_keeps_source_order (Close.lean), with
-- its sightings on loaded plans (Boundary.lean).  Gap 20's demote verb: see README.
-- ===================================================================
#print axioms Tm.siteLe_iff
#print axioms Tm.siteLe_total
#print axioms Tm.siteLe_trans
#print axioms Tm.insertBySite_perm
#print axioms Tm.sortBySite_perm
#print axioms Tm.insertBySite_sorted
#print axioms Tm.sortBySite_sorted
#print axioms Tm.closeCands_perm
#print axioms Tm.closeCands_sorted
#print axioms Tm.mem_closeCands_iff
#print axioms Tm.shiftRank_lt_iff
#print axioms Tm.rankBump_lt_iff
#print axioms Tm.shiftRank_min
#print axioms Tm.Site.bump_doc
#print axioms Tm.Site.bump_rank_of_doc
#print axioms Tm.Site.bump_of_ne
#print axioms Tm.Site.bump_none
#print axioms Tm.Site.bump_lt
#print axioms Tm.inComment_shiftFrom
#print axioms Tm.liveHeading_shiftFrom
#print axioms Tm.firstHeadingAbove_eq
#print axioms Tm.loOk_shift
#print axioms Tm.foldl_fhaStep_shift
#print axioms Tm.firstHeadingAbove_bump
#print axioms Tm.landingSpot_bump
#print axioms Tm.landingSpot_src
#print axioms Tm.le_foldl_max_nat
#print axioms Tm.live_rank_lt_endRank
#print axioms Tm.docs_shiftIn_getElem?
#print axioms Tm.landAt_moves
#print axioms Tm.closeAct_closed
#print axioms Tm.closeOne_moves
#print axioms Tm.carryTarget_frame
#print axioms Tm.closeTarget_frame
#print axioms Tm.landingSpot_docs
#print axioms Tm.sectionAt_docs
#print axioms Tm.get_of_map_eq_some
#print axioms Tm.closeOne_keeps_untaken
#print axioms Tm.fold_keeps_order_both
#print axioms Tm.closeAct_skel_frame
#print axioms Tm.fold_keeps_order_after_first
#print axioms Tm.fold_keeps_order
#print axioms Tm.sublist_pair_or
#print axioms Tm.close_keeps_source_order
#print axioms Tm.close_keeps_source_order_iff
#print axioms Tm.the_week_close_keeps_source_order_in_demoted
#print axioms Tm.the_month_close_keeps_source_order_in_its_section
#print axioms Tm.the_day_close_keeps_source_order_at_the_end_of_the_week
#print axioms Tm.the_month_close_orders_lines_by_the_destination_sections
#print axioms Tm.the_week_close_reports_in_source_order
-- ===================================================================
-- APPENDED 2026-09-13 (stage-4 session, rebuild-on-lean).  Step 9: gap 20's
-- remainder — the `demote` verb files into `# Demoted` through the close's
-- landing (Boundary.lean).
-- ===================================================================
#print axioms Tm.demoteSpot_is_the_week_close_landing
#print axioms Tm.the_demote_verb_files_into_demoted_ahead_of_the_next_section
#print axioms Tm.the_demote_verb_lands_at_the_end_of_a_month_without_demoted
-- ===================================================================
-- APPENDED 2026-09-13 (stage-4 hardening).  Step 1: README gap 62 — the fast
-- checker behind the same interface.  Every `@[csimp]` equality below lets the
-- compiler run a twin in place of a definition the proofs are about; the
-- lemmas beside them are what the equalities rest on.  No relational law.
-- ===================================================================
-- Fast.lean: `planWf`'s hot conjuncts, the store's table, the response's buckets
#print axioms Tm.render_keys
#print axioms Tm.lines_keys
#print axioms Tm.proseKeys_at
#print axioms Tm.ranksIn_keys
#print axioms Tm.docRanks_keys
#print axioms Tm.docRanks_eq_docRanksFast
#print axioms Tm.nodup_pairs_iff
#print axioms Tm.normalized_iff_keys
#print axioms Tm.keyLe_trans
#print axioms Tm.keyLe_total
#print axioms Tm.keyLt_trans
#print axioms Tm.strictAsc_iff
#print axioms Tm.strictAsc_iff_nodup
#print axioms Tm.normalized_eq_normalizedFast
#print axioms Tm.IdMap.size_empty
#print axioms Tm.IdMap.size_insert
#print axioms Tm.IdMap.slot_insert
#print axioms Tm.IdMap.get_empty
#print axioms Tm.IdMap.get_insert
#print axioms Tm.Store.ext_of
#print axioms Tm.compactStep_fold
#print axioms Tm.Store.compact_eq
#print axioms Tm.Store.set_eq_setFast
#print axioms Tm.pathsFresh_iff
#print axioms Tm.pathsDistinct_eq_pathsDistinctFast
#print axioms Tm.parentsAcyclic_eq_parentsAcyclicFast
#print axioms Tm.sitesInRange_eq_sitesInRangeFast
#print axioms Tm.foldl_commentAfter_false
#print axioms Tm.inComment_of_clean
#print axioms Tm.docFacts_live
#print axioms Tm.docFacts_heads
#print axioms Tm.foldl_if_and_filter
#print axioms Tm.lastHeadingBefore_facts
#print axioms Tm.all_if_filter
#print axioms Tm.headingsWfF_docFacts
#print axioms Tm.docFacts_kind
#print axioms Tm.docFacts_doc
#print axioms Tm.facts_get
#print axioms Tm.kindAtF_eq
#print axioms Tm.placementSectionWfF_eq
#print axioms Tm.sectionsWf_eq_sectionsWfFast
#print axioms Tm.shapesWf_eq_shapesWfFast
#print axioms Tm.itemsWf_eq_itemsWfFast
#print axioms Tm.planWf_eq_planWfFast
#print axioms Tm.firstItemFault_eq_firstItemFaultFast
#print axioms Tm.bucketByDoc_get
#print axioms Tm.linesByDoc_get
-- Close.lean: a shifted store is compacted
#print axioms Tm.Store.mapEntities_eq_mapEntitiesFast
-- Boundary.lean: the loader's grouping, dedup and store; the response renders once
#print axioms Tm.dedupStep_eq
#print axioms Tm.dedupStep_fold
#print axioms Tm.dedupIds_eq_dedupIdsFast
#print axioms Tm.groupStep_fold
#print axioms Tm.foldlM_snoc_eq_mapM
#print axioms Tm.buildEntities_eq_buildEntitiesFast
#print axioms Tm.loadStep_eq
#print axioms Tm.loadStep_fold
#print axioms Tm.loadStore_eq_loadStoreFast
#print axioms Tm.renderDocAt_eq_renderDocFrom
#print axioms Tm.runPlan_eq_runPlanFast
-- Step 2 (2026-09-13): README gap 53 — a week close (and the `demote` verb)
-- merges a line into its item's standing `# Demoted` record instead of refusing
-- `alreadyDemoted`: fork-point `demote_one`'s merge, with L15's floor.  Eight
-- names above were retired with the statements they carried (the README's step-2
-- block lists each beside its replacement); their replacements are here.
-- Cmd.lean: the merge, the stamps, the estimate through `demoteEst`
#print axioms Tm.refile_roundtrips
#print axioms Tm.refile_of_no_record
#print axioms Tm.refile_twice_is_not_a_thing
#print axioms Tm.refile_refuses_only_a_record
#print axioms Tm.foldl_stampStep_mem
#print axioms Tm.foldl_stampStep_nodup
#print axioms Tm.foldl_stampStep_of_nodup
#print axioms Tm.mergeStamps_of_nodup
#print axioms Tm.mergeStamps_spec
#print axioms Tm.unitValue_isSome
#print axioms Tm.estKeyTok_of_hasEst
#print axioms Tm.remainingOf_of_not_ownsEstimate
#print axioms Tm.carryEst_reads_as_demoteEst
#print axioms Tm.refile_conserves
#print axioms Tm.refile_respects_user
-- Close.lean: the restated laws, the refusal gone, the merge
#print axioms Tm.mapAt_error
#print axioms Tm.landAt_error
#print axioms Tm.landingSpot_error
#print axioms Tm.fileE_alreadyDemoted
#print axioms Tm.autoClose_stamps_each_line_with_no_record_at_most_once
-- Report.lean: the named disposition `copyMerging`
#print axioms Tm.CloseDid.ofStep_ne_carry
#print axioms Tm.skelAfter_stamps_of_not_merging
#print axioms Tm.skelAfter_stamps_merging
-- Boundary.lean: the verb, the loaded-plan witnesses, three refutations
#print axioms Tm.WfPlan.mapAt_congr
#print axioms Tm.demote_verb_is_cmdDemote_at_freshRank_without_a_shift_or_a_record
#print axioms Tm.the_week_close_merges_each_standing_record
#print axioms Tm.the_week_close_reports_each_merge
#print axioms Tm.the_demote_verb_merges_into_a_standing_record
#print axioms Tm.the_close_merge_witness_loads
#print axioms Tm.the_week_close_floors_m5_at_its_record
#print axioms Tm.autoClose_merges_m2s_stamps
#print axioms Tm.a_merged_record_is_rewritten_beyond_its_stamp
#print axioms Tm.a_merged_record_changes_a_remaining_estimate
#print axioms Tm.autoClose_merges_a_line_beyond_one_appended_stamp
-- Step 3 (2026-09-13): repair of steps 1-2 after an independent verification.
-- A week close (and the `demote` verb) refuses, `alreadyDemoted`, an item whose
-- tombstone is not its `# Demoted` record instead of merging into it and deleting
-- a `[-]` line from a closed week; two names narrowed in place at step 2 and two
-- names that said more than their statements are retired and restated; the merge
-- laws' hypotheses are instantiated together.  Six names above were retired (the
-- README's step-3 block lists each beside its replacement); no relational law.
-- Close.lean: the guard, where a close answers `alreadyDemoted`, the renames
#print axioms Tm.guardStray_ok
#print axioms Tm.guardStray_error
#print axioms Tm.guardStray_of_error
#print axioms Tm.guardStray_false
#print axioms Tm.closeOne_refuses_alreadyDemoted_only_over_a_stray_tomb
#print axioms Tm.closeOne_never_refuses_alreadyDemoted_without_a_stray_tomb
#print axioms Tm.closeOne_never_merges_into_a_stray_tomb
#print axioms Tm.close_answers_alreadyDemoted_only_at_a_copying_row
#print axioms Tm.stepSkel_appends_at_most_one_stamp_or_merges
#print axioms Tm.autoClose_appends_at_most_one_stamp_or_merges_each_line
-- Report.lean: the report's agreement, under a name that matches its stamp clause
#print axioms Tm.closeReport_agrees_with_close_stamping_or_merging
-- Boundary.lean: the refusals by name, the stray tombstone at both entry points,
-- three refutations, the merge laws not vacuous
#print axioms Tm.the_pre_close_pair_closes_on_a_loaded_plan
#print axioms Tm.the_pre_close_pair_is_not_a_named_refusal
#print axioms Tm.the_stray_tomb_witness_loads
#print axioms Tm.a_stray_tomb_refuses_the_week_close
#print axioms Tm.a_stray_tomb_refuses_autoClose
#print axioms Tm.the_demote_verb_refuses_a_stray_tomb
#print axioms Tm.the_week_close_merges_m2s_stamps_and_reports_one
#print axioms Tm.mergeHypsAt_spec
#print axioms Tm.the_merge_hypotheses_hold_together
#print axioms Tm.refile_merge_laws_are_not_vacuous
#print axioms Tm.a_close_can_refuse_alreadyDemoted
#print axioms Tm.closeReport_agrees_with_close_is_refuted_by_a_merge
-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final).  Step 2: README gap 55 closed — the owner's
-- D7 (a past-due `persist` line at a week close moves to `backlog.md # Overdue`,
-- box, bytes and tombstone kept) and D8 (a `# Demoted` record may carry a date;
-- the month rule reads outcomes only).  Five names above were retired with the
-- statements they carried and restated here (README "Stage 4 final", step 2):
-- `month_items_are_outcomes` -> `month_items_outside_demoted_are_undated` (old
-- statement refuted: `a_dated_demoted_record_is_a_month_item_with_a_date`);
-- `closePolicy_owes` -> `closePolicy_owes_only_the_child_fold` beside
-- `closePolicy_routes_overdue_only_at_week`; `closeAct_of_exempt` ->
-- `closeAct_never_files_an_exempt_line`; `closeReport_names_the_region_of_now` ->
-- `closeReport_names_the_destination_of_now`;
-- `each_close_refusal_is_named_on_a_loaded_plan` ->
-- `the_close_refusals_left_after_d7_are_named_on_loaded_plans` (old statement
-- refuted: `a_dated_line_no_longer_refuses_the_week_close_as_badHorizon`).  The
-- two-run laws this breaks are re-proved in place under their own names (D5):
-- `close_is_idempotent`, `close_keeps_source_order`(`_iff`) through
-- `closeOne_moves`/`fold_keeps_order`(`_after_first`), the L19 `autoClose_*`
-- theorems, `closeReport_agrees_with_close_stamping_or_merging` and
-- `move_has_no_inverse_command`; their audit lines above stand.
-- Plan.lean / Fast.lean: D8's narrowing and its csimp twin
#print axioms Tm.shapeWf_or_record_of_mem
#print axioms Tm.month_items_outside_demoted_are_undated
#print axioms Tm.a_dated_month_outcome_is_rejected
#print axioms Tm.secKindAtF_eq
#print axioms Tm.demotedRecordPlacementF_eq
-- Close.lean: the table's new column, the fourth action, the laws
#print axioms Tm.closePolicy_routes_overdue_only_at_week
#print axioms Tm.Core.skel_onMiss
#print axioms Tm.Skel.overdue_of_wallAhead
#print axioms Tm.overdueTarget_frame
#print axioms Tm.overdueTarget_spec
#print axioms Tm.closeAct_of_regionless
#print axioms Tm.closeAct_never_files_an_exempt_line
#print axioms Tm.spot_bound_after_step
#print axioms Tm.rank_lt_landing
#print axioms Tm.landed_rank_lt_next_spot
#print axioms Tm.Field.lookup_filterMap_cons_congr
#print axioms Tm.Field.isKeyTok_of_keyOf_ne
#print axioms Tm.Field.lookup_setKeyIn_other
#print axioms Tm.Field.lookup_insertBeforeId_other
#print axioms Tm.Field.lookupKey_setKey_other
#print axioms Tm.Field.isEstKey_keyOf
#print axioms Tm.Field.viewShape_congr
#print axioms Tm.lookupKey_carryEst_other
#print axioms Tm.viewShape_refiledLine
#print axioms Tm.refiledLine_stamps_mem
#print axioms Tm.Core.skel_overdue_iff
#print axioms Tm.kindOfGrain_is_never_backlog
#print axioms Tm.pairwise_of_ranksAscend
#print axioms Tm.prose_eq_of_rank
#print axioms Tm.foldl_congr_mem
#print axioms Tm.lastHeadingBefore_shiftFrom
#print axioms Tm.lastHeadingBefore_eq_foldl
#print axioms Tm.foldl_lhbStep_some
#print axioms Tm.foldl_lhbStep_ne_none
#print axioms Tm.lastHeadingBefore_eq_of_max
#print axioms Tm.foldl_fhaStep_some
#print axioms Tm.foldl_fhaStep_none
#print axioms Tm.prose_rank_lt_endRank
#print axioms Tm.landingSpot_overdue_is_under_overdue
#print axioms Tm.closeOne_lands_an_overdue_line_under_overdue
#print axioms Tm.fold_keeps_an_overdue_line_under_overdue
#print axioms Tm.fold_lands_an_overdue_line_under_overdue
#print axioms Tm.close_lands_every_overdue_line_under_overdue
#print axioms Tm.close_moves_a_past_due_persist_line_to_the_backlog
#print axioms Tm.Skel.overdue_of_not_yet_due
#print axioms Tm.close_week_moves_a_past_due_persist_line_to_the_backlog
-- Report.lean: the sixth disposition
#print axioms Tm.CloseDid.ofStep_ne_moveOverdue
#print axioms Tm.CloseDid.ofName?_refuses_near_overdue
#print axioms Tm.closeAct_overdue_iff
-- Boundary.lean: the refusals left, the loaded witnesses, two refutations
#print axioms Tm.the_close_refusals_left_after_d7_are_named_on_loaded_plans
#print axioms Tm.a_dated_line_no_longer_refuses_the_week_close_as_badHorizon
#print axioms Tm.the_week_close_routes_dated_work_on_a_loaded_plan
#print axioms Tm.the_week_close_reports_the_overdue_route
#print axioms Tm.the_close_overdue_witness_loads
#print axioms Tm.the_dated_route_hypotheses_hold_on_a_loaded_plan
#print axioms Tm.a_dated_record_loads_and_a_dated_outcome_does_not
#print axioms Tm.a_dated_demoted_record_is_a_month_item_with_a_date
#print axioms Tm.the_example_week_closes_with_d1_in_the_backlog_overdue
-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final).  Step 3: README gap 22 closed — the owner's
-- D6.  `Core.parent` is a view of the line (`Field.parentRef`), not a stored slot;
-- a dangling `@parent` refuses the whole tree `itemCheck: danglingParent`, a cycle
-- `itemCheck: parentCycle`; §3.2's prep rule, `effectiveCi` inheritance and
-- `rootPrio` fire on loaded plans.  No name retired.  Kept names whose statements
-- changed, recorded (README "Stage 4 final", step 3): `the_fields_are_the_line`
-- (gains `c.parent = d.parent`), `wf_ignores_the_item_fields` (the `parent :=`
-- binder is gone with the slot), `the_kernel_can_read_the_pairs_it_writes` (its
-- `parent = none` hypothesis is gone — strictly stronger),
-- `the_pre_close_pair_closes_on_a_loaded_plan` (gains `loadsOk … = true`: without
-- it the statement held of a request that no longer loads), and
-- `closePolicy_owes_only_the_child_fold` (the column's constructor renamed
-- `gap22Parent` -> `childFoldB3`).  Four close witnesses gained the outcome their
-- lines name (`specMonthDoc`, `closePreClosePairWitness`, `closeStrayTombWitness`,
-- `closeMergeWitness`); every theorem over them is re-decided under its own name,
-- and their audit lines above stand.  No two-run theorem's statement or proof
-- changed: L16, source order, L19, the report agreement, `move_has_no_inverse_command`
-- and the commute refutations build unchanged against the derived field.
-- State.lean / Plan.lean: the view, and `parentsTotal` both ways
#print axioms Tm.coreOfLine_parent
#print axioms Tm.parentsTotal_iff
-- State.lean: `parentRef` skips a line with no `@` word (a new csimp twin, D6's cost)
#print axioms Tm.Field.kParent_classifyWord
#print axioms Tm.Field.findSome_kParent_phase3
#print axioms Tm.Field.findSome_kParent_phase2
#print axioms Tm.Field.findSome_kParent_phase1
#print axioms Tm.Field.parentRef_of_no_at
#print axioms Tm.Field.parentRef_eq_parentRefFast
-- Fast.lean: one parent table per check, shared by the two parent conjuncts
-- (`parentsAcyclic_eq_parentsAcyclicFast`, `itemsWf_eq_itemsWfFast` and
-- `firstItemFault_eq_firstItemFaultFast` keep their names and audit lines above;
-- their twins now read the table, so their proofs are no longer `rfl`)
#print axioms Tm.tableStep_fold
#print axioms Tm.parentStep_of_not_mem
#print axioms Tm.parentTable_get
#print axioms Tm.anc_eq_ancIn
#print axioms Tm.parentsAcyclicIn_eq
#print axioms Tm.parentsTotalIn_eq
-- Boundary.lean: the refusals by name, the loads, and the derived fields firing
#print axioms Tm.loadPlan_itemCheck
#print axioms Tm.loadPlan_refuses_a_dangling_parent
#print axioms Tm.loadPlan_refuses_a_parent_cycle
#print axioms Tm.the_parent_tree_loads
#print axioms Tm.the_example_tree_loads_with_its_parents
#print axioms Tm.the_typo_tree_fails_parentsTotal_only
#print axioms Tm.the_cycle_tree_fails_parentsAcyclic_only
#print axioms Tm.a_typod_parent_refuses_the_whole_tree_by_name
#print axioms Tm.a_parent_cycle_refuses_the_whole_tree_by_name
#print axioms Tm.the_prep_rule_fires_on_a_loaded_plan
#print axioms Tm.effectiveCi_inherits_on_a_loaded_plan
#print axioms Tm.rootPrio_reads_the_root_on_a_loaded_plan
-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final).  Step 4: goal B3, the week row's child fold
-- — refuted and renamed, with §6.4's `max` law beside it; stage 4's goal count is
-- zero.  `close g now` gains the block length (`close g now bm`, `autoClose now
-- bm`); an unfinished child of a line the week close files from the same file is
-- dropped `[~]` in place and its own remaining floors that line's record (fork-point
-- `horizon::demote_est`'s `folded`).  Twelve names above were retired with the
-- statements they carried and restated here (README "Stage 4 final, step 4"), each
-- old statement refuted on the loaded fold witness where it is not a helper:
-- `closePolicy_owes_only_the_child_fold` -> `closePolicy_drops_children_only_at_week`
-- (+ `closePolicy_drops_children_only_at_a_copying_row`);
-- `stepSkel_line_is_stamped_or_merged` -> `stepSkel_line_is_stamped_merged_or_folded`;
-- `close_rewrites_a_line_only_by_stamping_or_merging_it` ->
-- `close_rewrites_a_line_only_by_stamping_merging_or_folding_it` (refuted:
-- `a_folded_record_is_rewritten_beyond_its_stamp`);
-- `close_rewrites_a_line_with_no_record_only_by_stamping_it` ->
-- `close_rewrites_a_line_with_no_record_only_by_stamping_or_folding_it` and
-- `close_rewrites_a_line_with_no_record_and_nothing_folded_only_by_stamping_it`
-- (refuted: `a_folded_line_with_no_record_is_rewritten_beyond_its_stamp`);
-- `close_reads_every_remaining_estimate_through_demoteEst` ->
-- `close_reads_every_remaining_estimate_through_demoteEst_and_the_fold` (refuted:
-- `a_folded_record_changes_a_remaining_estimate`);
-- `close_keeps_the_remaining_estimate_of_a_line_with_no_record` ->
-- `close_keeps_the_remaining_estimate_of_a_line_with_no_record_and_nothing_folded`
-- (refuted: `a_folded_line_with_no_record_changes_its_remaining_estimate`);
-- `close_files_a_taken_line_into_closeTo` ->
-- `close_files_a_taken_line_it_does_not_drop_into_closeTo` (refuted:
-- `a_dropped_child_is_not_filed_into_closeTo`);
-- `close_week_merges_a_standing_record` ->
-- `close_week_merges_a_standing_record_it_does_not_drop` (refuted:
-- `a_dropped_child_keeps_its_record_unmerged`), and its `_is_not_vacuous`;
-- `close_week_files_a_dated_line_keeping_its_date` ->
-- `close_week_files_a_dated_line_it_does_not_drop_keeping_its_date` (refuted:
-- `a_dropped_dated_child_is_not_filed_as_a_record`);
-- `close_week_demotes_a_not_yet_due_line_keeping_its_date` ->
-- `close_week_demotes_a_not_yet_due_line_it_does_not_drop_keeping_its_date`
-- (refuted: `a_not_yet_due_child_is_dropped_with_its_parent`);
-- `closeReport_names_the_destination_of_now` -> `closeReport_names_each_lines_destination`
-- (refuted: `a_dropped_child_is_reported_where_it_stays`).
-- The goal: `close_week_folds_a_dropped_child_into_its_parent` (Goals.lean, deleted)
-- -> `close_week_does_not_add_a_dropped_child_to_its_parent`.
-- The two-run laws this breaks are re-proved under their own names (D5), their
-- audit lines above standing: `close_is_idempotent` (L16; a `[~]` child is settled),
-- `close_keeps_source_order`(`_iff`) (the same action now includes the fold's drop:
-- `hfold`; the unextended form refuted as `a_dropped_child_and_its_filed_parent_part_ways`),
-- the L19 theorems (`autoClose_*`, through `stepSkel_leaves_nothing_a_close_takes` and
-- `close_keeps_foldFxOf_of_another_grain`), `closeReport_agrees_with_close_stamping_or_merging`
-- (three new dispositions), `two_closes_at_one_instant_commute_on_skeletons`,
-- `close_week_and_close_month_do_not_commute`, `move_has_no_inverse_command`, `close_spec`.
-- Cmd.lean: the fold's estimate, through `demoteEst`, and `refileX`
#print axioms Tm.find_setEstInTo
#print axioms Tm.foldEst_of_le
#print axioms Tm.foldEst_of_lt
#print axioms Tm.foldEst_reads_as_demoteEst
#print axioms Tm.foldEst_zero
#print axioms Tm.refiledLineX_none
#print axioms Tm.refiledLineX_of_apply
#print axioms Tm.refileX_none
#print axioms Tm.refileX_refuses_only_a_record
#print axioms Tm.refileX_roundtrips
#print axioms Tm.remainingOf_foldEst
#print axioms Tm.unitValue_digits_b
#print axioms Tm.unitValue_digits_h
#print axioms Tm.unitValue_digits_m
#print axioms Tm.unitValue_foldDur
#print axioms Tm.viewRemaining_setEstTo
-- Close.lean: the column, the fold, its laws, and the re-proofs' new lemmas
#print axioms Tm.children_of_not_copy
#print axioms Tm.closeAct_of_settled
#print axioms Tm.closeAct_of_takes_false
#print axioms Tm.close_dom
#print axioms Tm.close_files_a_taken_line_it_does_not_drop_into_closeTo
#print axioms Tm.close_keeps_foldFxOf_of_another_grain
#print axioms Tm.close_keeps_skel_of_another_grain
#print axioms Tm.close_keeps_the_remaining_estimate_of_a_line_with_no_record_and_nothing_folded
#print axioms Tm.closeOne_dom
#print axioms Tm.closePolicy_children_cases
#print axioms Tm.closePolicy_drops_children_only_at_a_copying_row
#print axioms Tm.closePolicy_drops_children_only_at_week
#print axioms Tm.close_reads_every_remaining_estimate_through_demoteEst_and_the_fold
#print axioms Tm.close_rewrites_a_line_only_by_stamping_merging_or_folding_it
#print axioms Tm.close_rewrites_a_line_with_no_record_and_nothing_folded_only_by_stamping_it
#print axioms Tm.close_rewrites_a_line_with_no_record_only_by_stamping_or_folding_it
#print axioms Tm.close_week_demotes_a_not_yet_due_line_it_does_not_drop_keeping_its_date
#print axioms Tm.close_week_drops_a_child_with_its_parent
#print axioms Tm.close_week_files_a_dated_line_it_does_not_drop_keeping_its_date
#print axioms Tm.close_week_folds_dropped_children_by_max
#print axioms Tm.close_week_keeps_a_dropped_childs_remaining_in_its_parents_record
#print axioms Tm.close_week_keeps_a_parent_that_covers_its_dropped_children
#print axioms Tm.close_week_lifts_a_parent_its_dropped_children_outweigh
#print axioms Tm.close_week_merges_a_standing_record_it_does_not_drop
#print axioms Tm.demoteEst_reads_zero
#print axioms Tm.dropE_skel
#print axioms Tm.dropsInto_congr
#print axioms Tm.dropsInto_of_asAnyLine
#print axioms Tm.dropsInto_spec
#print axioms Tm.filesLine_iff
#print axioms Tm.foldedMinutes_of_asAnyLine
#print axioms Tm.foldedMinutes_of_dropped
#print axioms Tm.foldFxOf_apply
#print axioms Tm.foldFxOf_congr
#print axioms Tm.foldFxOf_isDrop
#print axioms Tm.foldFxOf_of_asAnyLine
#print axioms Tm.fold_keeps_order_of_drop
#print axioms Tm.foldParent_congr
#print axioms Tm.foldParent_of_asAnyLine
#print axioms Tm.foldParent_spec
#print axioms Tm.foldTab_congr
#print axioms Tm.foldTab_of_asAnyLine
#print axioms Tm.foldTabSum_of_not_has
#print axioms Tm.foldParent_eq_foldParentFast
#print axioms Tm.foldTab_eq_foldTabFast
#print axioms Tm.foldTabSum_step
#print axioms Tm.foldUp_congr
#print axioms Tm.foldUp_spec
#print axioms Tm.landAt_dom
#print axioms Tm.le_foldTabSum
#print axioms Tm.lookupKey_apply_other
#print axioms Tm.Field.lookupKey_setEstTo_other
#print axioms Tm.Field.lookup_setEstInTo_other
#print axioms Tm.mem_foldTab
#print axioms Tm.ownMinutes_le_foldedMinutes
#print axioms Tm.refiledLineX_stamps_mem
#print axioms Tm.remainingOf_carriedLine
#print axioms Tm.skelAfter_week
#print axioms Tm.SkelKept.filesLine_eq
#print axioms Tm.SkelKept.get_none
#print axioms Tm.SkelKept.skel_of_files
#print axioms Tm.stepSkel_congr_fx
#print axioms Tm.stepSkel_leaves_nothing_a_close_takes
#print axioms Tm.stepSkel_line_is_stamped_merged_or_folded
#print axioms Tm.stepSkel_of_drop
#print axioms Tm.stepSkel_of_file
#print axioms Tm.viewShape_refiledLineX
#print axioms Tm.WfPlan.mapAt_dom
-- Report.lean: the three new dispositions, and where each line is
#print axioms Tm.CloseDid.ofName?_refuses_near_fold
#print axioms Tm.CloseDid.ofStep_folding_iff
#print axioms Tm.CloseDid.ofStep_merging_iff
#print axioms Tm.CloseDid.ofStep_ne_dropIntoParent
#print axioms Tm.closeReport_names_each_lines_destination
#print axioms Tm.foldFxOf_isLift_not_drop
#print axioms Tm.foldFxOf_isLift_week
-- Boundary.lean: the loaded fold witness, the refutations, non-vacuity
#print axioms Tm.a_dropped_child_and_its_filed_parent_part_ways
#print axioms Tm.a_dropped_child_is_not_filed_into_closeTo
#print axioms Tm.a_dropped_child_is_reported_where_it_stays
#print axioms Tm.a_dropped_child_keeps_its_record_unmerged
#print axioms Tm.a_dropped_dated_child_is_not_filed_as_a_record
#print axioms Tm.a_folded_line_with_no_record_changes_its_remaining_estimate
#print axioms Tm.a_folded_line_with_no_record_is_rewritten_beyond_its_stamp
#print axioms Tm.a_folded_record_changes_a_remaining_estimate
#print axioms Tm.a_folded_record_is_rewritten_beyond_its_stamp
#print axioms Tm.a_not_yet_due_child_is_dropped_with_its_parent
#print axioms Tm.archive_none_of_toNat
#print axioms Tm.beforeAfterFoldClose_some
#print axioms Tm.c5_dated_facts
#print axioms Tm.closeAct_file_facts
#print axioms Tm.close_week_does_not_add_a_dropped_child_to_its_parent
#print axioms Tm.close_week_drops_a_child_with_its_parent_is_not_vacuous
#print axioms Tm.close_week_folds_dropped_children_by_max_is_not_vacuous
#print axioms Tm.close_week_merges_a_standing_record_it_does_not_drop_is_not_vacuous
#print axioms Tm.fold_facts
#print axioms Tm.foldFacts_eq
#print axioms Tm.the_close_fold_witness_loads
#print axioms Tm.the_fold_facts_on_the_loaded_witness
#print axioms Tm.the_fold_on_the_loaded_witness
#print axioms Tm.the_fold_witness_links_and_dates
#print axioms Tm.the_merge_witness_drops_neither_record
#print axioms Tm.the_dated_witness_drops_nothing
#print axioms Tm.the_week_close_folds_dropped_children_on_a_loaded_plan
#print axioms Tm.the_week_close_reports_the_fold
#print axioms Tm.toNat_eq_one
#print axioms Tm.toNat_eq_zero

-- APPENDED 2026-09-13 (stage-4 final).  Repair: two defects of step 4 an independent
-- verification found (kernel/README.md "Stage 4 final, repair").  Defect 2: the mixed
-- pair — one line the fold drops, one it files, from one file by one action — gets the
-- order law `close_keeps_source_order` (whose `hfold` it falls outside) cannot state,
-- over the sites both leave in the source file; `close_keeps_source_order` and `_iff`
-- are unchanged.  Defect 3: the stage-one reader `unitValue` reads `NhMm`
-- (`hmValue`), so an `NhMm` child is folded at its minutes; `unitValue_estWord`,
-- `unitValue_isSome` and `Field.unitValue_none_of_mem` keep their statements, their
-- proofs re-run over the new branch.
#print axioms Tm.Entity.bumpIn_live
#print axioms Tm.Entity.bumpIn_archiveSite
#print axioms Tm.landAt_get
#print axioms Tm.closeOne_get_others
#print axioms Tm.fold_keeps_a_closed_site
#print axioms Tm.fold_keeps_a_dropped_line_in_place
#print axioms Tm.fold_leaves_a_copied_lines_tombstone_where_it_stood
#print axioms Tm.mem_closeCands_of_ne_stay
#print axioms Tm.files_of_isDrop
#print axioms Tm.close_leaves_a_dropped_line_where_it_stood
#print axioms Tm.close_leaves_a_copied_lines_tombstone_where_it_stood
#print axioms Tm.close_keeps_source_order_across_the_fold
#print axioms Tm.close_keeps_source_order_across_the_fold_is_not_vacuous
#print axioms Tm.the_mixed_pair_keeps_its_order_on_the_loaded_witness
#print axioms Tm.Field.hmValue_none_of_mem
#print axioms Tm.Field.unitValue_renderDur
#print axioms Tm.the_week_close_folds_an_hours_and_minutes_child

-- APPENDED 2026-09-14 (stage 5).  Step 1: §6.4's `remaining` and §5.4's series head
-- (kernel/README.md "Stage 5 step 1").  `Tree.lean` (new, imported after `Plan`):
-- `remainingMin` is fork-point `Tree::remaining` with structural fuel, proved to be
-- the one fixed point of its step on a well-formed plan; `seriesHead` is
-- `Tree::series_head` per document.  Goals discharged as stated:
-- `the_series_head_is_not_settled`, `the_series_head_ranks_first`.  Goals refuted as
-- written, the law that holds beside each: `remaining_is_the_est_key_when_set`,
-- `remaining_falls_back_to_the_leading_estimate`, `remaining_sums_the_children`
-- (`Boundary.lean`, on a loaded plan).  Gap 18 closed; gap 73 buildable, not rewired.
#print axioms Tm.viewFields_estLead
#print axioms Tm.ownRemaining_of_estKey
#print axioms Tm.ownRemaining_of_lead
#print axioms Tm.ownRemaining_of_dur
#print axioms Tm.ownRemaining_none
#print axioms Tm.parentStep_of_mem_childrenOf
#print axioms Tm.optAdd_getD
#print axioms Tm.remainingStep_congr
#print axioms Tm.remainingStep_missing
#print axioms Tm.remainingStep_settled
#print axioms Tm.remainingStep_own
#print axioms Tm.remainingStep_children
#print axioms Tm.anc_succ_bind
#print axioms Tm.anc_fuel_none
#print axioms Tm.WfPlan.acyclic
#print axioms Tm.anc_ne_of_child
#print axioms Tm.remainingAux_stable
#print axioms Tm.remainingAux_fuel_is_enough
#print axioms Tm.remainingOpt_step
#print axioms Tm.remainingOpt_is_the_unique_fixed_point
#print axioms Tm.foldl_optAdd_getD
#print axioms Tm.remaining_of_a_settled_item_is_zero
#print axioms Tm.remaining_of_a_missing_id_is_zero
#print axioms Tm.remaining_is_the_est_key_when_set_and_unsettled
#print axioms Tm.remaining_falls_back_to_the_leading_estimate_when_unsettled
#print axioms Tm.remaining_falls_back_to_dur_when_unsettled
#print axioms Tm.remaining_sums_the_children_when_unsettled_with_no_dur
#print axioms Tm.firstByRank_mem
#print axioms Tm.firstByRank_isSome_cons
#print axioms Tm.firstByRank_le
#print axioms Tm.firstByRank_eq_none
#print axioms Tm.mem_seriesOpen
#print axioms Tm.seriesHead_spec
#print axioms Tm.the_series_head_is_not_settled
#print axioms Tm.the_series_head_ranks_first
#print axioms Tm.seriesHead_isSome_of_an_unsettled_member
#print axioms Tm.seriesHead_none_when_every_member_is_settled
#print axioms Tm.the_tree_witness_loads
#print axioms Tm.remaining_reads_the_est_key_over_the_leading_estimate_on_a_loaded_plan
#print axioms Tm.remaining_reads_the_leading_estimate_on_a_loaded_plan
#print axioms Tm.remaining_sums_two_children_on_a_loaded_plan
#print axioms Tm.remaining_reads_dur_on_a_loaded_plan
#print axioms Tm.remaining_of_a_settled_line_is_zero_on_a_loaded_plan
#print axioms Tm.remaining_is_none_without_an_estimate_on_a_loaded_plan
#print axioms Tm.the_series_head_skips_a_settled_member_on_a_loaded_plan
#print axioms Tm.remaining_is_not_the_est_key_on_a_settled_line
#print axioms Tm.remaining_does_not_fall_back_to_the_leading_estimate_on_a_settled_line
#print axioms Tm.remaining_does_not_sum_the_children_over_a_dur

-- APPENDED 2026-09-14 (stage 5).  Step 2: §7.1's priority, §7.2's rule table and §7.4's
-- hysteresis (kernel/README.md "Stage 5 step 2").  `Priority.lean` (new, imported after
-- `Tree`): `prio` is `priority::clamp_p` over Arith's bin and `rootK` is
-- `Tree::root_priority`; the ladder takes a rational availability by
-- cross-multiplication (D10); `hysteresis` is `priority::apply_hysteresis`.  Goals
-- discharged as stated: `prio_of_hot_is_zero`, `prio_is_clamped`,
-- `prio_is_antitone_in_utilisation`, `hysteresis_improves_by_at_most_one_bin`,
-- `hysteresis_worsens_freely`, `hysteresis_never_delays_hot`.  Gap 27's loader check
-- has its smart constructor (`binsOf?`); the loader call waits for the config wiring.
#print axioms Tm.defaultPrioOf?_refuses_zero
#print axioms Tm.defaultPrioOf?_refuses_above_four
#print axioms Tm.defaultPrioOf?_accepts
#print axioms Tm.specDefaultPrio_is_three
#print axioms Tm.rootK_pos
#print axioms Tm.rootK_le_four
#print axioms Tm.rootK_of_a_root_with_k
#print axioms Tm.rootK_of_a_root_without_k
#print axioms Tm.prio_plus
#print axioms Tm.prio_of_hot_is_zero
#print axioms Tm.prio_is_clamped
#print axioms Tm.prio_mono_ix
#print axioms Tm.prio_is_antitone_in_utilisation
#print axioms Tm.prio_eq_zero_iff_hot
#print axioms Tm.prio_clamp_is_silent_on_the_default_ladder
#print axioms Tm.prio_clamp_fires_on_a_long_ladder
#print axioms Tm.utilQGe_cross
#print axioms Tm.utilQGe_eq_le
#print axioms Tm.utilQGe_is_division
#print axioms Tm.utilQGe_on_whole_minutes
#print axioms Tm.cross_transfer
#print axioms Tm.utilQGe_congr
#print axioms Tm.utilGe_scaled_pair_congr
#print axioms Tm.rungs_eq_of_utilGe_eq
#print axioms Tm.binOfQ_ix
#print axioms Tm.binOfScaledQ_ix
#print axioms Tm.binOfQ_on_whole_minutes
#print axioms Tm.utilScaledQGe_on_whole_minutes
#print axioms Tm.binOfScaledQ_on_whole_minutes
#print axioms Tm.utilScaledQGe_is_division
#print axioms Tm.binOfQ_congr
#print axioms Tm.binOfScaledQ_congr
#print axioms Tm.binOfQ_capacity_zero
#print axioms Tm.binOfScaledQ_capacity_zero
#print axioms Tm.zero_need_on_zero_capacity_is_hot
#print axioms Tm.binOfQ_anti_avail
#print axioms Tm.prio_is_antitone_in_rational_utilisation
#print axioms Tm.flooring_the_mixture_changes_the_bin
#print axioms Tm.Bins.ladder_eq_rungs
#print axioms Tm.binsOf?_isSome_iff
#print axioms Tm.binsOf?_val
#print axioms Tm.binsOf?_accepts_the_default
#print axioms Tm.binsOf?_refuses_unsorted_edges
#print axioms Tm.binsOf?_refuses_an_edge_above_hot
#print axioms Tm.binsOf?_refuses_an_infinite_edge
#print axioms Tm.binsOfPairs?_refuses_a_zero_denominator
#print axioms Tm.the_spec_decimals_are_the_default_ladder
#print axioms Tm.a_misconfigured_ladder_is_antitone_but_not_the_ladder
#print axioms Tm.safetyOf?_refuses_zero
#print axioms Tm.safetyOf?_refuses_a_zero_denominator
#print axioms Tm.safetyOf?_reads_the_spec
#print axioms Tm.hysteresis_cases
#print axioms Tm.hysteresis_improves_by_at_most_one_bin
#print axioms Tm.hysteresis_worsens_freely
#print axioms Tm.hysteresis_never_delays_hot
#print axioms Tm.hysteresis_never_raises_urgency
#print axioms Tm.hysteresis_holds_one_step_back
#print axioms Tm.hysteresis_le_max
#print axioms Tm.yesterdayOf?_refuses_eight
#print axioms Tm.yesterdayOf?_accepts
#print axioms Tm.applyHysteresis_without_yesterday
#print axioms Tm.applyHysteresis_disabled
#print axioms Tm.applyHysteresis_enabled
#print axioms Tm.applyHysteresis_zero
#print axioms Tm.applyHysteresis_cases
#print axioms Tm.hysteresisDays_closed_form
#print axioms Tm.hysteresis_settles_on_a_steady_priority
#print axioms Tm.hysteresis_holds_every_day_of_the_gap
#print axioms Tm.hysteresisDays_of_hot
#print axioms Tm.rawPrio_of_a_wall
#print axioms Tm.rawPrio_of_an_optional
#print axioms Tm.rawPrio_of_overdue
#print axioms Tm.rawPrio_of_a_mandatory_instance
#print axioms Tm.rawPrio_of_the_hot_flag
#print axioms Tm.rawPrio_of_a_pass
#print axioms Tm.rawPrio_of_pure_rank
#print axioms Tm.rawPrio_is_clamped
#print axioms Tm.rowOf_eq_wall_iff
#print axioms Tm.rawPrio_isNone_iff
#print axioms Tm.finalPrio_of_a_wall
#print axioms Tm.finalPrio_of_an_optional
#print axioms Tm.finalPrio_damps
#print axioms Tm.finalPrio_never_delays_zero
#print axioms Tm.finalPrio_is_clamped
#print axioms Tm.finalPrio_improves_by_at_most_one_step
#print axioms Tm.prio_reads_the_root_priority_on_a_loaded_plan
#print axioms Tm.a_root_without_k_takes_the_default_on_a_loaded_plan
#print axioms Tm.hot_is_zero_whatever_the_root_on_a_loaded_plan
#print axioms Tm.the_rule_table_ranks_a_loaded_plan

-- APPENDED 2026-09-14 (stage 5).  Step 3: §7.3's EDF reservation pass over given capacities
-- (kernel/README.md "Stage 5 step 3").  `Capacity.lean` (new, imported after `Priority`):
-- D10's exact minutes as numerators over one positive denominator; `reserveRest` is
-- `capacity::reserve` (earliest day first, highest matching level first, the ci filter),
-- `availUntil` is `capacity::available_until`, and `edf` / `edfGrants` are
-- `priority::compute`'s EDF loop over a stable due-ascending order.  Goals discharged, each
-- restated over rational minutes as D10 forces: `edf_keeps_the_days`,
-- `edf_only_spends_capacity`, `edf_reserves_only_before_the_deadline`.  Two-run laws proved
-- (D5): `edf_more_capacity_never_raises_a_shortfall`,
-- `edf_more_capacity_leaves_more_capacity`,
-- `edf_a_later_deadline_takes_nothing_from_an_earlier_one`.
#print axioms Tm.denOf?_refuses_zero
#print axioms Tm.denOf?_accepts
#print axioms Tm.levelOf?_refuses_six_and_above
#print axioms Tm.levelOf?_accepts
#print axioms Tm.minutesAt_le_iff
#print axioms Tm.minutesAt_eq_iff
#print axioms Tm.minutesAt_one
#print axioms Tm.stepLevel_val
#print axioms Tm.stepLevel_five_sub
#print axioms Tm.dayLeft_succ
#print axioms Tm.stepTake_le_left
#print axioms Tm.dayRest_eq_sub_take
#print axioms Tm.dayTake_eq_stepTake
#print axioms Tm.dayTake_le
#print axioms Tm.dayRest_le
#print axioms Tm.dayRest_below_ci
#print axioms Tm.dayLeft_eq_sub
#print axioms Tm.dayOut_eq
#print axioms Tm.dayOut_le
#print axioms Tm.topElig_mono_n
#print axioms Tm.topElig_mono_f
#print axioms Tm.eligAt_mono
#print axioms Tm.topElig_at
#print axioms Tm.topElig_at_le_eligAt
#print axioms Tm.topTake_add_dayLeft
#print axioms Tm.sum6_dayTake
#print axioms Tm.day_conserves
#print axioms Tm.day_gives_the_min
#print axioms Tm.dayRest_zero
#print axioms Tm.dayRest_drained
#print axioms Tm.dayRest_drained_of_dayOut_pos
#print axioms Tm.dayRest_drains_higher_levels
#print axioms Tm.dayRest_mono
#print axioms Tm.dayOut_mono
#print axioms Tm.reserveOut_eq
#print axioms Tm.reserveOut_le
#print axioms Tm.reserve_gives_the_min
#print axioms Tm.reserve_conserves
#print axioms Tm.reserveRest_zero
#print axioms Tm.reserving_the_clamped_request_is_the_same
#print axioms Tm.reserveRest_spent
#print axioms Tm.reserveRest_drains_earlier_days
#print axioms Tm.availUntil_mono
#print axioms Tm.reserveRest_mono
#print axioms Tm.reserveOut_anti
#print axioms Tm.perm_insertDue
#print axioms Tm.sortDue_perm
#print axioms Tm.mem_sortDue
#print axioms Tm.sorted_insertDue
#print axioms Tm.sortDue_sorted
#print axioms Tm.filter_due_insertDue
#print axioms Tm.sortDue_is_stable
#print axioms Tm.insertDue_append_last
#print axioms Tm.sortDue_append_last
#print axioms Tm.edfGrantsGo_deadlines
#print axioms Tm.edfGrants_deadlines
#print axioms Tm.edfGrants_length
#print axioms Tm.edf_serves_an_earlier_deadline_first
#print axioms Tm.edf_a_later_deadline_takes_nothing_from_an_earlier_one
#print axioms Tm.forall₂_refl
#print axioms Tm.forall₂_trans
#print axioms Tm.forall₂_length
#print axioms Tm.forall₂_getElem?
#print axioms Tm.edfCaps_spent
#print axioms Tm.edf_keeps_the_days
#print axioms Tm.edf_keeps_the_dates
#print axioms Tm.edf_only_spends_numerators
#print axioms Tm.edf_only_spends_capacity
#print axioms Tm.edf_reserves_only_before_the_deadline
#print axioms Tm.edf_spares_levels_below_every_ci
#print axioms Tm.edfCaps_conserves
#print axioms Tm.edf_spends_exactly_what_it_reserves
#print axioms Tm.Grant.hot_iff
#print axioms Tm.Grant.impossible_imp_hot
#print axioms Tm.grantOf_reserved
#print axioms Tm.edfGrantsGo_exact
#print axioms Tm.edf_reserves_the_min
#print axioms Tm.edf_reserves_no_more_than_the_need
#print axioms Tm.edf_reserves_no_more_than_was_available
#print axioms Tm.edf_reports_the_shortfall
#print axioms Tm.edf_shortfall_is_need_minus_avail
#print axioms Tm.edf_impossible_iff_shortfall
#print axioms Tm.edfCaps_mono
#print axioms Tm.edfGrantsGo_mono
#print axioms Tm.edf_more_capacity_leaves_more_capacity
#print axioms Tm.edf_more_capacity_never_raises_a_shortfall
#print axioms Tm.lookaheadOf?_refuses_a_zero_denominator
#print axioms Tm.lookaheadOf?_refuses_unsorted_days
#print axioms Tm.lookaheadOf?_accepts
#print axioms Tm.daysAscending_pairwise
#print axioms Tm.reserve_takes_the_best_levels_earliest
#print axioms Tm.edf_serves_the_earlier_deadline_first_on_a_witness
#print axioms Tm.edf_spends_before_the_deadline_and_not_after_on_a_witness
#print axioms Tm.flooring_the_capacity_changes_the_verdict
#print axioms Tm.the_ci_filter_on_a_witness
#print axioms Tm.sortDue_keeps_ties_in_input_order_on_a_witness
#print axioms Tm.lookaheadOf?_on_witnesses
#print axioms Tm.edf_five_deadlines_over_three_days
#print axioms Tm.edf_serves_a_loaded_plans_needs_earliest_deadline_first

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L1: D10's exact mixture
-- (kernel/README.md "Stage 5 D10 L1").  `Lookahead.lean` (new, imported after `Capacity`):
-- `capDen = 10^18` (D17), the weight decoder `mkWeight?` with its three named refusals,
-- `mix` (lounge and home weighed after each budget limit), `limitHist`, the threshold twin,
-- and the scaling laws that make `capDen` unobservable.  In-step (design §13.2); no goal
-- entered or left `Goals.lean`.  Two-run laws proved (D5): `edf_commutes_with_scaling`,
-- `edfGrants_commute_with_scaling`.
#print axioms Tm.Look.capDen_eq_pow
#print axioms Tm.Look.capDen_pos
#print axioms Tm.Look.mkWeight?_zero_den
#print axioms Tm.Look.mkWeight?_above_one
#print axioms Tm.Look.mkWeight?_precision
#print axioms Tm.Look.mkWeight?_refuses_more_than_18_places
#print axioms Tm.Look.mkWeight?_accepts
#print axioms Tm.Look.mkWeight?_ok_elim
#print axioms Tm.Look.mkWeight?_denotes
#print axioms Tm.Look.mkWeight?_accepted_width
#print axioms Tm.Look.mkWeight?_complement
#print axioms Tm.Look.mkWeight?_round2
#print axioms Tm.Look.mix_between_the_locations
#print axioms Tm.Look.mix_at_zero_is_home
#print axioms Tm.Look.mix_at_one_is_lounge
#print axioms Tm.Look.mixDay_at_a_certain_weight
#print axioms Tm.Look.mix_denotes_the_weighted_sum
#print axioms Tm.Look.mixDay_minutesAt_is_the_expectation
#print axioms Tm.Look.mix_width
#print axioms Tm.Look.topElig_lin
#print axioms Tm.Look.eligAt_mix
#print axioms Tm.Look.mix_atLeast_between_the_locations
#print axioms Tm.Look.limitHist_keeps_the_min
#print axioms Tm.Look.dayTake_scale
#print axioms Tm.Look.dayRest_scale
#print axioms Tm.Look.dayOut_scale
#print axioms Tm.Look.mixing_before_the_budget_agrees_at_a_certain_weight
#print axioms Tm.Look.mixing_before_the_budget_is_not_the_expectation
#print axioms Tm.Look.mixing_before_the_budget_on_the_witness
#print axioms Tm.Look.twin_is_the_forks_location
#print axioms Tm.Look.twin_is_the_forks_threshold
#print axioms Tm.Look.the_bin_does_not_see_capDen
#print axioms Tm.Look.availUntil_scale
#print axioms Tm.Look.reserveRest_scale
#print axioms Tm.Look.reserveOut_scale
#print axioms Tm.Look.edfCaps_scale
#print axioms Tm.Look.edfGrantsGo_scale
#print axioms Tm.Look.edf_commutes_with_scaling
#print axioms Tm.Look.edfGrants_commute_with_scaling
#print axioms Tm.Look.a_scaled_grant_keeps_its_verdicts
#print axioms Tm.Look.mkWeight?_on_witnesses
#print axioms Tm.Look.mix_on_a_witness

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step A1 (design §14.1): gap 44 closed.
-- The per-element recursions of the codec and splitDoc run as proved @[csimp]
-- accumulator twins (rule D9-21).  Json.lean: the emitter twin, then the parser twin;
-- Plan.lean: splitDoc's twin.  22 theorems.
#print axioms Tm.jemitRev_eq
#print axioms Tm.jemitTailAcc_go_eq
#print axioms Tm.jemitArrAcc_go_eq
#print axioms Tm.jemitOTailAcc_go_eq
#print axioms Tm.jemitPairAcc_go_eq
#print axioms Tm.jemitObjAcc_go_eq
#print axioms Tm.jemit_eq_jemitAcc
#print axioms Tm.jemitArr_eq_jemitArrAcc
#print axioms Tm.jemitTail_eq_jemitTailAcc
#print axioms Tm.jemitObj_eq_jemitObjAcc
#print axioms Tm.jemitPair_eq_jemitPairAcc
#print axioms Tm.jemitOTail_eq_jemitOTailAcc
#print axioms Tm.jparserAcc
#print axioms Tm.jval_eq_jvalAcc
#print axioms Tm.jarr_eq_jarrAcc
#print axioms Tm.jtail_eq_jtailAcc
#print axioms Tm.jobj_eq_jobjAcc
#print axioms Tm.jpair_eq_jpairAcc
#print axioms Tm.jotail_eq_jotailAcc
#print axioms Tm.splitDocCAcc_go
#print axioms Tm.splitDocC_eq_splitDocCAcc
#print axioms Tm.splitDoc_eq_splitDocAcc

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step A2 (design §14.1, §5.1): JSON gains an
-- exact decimal (`JVal.dec`), gaps 42 (surrogate pairs) and 43 (leading zeros) read as serde
-- reads, `jparse_jemit` re-proved unconditionally.  Json.lean, then Boundary.lean.  42 theorems;
-- two stage-3 lines above were renamed in place to their refutations
-- (`jparse_accepts_leading_zeros` -> `jparse_refuses_a_leading_zero`,
-- `jparse_refuses_what_the_fragment_has_no_type_for` -> `jparse_reads_what_the_fragment_had_no_type_for`).
#print axioms Tm.junescape_reads_a_surrogate_pair
#print axioms Tm.digitFin_finChar
#print axioms Tm.digitFin_of_not_digit
#print axioms Tm.finChar_is_digit
#print axioms Tm.jfinsTR_go
#print axioms Tm.jfins_eq_jfinsTR
#print axioms Tm.jdigitsTR_go
#print axioms Tm.jdigits_eq_jdigitsTR
#print axioms Tm.jfins_append
#print axioms Tm.notDigitStart_of_numEnd
#print axioms Tm.JDec.renderU_ne_nil
#print axioms Tm.digitsOf_zero_head
#print axioms Tm.jleadingZero_digitsOf
#print axioms Tm.numEnd_jemitTail
#print axioms Tm.numEnd_jemitOTail
#print axioms Tm.jval_minus
#print axioms Tm.notDigitStart_renderExp
#print axioms Tm.notDigitStart_renderFrac
#print axioms Tm.jexpAfter_digit
#print axioms Tm.jexp_renderExp
#print axioms Tm.jfrac_renderFrac
#print axioms Tm.jreadDec_renderU
#print axioms Tm.jval_render
#print axioms Tm.JVal.ofDec_plain
#print axioms Tm.JVal.ofDec_dec
#print axioms Tm.jemit_num_is_render
#print axioms Tm.jdigits_split
#print axioms Tm.jfins_length
#print axioms Tm.jparseNat_consumes
#print axioms Tm.jfrac_length
#print axioms Tm.jexpDigits_length
#print axioms Tm.jexp_length
#print axioms Tm.jreadDec_length
#print axioms Tm.jnumber_length
#print axioms Tm.jnumber_ne_outOfFuel
#print axioms Tm.jparse_reads_a_plain_numeral_as_num
#print axioms Tm.jparse_reads_a_signed_decimal_as_dec
#print axioms Tm.jparse_reads_an_exponent_as_written
#print axioms Tm.jparse_refuses_a_numeral_missing_a_digit
#print axioms Tm.the_jval_jemit_fraction_guard_bites
#print axioms Tm.a_request_number_that_is_not_a_nat_is_refused_by_its_reader
#print axioms Tm.respond_reads_a_decimal_and_a_surrogate_pair

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step B1 (design §14.2, §5.2, §6.1 kernel side, §6.3):
-- instants, offsets and chrono's leap-second durations; the zone as a host-probed table
-- (`offsetAt`, `localDate`); `instantOf`, the fork's `local_dt`.  Cal.lean.  64 theorems,
-- including the two in-step goals of design §15 (`offsetAt_reads_the_last_transition`, restated
-- in chrono's order, and `instantOf_is_local_dt_on_an_unambiguous_time`).
#print axioms Tm.Cal.Instant.lt_iff
#print axioms Tm.Cal.Instant.le_iff
#print axioms Tm.Cal.Instant.lt_irrefl
#print axioms Tm.Cal.Instant.lt_trans
#print axioms Tm.Cal.Instant.not_lt
#print axioms Tm.Cal.Instant.le_total
#print axioms Tm.Cal.Instant.le_antisymm
#print axioms Tm.Cal.the_instant_order_is_not_the_nanos_order
#print axioms Tm.Cal.Instant.lt_iff_nanos_off_a_leap_second
#print axioms Tm.Cal.localSecAt_utcSecAt
#print axioms Tm.Cal.utcSecAt_localSecAt
#print axioms Tm.Cal.minutesBetween_is_num_minutes_max_zero
#print axioms Tm.Cal.subMinutes_zero
#print axioms Tm.Cal.subMinutes_nanos
#print axioms Tm.Cal.subMinutes_wf
#print axioms Tm.Cal.durationBetween_across_a_leap_second
#print axioms Tm.Cal.the_leap_second_counts_within_a_day_but_not_across_midnight
#print axioms Tm.Cal.minutesBetween_truncates
#print axioms Tm.Cal.secondsBetween_truncates_toward_zero
#print axioms Tm.Cal.durationBetween_total
#print axioms Tm.Cal.minutesBetween_zero_of_le
#print axioms Tm.Cal.mkInstant?_isSome_iff
#print axioms Tm.Cal.mkInstant?_refuses_a_bad_nanosecond
#print axioms Tm.Cal.mkOffset?_isSome_iff
#print axioms Tm.Cal.mkOffset?_refuses_a_whole_day
#print axioms Tm.Cal.the_written_clock_is_not_the_instant_order
#print axioms Tm.Cal.the_origin_second_is_not_unambiguous
#print axioms Tm.Cal.transFrom_mem
#print axioms Tm.Cal.transFrom_tail
#print axioms Tm.Cal.Tz.transFrom
#print axioms Tm.Cal.Tz.trans_ns
#print axioms Tm.Cal.tz_transitions_strictly_increase
#print axioms Tm.Cal.mkTz?_isSome_iff
#print axioms Tm.Cal.mkTz?_refuses_a_long_key
#print axioms Tm.Cal.mkTz?_refuses_too_many_transitions
#print axioms Tm.Cal.mkTz?_refuses_an_unsorted_table
#print axioms Tm.Cal.offsetFold_none
#print axioms Tm.Cal.offsetFold_last
#print axioms Tm.Cal.offsetAt_reads_the_last_transition
#print axioms Tm.Cal.offsetAt_before_every_transition
#print axioms Tm.Cal.offsetAt_at_a_transition
#print axioms Tm.Cal.offsetAt_does_not_read_the_last_transition_by_nanos
#print axioms Tm.Cal.offsetAt_wf
#print axioms Tm.Cal.localDate_near_the_utc_date
#print axioms Tm.Cal.foldl_offsetStep_congr
#print axioms Tm.Cal.offsetAt_is_constant_between_transitions
#print axioms Tm.Cal.localDate_mono_between_transitions
#print axioms Tm.Cal.pushHit_reverse
#print axioms Tm.Cal.hitFold
#print axioms Tm.Cal.localHits_eq
#print axioms Tm.Cal.spansFrom_lo
#print axioms Tm.Cal.offsetFold_span
#print axioms Tm.Cal.exists_span
#print axioms Tm.Cal.localSec_of_mem_localHits
#print axioms Tm.Cal.mem_localHits_of_localSec
#print axioms Tm.Cal.localSec_instantOf
#print axioms Tm.Cal.instantOf_is_local_dt_on_an_unambiguous_time
#print axioms Tm.Cal.chicago2026_wf
#print axioms Tm.Cal.the_witness_seconds_are_the_dates_they_name
#print axioms Tm.Cal.chicago_2026_offsets
#print axioms Tm.Cal.localDate_is_not_constant_between_transitions
#print axioms Tm.Cal.instantOf_in_the_spring_gap
#print axioms Tm.Cal.instantOf_in_the_fall_fold
#print axioms Tm.Cal.instantOf_on_an_unambiguous_noon

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L2 (design §13.3, §14.8 row L2): the day's
-- window, E7, in real seconds; the two STAGE 6 E7 goals discharged in Lookahead.lean
-- (restated to overlap semantics and refuted as written), and the plan's walls.
#print axioms Tm.Look.wallOverlap_eq_countIn
#print axioms Tm.Look.countIn_of_le
#print axioms Tm.Look.countIn_succ
#print axioms Tm.Look.countIn_congr
#print axioms Tm.Look.countIn_or
#print axioms Tm.Look.countIn_wall
#print axioms Tm.Look.countIn_zero
#print axioms Tm.Look.covered_cons
#print axioms Tm.Look.covered_eq_true
#print axioms Tm.Look.countIn_covered_nil
#print axioms Tm.Look.WallChain.tail
#print axioms Tm.Look.extend_ge
#print axioms Tm.Look.extendStep_pos
#print axioms Tm.Look.extendStep_neg
#print axioms Tm.Look.countIn_covered_cons
#print axioms Tm.Look.extend_least
#print axioms Tm.Look.extend_solves
#print axioms Tm.Look.mergeStep_spec
#print axioms Tm.Look.foldl_mergeStep_spec
#print axioms Tm.Look.covered_reverse
#print axioms Tm.Look.mergeSorted_spec
#print axioms Tm.Look.insertByStart_perm
#print axioms Tm.Look.insertByStart_sorted
#print axioms Tm.Look.sortByStart_perm
#print axioms Tm.Look.sortByStart_sorted
#print axioms Tm.Look.mergeSort_start_sorted
#print axioms Tm.Look.clipWalls_mem
#print axioms Tm.Look.covered_clipWalls
#print axioms Tm.Look.covered_perm
#print axioms Tm.Look.walk_is_the_least_solution
#print axioms Tm.Look.the_window_end_solves_the_equation
#print axioms Tm.Look.windowEnd_le_of_prefixpoint
#print axioms Tm.Look.the_window_end_is_the_least_solution
#print axioms Tm.Look.windowEnd_eq_windowEndFast
#print axioms Tm.Look.windowBase_le_windowEnd
#print axioms Tm.Look.arrival_le_windowEnd
#print axioms Tm.Look.windowEnd_without_walls
#print axioms Tm.Look.the_window_end_is_not_the_least_solution_over_walls_wholly_inside
#print axioms Tm.Look.the_window_end_is_not_the_least_solution_as_stage_6_wrote_it
#print axioms Tm.Look.the_window_base_is_clamped_to_the_arrival
#print axioms Tm.Look.a_wall_begun_before_the_arrival_extends_the_window
#print axioms Tm.Look.the_window_end_does_not_solve_the_equation_as_stage_6_wrote_it
#print axioms Tm.Look.overlapping_walls_count_once
#print axioms Tm.Look.budgetOf_denotes
#print axioms Tm.Look.window_and_budget_on_witnesses
#print axioms Tm.Look.instantOf_ns
#print axioms Tm.Look.windowOn_solves_E7
#print axioms Tm.Look.the_witness_days_are_the_dates_they_name
#print axioms Tm.Look.budget_of_an_eight_hour_window
#print axioms Tm.Look.walls_extend_the_window
#print axioms Tm.Look.the_cap_bounds_the_window
#print axioms Tm.Look.wall_extension_reaches_a_fixed_point
#print axioms Tm.Look.the_window_counts_real_hours_across_the_spring_transition
#print axioms Tm.Look.shiftBack_zero
#print axioms Tm.Look.mem_wallsOn
#print axioms Tm.Look.mem_wallIndex
#print axioms Tm.Look.wallOfEntity_settled
#print axioms Tm.Look.wallOfEntity_interval
#print axioms Tm.Look.the_buffer_is_taken_off_the_local_clock
#print axioms Tm.Look.a_multi_day_wall_puts_one_evening_in_two_windows
