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
#print axioms Tm.a_demoted_section_is_a_month_section
#print axioms Tm.a_pinned_section_is_a_day_section
#print axioms Tm.a_day_file_holds_only_pinned_items
#print axioms Tm.month_items_are_outcomes
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
#print axioms Tm.jparse_accepts_leading_zeros
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
#print axioms Tm.jparse_refuses_what_the_fragment_has_no_type_for
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
