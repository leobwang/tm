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
#print axioms Tm.a_routine_line_need_not_carry_the_open_flag
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
#print axioms Tm.spec_line_is_an_item
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

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L3 (design §13.3, §14.8 row L3): the slot cut,
-- fork `free_intervals` and `cut_slots_around`, in whole seconds, pulled from stage 6 under D12;
-- the four `cutSlots_*` laws of the step row in-step, and the fork's tests as witnesses.
#print axioms Tm.Look.insertByStart_append
#print axioms Tm.Look.sortByStart_eq_mergeSort
#print axioms Tm.Look.sortByStart_eq_sortByStartFast
#print axioms Tm.Look.clipTo_mem
#print axioms Tm.Look.covered_clipTo
#print axioms Tm.Look.freeChain_spec
#print axioms Tm.Look.freeFold_spec
#print axioms Tm.Look.mem_ite_cons
#print axioms Tm.Look.freeIntervals_spec
#print axioms Tm.Look.freeIntervals_inside_the_window
#print axioms Tm.Look.freeIntervals_are_in_order
#print axioms Tm.Look.freeIntervals_are_the_free_units
#print axioms Tm.Look.cutStretch_fuel
#print axioms Tm.Look.cutSlots_fuel_is_enough
#print axioms Tm.Look.cutStretch_rec
#print axioms Tm.Look.minLast_pos
#print axioms Tm.Look.AccInv.mono
#print axioms Tm.Look.AccInv.nil
#print axioms Tm.Look.cutStretch_spec
#print axioms Tm.Look.cutFold_spec
#print axioms Tm.Look.cutSlots_spec
#print axioms Tm.Look.cutSlots_without_a_block_length_is_empty
#print axioms Tm.Look.cutSlots_inside_the_window
#print axioms Tm.Look.cutSlots_breaks_inside_the_window
#print axioms Tm.Look.cutSlots_avoid_the_walls
#print axioms Tm.Look.cutSlots_breaks_avoid_the_walls
#print axioms Tm.Look.cutSlots_block_is_block_min
#print axioms Tm.Look.cutSlots_short_block_is_at_least_min_last
#print axioms Tm.Look.cutSlots_break_is_break_min
#print axioms Tm.Look.cutSlots_slots_are_in_order
#print axioms Tm.Look.cutSlots_breaks_are_in_order
#print axioms Tm.Look.cutSlots_no_slot_overlaps_a_break
#print axioms Tm.Look.every_break_is_followed_by_a_slot
#print axioms Tm.Look.cut_slots_on_the_spec_day
#print axioms Tm.Look.a_routine_passed_as_a_wall_does_not_pay_off_the_break
#print axioms Tm.Look.cut_slots_around_a_placed_routine
#print axioms Tm.Look.cut_slots_from_a_pending_break
#print axioms Tm.Look.a_cut_never_ends_on_a_break
#print axioms Tm.Look.a_long_wall_leaves_eight_hours_to_cut
#print axioms Tm.Look.a_late_arrival_cuts_nothing
#print axioms Tm.Look.free_intervals_merge_overlapping_walls
#print axioms Tm.Look.a_cut_counts_real_minutes_across_the_fall_transition

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L4 (design §13.3, §14.8 row L4): energy and the
-- budget limit, fork `hours_since_wake`/`bucket`/`StepFn::at`/`prior_energy`/`prior_level`/`predict`/
-- `cap_for_location`/`energize`/`limit_to_budget`, pulled from stage 6 under D12; site R11, the four
-- goals of the step row in-step (`limitSlots_is_limitHist` equal to L1's `limitHist`), and the fork's
-- tests as witnesses.
#print axioms Tm.Look.hsw100_is_round_half_away
#print axioms Tm.Look.hsw100_nearest
#print axioms Tm.Look.hsw100_mono
#print axioms Tm.Look.hsw100_withinOne
#print axioms Tm.Look.bucket_mono
#print axioms Tm.Look.futureEnergy_home_is_capped
#print axioms Tm.Look.futureEnergy_lounge_is_the_prediction
#print axioms Tm.Look.foldl_levelStep
#print axioms Tm.Look.histOf'_cons
#print axioms Tm.Look.histOf'_of_below
#print axioms Tm.Look.histOf'_perm
#print axioms Tm.Look.topElig_bump
#print axioms Tm.Look.topElig_of_zero_above
#print axioms Tm.Look.limitHist_eq
#print axioms Tm.Look.greedy_spec
#print axioms Tm.Look.limitSlots_is_limitHist
#print axioms Tm.Look.limitSlots_eq_limitSlotsFast
#print axioms Tm.Look.sum6_bump
#print axioms Tm.Look.foldl_add_minutes
#print axioms Tm.Look.sum6_histOf'
#print axioms Tm.Look.dayHist_eq
#print axioms Tm.Look.dayHist_keeps_the_min
#print axioms Tm.Look.dayHist_home_is_capped
#print axioms Tm.Look.hsw100_on_witnesses
#print axioms Tm.Look.the_bucket_reads_seconds
#print axioms Tm.Look.the_bucket_reads_seconds_on_the_spec_day
#print axioms Tm.Look.buckets_clamp
#print axioms Tm.Look.prior_energy_lookup
#print axioms Tm.Look.predict_matches_the_prior_tables_at_boundaries
#print axioms Tm.Look.predict_falls_back_to_the_prior
#print axioms Tm.Look.predict_uses_the_learned_curve
#print axioms Tm.Look.a_curve_falls_back_as_the_config_does
#print axioms Tm.Look.energize_follows_the_prior_curve
#print axioms Tm.Look.energize_applies_the_home_cap
#print axioms Tm.Look.a_future_tuesday_keeps_its_budget
#print axioms Tm.Look.the_learned_curve_moves_an_hour_on_sunday
#print axioms Tm.Look.hours_since_wake_count_real_hours_across_the_fall_transition

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step B2 (design §14.2, §5.3): the log's timestamps,
-- chrono's RFC 3339 reader and its fallback (`parseStamp`), `fmt_timestamp` (`renderStamp`), the
-- `tm log` column (`displayStamp`) and chrono's stamp order (`stampBefore`).  Stamp.lean, namespace
-- `Tm.LogStamp`.  22 theorems, including the in-step `parseStamp_renderStamp` (restated with a
-- year bound; `parseStamp_renderStamp_fails_past_year_9999` refutes it as §15 writes it) and the
-- order witness `stamp_order_is_the_instant_order`.
#print axioms Tm.LogStamp.stampBefore_iff
#print axioms Tm.LogStamp.stampBefore_ignores_the_offset
#print axioms Tm.LogStamp.stampBefore_irrefl
#print axioms Tm.LogStamp.renderOffset_length
#print axioms Tm.LogStamp.rfcOffset_renderOffset
#print axioms Tm.LogStamp.year_of_a_day_before_the_end
#print axioms Tm.LogStamp.dateBase_renderDate
#print axioms Tm.LogStamp.renderDate_length
#print axioms Tm.LogStamp.localDateTod_spec
#print axioms Tm.LogStamp.fracOf_renderOffset
#print axioms Tm.LogStamp.rfc3339_renderStamp
#print axioms Tm.LogStamp.parseStamp_renderStamp_before_year_10000
#print axioms Tm.LogStamp.parseStamp_renderStamp_fails_past_year_9999
#print axioms Tm.LogStamp.renderStamp_is_fmt_timestamp
#print axioms Tm.LogStamp.renderStamp_writes_a_leap_second_as_60
#print axioms Tm.LogStamp.displayStamp_is_the_written_clock
#print axioms Tm.LogStamp.the_origin_west_of_utc_is_year_zero
#print axioms Tm.LogStamp.stamp_order_is_the_instant_order
#print axioms Tm.LogStamp.a_leap_second_stamp_is_before_the_next_second
#print axioms Tm.LogStamp.parseStamp_reads_the_rfc3339_spellings
#print axioms Tm.LogStamp.parseStamp_reads_the_fallback
#print axioms Tm.LogStamp.parseStamp_refuses_what_is_not_a_stamp

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step B3 (design §14.2, §5.4–§5.6): the typed event grammar
-- of `.tm/log.jsonl` in Log.lean (new; namespace `Tm.Log`) — 26 known kinds and `unknown`, `readLine`,
-- `renderLine`, serde's `finiteF64`, the small grammars — and `digitsOf`'s runtime twin in Text.lean
-- (README gap 101, closed).  107 theorems: 2 in Text.lean, 105 in Log.lean, including the four goals
-- §15 names for B3 (`the_log_reads_what_it_renders`, `a_known_event_is_never_read_as_unknown`,
-- `an_unknown_tag_is_never_a_warning`, `lineTooLong_bounds_every_string`), added and discharged in
-- this step, so Goals.lean never held them.
#print axioms Tm.digitsOfTR_go
#print axioms Tm.digitsOf_eq_digitsOfTR
#print axioms Tm.Log.lastVal_go
#print axioms Tm.Log.lastVal_cons
#print axioms Tm.Log.lastVal_append
#print axioms Tm.Log.lastVal_nil
#print axioms Tm.Log.lastVal_of_not_mem
#print axioms Tm.Log.lastVal_mem
#print axioms Tm.Log.allStrs_map
#print axioms Tm.Log.readF_renderF
#print axioms Tm.Log.readArgs_of_agrees
#print axioms Tm.Log.renderArgs_keys
#print axioms Tm.Log.agrees_renderArgs
#print axioms Tm.Log.Kind.build_of_split
#print axioms Tm.Log.Event.tag_of_split
#print axioms Tm.Log.Event.fields_of_split
#print axioms Tm.Log.Event.strings_of_split
#print axioms Tm.Log.Event.canonical_of_split
#print axioms Tm.Log.Event.split_build
#print axioms Tm.Log.Event.split_of_not_unknown
#print axioms Tm.Log.kindOf_tag
#print axioms Tm.Log.Kind.keys_nodup
#print axioms Tm.Log.Kind.no_t_key
#print axioms Tm.Log.Kind.no_ev_key
#print axioms Tm.Log.finiteF64_of_nat
#print axioms Tm.Log.allFiniteL_map_str
#print axioms Tm.Log.allFiniteO_append
#print axioms Tm.Log.u32_le_u64Max
#print axioms Tm.Log.u8_le_u64Max
#print axioms Tm.Log.allFiniteO_renderArgs
#print axioms Tm.Log.jemitOTail_ends
#print axioms Tm.Log.jemit_obj_ends
#print axioms Tm.Log.trimCR_of_last
#print axioms Tm.Log.trimCR_jemit_obj
#print axioms Tm.Log.not_blank_jemit_obj
#print axioms Tm.Log.charsLt_irrefl
#print axioms Tm.Log.charsLe_of_lt
#print axioms Tm.Log.ne_of_charsLt
#print axioms Tm.Log.dedup_of_pairwise
#print axioms Tm.Log.restOf_canonical
#print axioms Tm.Log.countP_of_not_mem
#print axioms Tm.Log.stamp_hyps
#print axioms Tm.Log.readT_line
#print axioms Tm.Log.lastVal_ev_line
#print axioms Tm.Log.readLine_of_parse
#print axioms Tm.Log.keys_of_fields_known
#print axioms Tm.Log.keys_of_rest
#print axioms Tm.Log.the_log_reads_what_it_renders
#print axioms Tm.Log.a_known_event_is_never_read_as_unknown
#print axioms Tm.Log.trimCR_prefix
#print axioms Tm.Log.scan_peak_mono
#print axioms Tm.Log.depthOf_prefix
#print axioms Tm.Log.skipWs_suffix
#print axioms Tm.Log.isRustSpace_digit
#print axioms Tm.Log.jparse_not_blank
#print axioms Tm.Log.an_unknown_tag_is_never_a_warning
#print axioms Tm.Log.map_cons_ok
#print axioms Tm.Log.junescape_length
#print axioms Tm.Log.jscan_strlen
#print axioms Tm.Log.jstring_strlen
#print axioms Tm.Log.jstrs_ofDec
#print axioms Tm.Log.jstrsO_cons
#print axioms Tm.Log.jval_strs_step
#print axioms Tm.Log.jarr_strs_step
#print axioms Tm.Log.jtail_strs_step
#print axioms Tm.Log.jobj_strs_step
#print axioms Tm.Log.jpair_strs_step
#print axioms Tm.Log.jotail_strs_step
#print axioms Tm.Log.jparser_strs
#print axioms Tm.Log.jparse_strs
#print axioms Tm.Log.FR.pair_ok
#print axioms Tm.Log.mem_jstrsO_of_mem
#print axioms Tm.Log.jstrsO_sub
#print axioms Tm.Log.allStrs_mem
#print axioms Tm.Log.readF_strs
#print axioms Tm.Log.readArgs_strs
#print axioms Tm.Log.dedupStep_sub
#print axioms Tm.Log.restOf_sub
#print axioms Tm.Log.readLine_entry_inv
#print axioms Tm.Log.lineTooLong_bounds_every_string
#print axioms Tm.Log.digitsValue_ge
#print axioms Tm.Log.capExp_none
#print axioms Tm.Log.capExp_fold
#print axioms Tm.Log.finiteF64_reads_only_the_sign_past_an_i32_exponent
#print axioms Tm.Log.readF_refuses_a_u8_past_255
#print axioms Tm.Log.readF_refuses_a_u32_past_its_width
#print axioms Tm.Log.readF_refuses_a_decimal_at_an_integer_field
#print axioms Tm.Log.readF_reads_hsw_as_written
#print axioms Tm.Log.readLine_refuses_a_line_past_the_bound
#print axioms Tm.Log.readLine_refuses_a_line_nested_past_the_bound
#print axioms Tm.Log.readLine_refuses_a_line_that_is_not_utf8
#print axioms Tm.Log.malformed_line_1_is_a_wake
#print axioms Tm.Log.malformed_line_2_is_not_json
#print axioms Tm.Log.malformed_line_3_is_a_wake_without_slept_min
#print axioms Tm.Log.malformed_line_4_has_no_t
#print axioms Tm.Log.malformed_line_5_is_a_done_with_est_min_sixty
#print axioms Tm.Log.malformed_line_6_has_a_t_that_is_not_a_stamp
#print axioms Tm.Log.malformed_line_7_is_an_array
#print axioms Tm.Log.malformed_line_8_is_blank
#print axioms Tm.Log.malformed_line_9_is_an_unknown_mood
#print axioms Tm.Log.malformed_line_10_has_an_ev_that_is_not_a_string
#print axioms Tm.Log.malformed_line_11_is_a_note
#print axioms Tm.Log.the_malformed_corpus_reads_as_the_fork_point_did
#print axioms Tm.Log.an_out_of_range_numeral_warns_even_in_an_unknown_event
#print axioms Tm.Log.every_line_warning_is_reachable
#print axioms Tm.Log.finiteF64_is_serdes_band
#print axioms Tm.Log.the_small_grammars_read_as_the_fork_does

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step B4 (design §14.2 row B4, §6.1, §10): the `tz` and
-- `log` sections of the request in Boundary.lean — `readTz` (the zone table Rust probes, built only
-- by `Cal.mkTz?`), `readLogReq` and `mkLogReq?` (R10), `logAnswer` (lines, warnings, headers with tag
-- and id, render) and `runWithLog`, which `respond` now calls.  31 theorems, all in Boundary.lean;
-- `the_response_shapes_emit_in_build_order` is extended in place (already audited above).
#print axioms Tm.run_ok_shape
#print axioms Tm.runPlan_ok_shape
#print axioms Tm.runWithLog_without_a_log_is_run
#print axioms Tm.a_request_without_tz_or_log_is_read_as_before
#print axioms Tm.runWithLog_refuses_a_log_section_first
#print axioms Tm.runWithLog_puts_the_log_after_the_report
#print axioms Tm.readStep_fold
#print axioms Tm.logVerdicts_eq
#print axioms Tm.mkLogReq?_ok_iff
#print axioms Tm.mkLogReq?_keeps_the_request
#print axioms Tm.mkLogReq?_error_is_the_fault
#print axioms Tm.mkLogReq?_refuses_a_from_of_zero_or_past_2_40
#print axioms Tm.mkLogReq?_refuses_too_many_lines
#print axioms Tm.mkLogReq?_refuses_headersFrom_past_2_40
#print axioms Tm.mkLogReq?_refuses_too_many_render_lines
#print axioms Tm.LogReq.wf_bounds
#print axioms Tm.mkLogReq?_refuses_a_render_line_outside_the_tail
#print axioms Tm.readTz_refuses_a_long_key
#print axioms Tm.readTz_refuses_too_many_transitions
#print axioms Tm.readLogReq_refuses_more_lines_than_the_bound
#print axioms Tm.lineStep_error
#print axioms Tm.lineStep_fold
#print axioms Tm.readLogReq_reads_the_lines_as_sent
#print axioms Tm.LogReq.wf_render_in_tail
#print axioms Tm.logAnswer_renders_the_line_at_its_number
#print axioms Tm.readTzOffset_reads_the_table_spelling
#print axioms Tm.readTzInstant_reads_utc_whole_seconds
#print axioms Tm.readTz_reads_the_witness_table
#print axioms Tm.readTz_refuses_by_name
#print axioms Tm.the_log_op_reads_a_four_line_tail
#print axioms Tm.the_log_section_refuses_by_name

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L5 (design §13.4, §14.8 row L5): the lookahead, fork
-- `capacity::lookahead` with D10's mixture; `mkInput?` (R10, the model-then-config fallbacks of D10-4),
-- a future day's wake through `local_dt` at second resolution (`wakeInstantOf`), `pureDay`, `dayOf` held
-- once (`@[csimp] dayOf_eq_dayOfFast`), the §15 laws in-step, the twin, and the loaded-plan witness in
-- Boundary.lean through `wallIndex`.
#print axioms Tm.Look.WakeClock.ofClock_wf
#print axioms Tm.Look.wakeInstantOf_ofClock
#print axioms Tm.Look.wakeInstantOf_on_an_unambiguous_time
#print axioms Tm.Look.mkInput?_refuses_too_many_days
#print axioms Tm.Look.pureDay_is_dayHist
#print axioms Tm.Look.Six.get_of
#print axioms Tm.Look.locSix_get
#print axioms Tm.Look.dayOf_eq_dayOfFast
#print axioms Tm.Look.foldl_cons_map
#print axioms Tm.Look.lookahead_eq_map
#print axioms Tm.Look.dayOf_day
#print axioms Tm.Look.lookahead_keeps_the_days
#print axioms Tm.Look.lookahead_dates
#print axioms Tm.Look.lookahead_getElem?
#print axioms Tm.Look.daysAscending_range'
#print axioms Tm.Look.lookahead_is_a_lookahead
#print axioms Tm.Look.lookahead_entry
#print axioms Tm.Look.lookahead_day_zero_is_the_kernels
#print axioms Tm.Look.lookahead_future_day_is_the_mixture
#print axioms Tm.Look.lookahead_between_the_locations
#print axioms Tm.Look.lookahead_at_a_certain_weight_is_the_pure_location
#print axioms Tm.Look.the_twin_forces_the_forks_location
#print axioms Tm.Look.pureDay_le_budget
#print axioms Tm.Look.lookahead_future_day_width
#print axioms Tm.Look.weightsOf?_ok
#print axioms Tm.Look.weightsOf?_of_ok
#print axioms Tm.Look.mkInput?_ok_elim
#print axioms Tm.Look.mkInput?_weight_is_the_model_then_config
#print axioms Tm.Look.mkInput?_arrival_and_wake
#print axioms Tm.Look.mkInput?_days_le
#print axioms Tm.Look.mkInput?_refuses_a_bad_weight
#print axioms Tm.Look.mkInput?_refuses_a_bad_wake
#print axioms Tm.Look.mkInput?_refuses_a_now_that_disagrees
#print axioms Tm.Look.mkInput?_accepts
#print axioms Tm.Look.wakeOf_without_a_logged_wake_is_wf
#print axioms Tm.Look.lookahead_is_the_expected_minutes
#print axioms Tm.Look.wakeInstantOf_on_witnesses
#print axioms Tm.Look.a_future_day_reads_todays_wake_to_the_second
#print axioms Tm.Look.the_twin_follows_the_learned_arrival_and_location
#print axioms Tm.Look.the_expected_tuesday
#print axioms Tm.Look.mkInput?_on_witnesses
#print axioms Tm.Look.sunday_mixes_at_its_own_weight
#print axioms Tm.Look.a_wednesday_wall_moves_the_window_and_keeps_the_budget
#print axioms Tm.the_look_wall_witness_loads
#print axioms Tm.the_look_wall_calendar_indexes_one_wednesday_wall
#print axioms Tm.a_loaded_wednesday_wall_moves_the_window_and_keeps_the_budget

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L6 (design §13.6, §10.4, §14.8 row L6): capacity on
-- the wire.  Lookahead.lean: every §13.6 bound mkInput? does not check, with its smart constructor and
-- rejection theorems (mkDayCfg?, mkStep?, curveOk, priorOk, energyOk, homeMaxOk).  Boundary.lean: `run`
-- split at runLoad, the `capacity` and `tz` readers (CapWire), runCap / respondCap / callCap with the
-- export moved to them, the bridge to `run` and `call`, what an answered request satisfies, and the
-- decided witnesses.  Gap 77 closed.
#print axioms Tm.Look.mkDayCfg?_wf
#print axioms Tm.Look.mkDayCfg?_of_wf
#print axioms Tm.Look.mkDayCfg?_refuses_blockMin
#print axioms Tm.Look.mkDayCfg?_refuses_breakMin
#print axioms Tm.Look.mkDayCfg?_refuses_breakAfterBlocks
#print axioms Tm.Look.mkDayCfg?_refuses_minLastBlockMin
#print axioms Tm.Look.mkDayCfg?_refuses_windowHours
#print axioms Tm.Look.mkDayCfg?_refuses_budgetRatio
#print axioms Tm.Look.DayCfg.wf_window_le_a_day
#print axioms Tm.Look.mkStep?_ok_iff
#print axioms Tm.Look.mkStep?_refuses_a_zero_denominator
#print axioms Tm.Look.mkStep?_refuses_a_wide_denominator
#print axioms Tm.Look.mkStep?_refuses_past_48_hours
#print axioms Tm.Look.mkStep?_refuses_an_empty_range
#print axioms Tm.Look.mkStep?_refuses_a_level_above_five
#print axioms Tm.Look.curveOk_refuses_too_many_ranges
#print axioms Tm.Look.curveOk_refuses_a_bad_range
#print axioms Tm.Look.curveOk_refuses_an_unsorted_curve
#print axioms Tm.Look.priorOk_refuses_too_many_curves
#print axioms Tm.Look.priorOk_refuses_a_long_key
#print axioms Tm.Look.priorOk_refuses_a_key_twice
#print axioms Tm.Look.priorOk_refuses_a_bad_curve
#print axioms Tm.Look.energyOk_refuses_a_curve_not_of_12
#print axioms Tm.Look.energyOk_refuses_an_entry_past_a_byte
#print axioms Tm.Look.homeMaxOk_iff
#print axioms Tm.Look.priorOk_widths
#print axioms Tm.Look.priorOk_keys_in_the_exact_domain
#print axioms Tm.Look.the_shipped_bounds_hold
#print axioms Tm.run_is_runLoad_then_runPlan
#print axioms Tm.capBind_ok_elim
#print axioms Tm.runCap_without_capacity_is_run
#print axioms Tm.respondCap_without_capacity_is_respond
#print axioms Tm.callExport_without_capacity_is_call
#print axioms Tm.the_exported_call_emits_parses_back
#print axioms Tm.runCap_answers_with_the_lookahead
#print axioms Tm.runCap_refuses_what_the_section_refuses
#print axioms Tm.runPlan_ok_is_docs_then_report
#print axioms Tm.runCap_answers_docs_report_lookahead
#print axioms Tm.CapWire.unitsJson_reads_back
#print axioms Tm.CapWire.lookaheadJson_days
#print axioms Tm.CapWire.readWeight_ok
#print axioms Tm.CapWire.readWeekAll_ok
#print axioms Tm.CapWire.readWeekOpt_ok
#print axioms Tm.CapWire.orErr_ok
#print axioms Tm.CapWire.mapError_ok
#print axioms Tm.CapWire.readModelTable_ok
#print axioms Tm.CapWire.readTables_ok
#print axioms Tm.CapWire.readEnergyCurve_ok
#print axioms Tm.CapWire.readEnergy_ok
#print axioms Tm.CapWire.readCurve_ok
#print axioms Tm.CapWire.readPrior_ok
#print axioms Tm.CapWire.readHomeMax_ok
#print axioms Tm.CapWire.mkDayCfg?_blockMin
#print axioms Tm.CapWire.readDay_ok
#print axioms Tm.CapWire.readPriority_ok
#print axioms Tm.CapWire.readSection_ok
#print axioms Tm.CapWire.readCapacity_ok
#print axioms Tm.CapWire.the_zone_texts_read_on_witnesses
#print axioms Tm.CapWire.readTz_on_witnesses
#print axioms Tm.CapWire.readWeight_on_witnesses
#print axioms Tm.CapWire.readDay_on_witnesses
#print axioms Tm.CapWire.readPrior_on_witnesses
#print axioms Tm.CapWire.readEnergy_on_witnesses
#print axioms Tm.CapWire.readPriority_on_witnesses
#print axioms Tm.CapWire.the_capacity_section_reads_the_corpus_model
#print axioms Tm.CapWire.the_lookahead_response_emits_in_build_order
#print axioms Tm.CapWire.runCap_reads_the_corpus_request
#print axioms Tm.CapWire.jget_pairJ
#print axioms Tm.CapWire.natOfDigits_digitsOf
#print axioms Tm.CapWire.pairWith_digits
#print axioms Tm.CapWire.readWeight_reads_every_representable_weight
#print axioms Tm.CapWire.readWeight_refuses_more_than_18_places
#print axioms Tm.CapWire.readHomeMax_on_the_bound
#print axioms Tm.CapWire.readTz_refuses_too_many_transitions

-- APPENDED 2026-09-14 (merge of rebuild-on-lean's D9 B2-B4 into stage5-lookahead's D10 L5-L6).
-- `runCap` now composes B4's `log` section (`logInto`), so the bridge to the old entry point is
-- restated over `runWithLog`; the L6 name `runPlan_ok_shape` collided with B4's and was renamed
-- `runPlan_ok_is_docs_then_report` in place above.  L6's second `tz` reader is gone (gap 108):
-- `CapWire.readTz_on_witnesses`, `CapWire.the_zone_texts_read_on_witnesses` and
-- `CapWire.readTz_refuses_too_many_transitions` are re-proved over B4's `readTz` (audited above).
#print axioms Tm.runCap_without_capacity_is_runWithEmit
#print axioms Tm.runCap_refuses_a_log_section_first
#print axioms Tm.runCap_answers_docs_report_log_lookahead

-- APPENDED 2026-09-14 (stage 5, W-2 repair).  The audit's two minors: B2's narrowed stamp round
-- trip is renamed `Tm.LogStamp.parseStamp_renderStamp_before_year_10000` (its B2 line above is
-- edited in place, since the old name no longer exists; the refutation keeps its line), and B4's
-- 142-character `log` conjunct is split into three conjuncts of at most 52 characters, composed by
-- the new `withLog_jone`.  `malformedLine5` is spelled pair by pair (no new theorem).
#print axioms Tm.withLog_jone

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L8, kernel half (design §13.6, §13.8): the grants
-- on the wire (gaps 80, 107), EDF compiled linear (gap 106), one zone reading (gap 110), and capacity
-- refused beside commands (gap 109).  Three existing statements gained hypotheses for the new wire
-- (`runCap_answers_with_the_lookahead`, `runCap_answers_docs_report_lookahead`,
-- `runCap_answers_docs_report_log_lookahead`: no candidates, no commands); their audit lines stand above.
#print axioms Tm.NumSix.get_of
#print axioms Tm.availUntil_foldl
#print axioms Tm.availUntil_eq_availUntilFast
#print axioms Tm.reserveRestAcc_eq
#print axioms Tm.edfStepFast_foldl
#print axioms Tm.edfGrantsGo_eq_edfGrantsGoFast
#print axioms Tm.edfCaps_eq_edfCapsFast
#print axioms Tm.reserveRest_eq_reserveRestFast
#print axioms Tm.reserveOut_eq_reserveOutFast
#print axioms Tm.edf_eq_edfFast
#print axioms Tm.edfGrants_eq_edfGrantsFast
#print axioms Tm.Look.enterOf_eq_some
#print axioms Tm.Look.mem_entering
#print axioms Tm.Look.insertDueIx_snd
#print axioms Tm.Look.sortDueIx_snd
#print axioms Tm.Look.perm_insertDueIx
#print axioms Tm.Look.sortDueIx_perm
#print axioms Tm.Look.edfGrantsGo_length
#print axioms Tm.Look.tagGrants_snd
#print axioms Tm.Look.servedGrants_are_the_pass
#print axioms Tm.Look.grantAt_servedGrants
#print axioms Tm.Look.grantAt_none_of_not_enters
#print axioms Tm.Look.grantAt_some_of_enters
#print axioms Tm.Look.priorities_length
#print axioms Tm.Look.priorities_getElem?
#print axioms Tm.Look.an_answer_carries_a_grant_iff_its_candidate_enters
#print axioms Tm.Look.an_answers_grant_reserves_the_min
#print axioms Tm.Look.an_answer_is_off_the_scale_iff_a_wall
#print axioms Tm.Look.finalPrio_of_pressure_hot
#print axioms Tm.Look.a_hot_answer_is_zero
#print axioms Tm.Look.priorities_on_a_witness
#print axioms Tm.readLogSection_is_zoneOf_then_logSectionWith
#print axioms Tm.zoneOf_ok_obj
#print axioms Tm.the_zone_is_read_once_and_feeds_both_sections
#print axioms Tm.runCap_with_capacity_reads_the_zone_once
#print axioms Tm.zoneOf_of_readLogSection
#print axioms Tm.runCap_answers_with_the_lookahead_and_grants
#print axioms Tm.runCap_refuses_what_the_candidates_refuse
#print axioms Tm.runCap_refuses_commands_beside_capacity
#print axioms Tm.an_answered_capacity_request_has_no_commands
#print axioms Tm.runCap_answers_docs_report_lookahead_grants
#print axioms Tm.CapWire.readCands_on_witnesses
#print axioms Tm.CapWire.runCap_refuses_a_command_beside_the_corpus_request
#print axioms Tm.CapWire.the_grant_response_emits_in_build_order

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L8, host half (design §13.8): the floor pass (gap
-- 79).  One existing statement gained a hypothesis for it (`runCap_answers_docs_report_lookahead_grants`:
-- no candidate carries a floor; its audit line stands above), and
-- `runCap_answers_docs_report_lookahead_floor_grants` states the general answer.
#print axioms Tm.Look.passLeft_is_edf
#print axioms Tm.Look.prioritiesWithFloors_length
#print axioms Tm.Look.prioritiesWithFloors_getElem?
#print axioms Tm.Look.lt_of_priorities_getElem?
#print axioms Tm.Look.prioritiesWithFloors_without_floors
#print axioms Tm.Look.a_floor_reserves_nothing
#print axioms Tm.Look.the_pass_wins_over_a_floor
#print axioms Tm.Look.an_ungranted_floor_is_answered_at_its_floor
#print axioms Tm.Look.a_floor_answer_reads_what_the_pass_left
#print axioms Tm.Look.a_hot_floor_answer_is_zero
#print axioms Tm.Look.prioritiesWithFloors_on_a_witness
#print axioms Tm.Look.prioritiesWithFloors_on_a_roomier_witness
#print axioms Tm.CapWire.grantJsonF_without_a_floor
#print axioms Tm.runCap_answers_docs_report_lookahead_floor_grants
#print axioms Tm.CapWire.readCands_reads_and_refuses_floors
#print axioms Tm.CapWire.the_floor_grant_response_emits_in_build_order

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step C1 (design §7.1, §14.4 row C1): the undo mask in
-- Replay.lean (new) and the `log` op's `facts.cancelled` in Boundary.lean.  The four goals §15 names for
-- C1 were added to Goals.lean and discharged in the step: `survivors_snoc_event`, `survivors_snoc_undo`,
-- `a_cancelled_event_is_never_revived` and `a_dangling_undo_dangles_in_every_extension` (the last
-- without §15's two unneeded hypotheses).  The fast twins are `survivors_eq_survivorsFast` and
-- `cancelledLines_eq_cancelledLinesFast`, both `@[csimp]`.
#print axioms Tm.Log.linesIncreasing_pairwise
#print axioms Tm.Replay.survivors_nil
#print axioms Tm.Replay.survivors_snoc_event
#print axioms Tm.Replay.survivors_snoc_undo
#print axioms Tm.Replay.mem_foldl_maskStep
#print axioms Tm.Replay.not_undo_of_mem_foldl_maskStep
#print axioms Tm.Replay.an_undo_never_survives
#print axioms Tm.Replay.mem_of_mem_survivors
#print axioms Tm.Replay.a_cancelled_event_is_never_revived
#print axioms Tm.Replay.danglingOf_fst_go
#print axioms Tm.Replay.danglingOf_fst
#print axioms Tm.Replay.danglingOf_snd_mono
#print axioms Tm.Replay.a_dangling_undo_dangles_in_every_extension
#print axioms Tm.Replay.an_entry_that_dangles_is_an_undo
#print axioms Tm.Replay.isUndo_of_tag_undo
#print axioms Tm.Replay.no_survivor_matches_an_undo_of_an_undo
#print axioms Tm.Replay.an_undo_of_an_undo_cancels_nothing_in_a_canonical_log
#print axioms Tm.Replay.dangleStep_of_no_match
#print axioms Tm.Replay.an_undo_of_an_undo_dangles_in_a_canonical_log
#print axioms Tm.Replay.maskStepI_map
#print axioms Tm.Replay.foldl_maskStepI_map
#print axioms Tm.Replay.zipIdx_map_fst
#print axioms Tm.Replay.stackI_map
#print axioms Tm.Replay.PosMap.size_set
#print axioms Tm.Replay.PosMap.get_empty
#print axioms Tm.Replay.find?_filter_ne
#print axioms Tm.Replay.PosMap.get_set
#print axioms Tm.Replay.pairKey_inj
#print axioms Tm.Replay.deadAt_set
#print axioms Tm.Replay.filter_dropWhile_cons
#print axioms Tm.Replay.filter_dropWhile_nil
#print axioms Tm.Replay.eraseP_eq_filter_pos
#print axioms Tm.Replay.eraseP_eq_self_of_filter_nil
#print axioms Tm.Replay.Inv.nodup
#print axioms Tm.Replay.filter_kill
#print axioms Tm.Replay.filter_kill1
#print axioms Tm.Replay.filter_pos_ne_comm
#print axioms Tm.Replay.foldl_snoc_maskStepI
#print axioms Tm.Replay.stack_positions_lt
#print axioms Tm.Replay.Inv.step_undo_none
#print axioms Tm.Replay.Inv.posLt_snoc
#print axioms Tm.Replay.Inv.incr_snoc
#print axioms Tm.Replay.Inv.step_undo_some
#print axioms Tm.Replay.maskFastStep_event
#print axioms Tm.Replay.maskStepI_event
#print axioms Tm.Replay.Inv.step_event
#print axioms Tm.Replay.Inv.step
#print axioms Tm.Replay.Inv.init
#print axioms Tm.Replay.maskFast_inv
#print axioms Tm.Replay.maskFast_stack
#print axioms Tm.Replay.cancelledAt_eq_deadAt
#print axioms Tm.Replay.survivors_are_the_uncancelled_entries
#print axioms Tm.Replay.survivors_eq_survivorsFast
#print axioms Tm.Replay.cancelledLines_eq_cancelledLinesFast
#print axioms Tm.Replay.cancelled_and_survivors_partition
#print axioms Tm.Replay.the_mask_ignores_isStateChange
#print axioms Tm.Replay.undo_mask_pairs_and_dangling_ported
#print axioms Tm.Replay.an_undo_of_an_undo_cancels_a_noncanonical_unknown_undo
#print axioms Tm.Replay.an_undo_with_an_id_passes_over_other_ids
#print axioms Tm.readLine_entry_line
#print axioms Tm.filterMap_entryOf_lines
#print axioms Tm.linesIncreasing_of_pairwise
#print axioms Tm.filterMap_entryOf_pairwise
#print axioms Tm.the_tail_entries_have_increasing_lines

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step C2 (design §6.2, §14.4 row C2): the day index in
-- Replay.lean and the `log` op's `facts.days` in Boundary.lean (the request carries its zone,
-- `LogReq.tz`).  The three goals §15 names for C2 were added to Goals.lean restated in chrono's order
-- (carried note 1) and discharged in the step: `dayOf_is_the_wake_date_within_a_day`,
-- `a_wake_day_is_shorter_than_a_day` and `keptWakes_append_of_later`; §15's nanosecond statements are
-- refuted by the three `…_by_nanos_is_refuted`.  Quirk Q6(a): `the_kept_wake_is_not_the_first_logged_wake`
-- and `the_kept_wake_is_the_first_logged_wake_when_wakes_are_logged_in_order`.  The fast twins are
-- `sortWakes_eq_sortWakesFast` and `entryDays_eq_entryDaysFast`, both `@[csimp]`.  Two existing
-- Boundary theorems gained the zone argument and keep their audit lines:
-- `readLogReq_refuses_more_lines_than_the_bound`, `readLogReq_reads_the_lines_as_sent`.
#print axioms Tm.Replay.instant_le_trans
#print axioms Tm.Replay.instant_le_refl
#print axioms Tm.Replay.instant_le_of_not_le
#print axioms Tm.Replay.instant_le_of_lt
#print axioms Tm.Replay.instant_not_le_of_lt
#print axioms Tm.Replay.insertWake_perm
#print axioms Tm.Replay.sortWakes_perm
#print axioms Tm.Replay.insertWake_sorted
#print axioms Tm.Replay.sortWakes_sorted
#print axioms Tm.Replay.eq_of_perm_of_sorted
#print axioms Tm.Replay.sortWakes_eq_sortWakesFast
#print axioms Tm.Replay.sortWakes_append_of_later
#print axioms Tm.Replay.foldl_keptStep_acc
#print axioms Tm.Replay.foldl_keptStep_head
#print axioms Tm.Replay.keptWakes_last
#print axioms Tm.Replay.keptWakes_append_of_later
#print axioms Tm.Replay.mem_foldl_keptStep
#print axioms Tm.Replay.mem_of_mem_keptFrom
#print axioms Tm.Replay.foldl_keptStep_sublist
#print axioms Tm.Replay.keptWakes_sorted
#print axioms Tm.Replay.foldl_lastWake_or
#print axioms Tm.Replay.lastWakeLe_cons
#print axioms Tm.Replay.lastWakeLe_le
#print axioms Tm.Replay.lastWakeLe_append_of_later
#print axioms Tm.Replay.dayOf_is_the_wake_date_within_a_day
#print axioms Tm.Replay.dayOf_without_a_recent_wake_is_the_local_date
#print axioms Tm.Replay.a_wake_day_is_shorter_than_a_day
#print axioms Tm.Replay.dayOf_agrees_below_a_later_wake
#print axioms Tm.Replay.an_instant_off_its_own_date_is_within_a_day_of_its_wake
#print axioms Tm.Replay.dedupFrom_append
#print axioms Tm.Replay.dedupFrom_last
#print axioms Tm.Replay.dedupFrom_single
#print axioms Tm.Replay.lastWakeLe_snoc
#print axioms Tm.Replay.lastWakeLe_of_all_le
#print axioms Tm.Replay.lastWakeLe_dedup_same_date
#print axioms Tm.Replay.a_wake_is_on_its_own_date
#print axioms Tm.Replay.find?_congr_mem
#print axioms Tm.Replay.find?_dedupFrom
#print axioms Tm.Replay.the_kept_wake_is_the_first_logged_wake_when_wakes_are_logged_in_order
#print axioms Tm.Replay.lePoint_spec
#print axioms Tm.Replay.lastWakeLe_of_point
#print axioms Tm.Replay.lastWakeLeArr_eq_lastWakeLe
#print axioms Tm.Replay.entryDays_eq_entryDaysFast
#print axioms Tm.Replay.day_index_wake_to_wake_ported
#print axioms Tm.Replay.the_kept_wake_is_not_the_first_logged_wake
#print axioms Tm.Replay.the_day_index_dedups_runs_not_dates
#print axioms Tm.Replay.dayOf_is_the_wake_date_within_a_day_by_nanos_is_refuted
#print axioms Tm.Replay.a_wake_day_is_shorter_than_a_day_by_nanos_is_refuted
#print axioms Tm.Replay.keptWakes_append_of_later_by_nanos_is_refuted
#print axioms Tm.Replay.a_wake_day_is_shorter_than_a_day_is_not_vacuous
#print axioms Tm.Replay.an_undone_wake_indexes_nothing

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C3 (design §8.1–§8.2, §14.4 row C3): the machine's
-- state, effects and keys in Replay.lean, the block family's arms (`start`, `pause`, `unpause`,
-- `interrupt`, `resume`, `stop`, `done` with partials, `extend`) with `credit`, `uncredit_cut` and `cut`
-- ported by name, the maps' laws (`KMap`, and `HMap`, the bucketed map of items and item days), and the
-- `log` op's `facts.block` in Boundary.lean (`the_log_op_answers_the_block_facts`).  The three goals §15 names for C3
-- were added to Goals.lean as written and discharged in the step: `applyEffects_touches_only_named_keys`,
-- `every_known_event_has_an_arm` and `credit_conserves_the_day_minutes`.  Site R8 (quirk Q6c, gap 83):
-- `worked_minutes_floor_each_subsegment` and its twin `worked_minutes_is_not_the_floor_of_the_block`.  Site R9:
-- `load_is_exact_fifths`.
-- §8.2's `an_extend_changes_only_the_bookkeeping` is refuted under the owner's D14
-- (`an_extend_changes_more_than_the_bookkeeping`) and restated
-- (`an_extend_changes_only_the_bookkeeping_and_its_extended_minutes`).  The `@[csimp]` twins are
-- `replay_eq_replayFast`, `sortObs_eq_sortObsFast` and `sortSegs_eq_sortSegsFast`.
#print axioms Tm.Replay.insBy_append
#print axioms Tm.Replay.insSort_eq_mergeSort
#print axioms Tm.Replay.sortObs_eq_sortObsFast
#print axioms Tm.Replay.sortSegs_eq_sortSegsFast
#print axioms Tm.Replay.replay_eq_replayFast
#print axioms Tm.Replay.KMap.get_nil
#print axioms Tm.Replay.KMap.get_cons
#print axioms Tm.Replay.KMap.get_append
#print axioms Tm.Replay.KMap.get_eq_none_of_keys
#print axioms Tm.Replay.KMap.get_eq_none_iff_keys
#print axioms Tm.Replay.KMap.get_filter_key
#print axioms Tm.Replay.KMap.get_alterGo
#print axioms Tm.Replay.KMap.get_alter
#print axioms Tm.Replay.KMap.get_map_snd
#print axioms Tm.Replay.KMap.vsum_append
#print axioms Tm.Replay.KMap.vsum_cons
#print axioms Tm.Replay.KMap.vsum_reverse
#print axioms Tm.Replay.KMap.get_le_vsum
#print axioms Tm.Replay.KMap.mem_keys_of_get
#print axioms Tm.Replay.KMap.filter_key_of_not_mem
#print axioms Tm.Replay.KMap.vsum_alterGo
#print axioms Tm.Replay.KMap.vsum_alter
#print axioms Tm.Replay.HMap.get_alter
#print axioms Tm.Replay.HMap.get_mapVals
#print axioms Tm.Replay.HMap.get_empty
#print axioms Tm.Replay.valueAt_applyEffect
#print axioms Tm.Replay.applyEffects_touches_only_named_keys
#print axioms Tm.Replay.closeSub_plain
#print axioms Tm.Replay.closePause_plain
#print axioms Tm.Replay.creditFx_plain
#print axioms Tm.Replay.obsFx_plain
#print axioms Tm.Replay.cut_plain
#print axioms Tm.Replay.not_header_of_plain
#print axioms Tm.Replay.uncreditFx_no_header
#print axioms Tm.Replay.doneClose_no_header
#print axioms Tm.Replay.doneFx_no_header
#print axioms Tm.Replay.arm_no_header
#print axioms Tm.Replay.every_known_event_has_an_arm
#print axioms Tm.Replay.Ci6.sum_add
#print axioms Tm.Replay.safe_of_plain
#print axioms Tm.Replay.DayAcc.bal_empty
#print axioms Tm.Replay.DayOp.bal_apply
#print axioms Tm.Replay.DayAcc.bal_uncredit
#print axioms Tm.Replay.applyEffects_append
#print axioms Tm.Replay.applyEffects_cons
#print axioms Tm.Replay.safe_apply
#print axioms Tm.Replay.safe_list
#print axioms Tm.Replay.machine_apply
#print axioms Tm.Replay.conserves_safe
#print axioms Tm.Replay.conserves_safe_then_machine
#print axioms Tm.Replay.closeSub_lastCut
#print axioms Tm.Replay.closePause_lastCut
#print axioms Tm.Replay.all_safe_of_plain
#print axioms Tm.Replay.unk_credit_none
#print axioms Tm.Replay.conserves_cut
#print axioms Tm.Replay.bal_apply_uncredit
#print axioms Tm.Replay.conserves_doneClose
#print axioms Tm.Replay.conserves_arm
#print axioms Tm.Replay.conserves_init
#print axioms Tm.Replay.conserves_step
#print axioms Tm.Replay.conserves_foldl
#print axioms Tm.Replay.credit_conserves_the_day_minutes
#print axioms Tm.Replay.Ci6.fifths_add
#print axioms Tm.Replay.DayOp.fifths_apply
#print axioms Tm.Replay.DayOp.fifths_alterFn
#print axioms Tm.Replay.allFifths_apply
#print axioms Tm.Replay.allFifths_foldl
#print axioms Tm.Replay.load_is_exact_fifths
#print axioms Tm.Replay.worked_minutes_floor_each_subsegment
#print axioms Tm.Replay.an_extend_changes_only_the_bookkeeping_and_its_extended_minutes
#print axioms Tm.Replay.a_start_cuts_any_open_block_even_the_same_id
#print axioms Tm.Replay.a_block_cut_by_start_is_never_replaced_by_done
#print axioms Tm.Replay.a_stop_then_done_replaces_the_cut_credit
#print axioms Tm.Replay.a_stop_for_another_id_is_ignored
#print axioms Tm.Replay.a_matched_done_discards_the_clock_minutes
#print axioms Tm.Replay.close_pause_does_not_clear_paused
#print axioms Tm.Replay.a_partial_done_credits_but_does_not_complete
#print axioms Tm.Replay.a_partial_done_after_stop_replaces_the_cut
#print axioms Tm.Replay.a_block_started_during_an_interruption_runs_from_resume
#print axioms Tm.Replay.worked_minutes_is_not_the_floor_of_the_block
#print axioms Tm.Replay.an_extend_changes_more_than_the_bookkeeping

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C4 (design §8.2–§8.4, §14.4 row C4): the completion
-- family in Replay.lean (`completionArm`: `done`'s `mark_done`, `routine`, `skip`, `event`; the keys
-- `doneDate`, `instDate`, `instOther` and `named`; `arm_ofBlock`, which keeps the block family's arm off
-- the completion state), the `log` op's `facts.completion` and `facts.replayWarnings` in Boundary.lean
-- (`the_log_op_answers_the_completion_facts`), and Log.lean's repair of `parse_date`'s byte length
-- (`the_date_grammars_count_bytes_not_characters`).  The C4 goals §15 names were added to Goals.lean and
-- discharged in the step: `an_instance_is_its_last_record_in_file_order` (as written),
-- `last_done_is_the_latest_by_instant` (`doneInstants` without the zone it does not read) and
-- `instances_and_last_done_order_differently`.  Quirk Q6(b) (gap 118) beside them:
-- `last_done_is_the_first_of_the_latest`, `last_done_keeps_the_first_of_equal_instants`.  Carried note 3:
-- `a_since_filter_does_not_commute_with_the_latest_by_instant` refutes §8.4's claim, and
-- `named_keeps_the_latest_by_instant_and_the_latest_by_local_date` is fork `LatestNamed`.
-- `conserves_step`, `conserves_foldl`, `allFifths_foldl` and `arm_no_header` (audited under C3) are
-- re-proved over the zone and the completion arm.
#print axioms Tm.Log.the_date_grammars_count_bytes_not_characters
#print axioms Tm.Replay.ofBlock_of_plain
#print axioms Tm.Replay.header_of_ofBlock
#print axioms Tm.Replay.uncreditFx_ofBlock
#print axioms Tm.Replay.doneClose_ofBlock
#print axioms Tm.Replay.doneFx_ofBlock
#print axioms Tm.Replay.arm_ofBlock
#print axioms Tm.Replay.completionArm_no_header
#print axioms Tm.Replay.completionArm_safe
#print axioms Tm.Replay.foldl_lastMaxStep_some
#print axioms Tm.Replay.lastMax?_eq_none_iff
#print axioms Tm.Replay.maxSplit_step
#print axioms Tm.Replay.maxSplit_foldl
#print axioms Tm.Replay.lastMax?_spec
#print axioms Tm.Replay.filterMap_cons_toList
#print axioms Tm.Replay.applyEffect_lastDone
#print axioms Tm.Replay.lastDone_applyEffects
#print axioms Tm.Replay.markOf_of_ofBlock
#print axioms Tm.Replay.arm_markOf
#print axioms Tm.Replay.completionArm_markOf
#print axioms Tm.Replay.stepWith_lastDone
#print axioms Tm.Replay.foldl_stepWith_lastDone
#print axioms Tm.Replay.replay_state
#print axioms Tm.Replay.last_done_is_the_latest_by_instant
#print axioms Tm.Replay.instLt_trans
#print axioms Tm.Replay.instLt_skip
#print axioms Tm.Replay.last_done_is_the_first_of_the_latest
#print axioms Tm.Replay.last_done_isSome_iff
#print axioms Tm.Replay.applyEffect_instances
#print axioms Tm.Replay.instances_applyEffects
#print axioms Tm.Replay.instOf_of_ofBlock
#print axioms Tm.Replay.stepWith_instances
#print axioms Tm.Replay.foldl_stepWith_instances
#print axioms Tm.Replay.an_instance_is_its_last_record_in_file_order
#print axioms Tm.Replay.applyEffect_named
#print axioms Tm.Replay.named_applyEffects
#print axioms Tm.Replay.completionArm_namedOf
#print axioms Tm.Replay.stepWith_named
#print axioms Tm.Replay.foldl_stepWith_named
#print axioms Tm.Replay.foldl_pushStep_latest
#print axioms Tm.Replay.foldl_pushStep_dated
#print axioms Tm.Replay.named_keeps_the_latest_by_instant_and_the_latest_by_local_date
#print axioms Tm.Replay.applyEffect_ofBlock_keeps
#print axioms Tm.Replay.completionArm_rwarns
#print axioms Tm.Replay.stepWith_rwarns
#print axioms Tm.Replay.the_replay_warnings_are_the_unknown_statuses_in_file_order
#print axioms Tm.Replay.applyEffect_doneDates
#print axioms Tm.Replay.applyEffects_doneDates
#print axioms Tm.Replay.completionArm_doneDates
#print axioms Tm.Replay.stepWith_doneDates
#print axioms Tm.Replay.a_done_date_is_a_survivors_completion_date
#print axioms Tm.Replay.instances_and_last_done_order_differently
#print axioms Tm.Replay.a_retro_done_marks_done_and_credits_nothing
#print axioms Tm.Replay.a_later_pending_does_not_undo_a_done_date
#print axioms Tm.Replay.an_unknown_status_warns_and_is_pending
#print axioms Tm.Replay.last_done_keeps_the_first_of_equal_instants
#print axioms Tm.Replay.a_routine_done_is_dated_by_its_inst_only_when_it_is_a_date
#print axioms Tm.Replay.a_since_filter_does_not_commute_with_the_latest_by_instant

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C5 (design §8.2–§8.4, §14.4 row C5): the day header and
-- records family in Replay.lean (`dayArm`: `wake`, `arrive`, `loc`, `break`, `energy`, `idle`, `routine`'s day
-- half, `plan`, `demote`, `drop`, `close`, unknown events; `DayAcc` the whole of fork `DayReplay`; days
-- bucketed; fork `slept_by_day` built before the walk and compiled as `sleptMap`), the `log` op's `facts.day`
-- in Boundary.lean (`the_log_op_answers_the_day_facts`), and Log.lean's port of chrono's signed `%Y`
-- (`a_signed_year_is_a_date_to_chrono`).  The C5 goals were added to Goals.lean and discharged in the step:
-- `energy_obs_slept_is_the_days_first_logged_sleep` (as §15 writes it), `the_first_leak_maximum_wins`,
-- `a_demote_stamp_reads_the_week_or_date_key` and `idle_and_idle_since_read_different_orders`.  Quirks Q6(f)
-- and Q6(g) with their separating witnesses.  Audited under C3/C4 and re-proved over the new arm (their
-- names unchanged): `arm_ofBlock`, `arm_no_header`, `arm_markOf`, `uncreditFx_ofBlock`, `doneClose_ofBlock`,
-- `doneFx_ofBlock`, `conserves_arm`, `conserves_step`, `conserves_foldl`, `allFifths_foldl`,
-- `credit_conserves_the_day_minutes`, `load_is_exact_fifths`, `replay_state`, `replay_eq_replayFast` and the
-- C4 `stepWith_*` laws.
#print axioms Tm.Log.a_signed_year_is_a_date_to_chrono
#print axioms Tm.Replay.foldl_sleptStep_get
#print axioms Tm.Replay.blockOnly_of_plain
#print axioms Tm.Replay.ofBlock_of_blockOnly
#print axioms Tm.Replay.isRec_of_blockOnly
#print axioms Tm.Replay.uncreditFx_blockOnly
#print axioms Tm.Replay.doneClose_blockOnly
#print axioms Tm.Replay.doneFx_blockOnly
#print axioms Tm.Replay.dayArm_ofBlock
#print axioms Tm.Replay.arm_split
#print axioms Tm.Replay.arm_filterMap_rec
#print axioms Tm.Replay.dayArm_safe
#print axioms Tm.Replay.sleptInv_apply
#print axioms Tm.Replay.sleptInv_applyEffects
#print axioms Tm.Replay.closeSub_pending
#print axioms Tm.Replay.closePause_pending
#print axioms Tm.Replay.closeSub_sleptOk
#print axioms Tm.Replay.closePause_sleptOk
#print axioms Tm.Replay.creditFx_sleptOk
#print axioms Tm.Replay.uncreditFx_sleptOk
#print axioms Tm.Replay.obsFx_sleptOk
#print axioms Tm.Replay.machine_sleptOk
#print axioms Tm.Replay.cut_sleptOk
#print axioms Tm.Replay.wentOn_fromStart
#print axioms Tm.Replay.doneClose_sleptOk
#print axioms Tm.Replay.doneFx_sleptOk
#print axioms Tm.Replay.dayArm_sleptOk
#print axioms Tm.Replay.completionArm_sleptOk
#print axioms Tm.Replay.resumeBlock_obs
#print axioms Tm.Replay.arm_sleptOk
#print axioms Tm.Replay.sleptInv_step
#print axioms Tm.Replay.sleptInv_foldl
#print axioms Tm.Replay.sleptInv_init
#print axioms Tm.Replay.insBy_perm
#print axioms Tm.Replay.insSort_perm
#print axioms Tm.Replay.isWake_eq_sleptOf
#print axioms Tm.Replay.sleptByDay_get
#print axioms Tm.Replay.energy_obs_slept_is_the_days_first_logged_sleep
#print axioms Tm.Replay.completionArm_noRec
#print axioms Tm.Replay.effectsWith_filterMap_rec
#print axioms Tm.Replay.applyEffects_longestLeak
#print axioms Tm.Replay.dayArm_leaks
#print axioms Tm.Replay.the_first_leak_maximum_wins
#print axioms Tm.Replay.leakLt_trans
#print axioms Tm.Replay.leakLt_skip
#print axioms Tm.Replay.the_longest_leak_is_the_first_of_the_longest
#print axioms Tm.Replay.applyEffects_records
#print axioms Tm.Replay.dayArm_records
#print axioms Tm.Replay.stepWith_records
#print axioms Tm.Replay.foldl_stepWith_records
#print axioms Tm.Replay.the_demotions_are_the_survivors_demotes_in_file_order
#print axioms Tm.Replay.the_closes_are_the_survivors_closes_in_file_order
#print axioms Tm.Replay.the_unknown_count_is_the_surviving_unknown_events
#print axioms Tm.Replay.a_demote_stamp_reads_the_week_or_date_key
#print axioms Tm.Replay.the_days_wake_is_its_first_logged_wake
#print axioms Tm.Replay.an_energy_line_before_its_wake_reads_the_wakes_sleep
#print axioms Tm.Replay.a_gap_is_on_the_day_it_began
#print axioms Tm.Replay.a_day_keeps_its_first_arrival_its_highest_replans_and_its_last_plan
#print axioms Tm.Replay.a_break_lasts_its_actual_minutes_else_its_planned
#print axioms Tm.Replay.the_first_of_equal_leaks_is_the_longest
#print axioms Tm.Replay.the_demote_stamps_of_a_week_a_date_and_a_month_key
#print axioms Tm.Replay.an_undo_of_a_close_cancels_its_own_period_and_an_older_one_still_cancels_the_latest
#print axioms Tm.Replay.the_calendar_today_is_not_the_replays_day_after_midnight
#print axioms Tm.Replay.idle_and_idle_since_read_different_orders

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C6 (design §8.2, §8.4, §11, §14.4 row C6): every line's header
-- (the survivors' `header` effects and the second pass over the cancelled lines, `entryHeaders` compiled as its
-- fast twin), the seams (`Effect.seam`, fork `DaySeam`), the observations in file order, `Effect.day?` and
-- `Key.date?`, and §8.4's view (`replayDoc`, `factsView`, `ask`, and the wire's grouping `dayOuts`, `winOuts`,
-- `itemOuts`) in Replay.lean; the `log` op's `facts` as the view and its headers with day, mask bit and display
-- in Boundary.lean (a header of a tail from any line but 1 refused by name).  The C6 goals were added to Goals.lean
-- and discharged in the step: `every_dated_output_names_its_day_key` (for every effect) and
-- `observations_are_in_file_order`, refuted as stated (`observations_are_not_in_file_order_when_a_line_repeats`)
-- and proved on increasing lines (`observations_are_in_file_order_on_increasing_lines`).  C5's owed equation:
-- `a_days_last_t_is_the_latest_stamp_of_its_survivors`.  Audited under C1–C5 and re-proved over the seam effect
-- and the new fields (names unchanged): `valueAt_applyEffect`, `every_known_event_has_an_arm`, `safe_apply`,
-- `conserves_step`, `an_extend_changes_only_the_bookkeeping_and_its_extended_minutes` (its key list gains the
-- seam's day), `stepWith_lastDone`, `stepWith_named`, `stepWith_doneDates`, the replay-warning step,
-- `sleptInv_step`, `effectsWith_filterMap_rec`, `the_log_op_reads_a_four_line_tail` (now from line 1),
-- `the_response_shapes_emit_in_build_order`, `logAnswer_facts` (restated over the view) and the five wire
-- witnesses `the_log_op_answers_*` (re-probed over the view).
#print axioms Tm.Replay.entryHeaders_eq_entryHeadersFast
#print axioms Tm.Replay.entryHeaders_length
#print axioms Tm.Replay.headerOf?_of_not_isHeader
#print axioms Tm.Replay.applyEffects_headers
#print axioms Tm.Replay.effectsWith_headers
#print axioms Tm.Replay.foldl_stepWith_headers
#print axioms Tm.Replay.the_survivors_headers_are_the_uncancelled_entry_headers
#print axioms Tm.Replay.the_two_header_passes_are_every_entrys_header
#print axioms Tm.Replay.seamOp_lastT
#print axioms Tm.Replay.applyEffects_seam_lastT
#print axioms Tm.Replay.dayArm_noSeam
#print axioms Tm.Replay.arm_noSeam
#print axioms Tm.Replay.completionArm_noSeam
#print axioms Tm.Replay.effectsWith_seams
#print axioms Tm.Replay.foldl_stepWith_seam_lastT
#print axioms Tm.Replay.a_days_last_t_is_the_latest_stamp_of_its_survivors
#print axioms Tm.Replay.every_dated_output_names_its_day_key
#print axioms Tm.Replay.every_leak_is_on_a_day_its_idle_record_names
#print axioms Tm.Replay.applyEffects_obs
#print axioms Tm.Replay.closeSub_obs
#print axioms Tm.Replay.closePause_obs
#print axioms Tm.Replay.creditFx_obs
#print axioms Tm.Replay.uncreditFx_obs
#print axioms Tm.Replay.obsFx_obs
#print axioms Tm.Replay.cut_obs
#print axioms Tm.Replay.doneClose_obs
#print axioms Tm.Replay.doneFx_obs
#print axioms Tm.Replay.dayArm_obs
#print axioms Tm.Replay.arm_obs
#print axioms Tm.Replay.completionArm_obs
#print axioms Tm.Replay.stepWith_obs
#print axioms Tm.Replay.foldl_stepWith_obs
#print axioms Tm.Replay.sublist_nodup_of_pairwise_lt
#print axioms Tm.Replay.survivors_lines_pairwise
#print axioms Tm.Replay.observations_are_not_in_file_order_when_a_line_repeats
#print axioms Tm.Replay.observations_are_in_file_order_on_increasing_lines
#print axioms Tm.Replay.ask_reads_the_facts
#print axioms Tm.Replay.replayDoc_eq_replayDocFast
#print axioms Tm.Replay.a_days_seam_holds_its_break_its_marks_and_its_latest_stamp
#print axioms Tm.Replay.the_since_break_anchor_is_the_first_start_without_a_break
#print axioms Tm.Replay.every_line_has_a_header_and_a_cancelled_one_is_marked
#print axioms Tm.Replay.a_start_observation_is_in_its_starts_place
#print axioms Tm.Replay.the_view_reads_a_small_log

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C7 (design §7.3, §14.4 row C7): the undo law in Replay.lean.
-- `undosFor` (what `tm undo` appends: one `undo{of: tag, id: primary id}` per event, most recent first) and
-- `untouchedBy`; the mask's half (`undoing_a_command_leaves_the_survivors_of_the_log_without_it`); the view reads only
-- the survivors, whatever its maps' bucket counts (`SameReadings`, `HMap.Keyed`, `HMap.perm_keys_pairs`,
-- `the_view_reads_only_the_survivors`).  The C7 goals were added to Goals.lean and discharged in the step:
-- `undoing_a_command_replays_the_log_without_it` (without §15's unused `hl`), `undo_of_a_silent_verb_cancels_an_older_event`
-- and `undo_after_housekeeping_cancels_the_housekeeping`, with the refutation twin in the law's conclusion
-- (`the_undo_law_fails_without_untouchedBy`) and quirk Q6(d)'s law and separation beside them.
#print axioms Tm.Replay.matches_its_own_undo
#print axioms Tm.Replay.foldl_maskStep_of_no_undo
#print axioms Tm.Replay.foldl_maskStep_undos
#print axioms Tm.Replay.undoing_a_command_leaves_the_survivors_of_the_log_without_it
#print axioms Tm.Replay.sameReadings_init
#print axioms Tm.Replay.SameReadings.apply
#print axioms Tm.Replay.SameReadings.applyEffects
#print axioms Tm.Replay.SameReadings.stepWith
#print axioms Tm.Replay.SameReadings.foldl
#print axioms Tm.Replay.KMap.mem_alterGo
#print axioms Tm.Replay.KMap.mem_alter
#print axioms Tm.Replay.KMap.nodup_alterGo
#print axioms Tm.Replay.KMap.nodup_alter
#print axioms Tm.Replay.HMap.keyed_empty
#print axioms Tm.Replay.HMap.keyed_alter
#print axioms Tm.Replay.HMap.keyed_mapVals
#print axioms Tm.Replay.HMap.mem_foldl_pairs
#print axioms Tm.Replay.HMap.nodup_foldl_pairs
#print axioms Tm.Replay.HMap.nodup_keys_pairs
#print axioms Tm.Replay.HMap.mem_keys_pairs_iff
#print axioms Tm.Replay.HMap.perm_keys_pairs
#print axioms Tm.Replay.HMap.keys_pairs_mapVals
#print axioms Tm.Replay.minDay?_perm
#print axioms Tm.Replay.maxDay?_perm
#print axioms Tm.Replay.pairsKeyed_init
#print axioms Tm.Replay.PairsKeyed.apply
#print axioms Tm.Replay.PairsKeyed.foldl
#print axioms Tm.Replay.doneKeys_filter
#print axioms Tm.Replay.doneCount_filter
#print axioms Tm.Replay.factsView_finish_of_sameReadings
#print axioms Tm.Replay.the_view_reads_only_the_survivors
#print axioms Tm.Replay.undoing_a_command_replays_the_log_without_it
#print axioms Tm.Replay.undoing_the_last_command_replays_the_log_without_it
#print axioms Tm.Replay.undoing_a_command_answers_every_fact_query_as_the_log_without_it
#print axioms Tm.Replay.a_silent_verb_undo_cancels_the_latest_event_of_its_name
#print axioms Tm.Replay.a_silent_verb_undo_cancels_nothing_iff_no_survivor_has_its_name
#print axioms Tm.Replay.move_toList
#print axioms Tm.Replay.undo_of_a_silent_verb_cancels_an_older_event
#print axioms Tm.Replay.undo_after_housekeeping_cancels_the_housekeeping
#print axioms Tm.Replay.the_undo_law_fails_without_untouchedBy
#print axioms Tm.Replay.a_done_undone_over_an_automatic_close_is_untouched

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W1 (design §9.2, §10.4, §14.5 row W1, §15 W block): the new module
-- Seal.lean.  The codec library (a round trip per combinator, for every value), the record codecs, the checkpoint's
-- keyed codec and law 10 (`readCkpt_emitCkpt`, `readDayRecord_emitDayRecord`, `readWindowRecord_emitWindowRecord`, each
-- with its smart-decoder converse and iff), R10 (`Ckpt.wf_bounds`, the missing-field refusal, `mkPolicy?`), the horizon
-- (`the_horizon_is_at_most_thirty_days_back`), carried note 1 (`the_answer_reads_the_replays_longest_leak`) and the
-- specification's ties to the replay (`replay_eq_finish_foldedState`, `entryHeaders_eq_foldedHeaders`,
-- `the_answer_reads_the_replays_scalar_facts`), and nine decided witnesses.  The sixteen W goals entered Goals.lean and
-- stay there until W2 (the burn-down rises 13 -> 29); nothing here depends on them.
#print axioms Tm.Seal.cNat_nonnull
#print axioms Tm.Seal.cStr_nonnull
#print axioms Tm.Seal.foldl_listStep_map
#print axioms Tm.Seal.cList_nonnull
#print axioms Tm.Seal.cTuple_nonnull
#print axioms Tm.Seal.cIso_nonnull
#print axioms Tm.Seal.cBool_nonnull
#print axioms Tm.Seal.cFin_nonnull
#print axioms Tm.Seal.cPair_nonnull
#print axioms Tm.Seal.cInstant_nonnull
#print axioms Tm.Seal.cAt_nonnull
#print axioms Tm.Seal.cVInstant_nonnull
#print axioms Tm.Seal.cVOffset_nonnull
#print axioms Tm.Seal.cNum_nonnull
#print axioms Tm.Seal.cEnergyObs_nonnull
#print axioms Tm.Seal.cLeakRec_nonnull
#print axioms Tm.Seal.cStamp_nonnull
#print axioms Tm.Seal.cDayAcc_nonnull
#print axioms Tm.Seal.cItemAcc_nonnull
#print axioms Tm.Seal.cBlock_nonnull
#print axioms Tm.Seal.cCut_nonnull
#print axioms Tm.Seal.cOpenInt_nonnull
#print axioms Tm.Seal.cSeamAcc_nonnull
#print axioms Tm.Seal.pos_enc
#print axioms Tm.Seal.key_enc
#print axioms Tm.Seal.ok_bind
#print axioms Tm.Seal.err_bind
#print axioms Tm.Seal.key_ne
#print axioms Tm.Seal.readDayFields_emit
#print axioms Tm.Seal.readDayRecord_emitDayRecord
#print axioms Tm.Seal.readDayRecord_wf
#print axioms Tm.Seal.readDayRecord_emitDayRecord_iff
#print axioms Tm.Seal.readWindowFields_emit
#print axioms Tm.Seal.readWindowRecord_emitWindowRecord
#print axioms Tm.Seal.readWindowRecord_wf
#print axioms Tm.Seal.readWindowRecord_emitWindowRecord_iff
#print axioms Tm.Seal.readCkptFields_emit
#print axioms Tm.Seal.readCkpt_emitCkpt
#print axioms Tm.Seal.readCkpt_wf
#print axioms Tm.Seal.readCkpt_emitCkpt_iff
#print axioms Tm.Seal.readCkpt_refuses_a_checkpoint_without_its_ledgerDay
#print axioms Tm.Seal.mkPolicy?_refuses_keepDays_past_31
#print axioms Tm.Seal.mkPolicy?_refuses_maxLine_past_2_40
#print axioms Tm.Seal.horizonOf_le
#print axioms Tm.Seal.the_horizon_is_at_most_thirty_days_back
#print axioms Tm.Seal.replay_eq_finish_foldedState
#print axioms Tm.Seal.entryHeaders_eq_foldedHeaders
#print axioms Tm.Seal.the_answer_reads_the_replays_longest_leak
#print axioms Tm.Seal.the_answer_reads_the_replays_scalar_facts
#print axioms Tm.Seal.orElse_eq_none
#print axioms Tm.Seal.check_eq_none
#print axioms Tm.Seal.Ckpt.wf_bounds
#print axioms Tm.Seal.the_checkpoint_of_nothing_is_the_empty_checkpoint
#print axioms Tm.Seal.the_empty_checkpoint_is_wf
#print axioms Tm.Seal.a_log_sealed_anywhere_answers_as_its_replay
#print axioms Tm.Seal.the_last_done_outlives_the_seal_of_its_days
#print axioms Tm.Seal.a_checkpoint_carries_the_last_cut
#print axioms Tm.Seal.the_horizon_of_2026_09_14
#print axioms Tm.Seal.an_undo_is_settled_when_its_target_is_folded_or_absent
#print axioms Tm.Seal.an_unfolded_undo_of_a_sealed_day_is_not_sealable
#print axioms Tm.Seal.a_future_dated_line_sets_the_future_floor
#print axioms Tm.Seal.sealed_and_live_observations_on_a_start_across_the_seal
#print axioms Tm.Seal.the_round_trips_are_not_vacuous

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 1 (design §9.5 laws 1 and 11, §14.5 row W2, §15 W block):
-- the new module SealLaw.lean.  Law 1's four goals and law 11 discharged under their names, with their companions
-- (law 1 needs neither `contiguousFrom` nor `sealable`; law 11 needs `contiguousFrom`), and the canonical-list,
-- keyed-map, stable-sort and observation-line lemmas beneath them.
#print axioms Tm.Seal.StrictTotal.eq_of_not
#print axioms Tm.Seal.StrictTotal.asymm
#print axioms Tm.Seal.mem_insUniq
#print axioms Tm.Seal.sorted_insUniq
#print axioms Tm.Seal.mem_foldl_insUniq
#print axioms Tm.Seal.sorted_foldl_insUniq
#print axioms Tm.Seal.mem_canon
#print axioms Tm.Seal.sorted_canon
#print axioms Tm.Seal.nodup_of_sorted
#print axioms Tm.Seal.nodup_canon
#print axioms Tm.Seal.eq_of_sorted_of_mem_iff
#print axioms Tm.Seal.canon_eq_of_mem_iff
#print axioms Tm.Seal.natLt_strictTotal
#print axioms Tm.Seal.charsLt_trans
#print axioms Tm.Seal.charsLt_total
#print axioms Tm.Seal.idLt_strictTotal
#print axioms Tm.Seal.lexLt_strictTotal
#print axioms Tm.Seal.optLt_strictTotal
#print axioms Tm.Seal.instKeyLt_strictTotal
#print axioms Tm.Seal.namedKeyLt_strictTotal
#print axioms Tm.Seal.find?_filterMap_of_nodup
#print axioms Tm.Seal.find?_map_filter_of_nodup
#print axioms Tm.Seal.allKeyed_init
#print axioms Tm.Seal.AllKeyed.apply
#print axioms Tm.Seal.AllKeyed.applyEffects
#print axioms Tm.Seal.AllKeyed.foldl
#print axioms Tm.Seal.allKeyed_foldedState
#print axioms Tm.Seal.get_eq_none_of_not_mem_keys
#print axioms Tm.Seal.mem_keys_of_get
#print axioms Tm.Seal.insBy_nil'
#print axioms Tm.Seal.insBy_cons'
#print axioms Tm.Seal.insSort_cons'
#print axioms Tm.Seal.insBy_of_all
#print axioms Tm.Seal.insBy_filter
#print axioms Tm.Seal.insBy_sorted
#print axioms Tm.Seal.insSort_sorted
#print axioms Tm.Seal.insSort_filter
#print axioms Tm.Seal.obsLe_trans
#print axioms Tm.Seal.obsLe_total
#print axioms Tm.Seal.sortObs_filter
#print axioms Tm.Seal.filter_day_eq_nil
#print axioms Tm.Seal.not_mem_dayKeys
#print axioms Tm.Seal.pendingOn_eq
#print axioms Tm.Seal.dayRead_state
#print axioms Tm.Seal.findDay_days
#print axioms Tm.Seal.get_filterMap_find
#print axioms Tm.Seal.not_mem_winKeys
#print axioms Tm.Seal.pair_not_mem_keys
#print axioms Tm.Seal.winRead_state
#print axioms Tm.Seal.findWin_windows
#print axioms Tm.Seal.find?_map_of_nodup
#print axioms Tm.Seal.not_mem_itemIds
#print axioms Tm.Seal.findItem_items
#print axioms Tm.Seal.doneDays_nil_of_not_mem
#print axioms Tm.Seal.items_read_state
#print axioms Tm.Seal.others_read_state
#print axioms Tm.Seal.scalars_read_state
#print axioms Tm.Seal.ckptOf_eq
#print axioms Tm.Seal.answer_ledgerDay
#print axioms Tm.Seal.answer_horizon
#print axioms Tm.Seal.answer_days
#print axioms Tm.Seal.answer_window
#print axioms Tm.Seal.answer_items
#print axioms Tm.Seal.answer_instOther
#print axioms Tm.Seal.answer_named
#print axioms Tm.Seal.answer_openBlock
#print axioms Tm.Seal.answer_openInterrupt
#print axioms Tm.Seal.answer_lastDay
#print axioms Tm.Seal.answer_lastEffective
#print axioms Tm.Seal.answer_entryCount
#print axioms Tm.Seal.answer_unknown
#print axioms Tm.Seal.answer_longestLeak
#print axioms Tm.Seal.answer_rwarns
#print axioms Tm.Seal.answer_reads_state
#print axioms Tm.Seal.day_records_read_state
#print axioms Tm.Seal.window_records_read_state
#print axioms Tm.Seal.replayLines_eq
#print axioms Tm.Seal.ckptOf_nil
#print axioms Tm.Seal.answer_reads_the_replay
#print axioms Tm.Seal.day_record_is_the_replays_day
#print axioms Tm.Seal.window_record_is_the_replays_window
#print axioms Tm.Seal.partition_is_the_replay
#print axioms Tm.Seal.Line.entry_line
#print axioms Tm.Seal.lineEntries_pairwise
#print axioms Tm.Seal.arm_durations_nil
#print axioms Tm.Seal.arm_obs_one
#print axioms Tm.Seal.stepWith_obs_one
#print axioms Tm.Seal.foldl_stepWith_obs_one
#print axioms Tm.Seal.foldedSurvivors_sublist
#print axioms Tm.Seal.foldedState_obs_nodup
#print axioms Tm.Seal.perm_flatMap_pointwise
#print axioms Tm.Seal.flatMap_append_perm
#print axioms Tm.Seal.flatMap_map_eq
#print axioms Tm.Seal.map_flatMap_eq
#print axioms Tm.Seal.sum_ite_mem
#print axioms Tm.Seal.perm_flatMap_filter
#print axioms Tm.Seal.eq_of_perm_of_pairwise_lt
#print axioms Tm.Seal.sortByLine_sorted
#print axioms Tm.Seal.sortByLine_eq_of_perm
#print axioms Tm.Seal.mem_dayKeys_energy
#print axioms Tm.Seal.mem_dayKeys_durations
#print axioms Tm.Seal.mem_dayKeys_pending
#print axioms Tm.Seal.obs_perm_state
#print axioms Tm.Seal.observations_read_state
#print axioms Tm.Seal.observations_read_lines
#print axioms Tm.Seal.the_answer_reads_the_replay
#print axioms Tm.Seal.a_day_record_is_the_replays_day
#print axioms Tm.Seal.a_window_record_is_the_replays_window
#print axioms Tm.Seal.seal_partition_is_the_replay
#print axioms Tm.Seal.sealed_and_live_observations_are_the_replays

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 2 (design §9.3 the guards, §9.5 laws 2, 3 and 8 and the
-- `now` anchor, §14.5 row W2, §15 W block): the new modules SealResume.lean (resume, G0–G4, the restored state and
-- the resumed answer; definitions only) through SealLaw2F.lean.  Law 2 (`resume_is_replay`, through the codec round
-- trips as rewrites), law 3, the `now` anchor, law 8 and its pair discharged under their names, with the route
-- beneath them: the mask splits under G1 (SealMask), the index agrees at folded instants and at or after the head
-- second (SealIndex), a step reads the index only at its queries (SealStep), late binding commutes with the fold
-- (SealRebind), a common effect keeps two states agreeing above the horizons (SealAgree), the restored state agrees
-- with the folded one (SealRestore), and the grouped answer is the whole log's (SealGroup, SealAgg, SealAgg2,
-- SealHeaders, SealLaw2A–2D).
#print axioms Tm.Seal.closeSub_congr
#print axioms Tm.Seal.closePause_congr
#print axioms Tm.Seal.closeSub_blockPaused
#print axioms Tm.Seal.cut_congr
#print axioms Tm.Seal.doneClose_congr
#print axioms Tm.Seal.arm_congr
#print axioms Tm.Seal.effectsWith_congr
#print axioms Tm.Seal.foldl_stepWith_congr
#print axioms Tm.Seal.stepQueries_sub
#print axioms Tm.Seal.closeSub_mi
#print axioms Tm.Seal.closePause_mi
#print axioms Tm.Seal.cut_mi
#print axioms Tm.Seal.doneFx_machines
#print axioms Tm.Seal.resumeBlock_since
#print axioms Tm.Seal.resumeBlock_pausedAt
#print axioms Tm.Seal.arm_mi
#print axioms Tm.Seal.stepWith_mi
#print axioms Tm.Seal.foldQueries_sub
#print axioms Tm.Seal.foldl_mi
#print axioms Tm.Seal.applyEffect_rebind
#print axioms Tm.Seal.applyEffects_rebind
#print axioms Tm.Seal.rebind_of_sleptOk
#print axioms Tm.Seal.map_rebind_of_all
#print axioms Tm.Seal.arm_sl
#print axioms Tm.Seal.effectsWith_machine
#print axioms Tm.Seal.effectsWith_rebind
#print axioms Tm.Seal.pendingStart_step
#print axioms Tm.Seal.stepWith_rebind
#print axioms Tm.Seal.foldl_rebind
#print axioms Tm.Seal.pendingStart_foldl
#print axioms Tm.Seal.rebind_rebind
#print axioms Tm.Seal.localDate_ne_of_far
#print axioms Tm.Seal.duration_of_far
#print axioms Tm.Seal.ns_lt_of_wf
#print axioms Tm.Seal.dayOf_of_far
#print axioms Tm.Seal.localDate_lt_of_head
#print axioms Tm.Seal.dayOf_lt_of_head
#print axioms Tm.Seal.sortWakes_eq_of_perm
#print axioms Tm.Seal.sortWakes_of_sorted
#print axioms Tm.Seal.sortWakes_three
#print axioms Tm.Seal.dedupFrom_cons
#print axioms Tm.Seal.dedupFrom_nil
#print axioms Tm.Seal.dedupFrom_of_noRuns
#print axioms Tm.Seal.lastKept_cons
#print axioms Tm.Seal.noRuns_dedupFrom
#print axioms Tm.Seal.dedupFrom_dedupFrom
#print axioms Tm.Seal.noRuns_drop
#print axioms Tm.Seal.dedupFrom_far
#print axioms Tm.Seal.sec_le_of_le
#print axioms Tm.Seal.filter_sec_split
#print axioms Tm.Seal.storedWakes_suffix
#print axioms Tm.Seal.lastWakeLe_isSome
#print axioms Tm.Seal.lastWakeLe_append
#print axioms Tm.Seal.lastWakeLe_append_of_mem
#print axioms Tm.Seal.keptWakes_eq
#print axioms Tm.Seal.lastKept_append
#print axioms Tm.Seal.dedupFrom_append'
#print axioms Tm.Seal.lastKept_mem
#print axioms Tm.Seal.mem_of_mem_dedupFrom
#print axioms Tm.Seal.mem_sortWakes
#print axioms Tm.Seal.mem_keptWakes
#print axioms Tm.Seal.lt_of_lt_of_le'
#print axioms Tm.Seal.lt_of_far
#print axioms Tm.Seal.far_of_lt_of_far
#print axioms Tm.Seal.dayOf_folded_agrees
#print axioms Tm.Seal.storedWakes_append_of_ge
#print axioms Tm.Seal.noRuns_of_far_start
#print axioms Tm.Seal.dedupFrom_sorted
#print axioms Tm.Seal.storedWakes_nil
#print axioms Tm.Seal.storedWakes_ne_nil
#print axioms Tm.Seal.noRuns_storedWakes
#print axioms Tm.Seal.sorted_storedWakes
#print axioms Tm.Seal.lastKept_none_eq
#print axioms Tm.Seal.noRuns_nil_dedup
#print axioms Tm.Seal.dayOf_tail_agrees
#print axioms Tm.Seal.eraseP_filter_of_first
#print axioms Tm.Seal.eraseP_filter_of_first_not
#print axioms Tm.Seal.tag_kept_or_overflow
#print axioms Tm.Seal.stackOf_append
#print axioms Tm.Seal.settledStep_fst
#print axioms Tm.Seal.Split.push
#print axioms Tm.Seal.Split.eraseP
#print axioms Tm.Seal.Split.foldl
#print axioms Tm.Seal.Split.eq
#print axioms Tm.Seal.eraseP_eq_self_of_find?_none
#print axioms Tm.Seal.part1
#print axioms Tm.Seal.part2
#print axioms Tm.Seal.mem_foldl_maskStep'
#print axioms Tm.Seal.unsettled_append
#print axioms Tm.Seal.unsettled_reverse
#print axioms Tm.Seal.unsettled_of_lines
#print axioms Tm.Seal.settled_lines_sub
#print axioms Tm.Seal.survivors_append_split
#print axioms Tm.Seal.mem_zipIdx_fst
#print axioms Tm.Seal.survivors_append_of_g1
#print axioms Tm.Seal.filter_cons_day
#print axioms Tm.Seal.AgreeAbove.apply
#print axioms Tm.Seal.AgreeAbove.applyEffects
#print axioms Tm.Seal.AgreeAbove.stepWith
#print axioms Tm.Seal.AgreeAbove.foldl
#print axioms Tm.Seal.AgreeAbove.trans
#print axioms Tm.Seal.AgreeAbove.symm
#print axioms Tm.Seal.AgreeAbove.of_sameReadings
#print axioms Tm.Seal.AgreeAbove.rebind
#print axioms Tm.Seal.get_foldl_step
#print axioms Tm.Seal.get_writeOpt
#print axioms Tm.Seal.get_foldl_pairs
#print axioms Tm.Seal.find?_pairs_of_mem
#print axioms Tm.Seal.find?_pairs_none
#print axioms Tm.Seal.get_writeAll_empty
#print axioms Tm.Seal.find?_openDays
#print axioms Tm.Seal.openDays_days_nodup
#print axioms Tm.Seal.restore_days
#print axioms Tm.Seal.restore_seams
#print axioms Tm.Seal.items_ids_nodup
#print axioms Tm.Seal.find?_items
#print axioms Tm.Seal.restore_items
#print axioms Tm.Seal.restore_lastDone
#print axioms Tm.Seal.restore_dropped
#print axioms Tm.Seal.filterMap_pair_fst_sublist
#print axioms Tm.Seal.mem_filterMap_pair
#print axioms Tm.Seal.restore_named
#print axioms Tm.Seal.mem_windowsFrom
#print axioms Tm.Seal.mem_itemMin
#print axioms Tm.Seal.mem_winKeys_of_itemDay
#print axioms Tm.Seal.nodup_flatMap_keyed
#print axioms Tm.Seal.windows_days_nodup
#print axioms Tm.Seal.itemMin_ids_nodup
#print axioms Tm.Seal.restore_itemDays
#print axioms Tm.Seal.mem_doneIds
#print axioms Tm.Seal.mem_winKeys_of_doneDate
#print axioms Tm.Seal.restore_doneDates
#print axioms Tm.Seal.mem_windowInst
#print axioms Tm.Seal.mem_instOther
#print axioms Tm.Seal.mem_winKeys_of_inst
#print axioms Tm.Seal.restore_instances
#print axioms Tm.Seal.filter_flatMap_days
#print axioms Tm.Seal.dayKeys_filter_nodup
#print axioms Tm.Seal.mem_dayKeys_filter
#print axioms Tm.Seal.restore_list
#print axioms Tm.Seal.map_pair_of_fst
#print axioms Tm.Seal.ckpt_openDays
#print axioms Tm.Seal.ckpt_items
#print axioms Tm.Seal.ckpt_window
#print axioms Tm.Seal.ckpt_instOther
#print axioms Tm.Seal.ckpt_named
#print axioms Tm.Seal.ckpt_machine
#print axioms Tm.Seal.ckpt_lastEff
#print axioms Tm.Seal.ckpt_rwarns
#print axioms Tm.Seal.ckpt_longestLeak
#print axioms Tm.Seal.ckpt_unknown
#print axioms Tm.Seal.ckpt_ledgerDay
#print axioms Tm.Seal.openDays_flatMap
#print axioms Tm.Seal.restore_agrees
#print axioms Tm.Seal.tailFold_fst
#print axioms Tm.Seal.tailFold_snd
#print axioms Tm.Seal.orElse_none
#print axioms Tm.Seal.stepCheck_none
#print axioms Tm.Seal.headerCheck_none
#print axioms Tm.Seal.resumeRun_ok
#print axioms Tm.Seal.idx_eq_of_pairwise_lt
#print axioms Tm.Seal.getElem?_of_mem_zipIdx
#print axioms Tm.Seal.mem_survivors_iff_uncancelled
#print axioms Tm.Seal.kmap_get_eq
#print axioms Tm.Seal.get_storedSlept
#print axioms Tm.Seal.sleptByDay_append
#print axioms Tm.Seal.filterMap_congr'
#print axioms Tm.Seal.sleptByDay_congr
#print axioms Tm.Seal.foldedState_nil
#print axioms Tm.Seal.applyEffect_keeps_keys
#print axioms Tm.Seal.foldl_keeps_keys
#print axioms Tm.Seal.applyEffects_below
#print axioms Tm.Seal.foldl_below
#print axioms Tm.Seal.instant_lt_or_le
#print axioms Tm.Seal.foldl_max_spec
#print axioms Tm.Seal.maxInstant?_spec
#print axioms Tm.Seal.maxInstant?_none
#print axioms Tm.Seal.foldl_min_spec
#print axioms Tm.Seal.minInstant?_spec
#print axioms Tm.Seal.minInstant?_none
#print axioms Tm.Seal.sep_of_bounds
#print axioms Tm.Seal.canon_filter
#print axioms Tm.Seal.mem_keys_map_iff
#print axioms Tm.Seal.mem_map_iff_filter_ne_nil
#print axioms Tm.Seal.mem_ids_of_day
#print axioms Tm.Seal.mem_keys_filter_iff
#print axioms Tm.Seal.winKeys_filter_eq
#print axioms Tm.Seal.windowOf_eq
#print axioms Tm.Seal.windowsFrom_eq
#print axioms Tm.Seal.instOtherOf_eq
#print axioms Tm.Seal.namedOf_eq
#print axioms Tm.Seal.dayKeys_filter_eq
#print axioms Tm.Seal.openDayOf_eq
#print axioms Tm.Seal.daysFrom_eq
#print axioms Tm.Seal.minDay?_nil
#print axioms Tm.Seal.minDay?_cons
#print axioms Tm.Seal.minOpt_assoc
#print axioms Tm.Seal.minDay?_append
#print axioms Tm.Seal.minDay?_spec
#print axioms Tm.Seal.minDay?_none_iff
#print axioms Tm.Seal.minDay?_eq_of_mem_iff
#print axioms Tm.Seal.maxDay?_cons
#print axioms Tm.Seal.maxOpt_assoc
#print axioms Tm.Seal.maxDay?_append
#print axioms Tm.Seal.maxDay?_spec
#print axioms Tm.Seal.maxDay?_none_iff
#print axioms Tm.Seal.maxDay?_eq_of_mem_iff
#print axioms Tm.Seal.storedHeaders_filter
#print axioms Tm.Seal.unsettled_cons
#print axioms Tm.Seal.tailHeaders_foldl
#print axioms Tm.Seal.tailHeaders_eq_spec
#print axioms Tm.Seal.mem_unsettled_sub
#print axioms Tm.Seal.tailHeadersSpec_eq
#print axioms Tm.Seal.mem_datesOf
#print axioms Tm.Seal.datesOf_nodup
#print axioms Tm.Seal.length_eq_of_mem_iff
#print axioms Tm.Seal.length_filter_split
#print axioms Tm.Seal.dates_union
#print axioms Tm.Seal.doneFirst_union
#print axioms Tm.Seal.doneCount_union
#print axioms Tm.Seal.lastDay_union
#print axioms Tm.Seal.mem_itemIds_iff
#print axioms Tm.Seal.ckpt_tagLast
#print axioms Tm.Seal.ckpt_tagOverflow
#print axioms Tm.Seal.ckpt_settled
#print axioms Tm.Seal.ckpt_maxT
#print axioms Tm.Seal.ckpt_futureFloor
#print axioms Tm.Seal.ckpt_wakes
#print axioms Tm.Seal.ckpt_sleptByDay
#print axioms Tm.Seal.ckpt_ledgerDay'
#print axioms Tm.Seal.wakeInstants_append
#print axioms Tm.Seal.mem_wakeInstants
#print axioms Tm.Seal.mem_foldQueries
#print axioms Tm.Seal.entryInstants_ns
#print axioms Tm.Seal.resume_survivors
#print axioms Tm.Seal.resume_sep
#print axioms Tm.Seal.resume_fold_congr
#print axioms Tm.Seal.rebindState_init
#print axioms Tm.Seal.Effect.key_rebind
#print axioms Tm.Seal.effectsWith_keys
#print axioms Tm.Seal.pendingStart_init
#print axioms Tm.Seal.keyed_foldl_step
#print axioms Tm.Seal.keyed_writeOpt
#print axioms Tm.Seal.keyed_writeAll
#print axioms Tm.Seal.get_foldl_alter_of_not_mem
#print axioms Tm.Seal.get_foldl_writeOpt_of_not_mem
#print axioms Tm.Seal.allKeyed_restore
#print axioms Tm.Seal.AllKeyed.rebind
#print axioms Tm.Seal.openDayOf_day
#print axioms Tm.Seal.windowOf_day
#print axioms Tm.Seal.restore_below
#print axioms Tm.Seal.AgreeAbove.refl
#print axioms Tm.Seal.kmap_get_append
#print axioms Tm.Seal.foldedState_eq
#print axioms Tm.Seal.pendingStart_restore
#print axioms Tm.Seal.foldedSurvivors_nil
#print axioms Tm.Seal.foldedIndex_nil
#print axioms Tm.Seal.mem_foldedSurvivors_iff
#print axioms Tm.Seal.map_zipIdx_eq
#print axioms Tm.Seal.valueAt_day_get
#print axioms Tm.Seal.valueAt_doneDate_get
#print axioms Tm.Seal.resume_index
#print axioms Tm.Seal.resume_state_agrees
#print axioms Tm.Seal.ckpt_lastDay
#print axioms Tm.Seal.ckpt_entryCount
#print axioms Tm.Seal.ckpt_warnings
#print axioms Tm.Seal.ckpt_warnOverflow
#print axioms Tm.Seal.answer_ckptOfEntries
#print axioms Tm.Seal.take_take_append
#print axioms Tm.Seal.lineEntries_nil
#print axioms Tm.Seal.window_done_count
#print axioms Tm.Seal.aggMerged_eq
#print axioms Tm.Seal.itemAggOf_eq
#print axioms Tm.Seal.items_merged_eq
#print axioms Tm.Seal.resume_headers
#print axioms Tm.Seal.resume_answer_eq
#print axioms Tm.Seal.resume_ok_run
#print axioms Tm.Seal.resume_answer_ignores_the_policy
#print axioms Tm.Seal.ys_mono
#print axioms Tm.Seal.monthStart_eq
#print axioms Tm.Seal.cumBefore_le_335
#print axioms Tm.Seal.monthStart_mono
#print axioms Tm.Seal.isoMonday_mono
#print axioms Tm.Seal.an_accepted_resume_covers_now
#print axioms Tm.Seal.horizonOf_zero
#print axioms Tm.Seal.keyAtOrAbove_zero
#print axioms Tm.Seal.g1_empty
#print axioms Tm.Seal.stepCheck_empty
#print axioms Tm.Seal.headerCheck_empty
#print axioms Tm.Seal.tailFold_empty
#print axioms Tm.Seal.resume_from_empty_never_refuses_by_guard
#print axioms Tm.Seal.resume_ok_answer
#print axioms Tm.Seal.readCkpt_emitCkpt_eq
#print axioms Tm.Seal.resume_is_replay
#print axioms Tm.Seal.resume_from_empty_is_replay
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 3 (design §9.5 laws 4 and 5, §15 W block): the new modules
-- SealReach.lean (law 5's spec side: reachFree on the whole list, tagsClear as G1 on the specification's tags),
-- SealLaw5A.lean and SealLaw5B.lean (acceptance both ways; the resume's steps against the whole log's, from either
-- side's head checks), SealPending.lean (a fold's pending start observation) and SealLaw4.lean (the whole log reads as
-- the folded lines below the horizons).  Laws 4 and 5 discharged under their names.
#print axioms Tm.Seal.foldAll_iff
#print axioms Tm.Seal.foldAll_eq_true
#print axioms Tm.Seal.tagsClear_iff
#print axioms Tm.Seal.contiguousFrom_append
#print axioms Tm.Seal.head_of_contiguousFrom
#print axioms Tm.Seal.stepCheck_eq_none
#print axioms Tm.Seal.tailFold_none_of
#print axioms Tm.Seal.headerCheck_none_of
#print axioms Tm.Seal.resumeRun_isOk_of
#print axioms Tm.Seal.index_facts
#print axioms Tm.Seal.folded_part_agrees
#print axioms Tm.Seal.steps_agree
#print axioms Tm.Seal.congr_of_spec
#print axioms Tm.Seal.maxInstant?_mem
#print axioms Tm.Seal.minInstant?_mem
#print axioms Tm.Seal.resume_isOk_eq
#print axioms Tm.Seal.isOk_iff_exists
#print axioms Tm.Seal.foldAll_append_vacuous
#print axioms Tm.Seal.reachFree_iff
#print axioms Tm.Seal.reachFree_of_accepted
#print axioms Tm.Seal.accepted_of_reachFree
#print axioms Tm.Seal.resume_ok_iff
#print axioms Tm.Seal.pending_none_of_pendLines
#print axioms Tm.Seal.arm_pending
#print axioms Tm.Seal.stepWith_pending
#print axioms Tm.Seal.foldl_pending
#print axioms Tm.Seal.AgreeBelow.symm
#print axioms Tm.Seal.pendingOn_below
#print axioms Tm.Seal.not_mem_pending_below
#print axioms Tm.Seal.winKeys_filter_below
#print axioms Tm.Seal.windowOf_below
#print axioms Tm.Seal.windowsIn_below
#print axioms Tm.Seal.dayKeys_filter_below
#print axioms Tm.Seal.openDayOf_below
#print axioms Tm.Seal.daysIn_below
#print axioms Tm.Seal.valueAt_day_view
#print axioms Tm.Seal.valueAt_itemDay_get
#print axioms Tm.Seal.valueAt_instDate_get
#print axioms Tm.Seal.filter_fst_eq_of_snd
#print axioms Tm.Seal.foldl_frame
#print axioms Tm.Seal.filter_rebind_below
#print axioms Tm.Seal.resume_below
#print axioms Tm.Seal.resume_keeps_the_sealed_records
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, in-step theorems (§14.5's W2 row): SealInStep.lean.  The stored
-- wakes' two edge cases, the fence's day-index law at three days with the two-day margin refuted on a two-transition
-- zone, a spurious G1 refusal, and a resume without the guards that is not the replay.
#print axioms Tm.Seal.an_instant_before_the_stored_wakes_is_sealed
#print axioms Tm.Seal.keptWakes_eq_nil
#print axioms Tm.Seal.dayOf_with_no_folded_wake_reads_the_tail
#print axioms Tm.Seal.dayOf_agrees_three_days_before
#print axioms Tm.Seal.a_spurious_tag_refusal_exists
#print axioms Tm.Seal.resume_without_the_guards_is_not_replay
#print axioms Tm.Seal.the_window_at_the_horizon_reads_the_replay
#print axioms Tm.Seal.dayOf_agrees_two_days_before_is_false
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 4b (design §9.4 the reseal, §9.5 law 6's pair, §14.5 row
-- W2's in-step theorems): SealFoldPoint.lean (the fold point is the greatest valid cut; an unterminated line is never
-- folded), SealLaw6Pair.lean (a reseal never seals past now), and the reseal's route at the cut: SealCutBounds.lean
-- (maxT, futureFloor), SealCutMask.lean (lines, folded survivors, undo targets), SealCutStep.lean (an undo past the cut
-- never reaches the folded lines; the folded lines' own mask; the settled undos), SealCutTags.lean (tag lines merge),
-- SealCutWakes.lean (stored wakes).
#print axioms Tm.Seal.foldl_last_valid
#print axioms Tm.Seal.getLast?_ge_of_sorted
#print axioms Tm.Seal.greatestValid_spec
#print axioms Tm.Seal.foldPoint_eq
#print axioms Tm.Seal.sealDay_eq
#print axioms Tm.Seal.foldPoint_valid
#print axioms Tm.Seal.foldPoint_greatest
#print axioms Tm.Seal.resealOf_some
#print axioms Tm.Seal.resume_some_reseal
#print axioms Tm.Seal.cutOk_parts
#print axioms Tm.Seal.the_unterminated_segment_is_never_folded
#print axioms Tm.Seal.foldl_min_le
#print axioms Tm.Seal.floorOf_le
#print axioms Tm.Seal.max_foldl_min_bound
#print axioms Tm.Seal.sealDayOf_bound
#print axioms Tm.Seal.le_sealDayOf
#print axioms Tm.Seal.a_reseal_never_seals_past_now
#print axioms Tm.Seal.instant_antisymm
#print axioms Tm.Seal.maxInstant?_some_of_ne_nil
#print axioms Tm.Seal.minInstant?_some_of_ne_nil
#print axioms Tm.Seal.maxInstant?_append
#print axioms Tm.Seal.minInstant?_append
#print axioms Tm.Seal.isFuture_migrates
#print axioms Tm.Seal.resealed_maxT
#print axioms Tm.Seal.resealed_futureFloor
#print axioms Tm.Seal.lineEntries_ge
#print axioms Tm.Seal.lineEntries_take
#print axioms Tm.Seal.lineEntries_drop
#print axioms Tm.Seal.foldedSurvivors_eq_filter
#print axioms Tm.Seal.foldedSurvivors_at_cut
#print axioms Tm.Seal.dangling_misses_the_folded
#print axioms Tm.Seal.undoTargets_eq
#print axioms Tm.Seal.undoStep_fst
#print axioms Tm.Seal.undoStep_snd_mono
#print axioms Tm.Seal.mem_undoTargets
#print axioms Tm.Seal.split_stackOf
#print axioms Tm.Seal.find?_split
#print axioms Tm.Seal.settled_lines_mono
#print axioms Tm.Seal.settled_prefix_lines
#print axioms Tm.Seal.foldl_maskStep_filter
#print axioms Tm.Seal.g1_prefix
#print axioms Tm.Seal.dangles_of_no_match
#print axioms Tm.Seal.unsettled_split_at
#print axioms Tm.Seal.cut_step_past
#print axioms Tm.Seal.cut_step_within
#print axioms Tm.Seal.cut_step
#print axioms Tm.Seal.survivors_at_cut
#print axioms Tm.Seal.dangleStep_fst
#print axioms Tm.Seal.settledStep_fst_one
#print axioms Tm.Seal.mem_of_mem_dangling
#print axioms Tm.Seal.cut_find_past
#print axioms Tm.Seal.cut_find_within
#print axioms Tm.Seal.cut_find_eq
#print axioms Tm.Seal.stackOf_snoc
#print axioms Tm.Seal.settled_at_cut
#print axioms Tm.Seal.tagLines_eq
#print axioms Tm.Seal.foldl_line_of_ne_nil
#print axioms Tm.Seal.lastLineOf_append
#print axioms Tm.Seal.find?_eq_of_mem_nodup
#print axioms Tm.Seal.find?_map_key
#print axioms Tm.Seal.tagLines_find
#print axioms Tm.Seal.tagLines_fst
#print axioms Tm.Seal.tagLines_append
#print axioms Tm.Seal.take_filter_of_prefix
#print axioms Tm.Seal.mem_take_iff_count
#print axioms Tm.Seal.headSec_mono
#print axioms Tm.Seal.storedWakes_prefix_absorb
#print axioms Tm.Seal.storedWakes_storedWakes
#print axioms Tm.Seal.lastKept_eq_getLast
#print axioms Tm.Seal.dedupFrom_far_noRuns
#print axioms Tm.Seal.getLast?_storedWakes
#print axioms Tm.Seal.storedWakes_at_cut
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 4c (design §9.4 the reseal, §9.5 laws 6 and 7):
-- SealLaw6.lean (a reseal is a seal; a resealed checkpoint accepts its own suffix), through SealRsDefs.lean (the
-- reseal's parts, named), SealLaw6Ctx.lean (an accepted resume and a valid cut as entries), SealLaw6Ckpt.lean (the
-- checkpoint and records at the cut), SealLaw6Seal.lean (sealable, and the reach condition, at the new ledger day), and
-- the route: SealCutState.lean (the state at the cut), SealCutHeaders.lean (headers; the unfolded lines cancel nothing
-- folded), SealCutSlept.lean (the stored slept_by_day), SealCutTags2.lean (the truncated tags merge), SealCutMachine.lean
-- (a fold's machine days), SealCutLows.lean (what bounds the new ledger day; a warning's line), SealCutGroup.lean (groups
-- at a later ledger day), SealCutSteps.lean (the unfolded steps), SealTagsSelf.lean (a checkpoint's own suffix leaves no
-- undo dangling).
#print axioms Tm.Seal.kmap_get_isSome_of_mem
#print axioms Tm.Seal.mem_storedSlept_keys
#print axioms Tm.Seal.storedSlept_congr
#print axioms Tm.Seal.mem_keys_iff_get
#print axioms Tm.Seal.storedSlept_congr_get
#print axioms Tm.Seal.cut_index_agrees
#print axioms Tm.Seal.restore_fold_mi
#print axioms Tm.Seal.cut_state_agrees
#print axioms Tm.Seal.closeSub_keeps
#print axioms Tm.Seal.closePause_keeps
#print axioms Tm.Seal.cut_keeps
#print axioms Tm.Seal.arm_lastCut
#print axioms Tm.Seal.arm_interrupt
#print axioms Tm.Seal.stepWith_machine_eq
#print axioms Tm.Seal.stepWith_machineDays
#print axioms Tm.Seal.foldl_machineDays
#print axioms Tm.Seal.keepTags_eq
#print axioms Tm.Seal.keptTags_eq_keepTags
#print axioms Tm.Seal.shortUnknown_key
#print axioms Tm.Seal.tagSorted_map
#print axioms Tm.Seal.tagSorted_tagLines
#print axioms Tm.Seal.tagSorted_merge
#print axioms Tm.Seal.find?_key_of_mem
#print axioms Tm.Seal.mem_tagLines_fst
#print axioms Tm.Seal.mem_merge_fst
#print axioms Tm.Seal.merge_filter_old
#print axioms Tm.Seal.keptBy_iff
#print axioms Tm.Seal.count_below_mono
#print axioms Tm.Seal.keptBy_filter
#print axioms Tm.Seal.keepTags_filter
#print axioms Tm.Seal.tag_line_exists
#print axioms Tm.Seal.merge_first_kept
#print axioms Tm.Seal.merge_kept_in
#print axioms Tm.Seal.keptTags_append
#print axioms Tm.Seal.length_keepTags_lt_iff
#print axioms Tm.Seal.tagOverflow_append
#print axioms Tm.Seal.foldedIndex_congr_er
#print axioms Tm.Seal.foldedState_congr_er
#print axioms Tm.Seal.cancelledAt_congr_er
#print axioms Tm.Seal.foldedHeaders_congr_er
#print axioms Tm.Seal.length_foldedHeaders
#print axioms Tm.Seal.foldedHeaders_at_cut
#print axioms Tm.Seal.stepLows_eq
#print axioms Tm.Seal.lowsStep_mono
#print axioms Tm.Seal.mem_lows
#print axioms Tm.Seal.foldl_min_le_of_mem
#print axioms Tm.Seal.sealDayOf_le_max
#print axioms Tm.Seal.filter_line_split
#print axioms Tm.Seal.survivors_sublist
#print axioms Tm.Seal.unsettled_sublist
#print axioms Tm.Seal.readObject_warn
#print axioms Tm.Seal.readValue_warn
#print axioms Tm.Seal.readLine_warn
#print axioms Tm.Seal.Line.warning_line
#print axioms Tm.Seal.lineWarnings_ge
#print axioms Tm.Seal.lineWarnings_take
#print axioms Tm.Seal.AgreeAbove.mono
#print axioms Tm.Seal.horizonOf_mono
#print axioms Tm.Seal.daysFrom_eq_raw
#print axioms Tm.Seal.daysIn_eq_filter
#print axioms Tm.Seal.windowsIn_eq_filter
#print axioms Tm.Seal.items_merged_eq_raw
#print axioms Tm.Seal.settledStep_snd
#print axioms Tm.Seal.mem_settledOf_iff
#print axioms Tm.Seal.isUndo_iff
#print axioms Tm.Seal.maskStep_push
#print axioms Tm.Seal.dangleStep_push
#print axioms Tm.Seal.stackOf_filter_nil
#print axioms Tm.Seal.tail_dangle_inv
#print axioms Tm.Seal.dangling_unsettled_self
#print axioms Tm.Seal.tagsClear_self
#print axioms Tm.Seal.resume_steps
#print axioms Tm.Seal.keyAtOrAbove_later
#print axioms Tm.Seal.headSec_later
#print axioms Tm.Seal.unfoldedEffects_eq
#print axioms Tm.Seal.mem_collect
#print axioms Tm.Seal.survivors_split
#print axioms Tm.Seal.resealOf_eq
#print axioms Tm.Seal.resealOf_parts
#print axioms Tm.Seal.rs_context
#print axioms Tm.Seal.rs_state_parts
#print axioms Tm.Seal.rs_sealable_reachFree
#print axioms Tm.Seal.reseal_is_seal
#print axioms Tm.Seal.a_resealed_checkpoint_accepts_its_own_suffix
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 4d (design §9.7 genesis, §9.5 law 9): SealGenesis.lean
-- (the chunked rebuild with exact pops; definitions only), SealLaw9A.lean (a call's lines, the records' splits and
-- restrictions, records above an answer's horizons, the empty log sealable, the stack's pops, the chunks' ends),
-- SealLaw9B.lean (law 9's invariant; one accepted call through laws 2, 4, 6 and 7), SealLaw9.lean (genesis' loop keeps
-- the invariant; law 9).
#print axioms Tm.Seal.contiguousFrom_take
#print axioms Tm.Seal.genLines_append
#print axioms Tm.Seal.genLines_take
#print axioms Tm.Seal.genLines_drop
#print axioms Tm.Seal.length_genLines
#print axioms Tm.Seal.filter_range_split
#print axioms Tm.Seal.finish_day
#print axioms Tm.Seal.daysIn_split
#print axioms Tm.Seal.windowsIn_split
#print axioms Tm.Seal.dayRecordsBetween_split
#print axioms Tm.Seal.windowRecordsBetween_split
#print axioms Tm.Seal.daysIn_restrict
#print axioms Tm.Seal.windowsIn_restrict
#print axioms Tm.Seal.dayRecordsBetween_restrict
#print axioms Tm.Seal.windowRecordsBetween_restrict
#print axioms Tm.Seal.mem_daysIn_finish
#print axioms Tm.Seal.mem_windowsIn
#print axioms Tm.Seal.mem_dayRecordsBetween
#print axioms Tm.Seal.mem_windowRecordsBetween
#print axioms Tm.Seal.askMerged_extra
#print axioms Tm.Seal.sealable_empty
#print axioms Tm.Seal.popTo_sub
#print axioms Tm.Seal.popTo_ne_nil
#print axioms Tm.Seal.endsFrom_spec
#print axioms Tm.Seal.genOk_empty
#print axioms Tm.Seal.genesis_call
#print axioms Tm.Seal.genLoop_ok
#print axioms Tm.Seal.genEnds_spec
#print axioms Tm.Seal.chunked_genesis_is_one_replay

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W3 (design §9.6–§9.8, §10, §14.5 row W3): the window crosses the wire.
-- SealWire.lean (new): the downward fold-point scan and the compiled twins of `cutOk`, `resumeRun` and `resealOf`
-- (`@[csimp]`), the reseal's emitters and their read-back, the sealed input and its merge (`askMerged`), law 13's
-- numeral check.  Boundary.lean, section W3: the op's R10 rows, G0 at the op, the op as the resume, law 13, laws 8 and
-- 2 at the wire, three witnesses.  RETIRED with C6's string-tagged facts (their lines removed above, recorded in the
-- README's W3 block): logAnswer_facts, logAnswer_headers, LogReq.wf_facts_from_line_one,
-- mkLogReq?_refuses_facts_of_a_tail_without_a_checkpoint, LogReq.wf_headers_from_line_one,
-- mkLogReq?_refuses_headers_of_a_tail_without_a_checkpoint, logSectionWith_passes_its_zone,
-- the_log_op_answers_the_cancelled_lines, the_log_op_answers_every_entrys_day, the_log_op_answers_the_block_facts,
-- the_log_op_answers_the_completion_facts, the_log_op_answers_the_day_facts.
#print axioms Tm.Seal.greatestValid_succ
#print axioms Tm.Seal.greatestValid_eq_down
#print axioms Tm.Seal.cutOk_eq_cutOkFast
#print axioms Tm.Seal.resumeRun_eq_resumeRunFast
#print axioms Tm.Seal.resealOf_eq_resealOfFast
#print axioms Tm.Seal.cOpenBlock_nonnull
#print axioms Tm.Seal.cInterruption_nonnull
#print axioms Tm.Seal.findSome?_eq_none_all
#print axioms Tm.Seal.emitResealed_reads_back
#print axioms Tm.Seal.findDay_filter_append
#print axioms Tm.Seal.findWin_filter_append
#print axioms Tm.Seal.the_merged_days_read_as_askMerged
#print axioms Tm.Seal.the_merged_window_reads_as_askMerged
#print axioms Tm.Seal.answer_ckptOf_days_ge
#print axioms Tm.Seal.numeralBound_eq
#print axioms Tm.Seal.jnumsBelow_obj
#print axioms Tm.Seal.jnumsBelow_arr
#print axioms Tm.logLineStep_fold
#print axioms Tm.logLines_eq
#print axioms Tm.contiguousFrom_zipIdx
#print axioms Tm.logLines_contiguous
#print axioms Tm.LogReq.fault_of_b4_bounds
#print axioms Tm.mkLogReq?_refuses_keepDays_past_31
#print axioms Tm.mkLogReq?_refuses_maxLine_past_2_40
#print axioms Tm.policyOk_any
#print axioms Tm.mkLogReq?_refuses_a_sealed_input_out_of_bounds
#print axioms Tm.mkLogReq?_refuses_a_checkpoint_out_of_bounds
#print axioms Tm.mkLogReq?_refuses_a_resume_without_now
#print axioms Tm.LogReq.wf_resume_bounds
#print axioms Tm.readCkptField_refuses_what_readCkpt_refuses
#print axioms Tm.readLogReq_refuses_a_checkpoint_its_reader_refuses
#print axioms Tm.readSealedField_refuses_more_than_62_records
#print axioms Tm.logOp_refuses_a_checkpoint_of_another_zone
#print axioms Tm.logOp_refuses_a_tail_not_at_its_checkpoints_cut
#print axioms Tm.logOp_refuses_what_the_resume_refuses
#print axioms Tm.logOp_answers_through_the_resume
#print axioms Tm.logOp_reads_without_a_replay
#print axioms Tm.within53_ok
#print axioms Tm.within53_refuses_by_name
#print axioms Tm.the_log_op_emits_only_numerals_below_2_53
#print axioms Tm.the_log_op_checks_every_numeral
#print axioms Tm.the_log_op_emits_only_what_its_readers_read_back
#print axioms Tm.the_log_op_facts_from_genesis_are_the_replays
#print axioms Tm.the_log_op_facts_from_a_stored_checkpoint_are_the_replays
#print axioms Tm.the_log_op_names_its_resume_refusals
#print axioms Tm.the_log_op_refuses_a_count_past_2_53_by_its_key
#print axioms Tm.the_log_op_merges_a_sealed_day_below_its_ledger_day

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W4 (design §14.5 row W4, §19 K1/K23; W5's gate failed): the replay's
-- compiled twins where the profile put the time.  SealTwin.lean (new): `canonDesc` and the csimp twins of the grouping
-- functions over the checkpoint's four orders, the window facts grouped by date, the item tables, `mergedItems` and
-- `resumedAnswer`, and the day index by bisection (`bisect`, `offsetAtArr`, `dayOfZ`, `dayFn`).  SealWire.lean: the resume
-- over caller-read entries and warnings (`resumeRunV`) and building only what its request wants (`resumeRunW`), the cut
-- check with its fixed parts given (`cutCheckAt`), the state at the cut and the unfolded lows in one fold (`foldCut`), the
-- reseal over caller-read warnings (`resealOfV`).  Boundary.lean: the `log` op reading each line once (`logOpFast`).
#print axioms Tm.Seal.canon_eq_canonDesc
#print axioms Tm.Seal.itemIds_eq_itemIdsFast
#print axioms Tm.Seal.dayKeys_eq_dayKeysFast
#print axioms Tm.Seal.winKeys_eq_winKeysFast
#print axioms Tm.Seal.windowOf_eq_windowOfFast
#print axioms Tm.Seal.instOtherOf_eq_instOtherOfFast
#print axioms Tm.Seal.namedOf_eq_namedOfFast
#print axioms Tm.Seal.storedSlept_eq_storedSleptFast
#print axioms Tm.Seal.mergeTagLines_eq_mergeTagLinesFast
#print axioms Tm.Seal.daysIn_eq_daysInT
#print axioms Tm.Seal.daysFrom_eq_daysFromT
#print axioms Tm.Seal.mem_foldl_groupStep
#print axioms Tm.Seal.windowOfG_eq
#print axioms Tm.Seal.windowsIn_eq_windowsInG
#print axioms Tm.Seal.windowsFrom_eq_windowsFromG
#print axioms Tm.Seal.foldl_firstStep_get
#print axioms Tm.Seal.foldl_doneStep
#print axioms Tm.Seal.foldl_doneIdStep_get
#print axioms Tm.Seal.foldl_incr_get
#print axioms Tm.Seal.foldl_winStep_get
#print axioms Tm.Seal.aggMergedT_eq
#print axioms Tm.Seal.mergedItems_eq_mergedItemsFast
#print axioms Tm.Seal.resumedAnswer_eq_resumedAnswerFast
#print axioms Tm.Seal.bisect_spec
#print axioms Tm.Seal.foldl_last_of_point
#print axioms Tm.Seal.offsetAtArr_eq
#print axioms Tm.Seal.localDateArr_eq
#print axioms Tm.Seal.dayOfZ_eq
#print axioms Tm.Seal.instAscending_pairwise
#print axioms Tm.Seal.dayFn_eq
#print axioms Tm.Seal.resumeRunV_eq
#print axioms Tm.Seal.resumeRunW_eq
#print axioms Tm.Seal.foldl_badStep_all
#print axioms Tm.Seal.firstBadLine_all
#print axioms Tm.Seal.and8_perm
#print axioms Tm.Seal.cutCheckAt_eq
#print axioms Tm.Seal.foldl_lowsStep_of_not
#print axioms Tm.Seal.filter_split_of_pairwise
#print axioms Tm.Seal.foldCut_eq_foldCutFast
#print axioms Tm.Seal.resealOfWith_spec
#print axioms Tm.Seal.resealOfV_eq
#print axioms Tm.foldl_logLineStep_map_verdict
#print axioms Tm.logLines_map_verdict
#print axioms Tm.lineEntries_eq_verdicts
#print axioms Tm.lineWarnings_eq_verdicts
#print axioms Tm.logOpZ_core
#print axioms Tm.logOpCore_map
#print axioms Tm.logOpZFast_core
#print axioms Tm.logOpZ_eq_logOpZFast

-- APPENDED 2026-09-16 (stage 5, W-12).  Step S2 (owner decision D16; design §22.1's "a new step
-- after S", §14.7 F5): the kernel writes the log lines it reads.  `Log.emitEvent`/`Log.emitLine`
-- reuse the reader (`readArgs`) and the writer (`renderLine`) rather than adding a third
-- definition of the format; the `emit` section puts them on the wire.  11 theorems, in Log.lean
-- and Boundary.lean.
#print axioms Tm.Log.renderLine_ignores_the_line
#print axioms Tm.Log.restOf_cons_t_ev
#print axioms Tm.Log.restOf_of_canonical
#print axioms Tm.Log.emitEvent_of_fields
#print axioms Tm.Log.the_log_emits_what_it_reads
#print axioms Tm.Log.the_log_reads_what_it_emits
#print axioms Tm.Log.emitEvent_refuses_what_a_line_could_not_carry
#print axioms Tm.Log.the_kernel_decides_what_is_left_out
#print axioms Tm.runWithEmit_without_an_emit_is_runWithLog
#print axioms Tm.a_request_without_an_emit_is_read_as_before
#print axioms Tm.runWithEmit_refuses_an_emit_section_first

-- APPENDED 2026-09-16 (stage 5, W-12).  Quirk **Q6(f)** (gap 86; owner answer Q6's last column,
-- "fix, after the switch"): a `close` carries `period:key` as its primary id, so `tm undo` of one
-- cancels *that* close and not whichever close is latest.  The quirk's own theorem is renamed in
-- place above, beside the rule it replaces
-- (`an_undo_of_a_close_cancels_its_own_period_and_an_older_one_still_cancels_the_latest`), and the
-- undo law's counterexample is re-witnessed rather than weakened.
#print axioms Tm.Replay.an_automatic_close_of_another_period_is_untouched

-- APPENDED 2026-09-16 (stage 6, W-13, track B).  **D24, gap 210: the seam is opened inside the
-- kernel.**  The `log` op now answers a `LogAnswer` — the bytes it always answered, and the
-- `Seal.Answer` those bytes were rendered from — and `runCapZ` hands that replay to the capacity
-- section, which could not previously reach it (`readCapacityZ` had no argument it could arrive
-- through).  `logOp` is kept as the bytes half, a *view* of `logOpZ`, so every law stated about it
-- before D24 keeps its exact text and its audit line above: the three W4 twin rows are the only
-- renames, and they are renamed in place (`logOpZ_core`, `logOpZFast_core`,
-- `logOpZ_eq_logOpZFast`), the `@[csimp]` now carrying the seam's fourth argument.
--
-- Re-proved over their current shapes, NOT weakened (D5), and audited by their standing lines
-- above: `readLogSection_is_zoneOf_then_logSectionWith` (3180) and
-- `runCap_without_capacity_is_runWithEmit` (3133) are **unchanged, word for word**;
-- `the_zone_is_read_once_and_feeds_both_sections` (3182) is **strengthened** — its capacity
-- conjunct now quantifies over the replay as well (`∀ plan clock rep cap`), so the old statement
-- is its `rep = none` instance and it says strictly more.
--
-- The seam's own laws follow.  `a_capacity_answer_can_depend_on_a_log_fact` is the one that makes
-- the parameter load-bearing rather than decorative (AGENTS §5.2, §5.6): its two `decide`
-- witnesses were probed under `MemoryMax=8G`, `timeout 120`.
#print axioms Tm.within53A_wire
#print axioms Tm.logAnswerOf_carries_the_op
#print axioms Tm.the_capacity_section_reads_the_log_sections_own_replay
#print axioms Tm.runCap_reads_the_capacity_section_against_its_own_log_answer
#print axioms Tm.Look.mkInput?_ok_wake_wf
#print axioms Tm.CapWire.wakeClockOf_sec_lt
#print axioms Tm.CapWire.wakeClockOf_wf
#print axioms Tm.CapWire.resolve_fromLog_without_a_replay
#print axioms Tm.CapWire.resolve_fromLog_without_a_day
#print axioms Tm.CapWire.readCapacityZ_refuses_a_logged_wake_without_a_replay
#print axioms Tm.CapWire.the_capacity_input_is_the_replays_wake
#print axioms Tm.CapWire.a_capacity_answer_can_depend_on_a_log_fact

-- ===========================================================================
-- APPENDED 2026-09-16 (stage 6, run W-13, step **L9** — day 0 is the kernel's
-- own; design §13.5, gap 93).  `Look.Input.day0` and the `badDay0` refusal are
-- **gone**: the kernel derives today from its own replay through D24's seam.
--
-- Two rows above were RENAMED with their theorems, not deleted:
-- `lookahead_day_zero_is_the_hosts` -> `lookahead_day_zero_is_the_kernels`
-- (restated: day 0 is `ofHist I.today (day0Hist I)`), and
-- `mkInput?_refuses_a_bad_day0` -> `mkInput?_refuses_a_now_that_disagrees`
-- (the refusal `badDay0` existed to raise is gone; `nowDisagrees` takes its
-- place in the same position of the constructor's order).
--
-- Site R10 lands here **with its caller** (`Look.todayEnergy`), which is why
-- W-6 and W-12 both refused to land it alone (AGENTS §5.6, §7.4 items 5, 11).
#print axioms Tm.Arith.roundAway_withinOne
#print axioms Tm.Arith.roundAway_mono
#print axioms Tm.Arith.roundAway_examples
#print axioms Tm.Look.predictAt_val
#print axioms Tm.Look.latestBefore_sound
#print axioms Tm.Look.latestBefore_none_of_all_after
#print axioms Tm.Look.weightAt_full
#print axioms Tm.Look.weightAt_zero
#print axioms Tm.Look.correctAt_without_a_report
#print axioms Tm.Look.the_posterior_rounds_a_half_the_way_the_fork_does
#print axioms Tm.Look.day0_slots_are_inside_the_window
#print axioms Tm.Look.day0_slots_avoid_the_walls
#print axioms Tm.Look.day0_after_the_window_is_empty
#print axioms Tm.Look.day0Six_get
#print axioms Tm.Look.the_day_zero_histogram_is_not_limited_to_the_budget
#print axioms Tm.Look.day_zero_is_the_spec_day_energised
#print axioms Tm.Look.day_zero_is_cut_from_now
#print axioms Tm.Look.day_zero_reads_the_stored_window
#print axioms Tm.Look.todays_posterior_moves_todays_levels
#print axioms Tm.Look.a_short_night_shifts_every_level
#print axioms Tm.Look.day_zero_reads_todays_location
#print axioms Tm.Look.weightAt_antitone
#print axioms Tm.CapWire.boundedPos_zero_den
#print axioms Tm.CapWire.boundedPos_wide_den
#print axioms Tm.CapWire.boundedPos_large_num
#print axioms Tm.CapWire.boundedPos_ok

-- ===========================================================================
-- APPENDED 2026-09-16 (stage 6, run **W-13 repair**, defect 1 — the nine
-- theorems step L9 declared and did not audit).
--
-- AGENTS §6.3 gives two ways to end a step: append the audit lines, **or**
-- record the omission by name in the README block.  `5ab24bf` did neither, and
-- its block said the opposite twice ("New theorems: **26**, every one with an
-- audit line").  The three §6.3 counts read 3984 / 3984 / **3993** at that
-- commit; they reconciled exactly at `0585e72`, `f9ee3d0` and `455ac8d`.
--
-- The nine are helper lemmas — nothing imports `Goals.lean` and check 3 finds
-- no `sorryAx`, so this was never a soundness hole; the audit was simply nine
-- short while the printed count said healthy.  That is gap 260's shape exactly
-- (the audit has a count, not a roster), and check 3 now carries the §6.3
-- reconciliation so a declared theorem can no longer go unaudited in silence.
#print axioms Tm.Arith.Signed.den_pos
#print axioms Tm.Arith.halfUpQ_of_zero_num
#print axioms Tm.Arith.roundAway_withinOne_aux
#print axioms Tm.Arith.roundAway_mono_aux
#print axioms Tm.Look.keepsIt_le
#print axioms Tm.Look.latestBefore_nil
#print axioms Tm.Look.latestBefore_go
#print axioms Tm.Look.SleepCfg.shiftOf_without_sleep
#print axioms Tm.Look.day0Cut_eq

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-14**, track P step **P0** — the
-- planner's vocabulary: `Planner.lean`, `Seg` on absolute seconds, `PlanReq`
-- without a second window).
--
-- Fifty-six theorems: R10's smart constructors and their rejections, R11's
-- `view ∘ set = id` pairs, the two `Look.Today` budget laws L9's `storedWindow`
-- needed beside it, and `dayPlan`'s shape.
--
-- Two of them were TRIPWIRES and were meant to stop compiling.  Step P1 took
-- the first one (`the_day_has_no_segments_until_the_first_step_lands`, deleted
-- with `dayPlan_diagnostics` and `dayPlan_assigns_nothing_yet`, which P1's body
-- made false); `the_plan_hash_is_a_placeholder_until_the_emitter_lands` still
-- stands and is P8's.  P1's own tripwire, in the block below, is
-- `the_day_assigns_nothing_after_now_until_the_assign_step_lands`.
-- ===========================================================================
#print axioms Tm.Look.Today.storedBudget_on_another_day
#print axioms Tm.Look.Today.storedBudget_today
#print axioms Tm.Look.Today.storedWindow_brings_a_budget
#print axioms Tm.Planner.Capped.ofList?_refuses_past_the_cap
#print axioms Tm.Planner.Capped.ofList?_accepts
#print axioms Tm.Planner.Capped.cons?_refuses_past_the_cap
#print axioms Tm.Planner.Capped.val_cons?
#print axioms Tm.Planner.mkBatch?_refuses_too_many_members
#print axioms Tm.Planner.mkBatch?_accepts
#print axioms Tm.Planner.mkSeg?_refuses_an_inverted_segment
#print axioms Tm.Planner.mkSeg?_refuses_past_the_horizon
#print axioms Tm.Planner.mkSeg?_accepts
#print axioms Tm.Planner.Seg.energy_withEnergy
#print axioms Tm.Planner.Seg.withEnergy_touches_only_the_energy
#print axioms Tm.Planner.Seg.wf_withEnergy
#print axioms Tm.Planner.Seg.note_withNote
#print axioms Tm.Planner.Seg.withNote_touches_only_the_note
#print axioms Tm.Planner.Seg.wf_withNote
#print axioms Tm.Planner.Diagnostics.notes_withNote
#print axioms Tm.Planner.Diagnostics.withNote_touches_only_the_notes
#print axioms Tm.Planner.Diagnostics.droppedTail_withDropped
#print axioms Tm.Planner.Diagnostics.withDropped_touches_only_the_dropped_tail
#print axioms Tm.Planner.mkHash?_refuses_a_short_digest
#print axioms Tm.Planner.mkHash?_refuses_a_non_hex_digit
#print axioms Tm.Planner.mkHash?_accepts
#print axioms Tm.Planner.mkBudget?_refuses_an_impossible_budget
#print axioms Tm.Planner.mkBudget?_accepts
#print axioms Tm.Planner.mkActive?_refuses_a_start_after_now
#print axioms Tm.Planner.mkActive?_refuses_an_estimate_past_the_day
#print axioms Tm.Planner.mkActive?_accepts
#print axioms Tm.Planner.mkBreak?_refuses_a_break_longer_than_a_day
#print axioms Tm.Planner.mkBreak?_refuses_a_start_after_now
#print axioms Tm.Planner.mkBreak?_accepts
#print axioms Tm.Planner.mkInterrupt?_refuses_a_start_after_now
#print axioms Tm.Planner.mkInterrupt?_accepts
#print axioms Tm.Planner.mkYesterday?_refuses_a_priority_past_seven
#print axioms Tm.Planner.mkYesterday?_refuses_too_many
#print axioms Tm.Planner.RuntimeIn.activeId_empty
#print axioms Tm.Planner.PlanOverrides.isEmpty_empty
#print axioms Tm.Planner.mkOverrides?_refuses_too_many_estimates
#print axioms Tm.Planner.mkOverrides?_refuses_too_many_drops
#print axioms Tm.Planner.assignedOf_empty
#print axioms Tm.Planner.blockSeconds_empty
#print axioms Tm.Planner.PlanReq.window_is_the_lookaheads
#print axioms Tm.Planner.PlanReq.budget_is_the_stored_one_when_there_is_one
#print axioms Tm.Planner.PlanReq.budget_is_the_formula_without_a_stored_one
#print axioms Tm.Planner.dayPlan_day
#print axioms Tm.Planner.dayPlan_window
#print axioms Tm.Planner.dayPlan_blockMin
#print axioms Tm.Planner.dayPlan_budgetBlocks
#print axioms Tm.Planner.the_plan_hash_is_a_placeholder_until_the_emitter_lands

-- ===========================================================================
-- STAGE 6, W-14 TRACK P, STEP P1 (2026-09-17): the walls
--
-- Appended for step P1 (design 14.2's P1 row): 8.2 step 1 in `Planner.lean`,
-- on the wall set stage 5 already indexes.  `Look.WallIx` is WIDENED, not
-- forked (AGENTS 5.3): it carries the item id it always had in scope and the
-- event's own start that `buffer:` used to fold away, and `Look.wallIxOn` is
-- `wallsOn`'s own selection with the projection left off, so the day's window,
-- the day's cut and the day's rows read ONE rule about which walls are today's.
--
-- Forty-one theorems.  Two are RUN rather than argued -- AGENTS 5.2's non-vacuity
-- check -- and two are findings named as such:
--
--   * `the_spec_days_walls_are_placed_where_they_are_written` and
--     `the_spec_days_clash_is_named_once` -- 8.2 step 1 evaluated on the 4.3
--     Monday with a `buffer:1h` meeting and a second one that clashes with it:
--     three rows at the six seconds the index wrote, and the pair named once.
--
--   * `plan_never_moves_a_wall_as_stage_6_wrote_it_is_refuted` -- the goal's
--     form is FALSE against the fork (a `buffer:` puts a second Wall row in
--     front of the event; a wall past midnight is clipped to the day), refuted
--     and restated with `plan_never_moves_a_wall` and
--     `a_wall_row_comes_from_the_index` beside it (AGENTS 3.1 item 3, D5).
--   * `the_day_assigns_nothing_after_now_until_the_assign_step_lands` -- the
--     TRIPWIRE P5 must delete.  Step 1 places no Block of its own, so
--     `plan_places_no_block_over_a_wall` is NOT discharged here: it is vacuous
--     over this body and design 6.4's row that gives it to P1 is wrong
--     (README gap 347).
--     [BANNER, W-17 track G: two names in this bullet have moved and the
--     sentence is left standing as the record of what was true when it was
--     written.  The tripwire is `Planner.the_day_assigns_nothing_after_now
--     _but_the_running_block` since step P3 (choice 5b's reservation made the
--     empty-list form false).  And `plan_places_no_block_over_a_wall` is
--     DISCHARGED as of W-17 -- still not by this body, which is what the
--     sentence says, but as `PlanCheck.plan_places_no_block_over_a_wall`, over
--     the Block rows that start at or after `now`, with its refutation in
--     `PlannerWit`.  See this file's last banner.]
-- ===========================================================================
#print axioms Tm.Look.mem_wallIxOn
#print axioms Tm.Look.wallsOn_eq_map_wallIxOn
#print axioms Tm.Look.wallOfEntity_lo_is_evLo_without_a_buffer
#print axioms Tm.Look.wallOfEntity_keeps_the_id
#print axioms Tm.Look.wallOfEntity_evLo_is_the_written_start
#print axioms Tm.Planner.Capped.ofListTake_keeps_everything_below_the_cap
#print axioms Tm.Planner.Capped.ofListTake_is_a_prefix
#print axioms Tm.Planner.mem_assignedOf
#print axioms Tm.Planner.a_wall_is_not_work
#print axioms Tm.Planner.instant_wf_of_sec
#print axioms Tm.Planner.the_horizon_is_cal_instants_own_bound
#print axioms Tm.Planner.Seg.wf_of
#print axioms Tm.Planner.clampSec_lt
#print axioms Tm.Planner.clampSec_id
#print axioms Tm.Planner.segOf_is_the_row_inside_the_calendar
#print axioms Tm.Planner.segOf_kind
#print axioms Tm.Planner.segOf_item
#print axioms Tm.Planner.wallsToday_is_wallsOfDay
#print axioms Tm.Planner.mem_wallsToday
#print axioms Tm.Planner.clipWall_id
#print axioms Tm.Planner.clipWall_within
#print axioms Tm.Planner.clipWall_id_inside
#print axioms Tm.Planner.the_spec_days_clash_is_named_once
#print axioms Tm.Planner.wallConflicts_nil
#print axioms Tm.Planner.mem_wallConflicts
#print axioms Tm.Planner.a_travel_day_has_no_budget
#print axioms Tm.Planner.remainingBudget_le_budget
#print axioms Tm.Planner.wallRows_are_walls_of_the_item
#print axioms Tm.Planner.the_event_row_is_the_event
#print axioms Tm.Planner.wallRows_without_a_buffer
#print axioms Tm.Planner.the_spec_days_walls_are_placed_where_they_are_written
#print axioms Tm.Planner.interruptRows_are_open_lost_time
#print axioms Tm.Planner.interruptRows_are_not_walls
#print axioms Tm.Planner.pastRows_end_at_now
#print axioms Tm.Planner.pastRows_are_not_walls
#print axioms Tm.Planner.sortRows_eq_sortRowsFast
#print axioms Tm.Planner.mem_sortRows
#print axioms Tm.Planner.mem_dayRows
#print axioms Tm.Planner.dayPlan_segments
#print axioms Tm.Planner.dayPlan_remaining_budget_is_the_forks_local
#print axioms Tm.Planner.plan_never_moves_a_wall_as_stage_6_wrote_it_is_refuted
#print axioms Tm.Planner.plan_never_moves_a_wall
#print axioms Tm.Planner.a_wall_row_comes_from_the_index

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-14**, track G — L26's eleven single-run
-- laws as one checker battery: `PlanCheck.lean`, design §6).
--
-- Fifty-nine theorems: the eleven reflection lemmas and their per-element
-- helpers, `checks_all` and the eleven one-line bridges a P step's discharge
-- will be, the fold induction's base case, the eleven non-vacuity witnesses
-- (AGENTS §5.2 — a battery that cannot refuse means nothing), and the list
-- arithmetic D29's refutation will apply.
--
-- ONE of them was a TRIPWIRE and IT FIRED.  `dayPlan_ok_core` is §6.1's lift
-- over the seven eligibility-free checks; track G proved it in one line over
-- P0's empty day, from
-- `Planner.the_day_has_no_segments_until_the_first_step_lands`.  P1 deleted that
-- theorem, and the LAND step (W-14, gaps 385-389) re-proved the lift over the
-- day P1 produces.  It could not be re-proved unchanged: the form track G wrote
-- is FALSE of the filled day, twice over -- the replayed past holds Blocks the
-- planner did not place, and `wallsUnmoved` is the form P1 refuted (`buffer:`,
-- the midnight clip).  NO CHECKER WAS WEAKENED; the two findings are carried as
-- named hypotheses (`hnopast`, `hagree`/`hplain`), exactly as P1 carried them on
-- `plan_never_moves_a_wall`.  Gap 385 is the record, and two theorems were added
-- beside the lift (`dayPlan_block_rows_come_from_the_log`, unconditional, and
-- `dayPlan_has_no_block_row`).
--
-- `dayPlan_ok_at_every_eligibility_while_the_day_is_empty` is GONE, and its name
-- is why: it was stated about a day with no segments and P1's day has some.  It
-- loses nothing -- `planOk_of_no_segments` is the general lemma and stays.
--
-- **No goal was discharged here** — see `Goals.lean`'s stage-6 header and
-- `PlanCheck.lean`'s own.
-- ===========================================================================
#print axioms Tm.PlanCheck.withoutActive_segments
#print axioms Tm.PlanCheck.noOverbook_iff
#print axioms Tm.PlanCheck.oneBlockAtATime_iff
#print axioms Tm.PlanCheck.energyOk_iff
#print axioms Tm.PlanCheck.energyFilterOk_iff
#print axioms Tm.PlanCheck.noBlockOverAWall_iff
#print axioms Tm.PlanCheck.noBlockOverABreak_iff
#print axioms Tm.PlanCheck.windDownOk_iff
#print axioms Tm.PlanCheck.noDemandingAfterWindDown_iff
#print axioms Tm.PlanCheck.wallUnmoved_iff
#print axioms Tm.PlanCheck.wallsUnmoved_iff
#print axioms Tm.PlanCheck.rankPairOk_iff
#print axioms Tm.PlanCheck.hotPairOk_iff
#print axioms Tm.PlanCheck.impossibleKept_iff
#print axioms Tm.PlanCheck.batchPairOk_iff
#print axioms Tm.PlanCheck.checksOf_length
#print axioms Tm.PlanCheck.checksCore_length
#print axioms Tm.PlanCheck.checks_all
#print axioms Tm.PlanCheck.checksCore_all
#print axioms Tm.PlanCheck.planOk_imp_core
#print axioms Tm.PlanCheck.overbook_from_the_battery
#print axioms Tm.PlanCheck.one_block_from_the_battery
#print axioms Tm.PlanCheck.energy_filter_from_the_battery
#print axioms Tm.PlanCheck.no_block_over_a_wall_from_the_battery
#print axioms Tm.PlanCheck.no_block_over_a_break_from_the_battery
#print axioms Tm.PlanCheck.wind_down_from_the_battery
#print axioms Tm.PlanCheck.walls_unmoved_from_the_battery
#print axioms Tm.PlanCheck.monotone_in_rank_from_the_battery
#print axioms Tm.PlanCheck.hot_before_queue_from_the_battery
#print axioms Tm.PlanCheck.impossible_kept_from_the_battery
#print axioms Tm.PlanCheck.mem_dom_of_get
#print axioms Tm.PlanCheck.assignedOf_of_no_segments
#print axioms Tm.PlanCheck.eligibleSomewhere_of_no_segments
#print axioms Tm.PlanCheck.planOkCore_of_no_segments
#print axioms Tm.PlanCheck.planOk_of_no_segments
#print axioms Tm.PlanCheck.a_replayed_row_is_a_row_of_the_day
#print axioms Tm.PlanCheck.a_replayed_block_is_assigned
#print axioms Tm.PlanCheck.dayPlan_has_no_block_row
#print axioms Tm.PlanCheck.dayPlan_ok_core
#print axioms Tm.PlanCheck.all_eq_false_of_mem
#print axioms Tm.PlanCheck.wSeg_wf
#print axioms Tm.PlanCheck.horizonOk
#print axioms Tm.PlanCheck.wDay_segments
#print axioms Tm.PlanCheck.effectiveCi_of_an_absent_id
#print axioms Tm.PlanCheck.aBlockOfAnHour_is_not_the_reservation
#print axioms Tm.PlanCheck.noOverbook_can_fail
#print axioms Tm.PlanCheck.oneBlockAtATime_can_fail
#print axioms Tm.PlanCheck.energyFilterOk_can_fail
#print axioms Tm.PlanCheck.noBlockOverAWall_can_fail
#print axioms Tm.PlanCheck.noBlockOverABreak_can_fail
#print axioms Tm.PlanCheck.noDemandingAfterWindDown_can_fail
#print axioms Tm.PlanCheck.wallsUnmoved_can_fail
#print axioms Tm.PlanCheck.assignedOf_theOnlyJIsAssignedDay
#print axioms Tm.PlanCheck.eligibleSomewhere_permissive
#print axioms Tm.PlanCheck.monotoneInRank_can_fail
#print axioms Tm.PlanCheck.hotBeforeQueue_can_fail
#print axioms Tm.PlanCheck.assignedOf_theBatchDay
#print axioms Tm.PlanCheck.batchDoesNotReachPast_can_fail
#print axioms Tm.PlanCheck.impossibleKept_can_fail
#print axioms Tm.PlanCheck.planOkCore_can_fail
#print axioms Tm.PlanCheck.planOk_can_fail
#print axioms Tm.PlanCheck.a_kept_reservation_defeats_the_prefix_but_not_the_erasure

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-15**, track P, step P2 — §8.2 step 2:
-- the routines, the evening, and gap 285's named refusal).
--
-- Thirty-two theorems.  Three are `Lookahead.lean`'s: `[day]` was WIDENED with
-- §16's `wind_down` and `bed` rather than forked into `Planner.lean`, and the
-- three `the_evening_keys_do_not_move_…` lines are the projections that say
-- every reader `DayCfg` had before P2 sees the record it had before P2
-- (AGENTS §5.3).  The rest are the step's own: the placement engine on L3's
-- `freeIntervals`, `mkRoutine?`'s five named refusals (the second of which IS
-- README gap 285), the fold invariant that a placed routine is inside its
-- window, and the four "no row step 2 places is a Wall / a Block / work"
-- lemmas that let P1's laws keep their proofs over a day with a fourth source
-- of rows.
--
-- One line above was EDITED rather than appended: `Tm.Planner.mem_stepOneRows`
-- is `Tm.Planner.mem_dayRows`, because the day's rows are no longer step one's
-- alone.  §6.3 forbids editing this file in *parallel*; a rename leaves check 3
-- naming an unknown constant, so it is fixed here and named in the README block.
-- ===========================================================================

#print axioms Tm.Look.the_evening_keys_do_not_move_the_window
#print axioms Tm.Look.the_evening_keys_do_not_move_the_cut
#print axioms Tm.Look.the_evening_keys_do_not_move_the_budget
#print axioms Tm.Planner.the_night_is_in_order
#print axioms Tm.Planner.earliestFree_inside
#print axioms Tm.Planner.earliestFree_is_free
#print axioms Tm.Planner.overlapsAny_false_covers_nothing
#print axioms Tm.Planner.overlapsAny_true_of_covered
#print axioms Tm.Planner.mkRoutine?_refuses_an_unknown_item
#print axioms Tm.Planner.mkRoutine?_refuses_a_window_the_item_does_not_declare
#print axioms Tm.Planner.mkRoutine?_refuses_an_empty_window
#print axioms Tm.Planner.mkRoutine?_refuses_past_the_horizon
#print axioms Tm.Planner.mkRoutine?_refuses_an_instance_with_no_minutes
#print axioms Tm.Planner.mkRoutine?_accepts
#print axioms Tm.Planner.mkRoutine?_ok_is_wf
#print axioms Tm.Planner.mkRoutines?_refuses_too_many
#print axioms Tm.Planner.mkRoutines?_refuses_when_one_is_refused
#print axioms Tm.Planner.isSleepId_accepts_the_written_spellings
#print axioms Tm.Planner.splitSleep_keeps_the_rest
#print axioms Tm.Planner.mem_sortRoutines
#print axioms Tm.Planner.placeStep_keeps_PlacedOk
#print axioms Tm.Planner.foldl_placeStep_keeps_PlacedOk
#print axioms Tm.Planner.a_placed_routine_is_inside_its_window
#print axioms Tm.Planner.stepTwoSegs_kinds
#print axioms Tm.Planner.stepTwoSegs_are_not_walls
#print axioms Tm.Planner.stepTwoSegs_are_not_blocks
#print axioms Tm.Planner.stepTwoSegs_are_not_work
#print axioms Tm.Planner.a_routine_row_is_where_the_placement_put_it
#print axioms Tm.Planner.the_wind_down_row_runs_to_bed
#print axioms Tm.Planner.the_earliest_free_position_is_run
#print axioms Tm.Planner.the_evening_is_closed_to_a_routine
#print axioms Tm.Planner.a_deferred_routine_has_no_row
-- W-15 track K, K3a (D31, gap 301): the item grammar widened — the state box
-- is optional and an id-less line is keyed by its title (`Field.titleKey`).
-- `Tm.parseLine` is the store's reading; `Tm.parseItem` stays the file's.
#print axioms Tm.an_unflagged_optional_is_open
#print axioms Tm.an_unflagged_routine_is_open
#print axioms Tm.bareOk_all
#print axioms Tm.bareOk_any
#print axioms Tm.bareOk_mk
#print axioms Tm.boxAt_box
#print axioms Tm.boxAt_eq_some
#print axioms Tm.boxAt_none_of_head
#print axioms Tm.canonicalKeyed_of_canonical
#print axioms Tm.Field.findSome_kParent_phase0
#print axioms Tm.Field.kinds_bare
#print axioms Tm.Field.kinds_boxed
#print axioms Tm.parseBody_bare
#print axioms Tm.parseBody_bare_head
#print axioms Tm.parseBody_bare_of_noBox
#print axioms Tm.parseBody_boxed
#print axioms Tm.parseLine_ok
#print axioms Tm.parseToks_ok
#print axioms Tm.serialize_parse_id
#print axioms Tm.serialize_parseLine
#print axioms Tm.the_flag_is_still_read_off_a_week_line
#print axioms Tm.the_spec_routine_line_is_a_title_keyed_item
#print axioms Tm.the_spec_routine_line_round_trips
#print axioms Tm.Field.titleKey_congr
#print axioms Tm.tokBare_head
#print axioms Tm.tokBare_sep
#print axioms Tm.a_boxless_line_cannot_carry_a_state
#print axioms Tm.a_boxless_todo_line_is_well_formed
#print axioms Tm.boxesWf_set
#print axioms Tm.boxWf_of_mem
#print axioms Tm.Field.setKey_boxed
#print axioms Tm.setVal_boxed
#print axioms Tm.a_routine_line_is_an_item
#print axioms Tm.an_optional_line_is_keyed_by_its_whole_title
#print axioms Tm.a_bare_line_has_no_positional_slots
#print axioms Tm.an_empty_bullet_is_prose
#print axioms Tm.a_front_matter_rule_is_prose
#print axioms Tm.a_line_with_a_bracket_is_not_a_bare_item
#print axioms Tm.a_bare_line_may_carry_its_id
#print axioms Tm.the_three_refusals_are_unchanged
#print axioms Tm.effectiveScope
#print axioms Tm.a_routine_line_loads_as_an_entity
#print axioms Tm.two_titles_in_one_file_are_a_dupId
#print axioms Tm.a_title_colliding_with_an_id_is_refused
#print axioms Tm.parseLine_serializeItem
/-! ############################################################################
## Stage 6, track W (run W-15): the `PlanReq` builder and its witnesses
`TmKernel/PlannerWit.lean` — README gap 348, and the three gaps it blocked (366's
refutation half, 393's witness half, 396).  Nothing imports this module; it is the
end-to-end witness `Planner.lean` and `PlanCheck.lean` could not write.
############################################################################ -/
#print axioms Tm.PlannerWit.mkPlanReq?_refuses_a_plan_the_loader_refuses
#print axioms Tm.PlannerWit.mkPlanReq?_refuses_an_input_the_decoder_refuses
#print axioms Tm.PlannerWit.mkPlanReq?_refuses_a_wall_index_that_is_not_the_plans
#print axioms Tm.PlannerWit.mkPlanReq?_refuses_a_run_the_guards_refuse
#print axioms Tm.PlannerWit.mkPlanReq?_refuses_a_zero_denominator
#print axioms Tm.PlannerWit.mkPlanReq?_ok_wallsAgree
#print axioms Tm.PlannerWit.mkPlanReq?_ok_parts
#print axioms Tm.PlannerWit.witInput_decodes_ok
#print axioms Tm.PlannerWit.witInput_decodes
#print axioms Tm.PlannerWit.witInput_fields
#print axioms Tm.PlannerWit.lookWallPlan_loads
#print axioms Tm.PlannerWit.witRun_resumes_ok
#print axioms Tm.PlannerWit.witRun_resumes
#print axioms Tm.PlannerWit.witCaps_ok
#print axioms Tm.PlannerWit.witCaps_eq
#print axioms Tm.PlannerWit.witBuilds
#print axioms Tm.PlannerWit.theRequest_wallsAgree
#print axioms Tm.PlannerWit.the_witness_day_is_two_replayed_blocks_the_written_wall_and_the_evening
#print axioms Tm.PlannerWit.the_witness_day_is_planned_from_two_in_the_afternoon
#print axioms Tm.PlannerWit.the_witness_assigns_the_two_replayed_blocks
#print axioms Tm.PlannerWit.the_witness_assigns_nothing_after_now
#print axioms Tm.PlannerWit.the_battery_passes_at_the_witness
#print axioms Tm.PlannerWit.the_witness_replays_a_block
#print axioms Tm.PlannerWit.the_witness_defeats_the_lifts_hypothesis
#print axioms Tm.PlannerWit.the_battery_bites_at_the_witness
#print axioms Tm.PlannerWit.witRun0_resumes_ok
#print axioms Tm.PlannerWit.witRun0_resumes
#print axioms Tm.PlannerWit.witBuilds0
#print axioms Tm.PlannerWit.the_quiet_day_assigns_nothing
#print axioms Tm.PlannerWit.the_budget_does_not_reach_the_assigned_set_until_the_assign_fold_lands

#print axioms Tm.PlannerWit.plan_tail_drop_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin
#print axioms Tm.PlannerWit.erasing_the_active_item_does_not_repair_a_law_whose_run_is_free

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-15**, the LAND step — the two
-- theorems the merge of tracks K, P and W had to add, plus one rename).
--
-- The rename is `Tm.PlannerWit.the_witness_day_is_two_replayed_blocks_and_the
-- _written_wall`, whose line above was EDITED rather than appended: P2 put
-- §16's `wind_down` and `bed` in the day track W wrote that equation against,
-- so the three-row form is FALSE and the equation is re-proved over five rows
-- under the name it now deserves (D5, AGENTS §5.2).  Every prose citation was
-- grepped and moved with it.
-- ===========================================================================
#print axioms Tm.Planner.mkRoutines?_of_none
#print axioms Tm.Planner.splitSleep_congr
#print axioms Tm.PlannerWit.the_witness_carries_no_routine
#print axioms Tm.PlannerWit.mkPlanReq?_refuses_a_routine_the_rule_refuses

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-16**, track A — **D32 item 1**, gap
-- 475: `LErr.dupId`, `.notADemotion` and `.ambiguousDemotion` widened to carry
-- BOTH colliding lines' `path` and `line`.
--
-- The order the two lines are named in is a total order on `Spot` (`charsLe`
-- on the path, then the line), because `pairedEntity_order_independent` — the
-- theorem that refutes AGENTS §5.6's defect — has to hold of what the refusal
-- *says* and not only of which constructor it uses.  `spotPair_comm` is that,
-- and `buildEntity_collision_is_a_projection` is §5.3's obligation: the two
-- new fields are `Placement.spot` of placements the loader already held, and
-- `.map Placement.id` over them gives back the one `Id` the error used to be.
--
-- MOVED at W-16's repair step: this block declared `Tm.charsLe_antisymm` and
-- `Tm.charsLe_total` over a SECOND `charsLe` written in `Boundary.lean`.  The
-- fork is deleted and both laws are proved on `Tm.Log.charsLe`, the one
-- lexicographic order this package has (AGENTS §5.3); the two lines moved to
-- the repair step's own banner at the end of this file, and `spotLe` now calls
-- `Log.charsLe`.
-- ===========================================================================
#print axioms Tm.spotLe_antisymm
#print axioms Tm.spotLe_total
#print axioms Tm.spotPair_comm
#print axioms Tm.placementSpots_comm
#print axioms Tm.spotPair_cases
#print axioms Tm.pairedEntity_error_spots
#print axioms Tm.buildEntity_collision_is_a_projection
#print axioms Tm.buildEntity_is_never_asked_about_an_absent_id
-- APPENDED 2026-09-17 (stage 6, run **W-16**, track K step **K3b** — §5's
-- recurrence family inside the kernel: `Recur.lean` (new, with its import line
-- in `TmKernel.lean`), the `doneDatesIn` widening in `Replay.lean` and
-- `SealAgg2.lean`, and the four end-to-end witnesses in `PlannerWit.lean`.
--
-- No goal is discharged and none is added: the burn-down is 12 before and 12
-- after.  Nothing in the shipped binary calls `Recur.lean`.
-- ===========================================================================
#print axioms Tm.Replay.mem_instancesOf

#print axioms Tm.Recur.dateOfT_atClock
#print axioms Tm.Recur.dateOfT_endOfDay
#print axioms Tm.Recur.a_close_at_or_after_now_needs_the_seconds
#print axioms Tm.Recur.parseInstKey_renderInstKey_nth
#print axioms Tm.Recur.eachDayGo_length_le
#print axioms Tm.Recur.eachDay_length_le
#print axioms Tm.Recur.eachDayGo_mem
#print axioms Tm.Recur.eachDay_mem
#print axioms Tm.Recur.phaseEpoch_is_1970_01_01
#print axioms Tm.Recur.the_two_epochs_are_the_dates_the_fork_names
#print axioms Tm.Recur.mondayOf_is_a_monday
#print axioms Tm.Recur.dayHere_length_le
#print axioms Tm.Recur.monthHere_length_le
#print axioms Tm.Recur.monthsGo_length_le
#print axioms Tm.Recur.weekHere_length_le
#print axioms Tm.Recur.mondaysGo_length_le
#print axioms Tm.Recur.placeMinutesOf_is_declaredDur_off_an_interval
#print axioms Tm.Recur.placeMinutesOf_and_declaredDur_differ_on_an_interval
#print axioms Tm.Recur.todayInstances_length_le
#print axioms Tm.Recur.todayInstances_singleton
#print axioms Tm.Recur.every_day_is_every_day
#print axioms Tm.Recur.every_weekday_and_every_thursday_pick_their_days
#print axioms Tm.Recur.every_three_days_counts_from_the_anchor_and_not_from_the_range
#print axioms Tm.Recur.every_two_weeks_skips_a_week
#print axioms Tm.Recur.every_week_is_monday_to_sunday
#print axioms Tm.Recur.every_month_31_clamps_in_february
#print axioms Tm.Recur.a_daily_window_closes_on_its_own_date_unless_it_runs_overnight
#print axioms Tm.Recur.an_instance_key_reads_back_both_ways
#print axioms Tm.Recur.a_future_anchor_does_not_collapse_the_phase

#print axioms Tm.PlannerWit.the_recur_witness_loads
#print axioms Tm.PlannerWit.recurDay_is_the_witness_wednesday
#print axioms Tm.PlannerWit.the_lunch_routine_is_todays_mandatory_window_at_noon
#print axioms Tm.PlannerWit.the_lunch_routine_is_gone_by_two_in_the_afternoon
#print axioms Tm.PlannerWit.the_persist_witness_loads
#print axioms Tm.PlannerWit.a_persist_routine_is_one_carried_obligation_not_sixty_one
-- APPENDED 2026-09-17: stage 6 (the planner), run W-16, track P, step P3 —
-- §8.2 step 3 (the slot cut, on L3's own `Look.cutSlots`, and the slot energies
-- on L4's own `Look.energizeToday`) and §8.2 choice 5b (the running block
-- reserved before the routines and before the cut).
--
-- THREE AUDIT LINES WERE DELETED BY THIS STEP, and each is a theorem the
-- reservation made FALSE, restated in the same commit (AGENTS §3.1 item 3, D5):
--   Tm.Planner.a_block_row_is_a_replayed_row
--       -> Tm.Planner.a_block_row_is_replayed_or_reserved
--   Tm.Planner.the_day_assigns_nothing_after_now_until_the_assign_step_lands
--       -> Tm.Planner.the_day_assigns_nothing_after_now_but_the_running_block
--   Tm.PlanCheck.dayPlan_block_rows_come_from_the_log
--       -> Tm.PlanCheck.dayPlan_block_rows_are_replayed_or_reserved
-- All three were grepped repo-wide, prose included, before the rename.
--
-- ONE GOAL LEFT Goals.lean: plan_reserves_one_block_at_a_time, restated over
-- the Block rows that start at or after `now` and proved in Planner.lean, with
-- PlannerWit.plan_reserves_one_block_at_a_time_as_stage_6_wrote_it_is_refuted
-- beside it.  Burn-down 12 -> 11.
-- ===========================================================================
#print axioms Tm.Look.day0Slots_is_energizeToday
#print axioms Tm.Planner.segOf_units
#print axioms Tm.Planner.PlanReq.activeAgrees_of_none
#print axioms Tm.Planner.PlanReq.activeAgrees_of_mkActive?
#print axioms Tm.Planner.PlanReq.blockMin_pos
#print axioms Tm.Planner.the_block_boundary_is_run
#print axioms Tm.Planner.PlanReq.currentBlockEnd_within_a_block
#print axioms Tm.Planner.PlanReq.activeRun_spec
#print axioms Tm.Planner.PlanReq.the_reservation_is_at_most_one_block
#print axioms Tm.Planner.PlanReq.the_reservation_is_free_of_every_wall
#print axioms Tm.Planner.PlanReq.the_reservation_stops_at_the_limit
#print axioms Tm.Planner.PlanReq.mem_activeRow
#print axioms Tm.Planner.PlanReq.activeRow_is_an_energyless_block
#print axioms Tm.Planner.placeStep_grows_the_blocked
#print axioms Tm.Planner.placeStep_keeps_PlacedOffThe
#print axioms Tm.Planner.foldl_placeStep_grows_the_blocked
#print axioms Tm.Planner.foldl_placeStep_keeps_PlacedOffThe
#print axioms Tm.Planner.a_routine_is_never_placed_over_the_running_block
#print axioms Tm.Planner.PlanReq.todayCut_is_the_lookaheads
#print axioms Tm.Planner.PlanReq.energisedSlots_are_the_lookaheads
#print axioms Tm.Planner.PlanReq.a_slots_level_is_todays_energy
#print axioms Tm.Planner.PlanReq.a_slot_is_inside_the_window
#print axioms Tm.Planner.PlanReq.a_slot_touches_nothing_blocked
#print axioms Tm.Planner.PlanReq.no_slot_touches_the_running_block
#print axioms Tm.Planner.PlanReq.no_slot_reaches_the_evening
#print axioms Tm.Planner.PlanReq.the_reservation_never_runs_under_a_wind_down_row
#print axioms Tm.Planner.PlanReq.no_slot_overlaps_a_break
#print axioms Tm.Planner.PlanReq.a_slot_is_at_most_one_block
#print axioms Tm.Planner.pastRows_are_not_wind_down
#print axioms Tm.Planner.a_wind_down_row_is_the_evenings
#print axioms Tm.Planner.reservationSegs_are_blocks
#print axioms Tm.Planner.reservationSegs_are_not_walls
#print axioms Tm.Planner.the_reservation_row_names_the_running_item
#print axioms Tm.Planner.the_reservation_row_is_exact
#print axioms Tm.Planner.mem_dayRows_of_mem
#print axioms Tm.Planner.mem_assignedFrom
#print axioms Tm.Planner.the_day_assigns_nothing_after_now_but_the_running_block
#print axioms Tm.Planner.a_wall_row_sits_in_a_blocked_span
#print axioms Tm.Planner.a_break_row_is_a_replayed_row
#print axioms Tm.Planner.a_wind_down_row_of_the_day
#print axioms Tm.Planner.a_block_row_is_replayed_or_reserved
#print axioms Tm.Planner.plan_reserves_one_block_at_a_time
#print axioms Tm.PlanCheck.dayPlan_block_rows_are_replayed_or_reserved
#print axioms Tm.PlanCheck.dayPlan_block_rows_are_the_reservation
#print axioms Tm.PlannerWit.witBuildsRun
#print axioms Tm.PlannerWit.the_running_request_agrees
#print axioms Tm.PlannerWit.the_reservation_is_clipped_to_the_block_it_is_in
#print axioms Tm.PlannerWit.the_reserved_day_is_the_witness_day_and_the_running_block
#print axioms Tm.PlannerWit.the_reservation_row_carries_no_energy
#print axioms Tm.PlannerWit.the_reserved_day_assigns_the_running_block
#print axioms Tm.PlannerWit.the_battery_passes_at_the_reserved_day
#print axioms Tm.PlannerWit.the_battery_bites_on_the_reservation
#print axioms Tm.PlannerWit.the_short_block_day_holds_a_block_longer_than_a_block
#print axioms Tm.PlannerWit.plan_reserves_one_block_at_a_time_as_stage_6_wrote_it_is_refuted

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-16**, the REPAIR step — the two
-- auditors' findings.
--
-- `Log.charsLe`'s three order laws.  W-16 shipped THREE definitions of one
-- lexicographic order — `Log.charsLe` (stage 4), `Boundary.charsLe` (track A,
-- `9fa58fc`) and `Recur.charsLe` (track K, `648a160`) — with the two new ones
-- covered by an explicit "re-implemented nothing" claim.  Both forks are
-- deleted and their call sites (`spotLe`, `keyedLe`) consume `Log.charsLe`;
-- the two laws track A proved on its fork are proved here on the real one, and
-- transitivity is added beside them.
--
-- That closes **gap 394** as well, which had stayed open for exactly these
-- lemmas: `Replay.insSort_eq_mergeSort` wants the order transitive and total,
-- so `Planner.wallsOfDay`'s and `sortRoutines`' specification sorts could not
-- have compiled twins.  Both have one now.
-- ===========================================================================
#print axioms Tm.Log.char_val_ne
#print axioms Tm.Log.char_lt_toNat
#print axioms Tm.Log.charsLe_antisymm
#print axioms Tm.Log.charsLe_total
#print axioms Tm.Log.charsLe_trans
#print axioms Tm.Planner.wallLe_trans
#print axioms Tm.Planner.wallLe_total
#print axioms Tm.Planner.sortWalls_eq_sortWallsFast
#print axioms Tm.Planner.mem_sortWalls
#print axioms Tm.Planner.routineLe_trans
#print axioms Tm.Planner.routine_span_total
#print axioms Tm.Planner.routineLe_total
#print axioms Tm.Planner.sortRoutines_eq_sortRoutinesFast

-- ===========================================================================
-- APPENDED 2026-09-18: stage 6, run **W-17**, track **G** -- the lift loses a
-- hypothesis, and §8.3's wall law leaves `Goals.lean`.
--
-- Three groups.
--
-- 1. **`PlanCheck.plan_places_no_block_over_a_wall` -- a goal DISCHARGED**
--    (AGENTS 3.2's burn-down protocol: proved in a shipped module, audited
--    here, then deleted from `Goals.lean`; burn-down 11 -> 10).  It is a
--    §3.1-item-3 discharge, not a plain one: the goal as `Goals.lean` wrote it
--    is FALSE, and
--    `PlannerWit.plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted`
--    is the compiled refutation, over the day a request whose calendar acquired
--    a meeting on an already-worked hour produces.  The restatement is over the
--    Block rows that start at or after `now` -- the fork's own
--    `assigned_set(day, w.now)` and step P3's own restriction for E1.
--
--    **The banner at `plan_never_moves_a_wall`'s block above is corrected in
--    place**: it says `plan_places_no_block_over_a_wall` "is NOT discharged
--    here", which was and remains true of step P1's body, and is no longer the
--    whole story.
--
-- 2. **`PlanCheck.dayPlan_ok_core_from_now` -- §6.1's lift without `hnopast`.**
--    `dayPlan_ok_core` carries "the log holds no Block for today", which is
--    false of every real day after breakfast and is not a fact about the
--    planner.  `withoutPast` names the restriction §8.3 is about instead of
--    assuming it away, and the same conjunction over the same seven checkers
--    goes through with five hypotheses, all R10 or decoder obligations.  Both
--    lifts are kept: they are incomparable, so nothing is weakened (D5).
--
-- 3. **README gap 396's other eight.**  `PlannerWit.the_battery_census_over_a
--    _produced_day` computes what each of the eleven ranges over on a day the
--    planner really produced -- six have a subject, five do not and each names
--    the step that ends that -- and `the_battery_bites_over_a_produced_day`
--    plus `the_whole_battery_refuses_each_mutation` take the battery from
--    three of eleven refusing something to **eleven of eleven**.
-- ===========================================================================
#print axioms Tm.PlanCheck.withoutPast_segments
#print axioms Tm.PlanCheck.mem_withoutPast
#print axioms Tm.PlanCheck.a_block_row_from_now_is_the_reservation
#print axioms Tm.PlanCheck.plan_places_no_block_over_a_wall
#print axioms Tm.PlanCheck.dayPlan_ok_core_from_now
#print axioms Tm.PlannerWit.the_morning_wall_day_lays_a_block_across_a_wall
#print axioms Tm.PlannerWit.plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted
#print axioms Tm.PlannerWit.the_stored_witness_loads
#print axioms Tm.PlannerWit.the_stored_witness_holds_two_ranked_siblings
#print axioms Tm.PlannerWit.the_stored_day_passes_the_whole_battery
#print axioms Tm.PlannerWit.the_battery_census_over_a_produced_day
#print axioms Tm.PlannerWit.the_battery_bites_over_a_produced_day
#print axioms Tm.PlannerWit.the_whole_battery_refuses_each_mutation
