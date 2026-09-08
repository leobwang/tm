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
#print axioms Tm.prose_is_never_an_item
#print axioms Tm.no_two_lines_of_one_id_in_one_path
#print axioms Tm.no_line_is_lost
#print axioms Tm.the_tombstone_is_behind_the_live_line
#print axioms Tm.transform_closed

-- the grammar
#print axioms Tm.readNat_digitsOf
#print axioms Tm.tokenize_raw
#print axioms Tm.tokenize_toks
#print axioms Tm.serialize_parse
#print axioms Tm.parse_serialize
#print axioms Tm.renderSplit_splitDoc
#print axioms Tm.splitDoc_prose_not_item
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
#print axioms Tm.demote_not_idem
#print axioms Tm.readopt_demote_not_id
#print axioms Tm.readopt_demote_id_mod_stamps
#print axioms Tm.floor_and_respect_are_incompatible
#print axioms Tm.demoteEst_conserves
#print axioms Tm.demoteEst_respects_user
#print axioms Tm.mapAt_ok_of_inRange
#print axioms Tm.mapAt_rejects_unoriented
#print axioms Tm.cmdMove_succeeds
#print axioms Tm.demote_into_a_horizon_that_does_not_follow_is_rejected
#print axioms Tm.resolveDest_rejects

-- the glyph is a function of placement, and the loader is its inverse
#print axioms Tm.glyphAt_statusOfGlyph
#print axioms Tm.glyphAt_statusOfGlyphDemoted
#print axioms Tm.every_glyph_has_a_state

-- the boundary
#print axioms Tm.grain_rejects_99
#print axioms Tm.lone_placement_renders_back
#print axioms Tm.orientPair_comm
#print axioms Tm.pairedEntity_order_independent
#print axioms Tm.unordered_horizons_are_rejected
#print axioms Tm.paired_placement_renders_back
#print axioms Tm.paired_renders_each_placement
#print axioms Tm.load_render_line
#print axioms Tm.scanLines_prose
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
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.denPos
#print axioms Tm.Arith.mkPos_num
#print axioms Tm.Arith.mkPos_den
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
#print axioms Tm.Arith.Q
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
#print axioms Tm.Store
#print axioms Tm.Store
#print axioms Tm.Store
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
#print axioms Tm.TagSet
#print axioms Tm.TagSet
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
