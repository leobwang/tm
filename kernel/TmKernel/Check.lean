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
