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

-- entity versus observation
#print axioms Tm.archive_elsewhere
#print axioms Tm.one_line_per_file
#print axioms Tm.exactly_one_live
#print axioms Tm.archive_line_is_demoted

-- the plan as one object
#print axioms Tm.no_two_lines_of_one_id_in_one_file
#print axioms Tm.lines_per_id_le_two
#print axioms Tm.prose_is_never_an_item
#print axioms Tm.every_transform_preserves_the_invariant
#print axioms Tm.every_transform_keeps_lines_le_two

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

-- the commands
#print axioms Tm.move_into_archive_file_is_rejected
#print axioms Tm.plan_move_into_archive_file_is_rejected
#print axioms Tm.move_idem
#print axioms Tm.move_last_wins
#print axioms Tm.move_last_wins_refuted_globally
#print axioms Tm.move_not_invertible
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

-- the boundary
#print axioms Tm.grain_rejects_99

-- §6.3's three close rows, generated from one rule at three grains
#eval (closeTo day 250, closeTo week 250, closeTo month 250)
-- the rule horizon.rs:1323 uses, versus the derived one, on a Sunday closed on Monday
#eval (targetContaining day 6, closeTo day 7)
