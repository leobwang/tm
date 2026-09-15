import TmKernel.SealLaw2D
/-!
# SealCutHeaders — the folded state and headers at the cut (stage 5, D9, W2: law 6)

The checkpoint of folded entries reads its unfolded entries only through the mask: two unfolded lists leaving the same
folded survivors give the same folded state and headers (`foldedState_congr_er`, `foldedHeaders_congr_er`).  At a
reseal's cut the folded headers are the stored ones then the tail's first ones (`foldedHeaders_at_cut`).
Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State survivors wakeInstants keptWakes dayOf)
open Log (Entry)

theorem foldedIndex_congr_er (z : Cal.Tz) (es er er' : List Entry) (h : foldedSurvivors es er = foldedSurvivors es er') :
    foldedIndex z es er = foldedIndex z es er' := by
  unfold foldedIndex; rw [h]

theorem foldedState_congr_er (z : Cal.Tz) (es er er' : List Entry) (h : foldedSurvivors es er = foldedSurvivors es er') :
    foldedState z es er = foldedState z es er' := by
  rw [foldedState_eq, foldedState_eq, foldedIndex_congr_er z es er er' h, h]

theorem cancelledAt_congr_er (es er er' : List Entry) (hd : (es ++ er).Pairwise (fun x y => x.line < y.line))
    (hd' : (es ++ er').Pairwise (fun x y => x.line < y.line)) (h : foldedSurvivors es er = foldedSurvivors es er')
    (i : Nat) (e : Entry) (he : es[i]? = some e) :
    Replay.cancelledAt (es ++ er) i = Replay.cancelledAt (es ++ er') i := by
  have h1 := mem_foldedSurvivors_iff es er hd i e he
  have h2 := mem_foldedSurvivors_iff es er' hd' i e he
  rw [h] at h1
  have h3 := h1.symm.trans h2
  cases hc : Replay.cancelledAt (es ++ er) i <;> cases hc' : Replay.cancelledAt (es ++ er') i <;> simp_all

theorem foldedHeaders_congr_er (z : Cal.Tz) (es er er' : List Entry)
    (hd : (es ++ er).Pairwise (fun x y => x.line < y.line)) (hd' : (es ++ er').Pairwise (fun x y => x.line < y.line))
    (h : foldedSurvivors es er = foldedSurvivors es er') : foldedHeaders z es er = foldedHeaders z es er' := by
  unfold foldedHeaders
  rw [foldedIndex_congr_er z es er er' h]
  apply List.map_congr_left
  intro p hp
  rw [cancelledAt_congr_er es er er' hd hd' h p.2 p.1 (getElem?_of_mem_zipIdx hp)]

theorem length_foldedHeaders (z : Cal.Tz) (es er : List Entry) : (foldedHeaders z es er).length = es.length := by
  simp [foldedHeaders]

/-- **The folded headers at the cut**: the stored lines' then the tail's first ones, when the whole index and the cut's
agree at every folded instant. -/
theorem foldedHeaders_at_cut (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (n : Nat) (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (K : Ckpt) (hK : K = ckptOfEntries z T₀ L cut As Rs ws)
    (sv : List Entry) (hsv : sv = survivors (unsettled K.settled (Rs ++ B')))
    (hg : g1 K (unsettled K.settled (Rs ++ B')) = none)
    (kw : List Cal.Instant) (hkw : kw = tailIndex z K sv)
    (sl : Nat → Option Nat)
    (hsteps : ∀ pre e post, sv = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl K (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).2 = none)
    (hhdr : headerCheck (dayOf z kw) K (Rs ++ B') = none)
    (Bj Brest : List Entry) (hsplit : Rs ++ B' = Bj ++ Brest)
    (hidx : ∀ q ∈ (As ++ Bj).flatMap entryInstants,
      dayOf z (keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv)) q
        = dayOf z (foldedIndex z (As ++ Bj) Brest) q) :
    foldedHeaders z (As ++ Bj) Brest
      = foldedHeaders z As Rs ++ (tailHeaders (dayOf z kw) K.settled (Rs ++ B')).take Bj.length := by
  have hH := resume_headers z T₀ L cut As Rs B' ws n hd K hK sv hsv hg kw hkw sl hsteps hhdr
  have hsurv := (resume_index z T₀ L cut As Rs B' ws n hd K hK sv hsv hg kw hkw sl hsteps).1
  have hI : foldedIndex z (As ++ (Rs ++ B')) []
      = keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv) := by
    rw [foldedIndex_nil, hsurv, wakeInstants_append]
  have e1 : foldedHeaders z (As ++ (Rs ++ B')) [] = ((As ++ Bj) ++ Brest).zipIdx.map (fun p =>
      (dayOf z (keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv)) p.1.t.val,
       Replay.HeaderRec.of p.1 (Replay.cancelledAt ((As ++ Bj) ++ Brest) p.2))) := by
    unfold foldedHeaders
    rw [hI, List.append_nil, hsplit, List.append_assoc]
  have hT : foldedHeaders z (As ++ Bj) Brest = (foldedHeaders z (As ++ (Rs ++ B')) []).take (As.length + Bj.length) := by
    rw [e1, List.zipIdx_append, List.map_append, List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]
    unfold foldedHeaders
    apply List.map_congr_left
    intro p hp
    have hmem : p.1 ∈ As ++ Bj := List.mem_of_getElem? (getElem?_of_mem_zipIdx hp)
    rw [hidx p.1.t.val (List.mem_flatMap.2 ⟨p.1, hmem, by simp [entryInstants]⟩)]
  rw [hT, hH, ← length_foldedHeaders z As Rs, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

end Seal
end Tm
