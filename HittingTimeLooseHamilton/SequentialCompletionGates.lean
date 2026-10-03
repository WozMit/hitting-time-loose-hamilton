module

public import HittingTimeLooseHamilton.SequentialCompletionPaths
public import HittingTimeLooseHamilton.BootstrapSequentialInputs

public section

noncomputable section
namespace LooseHamilton.SequentialCompletion
open Finset Migration BootstrapBases
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

@[expose] def exceptionBound (r N : ℕ) (ports : ℕ) : ℝ :=
  (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (FrameScales.alpha N)*N +
  Real.sqrt 2*(FrameScales.alpha N)^(1/4:ℝ)*N + (r-2:ℕ)+ports+1

theorem exceptionBound_nonneg (r N ports : ℕ) (ha : 0 ≤ FrameScales.alpha N) : 0 ≤ exceptionBound r N ports := by
  unfold exceptionBound
  positivity

/-- Every successful prefix is a genuine legal large source, so the already
proved one-step implications apply. No path-dependent mobility is assumed. -/
theorem step_bad_card_le (hr : 3 ≤ r) (hM : IsPairMatching original)
    (b : Base original) (H : SimpleHypergraph (Fin N)) (X c : ℝ) (hc : 0<c)
    (inputs : BootstrapSequentialInputs.Inputs (r := r) hM b H X c)
    (ha : 0 ≤ FrameScales.alpha N)
    (s : State ↥(active b) (r-2))
    (hs : s.Valid (r := r) (restrictEdges (active b) (markers hM b)))
    (hp : EndpointSourcePorts (fixedPorts b) (restrictEdges (active b) (markers hM b))
      s.first s.second)
    (hlarge : X/(N:ℝ)^(2*r) ≤
      (s.weight r (restrictEdges (active b) (markers hM b))
        (fixedPortHost (inducedHost (active b) H) (fixedPorts b)):ℝ))
    (e : ℕ) (he : e=1 ∨ e=2)
    (hordinary : e=2 → fixedPorts b = originalPorts (restrictEdges (active b) (markers hM b)))
    (k : ℕ) (hk : k<r-2+e) (p : ChoicePath ↥(active b) k)
    (hpath : Successful (Step s (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (fixedPorts b) c) k p) :
    ((univ.filter (fun v => ¬Step s (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (fixedPorts b) c k p v)).card:ℝ) ≤
      exceptionBound r N (fixedPorts b).card := by
  classical
  let M := restrictEdges (active b) (markers hM b)
  let G := fixedPortHost (inducedHost (active b) H) (fixedPorts b)
  let a := stateAt s k p
  have hvalid := successful_valid s M G (fixedPorts b) c hs hp k p hpath
  have hfloor := successful_floor hr s M G (fixedPorts b) c hc k p hpath
  have hkbound : k≤r := by rcases he with rfl|rfl <;> omega
  have hcut : X/(N:ℝ)^(3*r) ≤ (a.weight r M G:ℝ) :=
    ((inputs.cutoffs k hkbound _ hlarge).1).trans hfloor
  have hnonnegP : 0 ≤ (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (FrameScales.alpha N)*N := by positivity
  have hnonnegE : 0 ≤ Real.sqrt 2*(FrameScales.alpha N)^(1/4:ℝ)*N := by positivity
  suffices hex : ∃ E : Finset (Fin N), (E.card:ℝ) ≤ exceptionBound r N (fixedPorts b).card ∧
      ∀ v : ↥(active b), v.val ∉ E → Step s M G (fixedPorts b) c k p v by
    obtain ⟨E,hE,hv⟩ := hex
    apply le_trans _ hE
    apply Nat.cast_le.mpr
    apply card_le_card_of_injOn Subtype.val
    · intro v hbad
      by_contra h
      exact (mem_filter.mp hbad).2 (hv v h)
    · intro v hv w hw heq; exact Subtype.ext heq
  by_cases hprivate : k<r-2
  · let i : Fin (r-2) := ⟨k,hprivate⟩
    have hrem : (a.remainder i).card = r-3 := by rw [remainder_card a hvalid.1.1]; omega
    have hlegal : LegalPrivateCompletion r M (insert (a.coords i) (a.remainder i))
        {a.first,a.second} := by rw [←block_eq_insert]; exact hvalid.1.2
    have hcount : X/(N:ℝ)^(3*r) ≤ BootstrapPrivateMobility.sourceCount r hM b H
        (a.remainder i) {a.first,a.second} (a.coords i) := by
      change X/(N:ℝ)^(3*r) ≤ (completionCount r M G _ _:ℝ)
      rw [←block_eq_insert]
      exact hcut
    obtain ⟨E,hD,hE,ht⟩ := private_move hr hM b H a c hvalid.1 i
      (inputs.private_move _ _ _ hrem hlegal hcount)
    refine ⟨E,?_,?_⟩
    · unfold exceptionBound; linarith [(Nat.cast_nonneg (r-2) : (0:ℝ) ≤ _),(Nat.cast_nonneg (fixedPorts b).card : (0:ℝ) ≤ _)]
    intro v hv
    have ht' := ht v hv
    change (advance k a v).Valid (r := r) M ∧ _
    simp only [advance,hprivate,dif_pos,Step,factor,if_pos]
    exact ⟨ht'.1,hvalid.2,ht'.2⟩
  by_cases hfirst : k=r-2
  · obtain ⟨E,hE,ht⟩ := first_move hM b H a c hvalid.1 hvalid.2
      (inputs.endpoint_move _ _ _ hvalid.1.2 hvalid.2 hcut)
    refine ⟨E,?_,?_⟩
    · unfold exceptionBound; linarith
    intro v hv
    have ht' := ht v hv
    change (advance k a v).Valid (r := r) M ∧ _
    simp only [advance,hprivate,hfirst,Nat.lt_irrefl,↓reduceDIte,↓reduceIte,Step,factor]
    exact ht'
  · have he2 : e=2 := by rcases he with h|h; omega; exact h
    have hU := hordinary he2
    have hpSwap : EndpointSourcePorts (fixedPorts b) M a.second a.first := by
      rw [hU]
      apply EndpointSourcePorts.ordinary_frame
      intro hh
      exact disjoint_left.mp hvalid.1.2.ports_disjoint (show a.second ∈ a.block ∪ {a.first,a.second} from by simp) hh
    have hswaplarge : X/(N:ℝ)^(3*r) ≤ (a.swap.weight r M G:ℝ) := by
      simpa only [State.weight,State.swap,State.block,pair_comm] using hcut
    obtain ⟨E,hE,ht⟩ := first_move hM b H a.swap c (swap_valid a M hvalid.1) hpSwap
      (inputs.endpoint_move _ _ _ (swap_valid a M hvalid.1).2 hpSwap hswaplarge)
    refine ⟨E,?_,?_⟩
    · unfold exceptionBound; linarith
    intro v hv
    have ht' := ht v hv
    have hvld := swap_valid (a.swap.replaceFirst v) M ht'.1
    have hport : EndpointSourcePorts (fixedPorts b) M a.first v := by
      rw [hU]
      exact EndpointSourcePorts.ordinary_frame M _ _ (by
        simpa only [hU] using hvalid.2.root_ordinary)
    change (advance k a v).Valid (r := r) M ∧ _
    simp only [advance,hprivate,dif_neg,hfirst,if_neg]
    refine ⟨hvld,hport,?_⟩
    simpa [factor,advance,hprivate,hfirst,State.weight,State.swap,State.replaceFirst,
      State.replaceSecond,State.block,pair_comm,a,M,G] using ht'.2.2

end LooseHamilton.SequentialCompletion
