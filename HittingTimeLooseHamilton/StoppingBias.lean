module

public import HittingTimeLooseHamilton.StoppingBiasDeterministic
public import HittingTimeLooseHamilton.ProcessBoundaryProbability
public import HittingTimeLooseHamilton.DisjointEventSum

public section

/-! Lemma 3.1 (stopping bias) of the loose-Hamilton manuscript. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The manuscript's b(F): number of edges containing a degree-one vertex. -/
@[expose] def stoppingBias (F : SimpleHypergraph V) : ℕ := (criticalEdges F).card

/-- Exact probability of a prescribed stopped hypergraph under the original
uniform edge-order process. The nonempty vertex convention excludes the empty
process, which stops at time zero. No conditional-uniformity premise is used. -/
theorem stopping_bias {r : ℕ} (F : SimpleHypergraph V)
    (hF : F ⊆ completeEdges V r) (hNI : NoIsolated F) :
    (processLaw V r).event (fun σ => stoppingStateEvent σ F) =
      (stoppingBias F : ℝ) /
        ((F.card : ℝ) * ((Fintype.card V).choose r).choose F.card) := by
  classical
  let E : Edge V r → EdgeOrder V r → Prop := fun e σ =>
    e.val ∈ criticalEdges F ∧ processState σ F.card = F ∧
      edgeRank σ e = F.card - 1
  have hev : (fun σ => stoppingStateEvent σ F) = (fun σ => ∃ e, E e σ) := by
    funext σ
    apply propext
    rw [stoppingStateEvent_iff_last_critical σ F hF hNI]
    constructor
    · rintro ⟨hs,e,he,hr⟩; exact ⟨e,he,hs,hr⟩
    · rintro ⟨e,he,hs,hr⟩; exact ⟨hs,e,he,hr⟩
  rw [hev, event_exists_eq_sum (processLaw V r) E (by
    intro σ a b ha hb
    exact edgeRank_injective σ (ha.2.2.trans hb.2.2.symm))]
  let c : ℝ := 1 / ((F.card : ℝ) * ((Fintype.card V).choose r).choose F.card)
  have hevent (e : Edge V r) : (processLaw V r).event (E e) =
      if e.val ∈ criticalEdges F then c else 0 := by
    change (processLaw V r).event (fun σ => e.val ∈ criticalEdges F ∧
      processState σ F.card = F ∧ edgeRank σ e = F.card - 1) = _
    rw [FiniteEntropy.Law.event_const_and]
    split_ifs with he
    · exact process_boundary_probability hF hNI.card_pos e (mem_criticalEdges F e.val |>.mp he).1
    · rfl
  simp_rw [hevent]
  rw [← Finset.sum_filter]
  have hb : criticalEdges F ⊆ completeEdges V r := (filter_subset _ _).trans hF
  change (∑ _e ∈ liftEdges r (criticalEdges F), c) = _
  rw [Finset.sum_const, nsmul_eq_mul, liftEdges_card hb]
  simp only [c, stoppingBias, mul_one_div]

/-- Lemma 3.1 with the paper's explicit parameters n and m. -/
theorem lemma31 {n r m : ℕ} (hn : 0 < n) (F : SimpleHypergraph (Fin n))
    (hF : F ⊆ completeEdges (Fin n) r) (hm : F.card = m) (hNI : NoIsolated F) :
    (processLaw (Fin n) r).event (fun σ => stoppingStateEvent σ F) =
      (stoppingBias F : ℝ) / ((m : ℝ) * (n.choose r).choose m) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin, hm] using stopping_bias F hF hNI
end LooseHamilton
