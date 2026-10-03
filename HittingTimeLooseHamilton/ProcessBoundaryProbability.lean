module

public import HittingTimeLooseHamilton.ProcessOrderCoordinates
public import HittingTimeLooseHamilton.UniformOrderCounting

public section

/-! The probability of a fixed process state and a specified last edge. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- Every edge of a fixed nonempty prefix is equally likely to be its last edge.
The formula includes the probability of the prefix itself. -/
theorem process_boundary_probability {F : SimpleHypergraph V}
    (hF : F ⊆ completeEdges V r) (hpos : 0 < F.card)
    (e : Edge V r) (he : e.val ∈ F) :
    (processLaw V r).event (fun σ => processState σ F.card = F ∧
      edgeRank σ e = F.card - 1) =
      1 / ((F.card : ℝ) * ((Fintype.card V).choose r).choose F.card) := by
  classical
  letI : Nonempty (FiniteOrder (Edge V r)) := ⟨Fintype.equivFin _⟩
  let E : FiniteOrder (Edge V r) → Prop := fun ρ =>
    orderPrefix ρ F.card = liftEdges r F ∧ (ρ e).val = F.card - 1
  have ht := FiniteEntropy.Law.uniform_event_equiv (orderRankEquiv (Edge V r)) E
  have hm : F.card ≤ Fintype.card (Edge V r) := by
    simpa using card_le_card hF
  have hc := uniform_order_boundary_probability F.card hm hpos (liftEdges r F)
    (liftEdges_card hF) e ((mem_liftEdges F e).mpr he)
  have hev : (fun σ : EdgeOrder V r => processState σ F.card = F ∧
      edgeRank σ e = F.card - 1) = (fun σ => E (orderRankEquiv (Edge V r) σ)) := by
    funext σ
    apply propext
    exact and_congr (processState_eq_iff_rank_prefix hF σ F.card) Iff.rfl
  change (FiniteEntropy.uniform : FiniteEntropy.Law (EdgeOrder V r)).event _ = _
  have hp : (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder (Edge V r))).event E =
      1 / ((F.card : ℝ) * (Fintype.card (Edge V r)).choose F.card) := by
    rw [FiniteEntropy.Law.uniform_event]
    exact hc
  rw [hev, ht, hp]
  rw [Fintype.card_coe, completeEdges_card]
end LooseHamilton
