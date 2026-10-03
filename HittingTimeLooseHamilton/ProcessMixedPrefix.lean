module

public import HittingTimeLooseHamilton.MixedPrefixKernel

public section

/-! Mixed inclusion and avoidance in the original edge-permutation process. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

theorem liftEdges_subset_iff {K F : SimpleHypergraph V} (hK : K ⊆ completeEdges V r) :
    liftEdges r K ⊆ liftEdges r F ↔ K ⊆ F := by
  constructor
  · intro h e he
    exact (mem_liftEdges _ _).mp (h ((mem_liftEdges _ ⟨e,hK he⟩).mpr he))
  · intro h e he
    exact (mem_liftEdges _ _).mpr (h ((mem_liftEdges _ _).mp he))

theorem liftEdges_disjoint_iff {F D : SimpleHypergraph V} (hF : F ⊆ completeEdges V r) :
    Disjoint (liftEdges r F) (liftEdges r D) ↔ Disjoint F D := by
  simp only [disjoint_left]
  constructor
  · intro h e he hd
    exact h ((mem_liftEdges _ ⟨e,hF he⟩).mpr he) ((mem_liftEdges _ _).mpr hd)
  · intro h e he hd
    exact h ((mem_liftEdges _ _).mp he) ((mem_liftEdges _ _).mp hd)

/-- Conditioning on prescribed edges appearing by the upper time can cost at
most their number of lower-time positions. No independence assertion is used. -/
theorem process_mixed_prefix_bound (K D : SimpleHypergraph V)
    (hK : K ⊆ completeEdges V r) (hD : D ⊆ completeEdges V r)
    (a b : ℕ) (ha : a ≤ (completeEdges V r).card) (hk : K.card ≤ a)
    (hKD : Disjoint K D) :
    (processLaw V r).event (fun σ => K ⊆ processState σ b ∧ Disjoint (processState σ a) D) ≤
      (processLaw V r).event (fun σ => K ⊆ processState σ b) *
      ((((Fintype.card V).choose r-K.card-D.card).choose (a-K.card) : ℝ) /
        ((Fintype.card V).choose r-K.card).choose (a-K.card)) := by
  classical
  letI : Nonempty (FiniteOrder (Edge V r)) := ⟨Fintype.equivFin _⟩
  let E : FiniteOrder (Edge V r) → Prop := fun ρ => liftEdges r K ⊆ orderPrefix ρ b
  let P : FiniteOrder (Edge V r) → Prop := fun ρ => Disjoint (orderPrefix ρ a) (liftEdges r D)
  have hprefix (σ : EdgeOrder V r) (m : ℕ) :
      orderPrefix (orderRankEquiv (Edge V r) σ) m = liftEdges r (processState σ m) :=
    (processState_eq_iff_rank_prefix (processState_subset σ m) σ m).mp rfl
  have hE (σ : EdgeOrder V r) : E (orderRankEquiv (Edge V r) σ) ↔ K ⊆ processState σ b := by
    change liftEdges r K ⊆ orderPrefix _ b ↔ _
    rw [hprefix,liftEdges_subset_iff hK]
  have hP (σ : EdgeOrder V r) : P (orderRankEquiv (Edge V r) σ) ↔ Disjoint (processState σ a) D := by
    change Disjoint (orderPrefix _ a) (liftEdges r D) ↔ _
    rw [hprefix,liftEdges_disjoint_iff (processState_subset σ a)]
  have hev : (fun σ : EdgeOrder V r => K ⊆ processState σ b ∧ Disjoint (processState σ a) D) =
      (fun σ => E (orderRankEquiv (Edge V r) σ) ∧ P (orderRankEquiv (Edge V r) σ)) := by
    funext σ
    exact propext (and_congr (hE σ).symm (hP σ).symm)
  have hevE : (fun σ : EdgeOrder V r => K ⊆ processState σ b) =
      (fun σ => E (orderRankEquiv (Edge V r) σ)) := by
    funext σ
    exact propext (hE σ).symm
  have h := uniform_mixed_prefix_bound (liftEdges r K) (liftEdges r D) a b
    (by simpa only [Fintype.card_coe] using ha)
    (by simpa only [liftEdges_card hK] using hk)
    ((liftEdges_disjoint_iff hK).mpr hKD)
  change (FiniteEntropy.uniform : FiniteEntropy.Law (EdgeOrder V r)).event _ ≤
    (FiniteEntropy.uniform : FiniteEntropy.Law (EdgeOrder V r)).event _ * _
  rw [hev,hevE,FiniteEntropy.Law.uniform_event_equiv (orderRankEquiv (Edge V r)) (fun ρ => E ρ ∧ P ρ),
    FiniteEntropy.Law.uniform_event_equiv (orderRankEquiv (Edge V r)) E]
  simpa only [E,P,liftEdges_card hK,liftEdges_card hD,Fintype.card_coe,completeEdges_card] using h
end LooseHamilton
