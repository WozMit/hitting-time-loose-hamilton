module

public import HittingTimeLooseHamilton.ProcessBoundaryProbability
public import HittingTimeLooseHamilton.DisjointEventSum

public section

/-! The exact uniform-subset law of an edge-order prefix and its consequences. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators

section Orders
variable {A : Type*} [Fintype A] [DecidableEq A]

private def prefixSubset (m : ℕ) (hm : m ≤ Fintype.card A) (σ : FiniteOrder A) :
    ↥((univ : Finset A).powersetCard m) :=
  ⟨orderPrefix σ m,mem_powersetCard.mpr ⟨subset_univ _,orderPrefix_card σ m hm⟩⟩

/-- The prefix itself is uniform, including the empty prefix. -/
theorem uniform_order_prefix_probability (m : ℕ) (hm : m ≤ Fintype.card A)
    (S : Finset A) (hS : S.card = m) :
    ((univ.filter (fun σ : FiniteOrder A => orderPrefix σ m = S)).card : ℝ) /
      Fintype.card (FiniteOrder A) = 1 / (Fintype.card A).choose m := by
  classical
  letI : Nonempty (FiniteOrder A) := ⟨Fintype.equivFin A⟩
  let b : ↥((univ : Finset A).powersetCard m) := ⟨S,mem_powersetCard.mpr ⟨subset_univ _,hS⟩⟩
  have hequal (c : ↥((univ : Finset A).powersetCard m)) :
      (univ.filter (fun σ => prefixSubset m hm σ = c)).card =
        (univ.filter (fun σ => prefixSubset m hm σ = b)).card := by
    let e : ↥c.val ≃ ↥S := Finset.equivOfCardEq ((mem_powersetCard.mp c.property).2.trans hS.symm)
    let g : Equiv.Perm A := e.extendSubtype
    have hmem : ∀ x, x ∈ c.val ↔ g x ∈ S := by
      intro x
      constructor
      · exact e.extendSubtype_mem x
      · intro hx
        by_contra hn
        exact e.extendSubtype_not_mem x hn hx
    apply Kahn.Ordering.card_event_eq_of_equiv _ _ (Equiv.equivCongr g (Equiv.refl _))
    intro σ
    simp only [Subtype.ext_iff,prefixSubset]
    constructor
    · intro hs
      ext x
      rw [mem_orderPrefix]
      change (σ (g.symm x)).val < m ↔ x ∈ S
      rw [← mem_orderPrefix,hs,hmem]
      simp
    · intro hs
      ext x
      rw [mem_orderPrefix,hmem]
      have hh := congrArg (fun T => g x ∈ T) hs
      simpa [mem_orderPrefix,Equiv.equivCongr] using Iff.of_eq hh
  have h := Kahn.Ordering.uniform_fibre_probability (prefixSubset m hm) b hequal
  simpa only [Subtype.ext_iff,prefixSubset,b,Fintype.card_coe,card_powersetCard,card_univ] using h
end Orders

section Process
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- A fixed process state has the exact reciprocal-binomial probability. -/
theorem process_prefix_probability {F : SimpleHypergraph V}
    (hF : F ⊆ completeEdges V r) :
    (processLaw V r).event (fun σ => processState σ F.card = F) =
      1 / (((Fintype.card V).choose r).choose F.card : ℝ) := by
  classical
  letI : Nonempty (FiniteOrder (Edge V r)) := ⟨Fintype.equivFin _⟩
  let E : FiniteOrder (Edge V r) → Prop := fun ρ => orderPrefix ρ F.card = liftEdges r F
  have ht := FiniteEntropy.Law.uniform_event_equiv (orderRankEquiv (Edge V r)) E
  have hm : F.card ≤ Fintype.card (Edge V r) := by simpa using card_le_card hF
  have hc := uniform_order_prefix_probability F.card hm (liftEdges r F) (liftEdges_card hF)
  have hev : (fun σ : EdgeOrder V r => processState σ F.card = F) =
      (fun σ => E (orderRankEquiv (Edge V r) σ)) := by
    funext σ
    exact propext (processState_eq_iff_rank_prefix hF σ F.card)
  change (FiniteEntropy.uniform : FiniteEntropy.Law (EdgeOrder V r)).event _ = _
  have hp : (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder (Edge V r))).event E =
      1 / ((Fintype.card (Edge V r)).choose F.card : ℝ) := by
    rw [FiniteEntropy.Law.uniform_event]
    exact hc
  rw [hev,ht,hp,Fintype.card_coe,completeEdges_card]

/-- Full exact distribution of any property of the state at a fixed time. -/
theorem process_state_probability (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (P : SimpleHypergraph V → Prop) [DecidablePred P] :
    (processLaw V r).event (fun σ => P (processState σ m)) =
      (((completeEdges V r).powersetCard m).filter P).card /
        (((Fintype.card V).choose r).choose m : ℝ) := by
  classical
  let T := (completeEdges V r).powersetCard m
  let E : ↥T → EdgeOrder V r → Prop := fun F σ => P F.val ∧ processState σ m = F.val
  have hev : (fun σ => P (processState σ m)) = (fun σ => ∃ F, E F σ) := by
    funext σ
    apply propext
    constructor
    · intro hp
      have hs : processState σ m ∈ T := mem_powersetCard.mpr
        ⟨processState_subset σ m, by rw [processState_card,Nat.min_eq_left hm]⟩
      exact ⟨⟨processState σ m,hs⟩,hp,rfl⟩
    · rintro ⟨F,hp,hF⟩
      simpa only [hF] using hp
  rw [hev,event_exists_eq_sum (processLaw V r) E (by
    intro σ F G hF hG
    exact Subtype.ext (hF.2.symm.trans hG.2))]
  have hevent (F : ↥T) : (processLaw V r).event (E F) =
      if P F.val then 1 / (((Fintype.card V).choose r).choose m : ℝ) else 0 := by
    rw [show E F = (fun σ => P F.val ∧ processState σ m = F.val) from rfl,
      FiniteEntropy.Law.event_const_and]
    split_ifs with hp
    · have hF := mem_powersetCard.mp F.property
      simpa only [hF.2] using process_prefix_probability hF.1
    · rfl
  simp_rw [hevent]
  rw [show (∑ x : ↥T, if P x.val then 1 / (((Fintype.card V).choose r).choose m : ℝ) else 0) =
      ∑ F ∈ T, if P F then 1 / (((Fintype.card V).choose r).choose m : ℝ) else 0 from
      sum_coe_sort T (fun F => if P F then 1 / (((Fintype.card V).choose r).choose m : ℝ) else 0)]
  rw [← sum_filter]
  simp [T,mul_one_div,div_eq_mul_inv]

/-- Exact probability that all prescribed edges have appeared. -/
theorem process_contains_probability (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (K : SimpleHypergraph V) (hK : K ⊆ completeEdges V r) (hk : K.card ≤ m) :
    (processLaw V r).event (fun σ => K ⊆ processState σ m) =
      (((Fintype.card V).choose r - K.card).choose (m-K.card) : ℝ) /
        (((Fintype.card V).choose r).choose m : ℝ) := by
  rw [process_state_probability m hm]
  rw [Kahn.Ordering.card_subsets_containing _ K hK m hk,completeEdges_card]

/-- Avoiding a forbidden edge set is sampling entirely from its complement. -/
theorem process_avoids_probability (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (D : SimpleHypergraph V) (hD : D ⊆ completeEdges V r) :
    (processLaw V r).event (fun σ => Disjoint (processState σ m) D) =
      (((Fintype.card V).choose r - D.card).choose m : ℝ) /
        (((Fintype.card V).choose r).choose m : ℝ) := by
  classical
  rw [process_state_probability m hm (fun F => Disjoint F D)]
  have he : ((completeEdges V r).powersetCard m).filter (fun F => Disjoint F D) =
      ((completeEdges V r) \ D).powersetCard m := by
    ext F
    simp only [mem_filter,mem_powersetCard,subset_sdiff]
    tauto
  rw [he,card_powersetCard,card_sdiff_of_subset hD,completeEdges_card]
end Process
end LooseHamilton
