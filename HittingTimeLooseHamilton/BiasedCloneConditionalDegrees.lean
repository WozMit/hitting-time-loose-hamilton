module

public import HittingTimeLooseHamilton.BiasedCloneConditionalSize
public import HittingTimeLooseHamilton.BiasedCloneKahnDegrees

public section

/-! Actual host-degree and pair-degree inputs to Kahn's entropy/collision bounds. -/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r n : ℕ} {markers G : SimpleHypergraph V}
variable (hG : ∀ B ∈ G, B.card=r)
variable (root : ↥markers) (a : ↥root.val) (C₀ : BiasedCycleState r markers G)
variable (e : ↥(biasedCloneUniverse root a C₀) ≃ Fin n)

theorem biasedCloneKahnHost_card :
    (biasedCloneKahnHost hG root a C₀ e).edges.card =
      (cloneHost G (biasedCloneUniverse root a C₀)).card :=
  CloneRelabel.host_card _ _ _ _ _

theorem biasedCloneKahnHost_degree (v : Fin n) :
    Fintype.card (KahnIncident (biasedCloneKahnHost hG root a C₀ e) v) ≤
      r*r*maxVertexDegree G := by
  rw [biasedCloneKahnHost, CloneRelabel.kahnIncident_card]
  exact (cloneHost_degree_le _ _ r hG _).trans
    (Nat.mul_le_mul_left _ (le_sup (mem_univ ((e.symm v).val.1))))

theorem biasedCloneKahnHost_pairDegree (v w : Fin n) (hvw : v ≠ w) :
    pairDegree (biasedCloneKahnHost hG root a C₀ e).edges v w ≤ r*r*maxPairDegree G := by
  rw [biasedCloneKahnHost, CloneRelabel.host_pairDegree]
  have hne : (e.symm v).val ≠ (e.symm w).val := by
    intro h
    exact hvw (e.symm.injective (Subtype.ext h))
  by_cases hf : (e.symm v).val.1 = (e.symm w).val.1
  · rw [cloneHost_pairDegree_same_projection _ _ hne hf]
    exact Nat.zero_le _
  · apply (cloneHost_pairDegree_le _ _ r hG _ _).trans
    apply Nat.mul_le_mul_left
    unfold maxPairDegree
    exact le_sup (f := fun p : V × V => pairDegree G p.1 p.2)
      (mem_filter.mpr ⟨mem_univ ((e.symm v).val.1, (e.symm w).val.1), hf⟩)

/-- The collision theorem's two-element-subset formulation. -/
theorem biasedCloneKahnHost_pairSubset (q : Finset (Fin n)) (hq : q.card=2) :
    ((biasedCloneKahnHost hG root a C₀ e).edges.filter (q ⊆ ·)).card ≤
      r*r*maxPairDegree G := by
  obtain ⟨v,w,hvw,rfl⟩ := card_eq_two.mp hq
  simpa only [pairDegree, insert_subset_iff, singleton_subset_iff] using
    biasedCloneKahnHost_pairDegree hG root a C₀ e v w hvw

end LooseHamilton
