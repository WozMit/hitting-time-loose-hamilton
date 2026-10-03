module

public import HittingTimeLooseHamilton.AssociationModels

public section

/-! Exact counts of the forward source and reverse labels used in the
association switching. All labels refer to actual edges and vertices. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

private def graphIncidenceEquiv (F : SimpleHypergraph V) :
    ↥(graphIncidences F) ≃ Σ v : V, ↥(F.filter (fun e => v ∈ e)) where
  toFun p := ⟨p.val.2,⟨p.val.1,mem_filter.mpr ((mem_graphIncidences _ _).mp p.property)⟩⟩
  invFun p := ⟨(p.2.val,p.1),(mem_graphIncidences _ _).mpr (mem_filter.mp p.2.property)⟩
  left_inv p := by rcases p with ⟨⟨e,v⟩,h⟩; rfl
  right_inv p := by rcases p with ⟨v,⟨e,h⟩⟩; rfl

theorem graphIncidences_card (F : SimpleHypergraph V) :
    (graphIncidences F).card = ∑ v, vertexDegree F v := by
  have h := Fintype.card_congr (graphIncidenceEquiv F)
  simpa only [Fintype.card_coe,Fintype.card_sigma,vertexDegree] using h

private def associationSourceEquiv (F : SimpleHypergraph V) (y : V) (B : Finset V) :
    ↥(associationSources F y B) ≃ Σ z : ↥B, ↥(F.filter (fun e => y ∈ e ∧ z.val ∈ e)) where
  toFun p := ⟨⟨p.val.2,((mem_associationSources _ _ _ _).mp p.property).2.2.2⟩,
    ⟨p.val.1,mem_filter.mpr ⟨((mem_associationSources _ _ _ _).mp p.property).1,
      ((mem_associationSources _ _ _ _).mp p.property).2.2.1,
      ((mem_associationSources _ _ _ _).mp p.property).2.1⟩⟩⟩
  invFun p := ⟨(p.2.val,p.1.val),(mem_associationSources _ _ _ _).mpr
    ⟨(mem_filter.mp p.2.property).1,(mem_filter.mp p.2.property).2.2,
      (mem_filter.mp p.2.property).2.1,p.1.property⟩⟩
  left_inv p := by rcases p with ⟨⟨e,v⟩,h⟩; rfl
  right_inv p := by rcases p with ⟨⟨v,hv⟩,⟨e,h⟩⟩; rfl

theorem associationSources_card (F : SimpleHypergraph V) (y : V) (B : Finset V) :
    (associationSources F y B).card = associationStatistic F y B := by
  have h := Fintype.card_congr (associationSourceEquiv F y B)
  calc
    _ = ∑ z : ↥B, pairDegree F y z.val := by
      simpa only [Fintype.card_coe,Fintype.card_sigma,pairDegree] using h
    _ = _ := sum_coe_sort B (fun z => pairDegree F y z)

/-- A reverse move chooses an edge through y and a distinguished vertex other than y. -/
@[expose] def associationReverseHeads (F : SimpleHypergraph V) (y : V) : Finset (Finset V × V) :=
  (graphIncidences F).filter (fun p => y ∈ p.1 ∧ p.2 ≠ y)

/-- Incidences whose distinguished vertex belongs to B. -/
@[expose] def associationBIncidences (F : SimpleHypergraph V) (B : Finset V) : Finset (Finset V × V) :=
  (graphIncidences F).filter (fun p => p.2 ∈ B)

@[simp] theorem mem_associationReverseHeads (F : SimpleHypergraph V) (y : V) (p : Finset V × V) :
    p ∈ associationReverseHeads F y ↔ p.1 ∈ F ∧ p.2 ∈ p.1 ∧ y ∈ p.1 ∧ p.2 ≠ y := by
  simp only [associationReverseHeads,mem_filter,mem_graphIncidences]
  tauto

@[simp] theorem mem_associationBIncidences (F : SimpleHypergraph V) (B : Finset V) (p : Finset V × V) :
    p ∈ associationBIncidences F B ↔ p.1 ∈ F ∧ p.2 ∈ p.1 ∧ p.2 ∈ B := by
  simp only [associationBIncidences,mem_filter,mem_graphIncidences]
  tauto

private def reverseHeadsEquiv (F : SimpleHypergraph V) (y : V) :
    ↥(associationReverseHeads F y) ≃ Σ e : ↥(F.filter (fun e => y ∈ e)), ↥(e.val.erase y) where
  toFun p := ⟨⟨p.val.1,mem_filter.mpr
    ⟨((mem_associationReverseHeads _ _ _).mp p.property).1,
      ((mem_associationReverseHeads _ _ _).mp p.property).2.2.1⟩⟩,
    ⟨p.val.2,mem_erase.mpr ⟨((mem_associationReverseHeads _ _ _).mp p.property).2.2.2,
      ((mem_associationReverseHeads _ _ _).mp p.property).2.1⟩⟩⟩
  invFun p := ⟨(p.1.val,p.2.val),(mem_associationReverseHeads _ _ _).mpr
    ⟨(mem_filter.mp p.1.property).1,(mem_erase.mp p.2.property).2,
      (mem_filter.mp p.1.property).2,(mem_erase.mp p.2.property).1⟩⟩
  left_inv p := by rcases p with ⟨⟨e,v⟩,h⟩; rfl
  right_inv p := by rcases p with ⟨⟨e,he⟩,⟨v,hv⟩⟩; rfl

theorem associationReverseHeads_card {r : ℕ} (F : SimpleHypergraph V)
    (hF : F ⊆ completeEdges V r) (y : V) :
    (associationReverseHeads F y).card = vertexDegree F y * (r-1) := by
  have h := Fintype.card_congr (reverseHeadsEquiv F y)
  rw [Fintype.card_coe,Fintype.card_sigma] at h
  have he : ∀ e : ↥(F.filter (fun e => y ∈ e)), Fintype.card ↥(e.val.erase y) = r-1 := by
    intro e
    rw [Fintype.card_coe,card_erase_of_mem (mem_filter.mp e.property).2]
    rw [(mem_completeEdges _ _).mp (hF (mem_filter.mp e.property).1)]
  simp_rw [he] at h
  simpa only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id,vertexDegree] using h

private def bIncidenceEquiv (F : SimpleHypergraph V) (B : Finset V) :
    ↥(associationBIncidences F B) ≃ Σ z : ↥B, ↥(F.filter (fun e => z.val ∈ e)) where
  toFun p := ⟨⟨p.val.2,((mem_associationBIncidences _ _ _).mp p.property).2.2⟩,
    ⟨p.val.1,mem_filter.mpr ⟨((mem_associationBIncidences _ _ _).mp p.property).1,
      ((mem_associationBIncidences _ _ _).mp p.property).2.1⟩⟩⟩
  invFun p := ⟨(p.2.val,p.1.val),(mem_associationBIncidences _ _ _).mpr
    ⟨(mem_filter.mp p.2.property).1,(mem_filter.mp p.2.property).2,p.1.property⟩⟩
  left_inv p := by rcases p with ⟨⟨e,v⟩,h⟩; rfl
  right_inv p := by rcases p with ⟨⟨v,hv⟩,⟨e,h⟩⟩; rfl

theorem associationBIncidences_card (F : SimpleHypergraph V) (B : Finset V) :
    (associationBIncidences F B).card = ∑ z ∈ B, vertexDegree F z := by
  have h := Fintype.card_congr (bIncidenceEquiv F B)
  calc
    _ = ∑ z : ↥B, vertexDegree F z.val := by
      simpa only [Fintype.card_coe,Fintype.card_sigma,vertexDegree] using h
    _ = _ := sum_coe_sort B (fun z => vertexDegree F z)

/-- All possible reverse labels; requiring a valid reverse surgery would only
reduce this set. -/
@[expose] def associationReverseLabels (F : SimpleHypergraph V) (y : V) (B : Finset V) :=
  associationReverseHeads F y ×ˢ associationBIncidences F B

theorem fixed_graphIncidences_card {r : ℕ} {d : V → ℕ} (F : FixedDegreeState V r d) :
    (graphIncidences F.val).card = degreeSum d := by
  rw [graphIncidences_card]
  simp only [F.property.2,degreeSum]

theorem fixed_associationReverseLabels_card {r : ℕ} {d : V → ℕ}
    (F : FixedDegreeState V r d) (y : V) (B : Finset V) :
    (associationReverseLabels F.val y B).card = associationNumerator r d y B := by
  rw [associationReverseLabels,card_product,associationReverseHeads_card _ F.property.1,
    associationBIncidences_card,F.property.2]
  simp only [F.property.2,associationNumerator,degreeOn]
  ring
end LooseHamilton
