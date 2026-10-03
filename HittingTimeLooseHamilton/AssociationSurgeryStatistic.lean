module

public import HittingTimeLooseHamilton.AssociationSurgeryBasic
public import HittingTimeLooseHamilton.AssociationModels

public section

noncomputable section
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Contribution of one edge to the y-to-B association statistic. -/
@[expose] def edgeAssociation (e : Finset V) (y : V) (B : Finset V) : ℕ :=
  if y ∈ e then (e ∩ B).card else 0

lemma associationStatistic_eq_sum (F : SimpleHypergraph V) (y : V) (B : Finset V) :
    associationStatistic F y B = ∑ e ∈ F, edgeAssociation e y B := by
  unfold associationStatistic pairDegree
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hy : y ∈ e
  · simp [edgeAssociation,hy,Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.inter_comm]
  · simp [edgeAssociation,hy]

namespace AssociationSwitchValid
variable {F : SimpleHypergraph V} {e f : Finset V} {z a y : V} {B : Finset V}
variable (h : AssociationSwitchValid F e f z a)
include h

lemma statistic_add_one (hy : y ∈ e) (hyB : y ∉ B) (hzB : z ∈ B) (haB : a ∉ B) :
    associationStatistic (associationSwitch F e f z a) y B + 1 = associationStatistic F y B := by
  have hyz : y ≠ z := fun hz => hyB (hz.symm ▸ hzB)
  have hyf : y ∉ f := fun hh => Finset.disjoint_left.mp h.disjoint hy hh
  have hyE : y ∈ switchedEdge e z a := by simp [hyz,hy]
  have hyF : y ∉ switchedEdge f a z := by simp [hyz,hyf]
  have heq : switchedEdge e z a ∩ B = (e ∩ B).erase z := by
    ext x
    simp only [Finset.mem_inter, mem_switchedEdge, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | ⟨hxz,hxe⟩,hxB⟩
      · exact False.elim (haB hxB)
      · exact ⟨hxz,hxe,hxB⟩
    · rintro ⟨hxz,hxe,hxB⟩
      exact ⟨Or.inr ⟨hxz,hxe⟩,hxB⟩
  have hc : (switchedEdge e z a ∩ B).card + 1 = (e ∩ B).card := by
    rw [heq]
    exact Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨h.z_mem,hzB⟩)
  have hs := h.sum_switch_add (fun b => edgeAssociation b y B)
  rw [← associationStatistic_eq_sum, ← associationStatistic_eq_sum] at hs
  simp only [edgeAssociation,if_pos hy,if_neg hyf,if_pos hyE,if_neg hyF,Nat.add_zero] at hs
  omega

/-- The actual fixed-degree state after the legal two-edge surgery. -/
@[expose] def fixedState {r : ℕ} {d : V → ℕ} (hF : F ⊆ completeEdges V r)
    (hd : ∀ v, vertexDegree F v = d v) : FixedDegreeState V r d :=
  ⟨associationSwitch F e f z a,h.uniform hF,fun v => (h.degree v).trans (hd v)⟩

end AssociationSwitchValid
end LooseHamilton
