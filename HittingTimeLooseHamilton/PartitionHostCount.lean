module

public import HittingTimeLooseHamilton.PathRegularityModels
public import Mathlib.Data.Finset.Prod

public section

/-! Exact number of complete r-edges meeting a given set in exactly two vertices. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma partition_union_split (A B C : Finset V) (hB : B ⊆ A) (hC : C ⊆ univ \ A) :
    (B ∪ C) ∩ A = B ∧ (B ∪ C) \ A = C := by
  constructor <;> ext v
  · simp only [mem_inter,mem_union]
    constructor
    · rintro ⟨hv|hv,ha⟩
      · exact hv
      · exact False.elim ((mem_sdiff.mp (hC hv)).2 ha)
    · intro hv; exact ⟨Or.inl hv,hB hv⟩
  · simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hv|hv,ha⟩
      · exact False.elim (ha (hB hv))
      · exact hv
    · intro hv; exact ⟨Or.inr hv,(mem_sdiff.mp (hC hv)).2⟩

/-- The exact expectation numerator in equation (eq:partitions). -/
theorem complete_partition_count (r : ℕ) (hr : 2 ≤ r) (A : Finset V) :
    partitionCount (completeEdges V r) A =
      A.card.choose 2 * (Fintype.card V-A.card).choose (r-2) := by
  classical
  let T := A.powersetCard 2 ×ˢ (univ \ A).powersetCard (r-2)
  have hc : partitionCount (completeEdges V r) A = T.card := by
    apply card_bij (fun e _ => (e ∩ A,e \ A))
    · intro e he
      obtain ⟨her,hea⟩ := mem_filter.mp he
      have her' : e.card=r := (mem_completeEdges r e).mp her
      apply mem_product.mpr
      refine ⟨mem_powersetCard.mpr ⟨inter_subset_right,hea⟩,mem_powersetCard.mpr ⟨?_,?_⟩⟩
      · exact sdiff_subset_sdiff (subset_univ _) (Subset.refl _)
      · have hh := card_sdiff_of_subset (inter_subset_left : e ∩ A ⊆ e)
        have heq : e \ (e ∩ A) = e \ A := by ext; simp
        rw [heq,hea,her'] at hh
        exact hh
    · intro e he f hf h
      have h1 : e ∩ A=f ∩ A := congrArg Prod.fst h
      have h2 : e \ A=f \ A := congrArg Prod.snd h
      calc
        e = (e ∩ A) ∪ (e \ A) := (by ext; simp; tauto)
        _ = (f ∩ A) ∪ (f \ A) := by rw [h1,h2]
        _ = f := (by ext; simp; tauto)
    · intro q hq
      obtain ⟨hB,hC⟩ := mem_product.mp hq
      obtain ⟨hBA,hBc⟩ := mem_powersetCard.mp hB
      obtain ⟨hCA,hCc⟩ := mem_powersetCard.mp hC
      have hd : Disjoint q.1 q.2 := by
        apply disjoint_left.mpr
        intro v hvB hvC
        exact (mem_sdiff.mp (hCA hvC)).2 (hBA hvB)
      have hs := partition_union_split A q.1 q.2 hBA hCA
      refine ⟨q.1 ∪ q.2,mem_filter.mpr ⟨?_,?_⟩,?_⟩
      · apply (mem_completeEdges r _).mpr
        rw [card_union_of_disjoint hd,hBc,hCc]
        omega
      · rw [hs.1,hBc]
      · exact Prod.ext hs.1 hs.2
  rw [hc]
  simp [T,card_sdiff_of_subset (subset_univ A)]
end LooseHamilton
