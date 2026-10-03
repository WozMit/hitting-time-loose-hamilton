module

public import HittingTimeLooseHamilton.EdgeComplementModels

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restriction to any fixed edge universe is a bijection onto the residual
nested pairs. The witness supplies only consistency of the exposed record. -/
@[expose] def edgeComplementEquiv (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (w : EdgeComplementFiber r M ell j U A0 B0) :
    EdgeComplementFiber r M ell j U A0 B0 ≃
      EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card) := by
  classical
  have hA : A0 ⊆ completeEdges V r := by
    rw [← w.property.1]; exact (sdiff_subset).trans w.val.val.1.property.1
  have hB : B0 ⊆ completeEdges V r := by
    rw [← w.property.2]; exact (sdiff_subset).trans w.val.property.2.1
  have hAB : A0 ⊆ B0 := by
    simpa only [w.property.1,w.property.2] using
      (sdiff_subset_sdiff w.val.property.1 (Subset.refl U))
  have hAD : Disjoint A0 U := by
    rw [← w.property.1]; exact sdiff_disjoint
  have hBD : Disjoint B0 U := by
    rw [← w.property.2]; exact sdiff_disjoint
  have hAM : A0.card ≤ M := by
    simpa only [w.property.1,w.val.val.1.property.2.1] using
      (card_le_card (sdiff_subset : w.val.val.1.val \ U ⊆ w.val.val.1.val))
  have hBj : B0.card ≤ j := by
    simpa only [w.property.2,w.val.property.2.2] using
      (card_le_card (sdiff_subset : w.val.val.2 \ U ⊆ w.val.val.2))
  let f : EdgeComplementFiber r M ell j U A0 B0 →
      EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card) := fun p =>
    ⟨(p.val.val.1.val ∩ U,p.val.val.2 ∩ U), by
      refine ⟨inter_subset_inter p.val.property.1 (Subset.refl U), inter_subset_right, ?_, ?_, ?_⟩
      · rw [edgeComplement_card, p.val.val.1.property.2.1, p.property.1]
      · rw [edgeComplement_card, p.val.property.2.2, p.property.2]
      · have he : A0 ∪ (p.val.val.1.val ∩ U) = p.val.val.1.val := by
          simpa only [p.property.1] using edgeComplement_reconstruct p.val.val.1.val U
        rw [he]
        exact p.val.val.1.property.2.2⟩
  let g : EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card) →
      EdgeComplementFiber r M ell j U A0 B0 := fun q => by
    have hSU : q.val.1 ⊆ U := q.property.1.trans q.property.2.1
    have hAS : Disjoint A0 q.val.1 := hAD.mono_right hSU
    have hBJ : Disjoint B0 q.val.2 := hBD.mono_right q.property.2.1
    let T : TerminalState V r M ell := ⟨A0 ∪ q.val.1,
      union_subset hA (hSU.trans hU), by
        rw [card_union_of_disjoint hAS,q.property.2.2.1]; omega,
      q.property.2.2.2.2⟩
    refine ⟨⟨(T,B0 ∪ q.val.2),union_subset_union hAB q.property.1,
      union_subset hB (q.property.2.1.trans hU), ?_⟩, ?_, ?_⟩
    · rw [card_union_of_disjoint hBJ,q.property.2.2.2.1]; omega
    · change (A0 ∪ q.val.1) \ U = A0
      ext e
      have ha := disjoint_left.mp hAD
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨he,hn⟩; exact he.resolve_right (fun h => hn (hSU h))
      · intro he; exact ⟨Or.inl he, fun hu => ha he hu⟩
    · ext e
      have hb := disjoint_left.mp hBD
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨he,hn⟩; exact he.resolve_right (fun h => hn (q.property.2.1 h))
      · intro he; exact ⟨Or.inl he, fun hu => hb he hu⟩
  refine ⟨f,g,?_,?_⟩
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change A0 ∪ (p.val.val.1.val ∩ U) = p.val.val.1.val
      simpa only [p.property.1] using edgeComplement_reconstruct p.val.val.1.val U
    · change B0 ∪ (p.val.val.2 ∩ U) = p.val.val.2
      simpa only [p.property.2] using edgeComplement_reconstruct p.val.val.2 U
  · intro q
    apply Subtype.ext
    apply Prod.ext
    · change (A0 ∪ q.val.1) ∩ U = q.val.1
      ext e
      have hd := disjoint_left.mp hAD
      have hs := q.property.1.trans q.property.2.1
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨he,hu⟩; exact he.resolve_left (fun ha => hd ha hu)
      · intro he; exact ⟨Or.inr he,hs he⟩
    · change (B0 ∪ q.val.2) ∩ U = q.val.2
      ext e
      have hd := disjoint_left.mp hBD
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨he,hu⟩; exact he.resolve_left (fun hb => hd hb hu)
      · intro he; exact ⟨Or.inr he,q.property.2.1 he⟩

lemma edgeComplementEquiv_values (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (w p : EdgeComplementFiber r M ell j U A0 B0) :
    (edgeComplementEquiv r M ell j U A0 B0 hU w p).val =
      (p.val.val.1.val ∩ U,p.val.val.2 ∩ U) := rfl
end LooseHamilton
