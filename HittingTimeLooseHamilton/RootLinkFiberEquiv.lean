module

public import HittingTimeLooseHamilton.RootLinkModels

public section

/-! Exact reconstruction of a nested experiment from its fixed complementary parts. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma sdiff_card_inter {F U A : SimpleHypergraph V} (hA : F\U=A) :
    (F∩U).card=F.card-A.card := by
  have h := card_sdiff_add_card_inter F U
  rw [hA] at h
  omega

omit [Fintype V] in
lemma fixed_part_union_sdiff {A U S : SimpleHypergraph V}
    (hA : Disjoint A U) (hS : S ⊆ U) : (A∪S)\U=A := by
  ext e
  simp only [mem_sdiff,mem_union]
  constructor
  · rintro ⟨he,hn⟩
    exact he.resolve_right (fun he => hn (hS he))
  · intro he
    exact ⟨Or.inl he,fun hu => disjoint_left.mp hA he hu⟩

omit [Fintype V] in
lemma fixed_part_union_inter {A U S : SimpleHypergraph V}
    (hA : Disjoint A U) (hS : S ⊆ U) : (A∪S)∩U=S := by
  ext e
  simp only [mem_inter,mem_union]
  constructor
  · rintro ⟨he,hu⟩
    exact he.resolve_left (fun he => disjoint_left.mp hA he hu)
  · intro he
    exact ⟨Or.inr he,hS he⟩

@[expose] def rootLinkRestrict (r M : ℕ) (ell : V → ℕ) (m : ℕ) (U A B : SimpleHypergraph V)
    (p : RootLinkFiber r M ell m U A B) :
    RootLinkFeasibleState U A ell (M-A.card) (m-B.card) := by
  refine ⟨⟨⟨p.val.val.1.val∩U,p.val.val.2∩U⟩,
    inter_subset_inter p.val.property.1 (Subset.refl _),?_,mem_powersetCard.mpr ⟨inter_subset_right,?_⟩⟩,?_⟩
  · rw [sdiff_card_inter p.property.1,p.val.val.1.property.2.1]
  · rw [sdiff_card_inter p.property.2,p.val.property.2.2]
  · intro v
    change ell v ≤ vertexDegree (A∪(p.val.val.1.val∩U)) v
    simpa only [←p.property.1,sdiff_union_inter] using p.val.val.1.property.2.2 v

@[expose] def rootLinkRestore (r M : ℕ) (ell : V → ℕ) (m : ℕ) (U A B : SimpleHypergraph V)
    (hU : U ⊆ completeEdges V r) (W : RootLinkFiber r M ell m U A B)
    (p : RootLinkFeasibleState U A ell (M-A.card) (m-B.card)) :
    RootLinkFiber r M ell m U A B := by
  have hAB : A ⊆ B := by
    simpa only [W.property.1,W.property.2] using sdiff_subset_sdiff W.val.property.1 (Subset.refl U)
  have hA : A ⊆ W.val.val.1.val := by simpa only [W.property.1] using (sdiff_subset : W.val.val.1.val\U ⊆ W.val.val.1.val)
  have hB : B ⊆ W.val.val.2 := by simpa only [W.property.2] using (sdiff_subset : W.val.val.2\U ⊆ W.val.val.2)
  have hAc : A.card ≤ M := by simpa only [W.val.val.1.property.2.1] using card_le_card hA
  have hBc : B.card ≤ m := by simpa only [W.val.property.2.2] using card_le_card hB
  have hAU : Disjoint A U := by rw [←W.property.1]; exact sdiff_disjoint
  have hBU : Disjoint B U := by rw [←W.property.2]; exact sdiff_disjoint
  have houter := (mem_powersetCard.mp p.val.property.2.2).1
  have hinner := p.val.property.1.trans houter
  let F : TerminalState V r M ell := ⟨A∪p.val.val.1,
    union_subset (hA.trans W.val.val.1.property.1) (hinner.trans hU),by
      rw [card_union_of_disjoint (hAU.mono_right hinner),p.val.property.2.1]
      omega,p.property⟩
  let H : SimpleHypergraph V := B∪p.val.val.2
  have hHc : H.card=m := by
    dsimp only [H]
    rw [card_union_of_disjoint (hBU.mono_right houter),(mem_powersetCard.mp p.val.property.2.2).2]
    omega
  refine ⟨⟨⟨F,H⟩,union_subset_union hAB p.val.property.1,
    union_subset (hB.trans W.val.property.2.1) (houter.trans hU),hHc⟩,?_,?_⟩
  · exact fixed_part_union_sdiff hAU hinner
  · exact fixed_part_union_sdiff hBU houter

@[expose] def rootLinkFiberEquiv (r M : ℕ) (ell : V → ℕ) (m : ℕ) (U A B : SimpleHypergraph V)
    (hU : U ⊆ completeEdges V r) (W : RootLinkFiber r M ell m U A B) :
    RootLinkFiber r M ell m U A B ≃ RootLinkFeasibleState U A ell (M-A.card) (m-B.card) where
  toFun := rootLinkRestrict r M ell m U A B
  invFun := rootLinkRestore r M ell m U A B hU W
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change A∪(p.val.val.1.val∩U)=p.val.val.1.val
      simp only [←p.property.1,sdiff_union_inter]
    · change B∪(p.val.val.2∩U)=p.val.val.2
      simp only [←p.property.2,sdiff_union_inter]
  right_inv p := by
    have hAU : Disjoint A U := by rw [←W.property.1]; exact sdiff_disjoint
    have hBU : Disjoint B U := by rw [←W.property.2]; exact sdiff_disjoint
    have houter := (mem_powersetCard.mp p.val.property.2.2).1
    have hinner := p.val.property.1.trans houter
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact fixed_part_union_inter hAU hinner
    · exact fixed_part_union_inter hBU houter
end LooseHamilton
