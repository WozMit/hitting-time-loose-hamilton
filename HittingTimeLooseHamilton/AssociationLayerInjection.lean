module

public import HittingTimeLooseHamilton.AssociationLayerModels

public section

/-! An injective encoding of every legal degree-preserving association switch.
Decoding recovers both original edges, both distinguished vertices, and the
whole original graph; all switching labels remain explicit in the counting argument. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r t : ℕ} {d : V → ℕ} {y : V} {B : Finset V}

theorem forward_valid (x : associationForwardIncidence r d y B t) :
    AssociationSwitchValid x.1.val.val x.2.1.val.1 x.2.2.val.1 x.2.1.val.2 x.2.2.val.2 := by
  obtain ⟨he,hz,hy,hzB⟩ := (mem_associationSources _ _ _ _).mp x.2.1.property
  obtain ⟨hf,ha,haB,hdis,hne,hnf⟩ := (mem_associationGoodTargets _ _ _ _ _).mp x.2.2.property
  exact ⟨he,hf,hdis,hz,ha,hne,hnf⟩

/-- Send a legal switch to the resulting graph in the preceding association
layer, labelled by the two incidences that uniquely reverse it. -/
@[expose] def associationEncodeSwitch (hyB : y ∉ B)
    (x : associationForwardIncidence r d y B t) : associationReverseIncidence r d y B (t-1) := by
  let F := x.1
  let e := x.2.1.val.1
  let z := x.2.1.val.2
  let f := x.2.2.val.1
  let a := x.2.2.val.2
  let h := forward_valid x
  refine ⟨⟨h.fixedState F.val.property.1 F.val.property.2, ?_⟩,
    ⟨((switchedEdge e z a,a),(switchedEdge f a z,z)), ?_⟩⟩
  · obtain ⟨_,_,hy,hzB⟩ := (mem_associationSources _ _ _ _).mp x.2.1.property
    have haB := ((mem_associationGoodTargets _ _ _ _ _).mp x.2.2.property).2.2.1
    have hs := h.statistic_add_one hy hyB hzB haB
    have hF := F.property
    change associationStatistic (associationSwitch F.val.val e f z a) y B = t-1
    change associationStatistic (associationSwitch F.val.val e f z a) y B + 1 =
      associationStatistic F.val.val y B at hs
    omega
  · apply mem_product.mpr
    obtain ⟨_,_,hy,hzB⟩ := (mem_associationSources _ _ _ _).mp x.2.1.property
    have hyz : y ≠ z := fun heq => hyB (heq.symm ▸ hzB)
    have hay : a ≠ y := (ne_of_mem_of_not_mem hy h.a_not_mem).symm
    constructor
    · apply (mem_associationReverseHeads _ _ _).mpr
      refine ⟨?_,by simp,?_,hay⟩
      · exact mem_insert_self _ _
      · exact (mem_switchedEdge _ _ _ _).mpr (Or.inr ⟨hyz,hy⟩)
    · apply (mem_associationBIncidences _ _ _).mpr
      exact ⟨mem_insert_of_mem (mem_insert_self _ _),by simp,hzB⟩

/-- The complete original data, without proof fields. -/
@[expose] def associationForwardData (x : associationForwardIncidence r d y B t) :
    SimpleHypergraph V × (Finset V × V) × (Finset V × V) :=
  (x.1.val.val,x.2.1.val,x.2.2.val)

/-- Decode a reverse label. The formula is total; validity is needed only to
prove that it reverses an encoded legal move. -/
@[expose] def associationDecodeSwitch (x : associationReverseIncidence r d y B (t-1)) :
    SimpleHypergraph V × (Finset V × V) × (Finset V × V) :=
  (associationSwitch x.1.val.val x.2.val.1.1 x.2.val.2.1 x.2.val.1.2 x.2.val.2.2,
    (switchedEdge x.2.val.1.1 x.2.val.1.2 x.2.val.2.2,x.2.val.2.2),
    (switchedEdge x.2.val.2.1 x.2.val.2.2 x.2.val.1.2,x.2.val.1.2))

theorem associationDecodeEncode (hyB : y ∉ B) (x : associationForwardIncidence r d y B t) :
    associationDecodeSwitch (associationEncodeSwitch hyB x) = associationForwardData x := by
  let h := forward_valid x
  change (associationSwitch (associationSwitch x.1.val.val x.2.1.val.1 x.2.2.val.1 x.2.1.val.2 x.2.2.val.2)
      (switchedEdge x.2.1.val.1 x.2.1.val.2 x.2.2.val.2)
      (switchedEdge x.2.2.val.1 x.2.2.val.2 x.2.1.val.2) x.2.2.val.2 x.2.1.val.2,
    (switchedEdge (switchedEdge x.2.1.val.1 x.2.1.val.2 x.2.2.val.2) x.2.2.val.2 x.2.1.val.2,x.2.1.val.2),
    (switchedEdge (switchedEdge x.2.2.val.1 x.2.2.val.2 x.2.1.val.2) x.2.1.val.2 x.2.2.val.2,x.2.2.val.2)) = _
  rw [h.reverse,switchedEdge_reverse h.z_mem h.a_not_mem,switchedEdge_reverse h.a_mem h.z_not_mem]
  rfl

theorem associationForwardData_injective :
    Function.Injective (@associationForwardData V _ _ r t d y B) := by
  rintro ⟨F,⟨s,hs⟩,⟨p,hp⟩⟩ ⟨G,⟨u,hu⟩,⟨q,hq⟩⟩ h
  have hFG : F = G := Subtype.ext (Subtype.ext (congrArg Prod.fst h))
  subst G
  have hsu : s = u := congrArg (fun z => z.2.1) h
  subst u
  have hpq : p = q := congrArg (fun z => z.2.2) h
  subst q
  rfl

/-- Joint injectivity over graphs and all four switching labels. -/
theorem associationEncodeSwitch_injective (hyB : y ∉ B) :
    Function.Injective (@associationEncodeSwitch V _ _ r t d y B hyB) := by
  intro x x' h
  apply associationForwardData_injective
  rw [← associationDecodeEncode hyB x,← associationDecodeEncode hyB x',h]
end LooseHamilton
