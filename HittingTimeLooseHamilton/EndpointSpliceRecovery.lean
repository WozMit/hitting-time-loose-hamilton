module

public import HittingTimeLooseHamilton.ActiveOrientationUniqueness
public import HittingTimeLooseHamilton.EndpointSpliceModels
public import HittingTimeLooseHamilton.EndpointCutUniqueness
public import HittingTimeLooseHamilton.EndpointCutLegalBounds
public import HittingTimeLooseHamilton.EndpointCutCoreFacts

public section

/-! Joint recovery of endpoint labels from actual expanded edge sets. -/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem pair_right_recovery {x a b : V} (ha : a ≠ x)
    (h : ({x,a} : Finset V) = {x,b}) : a = b := by
  have hm : a ∈ ({x,b} : Finset V) := h ▸ (by simp)
  simpa [ha] using hm

private theorem cut_private_recovery {B R : Finset V} (h : Disjoint R B) :
    (B ∪ R) \ B = R := by
  ext v
  simp only [mem_sdiff, mem_union]
  constructor
  · rintro ⟨hmem, hn⟩
    exact hmem.resolve_left hn
  · intro hv
    exact ⟨Or.inr hv, fun hb => disjoint_left.mp h hv hb⟩

private theorem first_edge_unique {r : ℕ} {N E : Finset (Finset V)}
    {A : Finset V} {y : V} (C D : MixedCycleOnWitness r A N E)
    (hr : 3 ≤ r) (root : ↥N)
    (hroot : C.junction (C.slot.symm (.inl root)) = D.junction (D.slot.symm (.inl root)))
    {e f : Finset V} (he : e ∈ E) (hf : f ∈ E)
    (hye : C.junction (C.slot.symm (.inr ⟨e,he⟩)) = y)
    (hyf : D.junction (D.slot.symm (.inr ⟨f,hf⟩)) = y) : e = f := by
  have h := C.slot_label_eq_of_start D hr root hroot (.inr ⟨e,he⟩) (.inr ⟨f,hf⟩)
    (hye.trans hyf.symm)
  exact congrArg Subtype.val (Sum.inr.inj h)

theorem endpointSpliceCutI_recovery {r : ℕ} {M N G E : Finset (Finset V)}
    {A P : Finset V} {y z : V} {l k : EndpointCutLabelI V}
    (C D : MixedCycleOnWitness r A N E) (hr : 3 ≤ r) (root : ↥N)
    (hroot : C.junction (C.slot.symm (.inl root)) = D.junction (D.slot.symm (.inl root)))
    (hl : EndpointCutLegalI r M G P y z l) (hk : EndpointCutLegalI r M G P y z k)
    (hel : l.edge y ∈ E) (hek : k.edge y ∈ E)
    (hstartl : C.junction (C.slot.symm (.inr ⟨l.edge y,hel⟩)) = y)
    (hstartk : D.junction (D.slot.symm (.inr ⟨k.edge y,hek⟩)) = y)
    (hrolel : edgeEndpointPair N E (l.edge y) = {y,l.1})
    (hrolek : edgeEndpointPair N E (k.edge y) = {y,k.1}) : l = k := by
  have he : l.edge y = k.edge y := first_edge_unique C D hr root hroot hel hek hstartl hstartk
  have hne : l.1 ≠ y := by intro h; exact hl.endpoint_fresh (by simp [h])
  have ha : l.1 = k.1 := pair_right_recovery hne (hrolel.symm.trans (he ▸ hrolek))
  have recover : ∀ j, EndpointCutLegalI r M G P y z j → j.edge y \ {y,j.1} = j.2 := by
    intro j hj
    apply cut_private_recovery
    apply hj.private_disjoint.mono_right
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp
  apply Prod.ext ha
  rw [← recover l hl, ← recover k hk, he, ha]

theorem endpointSpliceCutII_recovery {r : ℕ} {M N G E : Finset (Finset V)}
    {A P : Finset V} {y z : V} {l k : EndpointCutLabelII V}
    (C D : MixedCycleOnWitness r A N E) (hr : 3 ≤ r) (root : ↥N)
    (hroot : C.junction (C.slot.symm (.inl root)) = D.junction (D.slot.symm (.inl root)))
    (hMN : M ⊆ N) (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M)
    (hl : EndpointCutLegalII r M G P y z l) (hk : EndpointCutLegalII r M G P y z k)
    (he1l : l.firstEdge y ∈ E) (he1k : k.firstEdge y ∈ E)
    (he2l : l.secondEdge ∈ E) (he2k : k.secondEdge ∈ E)
    (hstartl : C.junction (C.slot.symm (.inr ⟨l.firstEdge y,he1l⟩)) = y)
    (hstartk : D.junction (D.slot.symm (.inr ⟨k.firstEdge y,he1k⟩)) = y)
    (hr1l : edgeEndpointPair N E (l.firstEdge y) = {y,l.1})
    (hr1k : edgeEndpointPair N E (k.firstEdge y) = {y,k.1})
    (hr2l : edgeEndpointPair N E l.secondEdge = {l.2.1,l.2.2.1})
    (hr2k : edgeEndpointPair N E k.secondEdge = {k.2.1,k.2.2.1}) : l = k := by
  have ports : ∀ j, EndpointCutLegalII r M G P y z j →
      j.1 ∈ originalPorts M ∧ j.2.1 ∈ originalPorts M := by
    intro j hj
    constructor <;> apply mem_biUnion.mpr <;>
      exact ⟨j.oldMarker, hj.oldMarker_mem, by simp [EndpointCutLabelII.oldMarker]⟩
  have he1 : l.firstEdge y = k.firstEdge y := first_edge_unique C D hr root hroot he1l he1k hstartl hstartk
  have hne : l.1 ≠ y := by intro h; exact hy (h ▸ (ports l hl).1)
  have hu : l.1 = k.1 := pair_right_recovery hne (hr1l.symm.trans (he1 ▸ hr1k))
  have hv : l.2.1 = k.2.1 := by
    rw [← endpointCutMate_eq hM y _ _ hl.ports_ne hl.oldMarker_mem,
      ← endpointCutMate_eq hM y _ _ hk.ports_ne hk.oldMarker_mem, hu]
  have he2 : l.secondEdge = k.secondEdge := by
    exact congrArg Subtype.val (C.ordinary_incident_marked_unique (v := l.2.1)
      ⟨l.oldMarker, hMN hl.oldMarker_mem⟩ ⟨l.secondEdge,he2l⟩ ⟨k.secondEdge,he2k⟩
      (by simp [EndpointCutLabelII.oldMarker])
      (by simp [EndpointCutLabelII.secondEdge])
      (by simp [EndpointCutLabelII.secondEdge, hv]))
  have han : l.2.2.1 ≠ l.2.1 := by
    intro h
    apply hl.endpoint_fresh
    simp [h, (ports l hl).2]
  have ha : l.2.2.1 = k.2.2.1 := by
    apply pair_right_recovery han
    rw [← hr2l, he2, hr2k, hv]
  have recover : ∀ j, EndpointCutLegalII r M G P y z j →
      j.firstEdge y \ {y,j.1} = j.2.2.2.1 ∧
      j.secondEdge \ {j.2.1,j.2.2.1} = j.2.2.2.2 := by
    intro j hj
    have hp := ports j hj
    constructor
    · apply cut_private_recovery
      apply hj.first_private_disjoint.mono_right
      intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · simp
      · simp [hp.1]
    · apply cut_private_recovery
      apply hj.second_private_disjoint.mono_right
      intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · simp [hp.2]
      · simp
  have hR : l.2.2.2.1 = k.2.2.2.1 := by rw [← (recover l hl).1, ← (recover k hk).1, he1, hu]
  have hT : l.2.2.2.2 = k.2.2.2.2 := by rw [← (recover l hl).2, ← (recover k hk).2, he2, hv, ha]
  exact Prod.ext hu (Prod.ext hv (Prod.ext ha (Prod.ext hR hT)))

theorem endpointSpliceCut_types_disjoint {r : ℕ} {M N G E : Finset (Finset V)}
    {A P : Finset V} {y z : V} {l : EndpointCutLabelI V} {k : EndpointCutLabelII V}
    (C D : MixedCycleOnWitness r A N E) (hr : 3 ≤ r) (root : ↥N)
    (hroot : C.junction (C.slot.symm (.inl root)) = D.junction (D.slot.symm (.inl root)))
    (hl : EndpointCutLegalI r M G P y z l) (hk : EndpointCutLegalII r M G P y z k)
    (hel : l.edge y ∈ E) (hek : k.firstEdge y ∈ E)
    (hstartl : C.junction (C.slot.symm (.inr ⟨l.edge y,hel⟩)) = y)
    (hstartk : D.junction (D.slot.symm (.inr ⟨k.firstEdge y,hek⟩)) = y)
    (hrl : edgeEndpointPair N E (l.edge y) = {y,l.1})
    (hrk : edgeEndpointPair N E (k.firstEdge y) = {y,k.1}) : False := by
  have he : l.edge y = k.firstEdge y := first_edge_unique C D hr root hroot hel hek hstartl hstartk
  have hne : l.1 ≠ y := by intro h; exact hl.endpoint_fresh (by simp [h])
  have ha : l.1 = k.1 := pair_right_recovery hne (hrl.symm.trans (he ▸ hrk))
  have hp : k.1 ∈ originalPorts M :=
    mem_biUnion.mpr ⟨k.oldMarker, hk.oldMarker_mem, by simp [EndpointCutLabelII.oldMarker]⟩
  exact hl.endpoint_fresh (by simp [ha, hp])


end LooseHamilton
