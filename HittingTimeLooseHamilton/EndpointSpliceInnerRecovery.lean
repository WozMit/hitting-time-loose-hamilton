module

public import HittingTimeLooseHamilton.EndpointSpliceRecovery

public section

/-! Recovery of the inserted edge's private block and endpoint. -/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Explicit directed endpoints determine the intrinsic unordered endpoint pair. -/
theorem MixedCycleOnWitness.edgeEndpointPair_eq_of_directions
    {r : ℕ} {A : Finset V} {N E : Finset (Finset V)}
    (C : MixedCycleOnWitness r A N E) (hr : 3 ≤ r) (e : ↥E) {a b : V}
    (ha : C.junction (C.slot.symm (.inr e)) = a)
    (hb : C.junction (finRotate C.length (C.slot.symm (.inr e))) = b) :
    edgeEndpointPair N E e.val = {a,b} := by
  rw [C.edgeEndpointPair_eq hr e]
  simp only [MixedCycleOnWitness.endpointPair, ha, hb]

/-- The unique directed edge entering `y` recovers its endpoint and all its
private vertices, jointly over arbitrary legal cut labels. -/
theorem endpointSpliceInner_recovery {r : ℕ} {M N G E : Finset (Finset V)}
    {A P B B' Q Q' : Finset V} {y z a a' t v v' : V}
    (C D : MixedCycleOnWitness r A N E) (hr : 3 ≤ r) (root : ↥N)
    (hroot : C.junction (C.slot.symm (.inl root)) = D.junction (D.slot.symm (.inl root)))
    (hyB : y ∈ B) (hyB' : y ∈ B')
    (hl : EndpointSpliceLegal r M G P B y z a t Q v)
    (hk : EndpointSpliceLegal r M G P B' y z a' t Q' v')
    (hel : {y,v} ∪ Q ∈ E) (hek : {y,v'} ∪ Q' ∈ E)
    (hstartl : C.junction (C.slot.symm (.inr ⟨{y,v} ∪ Q,hel⟩)) = v)
    (hstartk : D.junction (D.slot.symm (.inr ⟨{y,v'} ∪ Q',hek⟩)) = v')
    (hendl : C.junction (finRotate C.length (C.slot.symm (.inr ⟨{y,v} ∪ Q,hel⟩))) = y)
    (hendk : D.junction (finRotate D.length (D.slot.symm (.inr ⟨{y,v'} ∪ Q',hek⟩))) = y) :
    Q = Q' ∧ v = v' := by
  have he' : (⟨{y,v} ∪ Q,hel⟩ : ↥E) = ⟨{y,v'} ∪ Q',hek⟩ := by
    exact Sum.inr.inj (C.slot_label_eq_of_end D hr root hroot
      (.inr ⟨{y,v} ∪ Q,hel⟩) (.inr ⟨{y,v'} ∪ Q',hek⟩) (hendl.trans hendk.symm))
  have he : {y,v} ∪ Q = {y,v'} ∪ Q' := congrArg Subtype.val he'
  have hv : v = v' := by
    calc
      v = C.junction (C.slot.symm (.inr ⟨{y,v} ∪ Q,hel⟩)) := hstartl.symm
      _ = D.junction (D.slot.symm (.inr ⟨{y,v} ∪ Q,hel⟩)) :=
        C.slot_start_eq_of_root D hr root hroot _
      _ = D.junction (D.slot.symm (.inr ⟨{y,v'} ∪ Q',hek⟩)) := by rw [he']
      _ = v' := hstartk
  have recover : ∀ (B Q : Finset V) (a v : V), y ∈ B →
      EndpointSpliceLegal r M G P B y z a t Q v →
      ({y,v} ∪ Q) \ {y,v} = Q := by
    intro B Q a v hy h
    have hd : Disjoint Q ({y,v} : Finset V) := by
      apply h.private_disjoint.mono_right
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · simp [hy]
      · simp
    ext w
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hw, hn⟩
      exact hw.resolve_left hn
    · intro hw
      exact ⟨Or.inr hw, fun hp => disjoint_left.mp hd hw hp⟩
  constructor
  · rw [← recover B Q a v hyB hl, ← recover B' Q' a' v' hyB' hk, he, hv]
  · exact hv

end LooseHamilton
