module

public import HittingTimeLooseHamilton.AuxiliaryFrameParameters
public import HittingTimeLooseHamilton.SurgeryDirections
public import HittingTimeLooseHamilton.EndpointSpliceDirections
public import HittingTimeLooseHamilton.PrivateContraction

public section

/-! Actual directed roles in a frame, retaining every simultaneous marker direction. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- A role in one actual connected directed frame cycle. -/
@[expose] def Role (F : Frame r original) (E : Finset (Finset V)) (c : Finset V × V × V) : Prop :=
  ∃ C : MixedCycleOnWitness r F.active F.markers E, F.Directed C ∧
    ∃ he : c.1 ∪ {c.2.1,c.2.2} ∈ E,
      C.privateBlock ⟨_,he⟩ = c.1 ∧
      C.junction (C.slot.symm (.inr ⟨_,he⟩)) = c.2.1 ∧
      C.junction (finRotate C.length (C.slot.symm (.inr ⟨_,he⟩))) = c.2.2

/-- Existing-edge roles are counted as edge sets, with no witness multiplicity. -/
@[expose] def roleFamily (F : Frame r original) (H : Finset (Finset V)) (c : Finset V × V × V) :=
  (F.cycleFamily H).filter (fun E => F.Role E c)

lemma role_contract (F : Frame r original) {H E : Finset (Finset V)}
    {c : Finset V × V × V} (hc : F.LegalCandidate c)
    (hE : E ∈ F.cycleFamily H) (hrole : F.Role E c) :
    E.erase (c.1 ∪ {c.2.1,c.2.2}) ∈ F.completionFamily H c := by
  obtain ⟨C,hD,he,hP,hu,hv⟩ := hrole
  let e : ↥E := ⟨_,he⟩
  have hpair : C.endpointPair e = {c.2.1,c.2.2} := by
    simp only [MixedCycleOnWitness.endpointPair, e, hu, hv]
  let A := C.contractUnmarked e hc.1.ports_disjoint
  have hold (p : V × V) (hp : Starts C p) : Starts A p := by
    obtain ⟨m,hm,hs⟩ := hp
    refine ⟨⟨m.val,mem_insert_of_mem m.property⟩,hm,?_⟩
    exact (C.contract_old_marker_start e _ _ m).trans hs
  have hnew : Starts A c.2 := by
    refine ⟨⟨C.endpointPair e,mem_insert_self _ _⟩,hpair,?_⟩
    exact (C.contract_new_marker_start e _ _).trans hu
  have hresult : ∃ A : MixedCycleOnWitness r (F.active \ C.privateBlock e)
      (insert (C.endpointPair e) F.markers) (E.erase e.val),
      F.Directed A ∧ Starts A c.2 :=
    ⟨A,⟨hold _ hD.1,fun p hp => hold p (hD.2 p hp)⟩,hnew⟩
  rw [hpair,show C.privateBlock e = c.1 from hP] at hresult
  exact (F.mem_completionFamily H c _).mpr
    ⟨(erase_subset _ _).trans ((F.mem_cycleFamily H E).mp hE).1,hresult⟩

lemma completion_edge_absent (F : Frame r original) (hr : 3 ≤ r)
    {H E : Finset (Finset V)} {c : Finset V × V × V}
    (hc : F.LegalCandidate c) (hE : E ∈ F.completionFamily H c) :
    c.1 ∪ {c.2.1,c.2.2} ∉ E := by
  obtain ⟨_,C,_⟩ := (F.mem_completionFamily H c E).mp hE
  have hp : c.1.Nonempty := by rw [← card_pos,hc.1.private_card]; omega
  obtain ⟨v,hv⟩ := hp
  intro he
  exact (mem_sdiff.mp (C.edge_subset_active he (mem_union_left _ hv))).2 hv

lemma completion_expand (F : Frame r original) (hr : 3 ≤ r)
    {H E : Finset (Finset V)} {c : Finset V × V × V}
    (hc : F.LegalCandidate c) (hedge : c.1 ∪ {c.2.1,c.2.2} ∈ F.rawHost H)
    (hE : E ∈ F.completionFamily H c) :
    insert (c.1 ∪ {c.2.1,c.2.2}) E ∈ F.roleFamily H c := by
  have hnot := F.completion_edge_absent hr hc hE
  obtain ⟨hsub,C,hD,hstart⟩ := (F.mem_completionFamily H c E).mp hE
  have hq : {c.2.1,c.2.2} ∉ F.markers :=
    new_pair_not_mem (by simp) (hc.1.ports_disjoint.mono_left (subset_union_right))
  have hPS : Disjoint c.1 (F.active \ c.1) := disjoint_sdiff_self_right
  have hnew : {c.2.1,c.2.2} ∪ c.1 ∉ E := by rwa [union_comm]
  let p : ↥(insert {c.2.1,c.2.2} F.markers) := ⟨_,mem_insert_self _ _⟩
  let A := C.expand p c.1 hc.1.private_card hPS hnew
  have hold (q : V × V) (hm : {q.1,q.2} ∈ F.markers) (hs : Starts C q) :
      Starts A q := by
    obtain ⟨m,hmp,hms⟩ := hs
    have hne : m.val ≠ p.val := by
      intro he
      apply hq
      have hqp : {q.1,q.2} = {c.2.1,c.2.2} := hmp.symm.trans he
      rwa [hqp] at hm
    refine ⟨⟨m.val,mem_erase.mpr ⟨hne,m.property⟩⟩,hmp,?_⟩
    exact (C.expand_old_marker_start p c.1 _ _ _ m hne).trans hms
  have hs : C.junction (C.slot.symm (.inl p)) = c.2.1 := by
    obtain ⟨m,hm,hh⟩ := hstart
    have he : m = p := Subtype.ext hm
    simpa only [he] using hh
  have ht : C.junction (finRotate C.length (C.slot.symm (.inl p))) = c.2.2 := by
    have hx := C.slot_edge (C.slot.symm (.inl p))
    simp only [Equiv.apply_symm_apply, p] at hx
    rw [hs] at hx
    have hne := C.junction_next_ne (C.slot.symm (.inl p))
    rw [hs] at hne
    have hz : c.2.1 ≠ c.2.2 := by
      intro h
      have := hc.1.pair_card
      simp [h] at this
    have hv : c.2.2 ∈ ({c.2.1, C.junction (finRotate C.length (C.slot.symm (.inl p)))} : Finset V) := by
      rw [← hx]
      simp
    exact ((mem_insert.mp hv).resolve_left (Ne.symm hz) |> mem_singleton.mp).symm
  have hx : ∃ A : MixedCycleOnWitness r ((F.active \ c.1) ∪ c.1)
      ((insert {c.2.1,c.2.2} F.markers).erase {c.2.1,c.2.2})
      (insert ({c.2.1,c.2.2} ∪ c.1) E),
      F.Directed A ∧ ∃ he : {c.2.1,c.2.2} ∪ c.1 ∈ insert ({c.2.1,c.2.2} ∪ c.1) E,
      A.privateBlock ⟨_,he⟩ = c.1 ∧
      A.junction (A.slot.symm (.inr ⟨_,he⟩)) = c.2.1 ∧
      A.junction (finRotate A.length (A.slot.symm (.inr ⟨_,he⟩))) = c.2.2 := by
    refine ⟨A,⟨hold _ F.property.root_mem hD.1,
      fun q hq => hold q (F.property.relative_mem q hq) (hD.2 q hq)⟩,
      mem_insert_self _ _,C.expand_privateBlock p c.1 _ _ _,?_,?_⟩
    · exact (C.expand_new_ordinary_start p c.1 _ _ _).trans hs
    · exact (C.expand_new_ordinary_end p c.1 _ _ _).trans ht
  rw [sdiff_union_of_subset (subset_union_left.trans hc.2.1),erase_insert hq,union_comm] at hx
  obtain ⟨A,hA,hrole⟩ := hx
  apply mem_filter.mpr
  exact ⟨(F.mem_cycleFamily H _).mpr
    ⟨insert_subset hedge hsub,⟨A,hA⟩⟩,⟨A,hA,hrole⟩⟩

end LooseHamilton.AuxiliaryFrame.Frame
