module

public import HittingTimeLooseHamilton.EndpointSpliceImages

public section

/-! Joint injectivity of endpoint splicing, over all cut and inner labels. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z t : V}

namespace MixedCycleOnWitness
variable {A : Finset V} {N E E' : Finset (Finset V)}
theorem castEdges_marker_start (C : MixedCycleOnWitness r A N E) (h : E = E') (m : ↥N) :
    (h ▸ C).junction ((h ▸ C).slot.symm (.inl m)) = C.junction (C.slot.symm (.inl m)) := by
  subst E'; rfl

theorem castEdges_edge_start (C : MixedCycleOnWitness r A N E) (h : E = E')
    (e : Finset V) (he : e ∈ E) :
    (h ▸ C).junction ((h ▸ C).slot.symm (.inr ⟨e,h ▸ he⟩)) =
      C.junction (C.slot.symm (.inr ⟨e,he⟩)) := by
  subst E'; rfl

theorem castEdges_edge_end (C : MixedCycleOnWitness r A N E) (h : E = E')
    (e : Finset V) (he : e ∈ E) :
    (h ▸ C).junction (finRotate (h ▸ C).length ((h ▸ C).slot.symm (.inr ⟨e,h ▸ he⟩))) =
      C.junction (finRotate C.length (C.slot.symm (.inr ⟨e,he⟩))) := by
  subst E'; rfl
end MixedCycleOnWitness

theorem endpointSpliceI_joint_injective (hr : 3 ≤ r)
    {l k : EndpointCutLabelI V} {b c : EndpointSpliceInnerLabel V}
    {F F' : Finset (Finset V)}
    (hl : EndpointCutLegalI r M G P y z l) (hk : EndpointCutLegalI r M G P y z k)
    (hb : EndpointSpliceLegalI r M G P y z t l b)
    (hc : EndpointSpliceLegalI r M G P y z t k c)
    (hF : F ∈ endpointSpliceInputFamilyI r M G P y z t l b)
    (hF' : F' ∈ endpointSpliceInputFamilyI r M G P y z t k c)
    (I : EndpointSpliceImageI r M G P y z t l b F)
    (J : EndpointSpliceImageI r M G P y z t k c F')
    (heq : endpointSpliceOutputI y l b F = endpointSpliceOutputI y k c F') :
    l = k ∧ b = c ∧ F = F' := by
  have H : l = k ∧ b = c := by
    let C := heq ▸ I.cycle
    let D := J.cycle
    have hroot : C.junction (C.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) =
        D.junction (D.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) := by
      exact (I.cycle.castEdges_marker_start heq _).trans (I.root_start.trans J.root_start.symm)
    have hel : l.edge y ∈ endpointSpliceOutputI y k c F' := heq ▸ (by simp [endpointSpliceOutputI])
    have hen : endpointSpliceNewEdge y b ∈ endpointSpliceOutputI y k c F' := heq ▸ (by simp [endpointSpliceOutputI])
    have hcs : C.junction (C.slot.symm (.inr ⟨l.edge y,hel⟩)) = y :=
      (I.cycle.castEdges_edge_start heq _ _).trans I.cut_start
    have his : C.junction (C.slot.symm (.inr ⟨endpointSpliceNewEdge y b,hen⟩)) = b.2 :=
      (I.cycle.castEdges_edge_start heq _ _).trans I.incoming_start
    have hie : C.junction (finRotate C.length (C.slot.symm (.inr ⟨endpointSpliceNewEdge y b,hen⟩))) = y :=
      (I.cycle.castEdges_edge_end heq _ _).trans I.incoming_end
    have hcr : edgeEndpointPair (insert {t,z} M) (endpointSpliceOutputI y k c F') (l.edge y) = {y,l.1} := heq ▸ I.cut_role
    have hlk := endpointSpliceCutI_recovery C D hr ⟨{t,z},mem_insert_self _ _⟩ hroot hl hk
      hel (by simp [endpointSpliceOutputI]) hcs J.cut_start hcr J.cut_role
    have hbc := endpointSpliceInner_recovery C D hr ⟨{t,z},mem_insert_self _ _⟩ hroot
      (by simp [EndpointCutLabelI.deleted]) (by simp [EndpointCutLabelI.deleted]) hb hc
      hen (by simp [endpointSpliceOutputI, endpointSpliceNewEdge]) his J.incoming_start hie J.incoming_end
    exact ⟨hlk,Prod.ext hbc.1 hbc.2⟩
  refine ⟨H.1,H.2,?_⟩
  have hh := congrArg (fun E => E \ {endpointSpliceNewEdge y b,l.edge y}) heq
  rw [endpointSpliceOutputI_recover hF] at hh
  rw [H.1,H.2,endpointSpliceOutputI_recover hF'] at hh
  exact hh

theorem endpointSpliceII_joint_injective (hr : 3 ≤ r)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M)
    {l k : EndpointCutLabelII V} {b c : EndpointSpliceInnerLabel V}
    {F F' : Finset (Finset V)}
    (hl : EndpointCutLegalII r M G P y z l) (hk : EndpointCutLegalII r M G P y z k)
    (hb : EndpointSpliceLegalII r M G P y z t l b)
    (hc : EndpointSpliceLegalII r M G P y z t k c)
    (hF : F ∈ endpointSpliceInputFamilyII r M G P y z t l b)
    (hF' : F' ∈ endpointSpliceInputFamilyII r M G P y z t k c)
    (I : EndpointSpliceImageII r M G P y z t l b F)
    (J : EndpointSpliceImageII r M G P y z t k c F')
    (heq : endpointSpliceOutputII y l b F = endpointSpliceOutputII y k c F') :
    l = k ∧ b = c ∧ F = F' := by
  have H : l = k ∧ b = c := by
    let C := heq ▸ I.cycle
    let D := J.cycle
    have hroot : C.junction (C.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) =
        D.junction (D.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) := by
      exact (I.cycle.castEdges_marker_start heq _).trans (I.root_start.trans J.root_start.symm)
    have hel : l.firstEdge y ∈ endpointSpliceOutputII y k c F' := heq ▸ (by simp [endpointSpliceOutputII])
    have hen : endpointSpliceNewEdge y b ∈ endpointSpliceOutputII y k c F' := heq ▸ (by simp [endpointSpliceOutputII])
    have hcs : C.junction (C.slot.symm (.inr ⟨l.firstEdge y,hel⟩)) = y :=
      (I.cycle.castEdges_edge_start heq _ _).trans I.cut_start
    have his : C.junction (C.slot.symm (.inr ⟨endpointSpliceNewEdge y b,hen⟩)) = b.2 :=
      (I.cycle.castEdges_edge_start heq _ _).trans I.incoming_start
    have hie : C.junction (finRotate C.length (C.slot.symm (.inr ⟨endpointSpliceNewEdge y b,hen⟩))) = y :=
      (I.cycle.castEdges_edge_end heq _ _).trans I.incoming_end
    have hcr : edgeEndpointPair (insert {t,z} M) (endpointSpliceOutputII y k c F') (l.firstEdge y) = {y,l.1} := heq ▸ I.cut_role
    have hlk := endpointSpliceCutII_recovery C D hr ⟨{t,z},mem_insert_self _ _⟩ hroot
      (fun _ h => mem_insert_of_mem h) hM hy hl hk
      hel (by simp [endpointSpliceOutputII])
      (heq ▸ (by simp [endpointSpliceOutputII])) (by simp [endpointSpliceOutputII])
      hcs J.cut_start hcr J.cut_role (heq ▸ I.second_role) J.second_role
    have hbc := endpointSpliceInner_recovery C D hr ⟨{t,z},mem_insert_self _ _⟩ hroot
      (by simp [EndpointCutLabelII.deleted]) (by simp [EndpointCutLabelII.deleted]) hb hc
      hen (by simp [endpointSpliceOutputII, endpointSpliceNewEdge]) his J.incoming_start hie J.incoming_end
    exact ⟨hlk,Prod.ext hbc.1 hbc.2⟩
  refine ⟨H.1,H.2,?_⟩
  have hh := congrArg (fun E => E \ {endpointSpliceNewEdge y b,l.firstEdge y,l.secondEdge}) heq
  rw [endpointSpliceOutputII_recover hF] at hh
  rw [H.1,H.2,endpointSpliceOutputII_recover hF'] at hh
  exact hh

theorem endpointSplice_types_disjoint (hr : 3 ≤ r)
    {l : EndpointCutLabelI V} {k : EndpointCutLabelII V}
    {b c : EndpointSpliceInnerLabel V} {F F' : Finset (Finset V)}
    (hl : EndpointCutLegalI r M G P y z l) (hk : EndpointCutLegalII r M G P y z k)
    (I : EndpointSpliceImageI r M G P y z t l b F)
    (J : EndpointSpliceImageII r M G P y z t k c F')
    (heq : endpointSpliceOutputI y l b F = endpointSpliceOutputII y k c F') : False := by
  let C := heq ▸ I.cycle
  let D := J.cycle
  have hroot : C.junction (C.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) =
      D.junction (D.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) := by
    exact (I.cycle.castEdges_marker_start heq _).trans (I.root_start.trans J.root_start.symm)
  have hel : l.edge y ∈ endpointSpliceOutputII y k c F' := heq ▸ (by simp [endpointSpliceOutputI])
  have hcs : C.junction (C.slot.symm (.inr ⟨l.edge y,hel⟩)) = y :=
    (I.cycle.castEdges_edge_start heq _ _).trans I.cut_start
  exact endpointSpliceCut_types_disjoint C D hr ⟨{t,z},mem_insert_self _ _⟩ hroot hl hk
    hel (by simp [endpointSpliceOutputII]) hcs J.cut_start (heq ▸ I.cut_role) J.cut_role

end LooseHamilton
