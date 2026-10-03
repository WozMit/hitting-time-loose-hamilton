module

public import HittingTimeLooseHamilton.FrameEntropyBridgeCounting
public import HittingTimeLooseHamilton.ActiveOrientationUniqueness

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- On a legal candidate the endpoint role already determines the private block. -/
theorem role_iff_endpoints (F : Frame r original) (hr : 3 ≤ r)
    {E : Finset (Finset V)} {c : Finset V × V × V} (hc : F.LegalCandidate c) :
    F.Role E c ↔
      ∃ C : MixedCycleOnWitness r F.active F.markers E, F.Directed C ∧
        ∃ he : c.1 ∪ {c.2.1,c.2.2} ∈ E,
          C.junction (C.slot.symm (.inr ⟨_,he⟩)) = c.2.1 ∧
          C.junction (finRotate C.length (C.slot.symm (.inr ⟨_,he⟩))) = c.2.2 := by
  constructor
  · rintro ⟨C,hD,he,_,hu,hv⟩
    exact ⟨C,hD,he,hu,hv⟩
  · rintro ⟨C,hD,he,hu,hv⟩
    refine ⟨C,hD,he,?_,hu,hv⟩
    rw [C.private_eq_sdiff_endpointPair hr ⟨_,he⟩,
      C.edgeEndpointPair_eq hr ⟨_,he⟩]
    have hp : C.endpointPair ⟨_,he⟩ = {c.2.1,c.2.2} := by
      simp only [MixedCycleOnWitness.endpointPair,hu,hv]
    rw [hp]
    exact union_sdiff_cancel_right hc.1.private_pair_disjoint

/-- One fixed witnessing presentation of a counted cycle suffices to test a role:
the root direction fixes all slot endpoints. -/
theorem role_iff_in_witness (F : Frame r original) (hr : 3 ≤ r)
    {E : Finset (Finset V)} {c : Finset V × V × V} (hc : F.LegalCandidate c)
    (C : MixedCycleOnWitness r F.active F.markers E) (hC : F.Directed C) :
    F.Role E c ↔ ∃ he : c.1 ∪ {c.2.1,c.2.2} ∈ E,
      C.junction (C.slot.symm (.inr ⟨_,he⟩)) = c.2.1 ∧
      C.junction (finRotate C.length (C.slot.symm (.inr ⟨_,he⟩))) = c.2.2 := by
  rw [F.role_iff_endpoints hr hc]
  constructor
  · rintro ⟨D,hD,he,hu,hv⟩
    obtain ⟨m,hm,hrootC⟩ := hC.1
    obtain ⟨m',hm',hrootD⟩ := hD.1
    have heq : m' = m := Subtype.ext (hm'.trans hm.symm)
    subst m'
    have hroot := hrootC.trans hrootD.symm
    exact ⟨he,(C.slot_start_eq_of_root D hr m hroot _).trans hu,
      (C.slot_end_eq_of_root D hr m hroot _).trans hv⟩
  · rintro ⟨he,hu,hv⟩
    exact ⟨C,hC,he,hu,hv⟩

end LooseHamilton.AuxiliaryFrame.Frame
