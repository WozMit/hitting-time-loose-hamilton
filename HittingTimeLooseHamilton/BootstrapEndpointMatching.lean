module

public import HittingTimeLooseHamilton.EndpointCutMatching
public import HittingTimeLooseHamilton.EndpointSpliceLegal
public import HittingTimeLooseHamilton.EndpointSpliceCounts
public import HittingTimeLooseHamilton.CompletionMatching

public section

/-! Actual endpoint-cut and splice marker families are pair matchings. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z t : V}

theorem endpointCutI_pairMatching (hs : LegalPrivateCompletion r M P {y,z})
    (hM : IsPairMatching M) {l : EndpointCutLabelI V}
    (hl : EndpointCutLegalI r M G P y z l) : IsPairMatching (l.markers M z) := by
  refine ⟨?_, endpointCutI_matching hs hM.2 hl⟩
  intro m hm
  rcases mem_insert.mp hm with rfl | hm
  · have hne : l.1 ≠ z := fun he => hl.endpoint_fresh (by simp [he])
    simp [hne]
  · exact hM.1 m hm

theorem endpointCutII_pairMatching (hs : LegalPrivateCompletion r M P {y,z})
    (hM : IsPairMatching M) {l : EndpointCutLabelII V}
    (hl : EndpointCutLegalII r M G P y z l) : IsPairMatching (l.markers M z) := by
  refine ⟨?_, endpointCutII_matching hs hM.2 hl⟩
  intro m hm
  rcases mem_insert.mp hm with rfl | hm
  · have hne : l.2.2.1 ≠ z := fun he => hl.endpoint_fresh (by simp [he])
    simp [hne]
  · exact hM.1 m (mem_erase.mp hm).2

/-- The splice's new pair and private block avoid every actual cut marker. -/
theorem endpointSpliceLegal_privateCompletion {D Q : Finset V} {a v : V}
    {K : Finset (Finset V)} (hK : K ⊆ M)
    (h : EndpointSpliceLegal r M G P D y z a t Q v) :
    LegalPrivateCompletion r (insert {a,z} K) Q {v,t} := by
  have hports : originalPorts (insert {a,z} K) ⊆ originalPorts M ∪ {a,z} := by
    intro x hx
    obtain ⟨m,hm,hxm⟩ := mem_biUnion.mp hx
    rcases mem_insert.mp hm with rfl | hm
    · exact mem_union_right _ hxm
    · exact mem_union_left _ (mem_biUnion.mpr ⟨m,hK hm,hxm⟩)
  refine ⟨h.private_card, by simp [h.newEndpoint_ne_t], ?_, ?_⟩
  · exact h.private_disjoint.mono_right (by intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> simp)
  · apply disjoint_left.mpr
    intro x hx hxM
    have hp := hports hxM
    rcases mem_union.mp hx with hxQ | hxpair
    · exact disjoint_left.mp h.private_disjoint hxQ (by
        simp only [mem_union, mem_insert, mem_singleton] at hp ⊢; tauto)
    · simp only [mem_insert, mem_singleton] at hxpair
      rcases hxpair with rfl | rfl
      · exact h.newEndpoint_fresh (by
          simp only [mem_union, mem_insert, mem_singleton] at hp ⊢; tauto)
      · exact h.target_fresh (by
          simp only [mem_union, mem_insert, mem_singleton] at hp ⊢; tauto)

theorem endpointSpliceI_pairMatching (hs : LegalPrivateCompletion r M P {y,z})
    (hM : IsPairMatching M) {l : EndpointCutLabelI V}
    (hl : EndpointCutLegalI r M G P y z l) {b : EndpointSpliceInnerLabel V}
    (hb : EndpointSpliceLegalI r M G P y z t l b) :
    IsPairMatching (insert {b.2,t} (l.markers M z)) :=
  (endpointSpliceLegal_privateCompletion (Subset.refl M) hb).augmented_matching
    (endpointCutI_pairMatching hs hM hl)

theorem endpointSpliceII_pairMatching (hs : LegalPrivateCompletion r M P {y,z})
    (hM : IsPairMatching M) {l : EndpointCutLabelII V}
    (hl : EndpointCutLegalII r M G P y z l) {b : EndpointSpliceInnerLabel V}
    (hb : EndpointSpliceLegalII r M G P y z t l b) :
    IsPairMatching (insert {b.2,t} (l.markers M z)) :=
  (endpointSpliceLegal_privateCompletion (erase_subset _ _) hb).augmented_matching
    (endpointCutII_pairMatching hs hM hl)

end LooseHamilton
