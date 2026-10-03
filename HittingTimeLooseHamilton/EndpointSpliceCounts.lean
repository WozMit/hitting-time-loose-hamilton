module

public import HittingTimeLooseHamilton.ActiveDirectedCounting
public import HittingTimeLooseHamilton.EndpointSpliceModels
public import HittingTimeLooseHamilton.EndpointCoreCounts

public section

/-! The inner summands are precisely the manuscript's existing directed counts
on the fixed induced host after both deletions. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem splice_markers_survive {r : ℕ} {M K G : Finset (Finset V)}
    {P D Q : Finset V} {y z a t v : V}
    (hK : K ⊆ M)
    (hcore : ∀ m ∈ insert ({a,z} : Finset V) K, m ⊆ univ \ (P ∪ D))
    (h : EndpointSpliceLegal r M G P D y z a t Q v) :
    ∀ m ∈ insert ({v,t} : Finset V) (insert {a,z} K), m ⊆ univ \ (P ∪ D ∪ Q) := by
  intro m hm w hw
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro hdel
  rcases mem_insert.mp hm with rfl | hm
  · simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · rcases mem_union.mp hdel with hpd | hq
      · exact h.newEndpoint_fresh (mem_union_left _ (mem_union_left _ hpd))
      · exact disjoint_left.mp h.private_disjoint hq (by simp)
    · rcases mem_union.mp hdel with hpd | hq
      · exact h.target_fresh (mem_union_left _ (mem_union_left _ hpd))
      · exact disjoint_left.mp h.private_disjoint hq (by simp)
  · rcases mem_union.mp hdel with hpd | hq
    · exact (mem_sdiff.mp (hcore m hm hw)).2 hpd
    · apply disjoint_left.mp h.private_disjoint hq
      rcases mem_insert.mp hm with rfl | hm
      · simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl <;> simp
      · have hwM : w ∈ originalPorts M := mem_biUnion.mpr ⟨m,hK hm,hw⟩
        simp only [mem_union]
        tauto

theorem endpointSpliceI_markers_survive {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z t : V} (hs : LegalPrivateCompletion r M P {y,z})
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r M G P y z l)
    {b : EndpointSpliceInnerLabel V} (hb : EndpointSpliceLegalI r M G P y z t l b) :
    ∀ m ∈ insert ({b.2,t} : Finset V) (l.markers M z),
      m ⊆ univ \ (P ∪ l.deleted y ∪ b.1) :=
  splice_markers_survive (Subset.refl M) (endpointCutI_markers_survive hs hl) hb

theorem endpointSpliceII_markers_survive {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z t : V} (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelII V} (hl : EndpointCutLegalII r M G P y z l)
    {b : EndpointSpliceInnerLabel V} (hb : EndpointSpliceLegalII r M G P y z t l b) :
    ∀ m ∈ insert ({b.2,t} : Finset V) (l.markers M z),
      m ⊆ univ \ (P ∪ l.deleted y ∪ b.1) :=
  splice_markers_survive (erase_subset _ _) (endpointCutII_markers_survive hs hM hl) hb

/-- Type I inner completions equal `Y`, with the cut root directed `a→z`
and the inserted marker directed `v→t`. -/
theorem endpointSpliceCountI_eq_Y {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z t : V} (hr : 3 ≤ r) (hs : LegalPrivateCompletion r M P {y,z})
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r M G P y z l)
    {b : EndpointSpliceInnerLabel V} (hb : EndpointSpliceLegalI r M G P y z t l b) :
    let S := univ \ (P ∪ l.deleted y ∪ b.1)
    let marks := insert ({b.2,t} : Finset V) (l.markers M z)
    let root : ↥marks := ⟨{l.1,z}, mem_insert_of_mem (mem_insert_self _ _)⟩
    let pair : ↥marks := ⟨{b.2,t}, mem_insert_self _ _⟩
    let hm := endpointSpliceI_markers_survive hs hl hb
    (endpointSpliceInputFamilyI r M G P y z t l b).card =
      directedCycleCount r (restrictEdges S marks) (inducedHost S G) ∅
        (activeRestrictedMarker S root) (activeRestrictedMarker S pair)
        (activeRestrictedRootPoint S hm root ⟨l.1, by change l.1 ∈ ({l.1,z} : Finset V); simp⟩)
        ⟨b.2, hm _ pair.property (by change b.2 ∈ ({b.2,t} : Finset V); simp)⟩ := by
  dsimp only
  exact directedCycleOnCount_eq_directedCycleCount hr _ _ _
    (endpointSpliceI_markers_survive hs hl hb) _ _ ⟨l.1, by simp⟩
    ⟨b.2, endpointSpliceI_markers_survive hs hl hb _ (mem_insert_self _ _) (by simp)⟩

/-- Type II inner completions equal `Y`, with the cut root directed `a→z`
and the inserted marker directed `v→t`. -/
theorem endpointSpliceCountII_eq_Y {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z t : V} (hr : 3 ≤ r) (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelII V} (hl : EndpointCutLegalII r M G P y z l)
    {b : EndpointSpliceInnerLabel V} (hb : EndpointSpliceLegalII r M G P y z t l b) :
    let S := univ \ (P ∪ l.deleted y ∪ b.1)
    let marks := insert ({b.2,t} : Finset V) (l.markers M z)
    let root : ↥marks := ⟨{l.2.2.1,z}, mem_insert_of_mem (mem_insert_self _ _)⟩
    let pair : ↥marks := ⟨{b.2,t}, mem_insert_self _ _⟩
    let hm := endpointSpliceII_markers_survive hs hM hl hb
    (endpointSpliceInputFamilyII r M G P y z t l b).card =
      directedCycleCount r (restrictEdges S marks) (inducedHost S G) ∅
        (activeRestrictedMarker S root) (activeRestrictedMarker S pair)
        (activeRestrictedRootPoint S hm root ⟨l.2.2.1, by change l.2.2.1 ∈ ({l.2.2.1,z} : Finset V); simp⟩)
        ⟨b.2, hm _ pair.property (by change b.2 ∈ ({b.2,t} : Finset V); simp)⟩ := by
  dsimp only
  exact directedCycleOnCount_eq_directedCycleCount hr _ _ _
    (endpointSpliceII_markers_survive hs hM hl hb) _ _ ⟨l.2.2.1, by simp⟩
    ⟨b.2, endpointSpliceII_markers_survive hs hM hl hb _ (mem_insert_self _ _) (by simp)⟩

end LooseHamilton
