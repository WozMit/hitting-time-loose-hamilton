module

public import HittingTimeLooseHamilton.BootstrapEndpointFrames

public section

/-! Exact unoriented-core and two-direction candidate count dictionaries.
The initial base deletion is explicit, including for original-port bases. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointFrames
open Finset BootstrapBases AuxiliaryFrame
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

theorem endpointI_core_count (ho : IsPairMatching original) (b : Base original)
    (F : Frame r original) (H : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelI V)
    (hD : F.val.deleted = deleted b ∪ (P ∪ l.deleted y))
    (hM : F.val.markers original = l.markers (markers ho b) z)
    (hq : F.val.relative = none) :
    F.cycleCount H = cycleOnCount r
      (univ \ (deleted b ∪ (P ∪ l.deleted y))) (l.markers (markers ho b) z)
      (H ∩ allowedEdges r (originalPorts original)) := by
  have h := F.cycleCount_no_relative hq H
  simpa only [Frame.active, Code.active, hD, Frame.markers, hM] using h

theorem endpointI_candidate_count (ho : IsPairMatching original) (b : Base original)
    (F : Frame r original) (H : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelI V)
    (t : V) (q : EndpointSpliceInnerLabel V)
    (hD : F.val.deleted = deleted b ∪ (P ∪ l.deleted y ∪ q.1))
    (hM : F.val.markers original = insert {q.2,t} (l.markers (markers ho b) z))
    (hp : F.val.root = (l.1,z))
    (hq : F.val.relative = some (q.2,t)) :
    F.cycleCount H = directedCycleOnCount r
      (univ \ (deleted b ∪ (P ∪ l.deleted y ∪ q.1))) (insert {q.2,t} (l.markers (markers ho b) z))
      (H ∩ allowedEdges r (originalPorts original))
      ⟨{l.1,z}, mem_insert_of_mem (mem_insert_self _ _)⟩
      ⟨{q.2,t}, mem_insert_self _ _⟩ l.1 q.2 := by
  unfold Frame.cycleCount directedCycleOnCount
  apply congrArg Finset.card
  ext E
  rw [F.mem_cycleFamily, mem_directedCycleOnFamily, mem_cycleOnFamily]
  simp only [Frame.Directed, Frame.active, Code.active, hD, Frame.markers, hM, hp, hq]
  rw [hD, hM]
  constructor
  · rintro ⟨hE,C,hroot,hpair⟩
    refine ⟨⟨⟨C⟩,fun e he => (mem_filter.mp (hE he)).1⟩,C,?_,?_⟩
    · exact (starts_iff_marker_start C (l.1,z) _).mp hroot
    · exact (starts_iff_marker_start C (q.2,t) _).mp (hpair (q.2,t) (by simp))
  · rintro ⟨⟨_,hE⟩,C,hroot,hpair⟩
    refine ⟨?_,C,?_,?_⟩
    · intro e he
      apply mem_filter.mpr
      refine ⟨hE he,?_⟩
      simpa only [Frame.active, Code.active, hD] using C.edge_subset_active he
    · exact (starts_iff_marker_start C (l.1,z) _).mpr hroot
    · intro p hp'
      have heq : p = (q.2,t) := by simpa [eq_comm] using hp'
      subst p
      exact (starts_iff_marker_start C (q.2,t) _).mpr hpair

theorem endpointII_core_count (ho : IsPairMatching original) (b : Base original)
    (F : Frame r original) (H : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelII V)
    (hD : F.val.deleted = deleted b ∪ (P ∪ l.deleted y))
    (hM : F.val.markers original = l.markers (markers ho b) z)
    (hq : F.val.relative = none) :
    F.cycleCount H = cycleOnCount r
      (univ \ (deleted b ∪ (P ∪ l.deleted y))) (l.markers (markers ho b) z)
      (H ∩ allowedEdges r (originalPorts original)) := by
  have h := F.cycleCount_no_relative hq H
  simpa only [Frame.active, Code.active, hD, Frame.markers, hM] using h

theorem endpointII_candidate_count (ho : IsPairMatching original) (b : Base original)
    (F : Frame r original) (H : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelII V)
    (t : V) (q : EndpointSpliceInnerLabel V)
    (hD : F.val.deleted = deleted b ∪ (P ∪ l.deleted y ∪ q.1))
    (hM : F.val.markers original = insert {q.2,t} (l.markers (markers ho b) z))
    (hp : F.val.root = (l.2.2.1,z))
    (hq : F.val.relative = some (q.2,t)) :
    F.cycleCount H = directedCycleOnCount r
      (univ \ (deleted b ∪ (P ∪ l.deleted y ∪ q.1))) (insert {q.2,t} (l.markers (markers ho b) z))
      (H ∩ allowedEdges r (originalPorts original))
      ⟨{l.2.2.1,z}, mem_insert_of_mem (mem_insert_self _ _)⟩
      ⟨{q.2,t}, mem_insert_self _ _⟩ l.2.2.1 q.2 := by
  unfold Frame.cycleCount directedCycleOnCount
  apply congrArg Finset.card
  ext E
  rw [F.mem_cycleFamily, mem_directedCycleOnFamily, mem_cycleOnFamily]
  simp only [Frame.Directed, Frame.active, Code.active, hD, Frame.markers, hM, hp, hq]
  rw [hD, hM]
  constructor
  · rintro ⟨hE,C,hroot,hpair⟩
    refine ⟨⟨⟨C⟩,fun e he => (mem_filter.mp (hE he)).1⟩,C,?_,?_⟩
    · exact (starts_iff_marker_start C (l.2.2.1,z) _).mp hroot
    · exact (starts_iff_marker_start C (q.2,t) _).mp (hpair (q.2,t) (by simp))
  · rintro ⟨⟨_,hE⟩,C,hroot,hpair⟩
    refine ⟨?_,C,?_,?_⟩
    · intro e he
      apply mem_filter.mpr
      refine ⟨hE he,?_⟩
      simpa only [Frame.active, Code.active, hD] using C.edge_subset_active he
    · exact (starts_iff_marker_start C (l.2.2.1,z) _).mpr hroot
    · intro p hp'
      have heq : p = (q.2,t) := by simpa [eq_comm] using hp'
      subst p
      exact (starts_iff_marker_start C (q.2,t) _).mpr hpair

end LooseHamilton.BootstrapEndpointFrames
