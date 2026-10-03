module

public import HittingTimeLooseHamilton.BootstrapFrameCounts
public import HittingTimeLooseHamilton.CompletionMatching

public section

/-! Actual directed frame families, as opposed to registration tags. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- The single relative label describes exactly the two prescribed starts. -/
theorem cycleFamily_relative_some (F : Frame r original) (q : V × V)
    (hq : F.val.relative = some q) (H : Finset (Finset V)) :
    F.cycleFamily H = directedCycleOnFamily r F.active F.markers
      (H ∩ allowedEdges r (originalPorts original))
      ⟨{F.val.root.1,F.val.root.2},F.property.root_mem⟩
      ⟨{q.1,q.2},F.property.relative_mem q (by simp [hq])⟩ F.val.root.1 q.1 := by
  ext E
  rw [F.mem_cycleFamily, mem_directedCycleOnFamily, mem_cycleOnFamily]
  constructor
  · rintro ⟨hE,C,hr,hrel⟩
    refine ⟨⟨⟨C⟩,fun e he => (mem_filter.mp (hE he)).1⟩,C,?_,?_⟩
    · exact (starts_iff_marker_start C _ F.property.root_mem).mp hr
    · exact (starts_iff_marker_start C q _).mp (hrel q (by simp [hq]))
  · rintro ⟨⟨_,hE⟩,C,hr,hrel⟩
    refine ⟨?_,C,?_,?_⟩
    · intro e he
      exact mem_filter.mpr ⟨hE he,C.edge_subset_active he⟩
    · exact (starts_iff_marker_start C _ F.property.root_mem).mpr hr
    · intro p hp
      have : p = q := by simpa [hq, eq_comm] using hp
      subst p
      exact (starts_iff_marker_start C q _).mpr hrel

/-- The family dictionary is an equality of actual counts, without a factor two. -/
theorem cycleCount_relative_some (F : Frame r original) (q : V × V)
    (hq : F.val.relative = some q) (H : Finset (Finset V)) :
    F.cycleCount H = directedCycleOnCount r F.active F.markers
      (H ∩ allowedEdges r (originalPorts original))
      ⟨{F.val.root.1,F.val.root.2},F.property.root_mem⟩
      ⟨{q.1,q.2},F.property.relative_mem q (by simp [hq])⟩ F.val.root.1 q.1 := by
  exact congrArg Finset.card (F.cycleFamily_relative_some q hq H)

/-- A candidate of a frame without a relative label becomes an actual frame
with one relative label. Matching and retention follow from candidate legality. -/
theorem exists_actual_candidate (F : Frame r original) (ho : IsPairMatching original)
    (c : Finset V × V × V) (hc : F.LegalCandidate c)
    (hd : (F.val.deleted ∪ c.1).card ≤ 4*r)
    (hb : MarkerBudget original (insert {c.2.1,c.2.2} F.markers)) :
    ∃ G : Frame r original, G.val.deleted = F.val.deleted ∪ c.1 ∧
      G.markers = insert {c.2.1,c.2.2} F.markers ∧ G.val.root = F.val.root ∧
      G.val.relative = some c.2 := by
  apply exists_frame r original _ _ F.val.root (some c.2) ho
    (hc.1.augmented_matching F.property.matching) hd hb
  · intro e he v hv
    have hp := hc.1.augmented_subset_active e he hv
    have ha : v ∈ F.active := by
      rcases mem_insert.mp he with rfl | he
      · exact hc.2.1 (mem_union_right _ hv)
      · exact F.property.retained e he hv
    simp only [active,Code.active,mem_sdiff,mem_univ,true_and] at ha
    simp only [mem_sdiff,mem_univ,mem_union,true_and]
    exact fun h => h.elim ha (mem_sdiff.mp hp).2
  · exact mem_insert_of_mem F.property.root_mem
  · intro p hp
    have : p = c.2 := by simpa [eq_comm] using hp
    subst p
    exact mem_insert_self _ _

/-- The newly constructed relative frame counts precisely the source candidate,
including its direction; it is not a tag for some unrelated event family. -/
theorem actual_candidate_family (F G : Frame r original)
    (hrel : F.val.relative = none) (c : Finset V × V × V)
    (hd : G.val.deleted = F.val.deleted ∪ c.1)
    (hm : G.markers = insert {c.2.1,c.2.2} F.markers)
    (hp : G.val.root = F.val.root) (hq : G.val.relative = some c.2)
    (H : Finset (Finset V)) :
    G.cycleFamily H = F.completionFamily H c := by
  have ha : G.active = F.active \ c.1 := by
    ext v
    simp [active,Code.active,hd,not_or]
  ext E
  simp only [mem_cycleFamily, mem_completionFamily]
  rw [ha,hm]
  constructor
  · rintro ⟨hE,C,hr,hq'⟩
    refine ⟨?_,C,⟨?_,?_⟩,?_⟩
    · intro e he
      have hg := mem_filter.mp (hE he)
      exact mem_filter.mpr ⟨hg.1,fun v hv => (mem_sdiff.mp (ha ▸ hg.2 hv)).1⟩
    · simpa only [hp] using hr
    · simp [hrel]
    · exact hq' c.2 (by simp [hq])
  · rintro ⟨hE,C,⟨hr,_⟩,hc⟩
    refine ⟨?_,C,?_,?_⟩
    · intro e he
      exact mem_filter.mpr ⟨(mem_filter.mp (hE he)).1,ha.symm ▸ C.edge_subset_active he⟩
    · simpa only [hp] using hr
    · intro p hp'
      have : p = c.2 := by simpa [hq,eq_comm] using hp'
      subst p
      exact hc

theorem actual_candidate_count (F G : Frame r original)
    (hrel : F.val.relative = none) (c : Finset V × V × V)
    (hd : G.val.deleted = F.val.deleted ∪ c.1)
    (hm : G.markers = insert {c.2.1,c.2.2} F.markers)
    (hp : G.val.root = F.val.root) (hq : G.val.relative = some c.2)
    (H : Finset (Finset V)) : G.cycleCount H = F.completionCount H c :=
  congrArg Finset.card (actual_candidate_family F G hrel c hd hm hp hq H)

end LooseHamilton.AuxiliaryFrame.Frame
