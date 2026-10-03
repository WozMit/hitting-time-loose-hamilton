module

public import HittingTimeLooseHamilton.AuxiliaryFrameEncoding
public import HittingTimeLooseHamilton.AuxiliaryFrameParameters
public import HittingTimeLooseHamilton.ActiveCycleNormalization
public import HittingTimeLooseHamilton.ActiveOrientationUniqueness

public section

/-! Exact dictionaries for bootstrap frames with no additional relative
direction. Choosing a root orientation does not discard any unoriented cycle. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem starts_iff_marker_start {r : ℕ} {S : Finset V}
    {markers edges : Finset (Finset V)}
    (C : MixedCycleOnWitness r S markers edges) (p : V × V)
    (hp : {p.1,p.2} ∈ markers) :
    Starts C p ↔ C.junction (C.slot.symm (.inl ⟨{p.1,p.2},hp⟩)) = p.1 := by
  constructor
  · rintro ⟨m,hm,hs⟩
    have he : m = ⟨{p.1,p.2},hp⟩ := Subtype.ext hm
    simpa only [he] using hs
  · intro hs
    exact ⟨⟨{p.1,p.2},hp⟩,rfl,hs⟩

namespace Frame
variable {r : ℕ} {original : Finset (Finset V)}

theorem cycleFamily_no_relative (F : Frame r original)
    (hrel : F.val.relative = none) (H : Finset (Finset V)) :
    F.cycleFamily H = cycleOnFamily r F.active F.markers (F.rawHost H) := by
  ext E
  rw [F.mem_cycleFamily, mem_cycleOnFamily]
  constructor
  · rintro ⟨hE,C,hdir⟩
    exact ⟨⟨C⟩,hE⟩
  · rintro ⟨⟨C⟩,hE⟩
    let root : ↥F.markers := ⟨{F.val.root.1,F.val.root.2},F.property.root_mem⟩
    let a : ↥root.val := ⟨F.val.root.1,by simp [root]⟩
    refine ⟨hE,C.orient root a,?_,?_⟩
    · exact ⟨root,rfl,C.orient_start root a⟩
    · simp [hrel]

theorem cycleCount_no_relative (F : Frame r original)
    (hrel : F.val.relative = none) (H : Finset (Finset V)) :
    F.cycleCount H = cycleOnCount r F.active F.markers
      (H ∩ allowedEdges r (originalPorts original)) := by
  unfold cycleCount cycleOnCount
  rw [cycleFamily_no_relative F hrel]
  unfold rawHost
  rw [← cycleOnFamily_eq_filter_active]

/-- Literal private-source identification; the root orientation is only a
choice of traversal, and the fixed original-port filter is retained. -/
theorem cycleCount_private_source (F : Frame r original)
    (hrel : F.val.relative = none) (H M : Finset (Finset V)) (D q : Finset V)
    (hD : F.val.deleted = D) (hM : F.markers = insert q M) :
    F.cycleCount H = LooseHamilton.completionCount r M
      (H ∩ allowedEdges r (originalPorts original)) D q := by
  rw [cycleCount_no_relative F hrel, hM]
  simp only [active,Code.active,hD,LooseHamilton.completionCount]

/-- The two fresh-pair directions partition the unoriented completions. -/
theorem completionFamily_directions (F : Frame r original)
    (hrel : F.val.relative = none) (H : Finset (Finset V)) (P : Finset V) (u v : V) :
    F.completionFamily H (P,u,v) ∪ F.completionFamily H (P,v,u) =
      cycleOnFamily r (F.active \ P) (insert {u,v} F.markers) (F.rawHost H) := by
  ext E
  rw [mem_union, mem_cycleOnFamily]
  constructor
  · rintro (he | he)
    · obtain ⟨hs,C,_⟩ := (F.mem_completionFamily H (P,u,v) E).mp he
      exact ⟨⟨C⟩,hs⟩
    · obtain ⟨hs,C,_⟩ := (F.mem_completionFamily H (P,v,u) E).mp he
      exact ⟨⟨by simpa only [pair_comm v u] using C⟩,hs⟩
  · rintro ⟨⟨C⟩,hs⟩
    let root : ↥(insert {u,v} F.markers) :=
      ⟨{F.val.root.1,F.val.root.2},mem_insert_of_mem F.property.root_mem⟩
    let a : ↥root.val := ⟨F.val.root.1,by simp [root]⟩
    let D := C.orient root a
    have hdir : F.Directed D := by
      refine ⟨⟨root,rfl,C.orient_start root a⟩,?_⟩
      simp [hrel]
    let m : ↥(insert {u,v} F.markers) := ⟨{u,v},mem_insert_self _ _⟩
    have hm := D.slot_edge (D.slot.symm (.inl m))
    rw [D.slot.apply_symm_apply] at hm
    have hstart : D.junction (D.slot.symm (.inl m)) ∈ ({u,v}:Finset V) := by
      change D.junction (D.slot.symm (.inl m)) ∈ m.val
      rw [hm]
      exact mem_insert_self _ _
    simp only [mem_insert, mem_singleton] at hstart
    rcases hstart with hu | hv
    · exact Or.inl ((F.mem_completionFamily H (P,u,v) E).mpr
        ⟨hs,D,hdir,⟨m,rfl,hu⟩⟩)
    · apply Or.inr
      have he : E ∈ F.completionFamily H (P,v,u) := by
        rw [F.mem_completionFamily]
        dsimp only
        rw [pair_comm v u]
        exact ⟨hs,D,hdir,⟨m,pair_comm u v,hv⟩⟩
      exact he

/-- A fixed root direction prevents the same edge set from occurring in both
fresh-pair directions. -/
theorem completionFamily_directions_disjoint (F : Frame r original)
    (hr : 3 ≤ r) (H : Finset (Finset V)) (P : Finset V) (u v : V) (huv : u ≠ v) :
    Disjoint (F.completionFamily H (P,u,v)) (F.completionFamily H (P,v,u)) := by
  apply disjoint_left.mpr
  intro E he hf
  obtain ⟨_,C,hC,hCu⟩ := (F.mem_completionFamily H (P,u,v) E).mp he
  have hf' : ∃ D : MixedCycleOnWitness r (F.active \ P) (insert {u,v} F.markers) E,
      F.Directed D ∧ Starts D (v,u) := by
    have hh := ((F.mem_completionFamily H (P,v,u) E).mp hf).2
    rw [pair_comm v u] at hh
    exact hh
  obtain ⟨D,hD,hDv⟩ := hf'
  let root : ↥(insert {u,v} F.markers) :=
    ⟨{F.val.root.1,F.val.root.2},mem_insert_of_mem F.property.root_mem⟩
  let m : ↥(insert {u,v} F.markers) := ⟨{u,v},mem_insert_self _ _⟩
  have hroot := (starts_iff_marker_start C F.val.root root.property).mp hC.1
  have hroot' := (starts_iff_marker_start D F.val.root root.property).mp hD.1
  have hu := (starts_iff_marker_start C (u,v) m.property).mp hCu
  have hv : D.junction (D.slot.symm (.inl m)) = v := by
    obtain ⟨m',hm',hv⟩ := hDv
    have heq : m' = m := Subtype.ext (hm'.trans (pair_comm v u))
    simpa only [heq] using hv
  exact huv (hu.symm.trans ((C.slot_start_eq_of_root D hr root
    (hroot.trans hroot'.symm) (.inl m)).trans hv))

/-- Exact two-direction count identity with the original-port filter fixed. -/
theorem completionCount_two_directions (F : Frame r original)
    (hr : 3 ≤ r) (hrel : F.val.relative = none)
    (H : Finset (Finset V)) (P : Finset V) (u v : V) (huv : u ≠ v) :
    F.completionCount H (P,u,v) + F.completionCount H (P,v,u) =
      cycleOnCount r (F.active \ P) (insert {u,v} F.markers)
        (H ∩ allowedEdges r (originalPorts original)) := by
  unfold completionCount cycleOnCount
  rw [← card_union_of_disjoint (F.completionFamily_directions_disjoint hr H P u v huv),
    F.completionFamily_directions hrel H P u v]
  congr 1
  apply cycleOnFamily_congr_inducedHost
  ext e
  simp only [mem_inducedHost, rawHost, mem_filter]
  have hs : ambientEdge (F.active \ P) e ⊆ F.active := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hw
    exact (mem_sdiff.mp z.property).1
  exact and_iff_left hs

end Frame
end LooseHamilton.AuxiliaryFrame
