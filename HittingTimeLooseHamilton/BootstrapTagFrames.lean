module

public import HittingTimeLooseHamilton.BootstrapBases
public import HittingTimeLooseHamilton.AuxiliaryFrameEncoding
public import HittingTimeLooseHamilton.SpliceMarkerExchange

public section

/-! Fixed legal frames used only as registration tags. No host occurs in their
construction, and no event family is required to be the tag frame's family. -/
noncomputable section
namespace LooseHamilton.BootstrapTagFrames
open Finset BootstrapBases
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {M : Finset (Finset V)} {r : ℕ}

theorem markers_subset (hM : IsPairMatching M) (b : Base M) : markers hM b ⊆ M := by
  cases b with
  | none => exact Subset.rfl
  | some a => exact erase_subset _ _

theorem unused_survives (b : Base M) {v : V} (hv : v ∉ originalPorts M) :
    v ∈ active b := by
  cases b with
  | none => simp
  | some a =>
    simp only [active, deleted, mem_sdiff, mem_univ, mem_singleton, true_and]
    intro h
    exact hv (h ▸ a.property)

theorem deleted_injective : Function.Injective (@deleted V _ M) := by
  intro b c h
  cases b with
  | none =>
    cases c with
    | none => rfl
    | some a => exact False.elim (by have := congrArg Finset.card h; simp [deleted] at this)
  | some a =>
    cases c with
    | none => simpa [deleted] using h
    | some b =>
      have : a.val = b.val := singleton_injective h
      exact congrArg some (Subtype.ext this)

theorem tag_matching (hM : IsPairMatching M) (b : Base M) (p q : V)
    (hp : p ∉ originalPorts M) (hq : q ∉ originalPorts M) (hpq : p ≠ q) :
    IsPairMatching (insert {p,q} (markers hM b)) := by
  constructor
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · simp [hpq]
    · exact (markers_matching hM b).1 e he
  · apply insert_marker_matching (markers_matching hM b).2
    apply disjoint_left.mpr
    intro v hv hm
    obtain ⟨e,he,hve⟩ := mem_biUnion.mp hm
    have hvM : v ∈ originalPorts M := mem_biUnion.mpr ⟨e,markers_subset hM b he,hve⟩
    rcases mem_insert.mp hv with rfl | hv
    · exact hp hvM
    · exact hq ((mem_singleton.mp hv) ▸ hvM)

theorem exists_tag (hM : IsPairMatching M) (hr : 3 ≤ r) (p q : V)
    (hp : p ∉ originalPorts M) (hq : q ∉ originalPorts M) (hpq : p ≠ q)
    (b : Base M) :
    ∃ F : AuxiliaryFrame.Frame r M, F.val.deleted = deleted b ∧
      F.val.markers M = insert {p,q} (markers hM b) ∧
      F.val.root = (p,q) ∧ F.val.relative = none := by
  apply AuxiliaryFrame.exists_frame r M _ (deleted b) (p,q) none hM
    (tag_matching hM b p q hp hq hpq)
  · have := deleted_card_le b
    omega
  · cases b with
    | none => exact markerBudget_insert M {p,q}
    | some a => exact markerBudget_erase_insert M _ {p,q}
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact unused_survives b hp
      · exact (mem_singleton.mp hv) ▸ unused_survives b hq
    · exact markers_retained hM b he
  · exact mem_insert_self _ _
  · simp

@[expose] def tag (hM : IsPairMatching M) (hr : 3 ≤ r) (p q : V)
    (hp : p ∉ originalPorts M) (hq : q ∉ originalPorts M) (hpq : p ≠ q)
    (b : Base M) : AuxiliaryFrame.Frame r M :=
  (exists_tag hM hr p q hp hq hpq b).choose

@[simp] theorem tag_deleted (hM : IsPairMatching M) (hr : 3 ≤ r) (p q : V)
    (hp : p ∉ originalPorts M) (hq : q ∉ originalPorts M) (hpq : p ≠ q)
    (b : Base M) : (tag hM hr p q hp hq hpq b).val.deleted = deleted b :=
  (exists_tag hM hr p q hp hq hpq b).choose_spec.1
@[simp] theorem tag_markers (hM : IsPairMatching M) (hr : 3 ≤ r) (p q : V)
    (hp : p ∉ originalPorts M) (hq : q ∉ originalPorts M) (hpq : p ≠ q)
    (b : Base M) : (tag hM hr p q hp hq hpq b).val.markers M =
      insert {p,q} (markers hM b) :=
  (exists_tag hM hr p q hp hq hpq b).choose_spec.2.1
@[simp] theorem tag_root (hM : IsPairMatching M) (hr : 3 ≤ r) (p q : V)
    (hp : p ∉ originalPorts M) (hq : q ∉ originalPorts M) (hpq : p ≠ q)
    (b : Base M) : (tag hM hr p q hp hq hpq b).val.root = (p,q) :=
  (exists_tag hM hr p q hp hq hpq b).choose_spec.2.2.1
@[simp] theorem tag_relative (hM : IsPairMatching M) (hr : 3 ≤ r) (p q : V)
    (hp : p ∉ originalPorts M) (hq : q ∉ originalPorts M) (hpq : p ≠ q)
    (b : Base M) : (tag hM hr p q hp hq hpq b).val.relative = none :=
  (exists_tag hM hr p q hp hq hpq b).choose_spec.2.2.2

theorem tag_injective (hM : IsPairMatching M) (hr : 3 ≤ r) (p q : V)
    (hp : p ∉ originalPorts M) (hq : q ∉ originalPorts M) (hpq : p ≠ q) :
    Function.Injective (tag hM hr p q hp hq hpq) := by
  intro b c h
  apply deleted_injective
  simpa using congrArg (fun F : AuxiliaryFrame.Frame r M => F.val.deleted) h

theorem exists_unused_pair (hM : IsPairMatching M)
    (hN : 2 * M.card + 2 ≤ Fintype.card V) :
    ∃ p q : V, p ∉ originalPorts M ∧ q ∉ originalPorts M ∧ p ≠ q := by
  have hc : 2 ≤ (univ \ originalPorts M).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hM.ports_card]
    omega
  obtain ⟨p,hp,q,hq,hpq⟩ := one_lt_card.mp (by omega : 1 < (univ \ originalPorts M).card)
  exact ⟨p,q,(mem_sdiff.mp hp).2,(mem_sdiff.mp hq).2,hpq⟩
end LooseHamilton.BootstrapTagFrames
