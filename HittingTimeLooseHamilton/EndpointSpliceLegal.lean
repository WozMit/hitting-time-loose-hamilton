module

public import HittingTimeLooseHamilton.EndpointSpliceModels
public import HittingTimeLooseHamilton.EndpointExpansionLegal
public import HittingTimeLooseHamilton.SpliceMarkerExchange

public section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P D Q : Finset V} {y z a t v : V}

namespace EndpointSpliceLegal
variable (h : EndpointSpliceLegal r M G P D y z a t Q v)
include h

theorem private_deleted_disjoint : Disjoint Q D :=
  h.private_disjoint.mono_right (by intro x hx; simp only [mem_union]; exact Or.inl (Or.inl (Or.inr hx)))
theorem private_block_disjoint : Disjoint Q P :=
  h.private_disjoint.mono_right (by intro x hx; simp only [mem_union]; exact Or.inl (Or.inl (Or.inl hx)))
theorem newEndpoint_not_ports : v ∉ originalPorts M := by
  intro hv; exact h.newEndpoint_fresh (by simp only [mem_union]; tauto)
theorem target_not_ports : t ∉ originalPorts M := by
  intro ht; exact h.target_fresh (by simp only [mem_union]; tauto)
theorem newEndpoint_not_deleted : v ∉ D := by
  intro hv; exact h.newEndpoint_fresh (by simp only [mem_union]; tauto)
theorem target_not_deleted : t ∉ D := by
  intro ht; exact h.target_fresh (by simp only [mem_union]; tauto)
theorem newEndpoint_ne_y : v ≠ y := by
  intro hv; exact h.newEndpoint_fresh (by simp [hv])
theorem newEndpoint_ne_z : v ≠ z := by
  intro hv; exact h.newEndpoint_fresh (by simp [hv])
theorem newEndpoint_ne_a : v ≠ a := by
  intro hv; exact h.newEndpoint_fresh (by simp [hv])
theorem newEndpoint_ne_t : v ≠ t := by
  intro hv; exact h.newEndpoint_fresh (by simp [hv])
theorem target_ne_y : t ≠ y := by
  intro ht; exact h.target_fresh (by simp [ht])
theorem target_ne_z : t ≠ z := by
  intro ht; exact h.target_fresh (by simp [ht])
theorem target_ne_a : t ≠ a := by
  intro ht; exact h.target_fresh (by simp [ht])

theorem pair_fresh (w : V) : {v,w} ∉ insert {t,z} M := by
  intro hm
  rcases mem_insert.mp hm with he | hm
  · have hv : v ∈ ({t,z} : Finset V) := he ▸ (by simp : v ∈ ({v,w} : Finset V))
    simp only [mem_insert, mem_singleton] at hv
    exact hv.elim h.newEndpoint_ne_t h.newEndpoint_ne_z
  · exact h.newEndpoint_not_ports (mem_biUnion.mpr ⟨{v,w},hm,by simp⟩)

theorem pair_fresh_erase (w : V) (m : Finset V) : {v,w} ∉ insert {t,z} (M.erase m) := by
  intro hm
  exact h.pair_fresh w (insert_subset_insert _ (erase_subset _ _) hm)

theorem old_marker_fresh {m : Finset V} (hm : m ∈ M) :
    m ∉ insert {v,y} (insert {t,z} (M.erase m)) := by
  intro hmem
  rcases mem_insert.mp hmem with he | hmem
  · have hv : v ∈ m := he.symm ▸ (by simp : v ∈ ({v,y} : Finset V))
    exact h.newEndpoint_not_ports (mem_biUnion.mpr ⟨m,hm,hv⟩)
  · rcases mem_insert.mp hmem with he | hmem
    · have ht : t ∈ m := he.symm ▸ (by simp : t ∈ ({t,z} : Finset V))
      exact h.target_not_ports (mem_biUnion.mpr ⟨m,hm,ht⟩)
    · exact (mem_erase.mp hmem).1 rfl

theorem private_restored_disjoint : Disjoint Q (univ \ (P ∪ Q)) := by
  apply disjoint_left.mpr
  intro x hx hs
  exact (mem_sdiff.mp hs).2 (mem_union_right _ hx)

/-- The restored two markers form a matching together with all original markers. -/
theorem restored_matching (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) :
    ((insert {v,y} (insert {t,z} M) : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  have hy : y ∉ originalPorts M := fun hm =>
    disjoint_left.mp hs.ports_disjoint (by simp) hm
  have hz : z ∉ originalPorts M := fun hm =>
    disjoint_left.mp hs.ports_disjoint (by simp) hm
  have hyz : y ≠ z := by
    intro he
    have hc := hs.pair_card
    simp [he] at hc
  apply insert_two_markers_matching hM
  · simp only [disjoint_left, mem_insert, mem_singleton]
    intro x hx hxM
    rcases hx with rfl | rfl
    · exact h.newEndpoint_not_ports hxM
    · exact hy hxM
  · simp only [disjoint_left, mem_insert, mem_singleton]
    intro x hx hxM
    rcases hx with rfl | rfl
    · exact h.target_not_ports hxM
    · exact hz hxM
  · simp only [disjoint_left, mem_insert, mem_singleton]
    intro x hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with he | he
    · exact h.newEndpoint_ne_t he
    · exact h.newEndpoint_ne_z he
    · exact h.target_ne_y he.symm
    · exact hyz he
end EndpointSpliceLegal

/-- Restoring a deleted cut while retaining a second deleted block. -/
theorem splice_restore_deleted (hDP : Disjoint D P) (hDQ : Disjoint D Q) :
    (univ \ (P ∪ D ∪ Q)) ∪ D = univ \ (P ∪ Q) := by
  ext x
  simp only [mem_union, mem_sdiff, mem_univ, true_and]
  have hP : x ∈ D → x ∉ P := fun hx => disjoint_left.mp hDP hx
  have hQ : x ∈ D → x ∉ Q := fun hx => disjoint_left.mp hDQ hx
  tauto

theorem splice_core_subset :
    univ \ (P ∪ D ∪ Q) ⊆ univ \ (P ∪ D) := by
  intro x hx
  exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hx).2 (mem_union_left _ h)⟩

namespace EndpointCutLegalI
variable {l : EndpointCutLabelI V}
theorem splice_y_not_core (hl : EndpointCutLegalI r M G P y z l) :
    y ∉ univ \ (P ∪ l.deleted y ∪ Q) := fun h => hl.y_not_core (splice_core_subset h)
theorem splice_private_core_disjoint (hl : EndpointCutLegalI r M G P y z l) :
    Disjoint (univ \ (P ∪ l.deleted y ∪ Q)) l.2 :=
  hl.private_core_disjoint.mono_left splice_core_subset

theorem splice_restore_active (hl : EndpointCutLegalI r M G P y z l)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hb : EndpointSpliceLegalI r M G P y z t l (Q,v)) :
    (univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y} ∪ l.2 = univ \ (P ∪ Q) := by
  rw [union_assoc, show ({y} : Finset V) ∪ l.2 = l.deleted y from by
    ext x; simp [EndpointCutLabelI.deleted]]
  exact splice_restore_deleted (hl.deleted_disjoint hs) hb.private_deleted_disjoint.symm
end EndpointCutLegalI
namespace EndpointCutLegalII
variable {l : EndpointCutLabelII V}
theorem splice_added_not_core (hl : EndpointCutLegalII r M G P y z l) (i : Fin 3) :
    ![y,l.1,l.2.1] i ∉ univ \ (P ∪ l.deleted y ∪ Q) :=
  fun h => hl.added_not_core i (splice_core_subset h)
theorem splice_private_core_disjoint (hl : EndpointCutLegalII r M G P y z l) (i : Fin 2) :
    Disjoint (univ \ (P ∪ l.deleted y ∪ Q)) (![l.2.2.2.1,l.2.2.2.2] i) :=
  (hl.private_core_disjoint i).mono_left splice_core_subset

theorem splice_restore_active (hl : EndpointCutLegalII r M G P y z l)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hb : EndpointSpliceLegalII r M G P y z t l (Q,v)) :
    (univ \ (P ∪ l.deleted y ∪ Q)) ∪ {y,l.1,l.2.1} ∪ (l.2.2.2.1 ∪ l.2.2.2.2) =
      univ \ (P ∪ Q) := by
  simpa [EndpointCutLabelII.deleted, union_assoc] using
    splice_restore_deleted (hl.deleted_disjoint hs) hb.private_deleted_disjoint.symm
end EndpointCutLegalII
end LooseHamilton
