module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Powerset

public section

/-! Perfect matchings and the collision statistic of Kahn, equation (27). -/
namespace Kahn

/-- A partition of `Fin n` into blocks of size `r`, represented by its edge set. -/
@[expose] def IsPerfectMatching {n : ℕ} (r : ℕ) (M : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ M, B.card = r) ∧ ∀ v : Fin n, ∃! B, B ∈ M ∧ v ∈ B

/-- Perfect matchings of the complete `r`-uniform hypergraph. -/
@[expose] def PerfectMatching (n r : ℕ) :=
  {M : Finset (Finset (Fin n)) // IsPerfectMatching r M}

@[expose] noncomputable instance (n r : ℕ) : Fintype (PerfectMatching n r) := by
  classical
  unfold PerfectMatching
  infer_instance

namespace PerfectMatching
variable {n r : ℕ} (M : PerfectMatching n r)

/-- The unique matching edge containing a vertex. -/
@[expose] noncomputable def edge (v : Fin n) : Finset (Fin n) :=
  Classical.choose (M.property.2 v).exists

theorem edge_mem (v : Fin n) : M.edge v ∈ M.val :=
  (Classical.choose_spec (M.property.2 v).exists).1

theorem mem_edge (v : Fin n) : v ∈ M.edge v :=
  (Classical.choose_spec (M.property.2 v).exists).2

theorem edge_card (v : Fin n) : (M.edge v).card = r :=
  M.property.1 _ (M.edge_mem v)

theorem eq_edge_of_mem {v : Fin n} {B : Finset (Fin n)}
    (hB : B ∈ M.val) (hv : v ∈ B) : B = M.edge v :=
  (M.property.2 v).unique ⟨hB, hv⟩ ⟨M.edge_mem v, M.mem_edge v⟩

/-- Kahn's `f(v)`, the edge at `v` with `v` removed. -/
@[expose] noncomputable def companion (v : Fin n) : Finset (Fin n) := (M.edge v).erase v

@[simp] theorem not_mem_companion (v : Fin n) : v ∉ M.companion v := by
  classical
  exact Finset.notMem_erase _ _

theorem companion_card (v : Fin n) : (M.companion v).card = r - 1 := by
  classical
  rw [companion, Finset.card_erase_of_mem (M.mem_edge v), M.edge_card v]

/-- The edge can be recovered by reinserting its distinguished vertex. -/
theorem insert_companion (v : Fin n) : insert v (M.companion v) = M.edge v := by
  classical
  exact Finset.insert_erase (M.mem_edge v)

/-- Companion data at every vertex determine the whole perfect matching. -/
theorem ext_companion (hr : 0 < r) {N : PerfectMatching n r}
    (h : ∀ v, M.companion v = N.companion v) : M = N := by
  classical
  apply Subtype.ext
  have hedge : ∀ v, M.edge v = N.edge v := by
    intro v
    rw [← M.insert_companion v, ← N.insert_companion v, h v]
  apply Finset.ext
  intro B
  constructor
  · intro hB
    have hpos : 0 < B.card := by rw [M.property.1 B hB]; exact hr
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    rw [M.eq_edge_of_mem hB hv, hedge v]
    exact N.edge_mem v
  · intro hB
    have hpos : 0 < B.card := by rw [N.property.1 B hB]; exact hr
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    rw [N.eq_edge_of_mem hB hv, ← hedge v]
    exact M.edge_mem v

/-- The matching edges other than the edge at `v` that intersect `Y`. -/
@[expose] noncomputable def touching (v : Fin n) (Y : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  M.val.filter fun B => B ≠ M.edge v ∧ (B ∩ Y).Nonempty

/-- The number `τ(v,f,Y)` in the paper. -/
@[expose] noncomputable def tau (v : Fin n) (Y : Finset (Fin n)) : ℕ :=
  (M.touching v Y).card

/-- A concrete image description of the blocks counted by `τ`. -/
theorem touching_eq_image_erase (v : Fin n) (Y : Finset (Fin n)) :
    M.touching v Y = (Y.image M.edge).erase (M.edge v) := by
  classical
  ext B
  constructor
  · intro hB
    obtain ⟨hBM, hne, x, hx⟩ := Finset.mem_filter.mp hB
    obtain ⟨hxB, hxY⟩ := Finset.mem_inter.mp hx
    apply Finset.mem_erase.mpr
    refine ⟨hne, Finset.mem_image.mpr ⟨x, hxY, ?_⟩⟩
    exact (M.eq_edge_of_mem hBM hxB).symm
  · intro hB
    obtain ⟨hne, hB⟩ := Finset.mem_erase.mp hB
    obtain ⟨x, hxY, rfl⟩ := Finset.mem_image.mp hB
    apply Finset.mem_filter.mpr
    exact ⟨M.edge_mem x, hne, x, Finset.mem_inter.mpr ⟨M.mem_edge x, hxY⟩⟩

/-- Maximum collision count means distinct blocks for the vertices of `Y`,
all different from the block at `v`. -/
theorem tau_eq_card_iff (v : Fin n) (Y : Finset (Fin n)) :
    M.tau v Y = Y.card ↔
      Set.InjOn M.edge (Y : Set (Fin n)) ∧ ∀ x ∈ Y, M.edge x ≠ M.edge v := by
  classical
  rw [tau, M.touching_eq_image_erase]
  constructor
  · intro h
    have hi : (Y.image M.edge).card = Y.card := by
      have he := Finset.card_erase_le (s := Y.image M.edge) (a := M.edge v)
      have hm := Finset.card_image_le (s := Y) (f := M.edge)
      omega
    refine ⟨Finset.card_image_iff.mp hi, ?_⟩
    intro x hx heq
    have hm : M.edge v ∈ Y.image M.edge := Finset.mem_image.mpr ⟨x, hx, heq⟩
    have hlt := Finset.card_erase_lt_of_mem hm
    omega
  · rintro ⟨hi, hd⟩
    have hnot : M.edge v ∉ Y.image M.edge := by
      intro hm
      obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
      exact hd x hx heq
    rw [Finset.erase_eq_of_notMem hnot]
    exact Finset.card_image_iff.mpr hi

/-- Different matching blocks can account for at most one block per vertex of `Y`. -/
theorem tau_le_card (v : Fin n) (Y : Finset (Fin n)) : M.tau v Y ≤ Y.card := by
  classical
  unfold tau
  apply Finset.card_le_card_of_surjOn M.edge
  intro B hB
  obtain ⟨hBM, _, x, hx⟩ := Finset.mem_filter.mp hB
  obtain ⟨hxB, hxY⟩ := Finset.mem_inter.mp hx
  exact ⟨x, hxY, (M.eq_edge_of_mem hBM hxB).symm⟩

theorem tau_le (v : Fin n) (Y : Finset (Fin n)) (hY : Y.card = r - 1) :
    M.tau v Y ≤ r - 1 := by
  simpa only [hY] using M.tau_le_card v Y

theorem touching_companion (v : Fin n) : M.touching v (M.companion v) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro B hB
  obtain ⟨hBM, hne, x, hx⟩ := Finset.mem_filter.mp hB
  obtain ⟨hxB, hxY⟩ := Finset.mem_inter.mp hx
  have hxE : x ∈ M.edge v := (Finset.mem_erase.mp hxY).2
  have hBE : B = M.edge v :=
    (M.eq_edge_of_mem hBM hxB).trans (M.eq_edge_of_mem (M.edge_mem v) hxE).symm
  exact hne hBE

@[simp] theorem tau_companion (v : Fin n) : M.tau v (M.companion v) = 0 := by
  rw [tau, M.touching_companion]
  rfl

/-- The bad event of equation (27), evaluated on a single matching. -/
@[expose] def Bad (v : Fin n) (Y : Finset (Fin n)) : Prop := M.tau v Y < r - 1

theorem bad_companion (hr : 2 ≤ r) (v : Fin n) : M.Bad v (M.companion v) := by
  unfold Bad
  rw [M.tau_companion]
  omega

/-- An atom of the companion marginal is contained in its collision event. -/
theorem bad_of_companion_eq (hr : 2 ≤ r) (v : Fin n) (Y : Finset (Fin n))
    (h : M.companion v = Y) : M.Bad v Y := by
  rw [← h]
  exact M.bad_companion hr v

end PerfectMatching
end Kahn
