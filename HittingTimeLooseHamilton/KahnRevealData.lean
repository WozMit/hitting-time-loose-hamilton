module

public import HittingTimeLooseHamilton.KahnMatching
public import Mathlib.Data.Finset.Union

public section

/-! Deterministic reveal data for the entropy argument in Theorem 4.2. -/
noncomputable section
namespace Kahn.PerfectMatching
variable {n r : ℕ} (M : Kahn.PerfectMatching n r)

/-- Vertices preceding `v` in the order `σ`. -/
@[expose] def predecessors (σ : Equiv.Perm (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w => σ w < σ v

/-- The union of matching edges exposed by earlier vertices. -/
@[expose] def earlierEdges (σ : Equiv.Perm (Fin n)) (v : Fin n) : Finset (Fin n) :=
  (predecessors σ v).biUnion M.edge

/-- Companion information visible strictly before `v`. -/
@[expose] def past (σ : Equiv.Perm (Fin n)) (v : Fin n) : Fin n → Option (Finset (Fin n)) :=
  fun w => if σ w < σ v then some (M.companion w) else none

/-- Vertices still available when `v` has not yet been exposed. -/
@[expose] def available (σ : Equiv.Perm (Fin n)) (v : Fin n) : Finset (Fin n) :=
  (Finset.univ \ M.earlierEdges σ v).erase v

/-- Tagged evidence: either the already determined companion, or the available vertices. -/
@[expose] def evidence (σ : Equiv.Perm (Fin n)) (v : Fin n) : Bool × Finset (Fin n) :=
  if v ∈ M.earlierEdges σ v then (true, M.companion v) else (false, M.available σ v)

lemma mem_earlierEdges (σ : Equiv.Perm (Fin n)) (v x : Fin n) :
    x ∈ M.earlierEdges σ v ↔ ∃ w, σ w < σ v ∧ x ∈ M.edge w := by
  simp [earlierEdges, predecessors]

lemma mem_edge_comm (v w : Fin n) : v ∈ M.edge w ↔ w ∈ M.edge v := by
  constructor
  · intro h
    have he : M.edge w = M.edge v := M.eq_edge_of_mem (M.edge_mem w) h
    rw [← he]
    exact M.mem_edge w
  · intro h
    have he : M.edge v = M.edge w := M.eq_edge_of_mem (M.edge_mem v) h
    rw [← he]
    exact M.mem_edge v

lemma companion_eq_of_past_eq {N : Kahn.PerfectMatching n r}
    (σ : Equiv.Perm (Fin n)) (v w : Fin n)
    (h : M.past σ v = N.past σ v) (hw : σ w < σ v) :
    M.companion w = N.companion w := by
  have he := congrFun h w
  simpa [past, hw] using he

lemma edge_eq_of_past_eq {N : Kahn.PerfectMatching n r}
    (σ : Equiv.Perm (Fin n)) (v w : Fin n)
    (h : M.past σ v = N.past σ v) (hw : σ w < σ v) :
    M.edge w = N.edge w := by
  rw [← M.insert_companion w, ← N.insert_companion w,
    M.companion_eq_of_past_eq σ v w h hw]

lemma earlierEdges_eq_of_past_eq {N : Kahn.PerfectMatching n r}
    (σ : Equiv.Perm (Fin n)) (v : Fin n) (h : M.past σ v = N.past σ v) :
    M.earlierEdges σ v = N.earlierEdges σ v := by
  ext x
  simp only [mem_earlierEdges]
  constructor
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, hw, (M.edge_eq_of_past_eq σ v w h hw) ▸ hx⟩
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, hw, (M.edge_eq_of_past_eq σ v w h hw).symm ▸ hx⟩

lemma known_companion_eq_of_past_eq {N : Kahn.PerfectMatching n r}
    (σ : Equiv.Perm (Fin n)) (v : Fin n) (h : M.past σ v = N.past σ v)
    (hv : v ∈ M.earlierEdges σ v) : M.companion v = N.companion v := by
  obtain ⟨w, hw, hvw⟩ := (M.mem_earlierEdges σ v v).mp hv
  have hew := M.edge_eq_of_past_eq σ v w h hw
  have heM := M.eq_edge_of_mem (M.edge_mem w) hvw
  have heN := N.eq_edge_of_mem (N.edge_mem w) (hew ▸ hvw)
  have he : M.edge v = N.edge v := heM.symm.trans (hew.trans heN)
  exact congrArg (fun B : Finset (Fin n) => B.erase v) he

/-- Coarsening is legitimate: the evidence is a deterministic function of the past data. -/
lemma evidence_eq_of_past_eq {N : Kahn.PerfectMatching n r}
    (σ : Equiv.Perm (Fin n)) (v : Fin n) (h : M.past σ v = N.past σ v) :
    M.evidence σ v = N.evidence σ v := by
  have he := M.earlierEdges_eq_of_past_eq σ v h
  by_cases hv : v ∈ M.earlierEdges σ v
  · have hvN : v ∈ N.earlierEdges σ v := he ▸ hv
    simp only [evidence, if_pos hv, if_pos hvN]
    exact congrArg (fun Y => (true, Y)) (M.known_companion_eq_of_past_eq σ v h hv)
  · have hvN : v ∉ N.earlierEdges σ v := he ▸ hv
    simp only [evidence, if_neg hv, if_neg hvN, available, he]

/-- A total function from histories to evidence. Unrealizable histories receive
an arbitrary value; on every realizable history the value is uniquely determined. -/
@[expose] def evidenceFromPast (r : ℕ) (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (p : Fin n → Option (Finset (Fin n))) : Bool × Finset (Fin n) := by
  classical
  exact if h : ∃ N : Kahn.PerfectMatching n r, N.past σ v = p then
    (Classical.choose h).evidence σ v else (false, ∅)

/-- Explicit deterministic factorization needed for conditional-entropy coarsening. -/
lemma evidenceFromPast_eq (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    evidenceFromPast r σ v (M.past σ v) = M.evidence σ v := by
  classical
  have h : ∃ N : Kahn.PerfectMatching n r, N.past σ v = M.past σ v := ⟨M, rfl⟩
  rw [evidenceFromPast, dif_pos h]
  exact (Classical.choose h).evidence_eq_of_past_eq σ v (Classical.choose_spec h)

lemma evidence_known (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (h : v ∈ M.earlierEdges σ v) : M.evidence σ v = (true, M.companion v) := by
  simp [evidence, h]

lemma evidence_unknown (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (h : v ∉ M.earlierEdges σ v) : M.evidence σ v = (false, M.available σ v) := by
  simp [evidence, h]

lemma evidence_eq_true_iff (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (Y : Finset (Fin n)) : M.evidence σ v = (true, Y) ↔
      v ∈ M.earlierEdges σ v ∧ M.companion v = Y := by
  by_cases h : v ∈ M.earlierEdges σ v <;> simp [evidence, h]

lemma evidence_eq_false_iff (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (Y : Finset (Fin n)) : M.evidence σ v = (false, Y) ↔
      v ∉ M.earlierEdges σ v ∧ M.available σ v = Y := by
  by_cases h : v ∈ M.earlierEdges σ v <;> simp [evidence, h]

/-- The unknown branch occurs exactly when `v` is first in its matching block. -/
lemma unknown_iff_first (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    v ∉ M.earlierEdges σ v ↔ ∀ w ∈ M.edge v, σ v ≤ σ w := by
  constructor
  · intro h w hw
    by_contra hn
    have hlt : σ w < σ v := lt_of_not_ge hn
    exact h ((M.mem_earlierEdges σ v v).mpr
      ⟨w, hlt, (M.mem_edge_comm v w).mpr hw⟩)
  · intro h hv
    obtain ⟨w, hw, hvw⟩ := (M.mem_earlierEdges σ v v).mp hv
    exact (not_lt_of_ge (h w ((M.mem_edge_comm v w).mp hvw))) hw

/-- A vertex is unexposed precisely when every vertex of its block is at or after `v`. -/
lemma not_mem_earlierEdges (σ : Equiv.Perm (Fin n)) (v x : Fin n) :
    x ∉ M.earlierEdges σ v ↔ ∀ w ∈ M.edge x, σ v ≤ σ w := by
  constructor
  · intro h w hw
    by_contra hn
    exact h ((M.mem_earlierEdges σ v x).mpr
      ⟨w, lt_of_not_ge hn, (M.mem_edge_comm x w).mpr hw⟩)
  · intro h hx
    obtain ⟨w, hw, hxw⟩ := (M.mem_earlierEdges σ v x).mp hx
    exact (not_lt_of_ge (h w ((M.mem_edge_comm x w).mp hxw))) hw

lemma subset_available_iff (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (Y : Finset (Fin n)) : Y ⊆ M.available σ v ↔
      v ∉ Y ∧ ∀ x ∈ Y, ∀ w ∈ M.edge x, σ v ≤ σ w := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hv
      exact Finset.notMem_erase v _ (h hv)
    · intro x hx
      have hnot := (Finset.mem_sdiff.mp (Finset.mem_erase.mp (h hx)).2).2
      exact (M.not_mem_earlierEdges σ v x).mp hnot
  · rintro ⟨hv, h⟩ x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    · intro he
      subst x
      exact hv hx
    · exact (M.not_mem_earlierEdges σ v x).mpr (h x hx)

/-- On the unknown branch, availability of `Y` is precisely survival of every
other matching block meeting `Y`. This is the deterministic part of (38). -/
lemma subset_available_iff_touching (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (Y : Finset (Fin n)) (hvY : v ∉ Y) (hfirst : v ∉ M.earlierEdges σ v) :
    Y ⊆ M.available σ v ↔
      ∀ B ∈ M.touching v Y, ∀ w ∈ B, σ v ≤ σ w := by
  constructor
  · intro h B hB w hw
    obtain ⟨hBM, _, x, hx⟩ := Finset.mem_filter.mp hB
    obtain ⟨hxB, hxY⟩ := Finset.mem_inter.mp hx
    have he : B = M.edge x := M.eq_edge_of_mem hBM hxB
    exact ((M.subset_available_iff σ v Y).mp h).2 x hxY w (he ▸ hw)
  · intro h
    apply (M.subset_available_iff σ v Y).mpr
    refine ⟨hvY, ?_⟩
    intro x hx w hw
    by_cases he : M.edge x = M.edge v
    · exact ((M.unknown_iff_first σ v).mp hfirst) w (he ▸ hw)
    · apply h (M.edge x) ?_ w hw
      apply Finset.mem_filter.mpr
      exact ⟨M.edge_mem x, he, x, Finset.mem_inter.mpr ⟨M.mem_edge x, hx⟩⟩

/-- Whenever a companion is still unknown, its actual value is one of the available sets. -/
lemma companion_subset_available (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (hfirst : v ∉ M.earlierEdges σ v) : M.companion v ⊆ M.available σ v := by
  apply (M.subset_available_iff_touching σ v (M.companion v)
    (M.not_mem_companion v) hfirst).mpr
  simp [M.touching_companion]

end Kahn.PerfectMatching
