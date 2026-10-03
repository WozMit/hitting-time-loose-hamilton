module

public import HittingTimeLooseHamilton.StoppingBiasDeterministic
public import Mathlib.Tactic

public section

noncomputable section
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replace the distinguished vertex by a vertex outside the edge. -/
@[expose] def switchedEdge (e : Finset V) (v w : V) : Finset V := insert w (e.erase v)

@[simp] theorem mem_switchedEdge (e : Finset V) (v w x : V) :
    x ∈ switchedEdge e v w ↔ x = w ∨ x ≠ v ∧ x ∈ e := by
  simp [switchedEdge]

theorem switchedEdge_card {e : Finset V} {v w : V} (hv : v ∈ e) (hw : w ∉ e) :
    (switchedEdge e v w).card = e.card := by
  have hwe : w ∉ e.erase v := fun h => hw (Finset.mem_of_mem_erase h)
  simp [switchedEdge, hwe, Finset.card_erase_of_mem hv]
  have := Finset.card_pos.mpr ⟨v, hv⟩
  omega

theorem switchedEdge_not_mem {e : Finset V} {v w : V} (hv : v ∈ e) (hw : w ∉ e) :
    v ∉ switchedEdge e v w := by
  have : v ≠ w := fun h => hw (h ▸ hv)
  simp [this]

theorem switchedEdge_reverse {e : Finset V} {v w : V} (hv : v ∈ e) (hw : w ∉ e) :
    switchedEdge (switchedEdge e v w) w v = e := by
  have hvw : v ≠ w := fun h => hw (h ▸ hv)
  ext x
  simp only [mem_switchedEdge]
  constructor
  · rintro (rfl | ⟨_, rfl | ⟨_, h⟩⟩)
    · exact hv
    · contradiction
    · exact h
  · intro h
    by_cases hxv : x = v
    · exact Or.inl hxv
    · exact Or.inr ⟨(fun hxw => hw (hxw ▸ h)), Or.inr ⟨hxv, h⟩⟩

/-- A simple one-edge replacement in the graph. -/
@[expose] def switchGraph (F : SimpleHypergraph V) (e : Finset V) (v w : V) :
    SimpleHypergraph V := insert (switchedEdge e v w) (F.erase e)

theorem switchGraph_card {F : SimpleHypergraph V} {e : Finset V} {v w : V}
    (he : e ∈ F) (ha : switchedEdge e v w ∉ F) :
    (switchGraph F e v w).card = F.card := by
  have hh : switchedEdge e v w ∉ F.erase e := fun h => ha (Finset.mem_of_mem_erase h)
  simp [switchGraph, hh, Finset.card_erase_of_mem he]
  have := Finset.card_pos.mpr ⟨e, he⟩
  omega

theorem vertexDegree_insert {F : SimpleHypergraph V} {e : Finset V} (he : e ∉ F)
    (x : V) : vertexDegree (insert e F) x = vertexDegree F x + if x ∈ e then 1 else 0 := by
  unfold vertexDegree
  by_cases hx : x ∈ e
  · simp [Finset.filter_insert, hx, he]
  · simp [Finset.filter_insert, hx]

theorem switchGraph_degree_source {F : SimpleHypergraph V} {e : Finset V} {v w : V}
    (he : e ∈ F) (hv : v ∈ e) (hw : w ∉ e) (ha : switchedEdge e v w ∉ F) :
    vertexDegree (switchGraph F e v w) v = vertexDegree F v - 1 := by
  have hh : switchedEdge e v w ∉ F.erase e := fun h => ha (Finset.mem_of_mem_erase h)
  rw [switchGraph, vertexDegree_insert hh, if_neg (switchedEdge_not_mem hv hw),
    Nat.add_zero, vertexDegree_erase_of_mem he hv]

theorem switchGraph_degree_other {F : SimpleHypergraph V} {e : Finset V} {v w x : V}
    (he : e ∈ F) (hv : v ∈ e) (hw : w ∉ e) (ha : switchedEdge e v w ∉ F)
    (hx : x ≠ v) : vertexDegree F x ≤ vertexDegree (switchGraph F e v w) x := by
  have hh : switchedEdge e v w ∉ F.erase e := fun h => ha (Finset.mem_of_mem_erase h)
  rw [switchGraph, vertexDegree_insert hh]
  by_cases hxe : x ∈ e
  · rw [vertexDegree_erase_of_mem he hxe, if_pos (mem_switchedEdge _ _ _ _ |>.mpr (Or.inr ⟨hx, hxe⟩))]
    have hp : 0 < vertexDegree F x := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hxe⟩⟩
    omega
  · rw [vertexDegree_erase_of_not_mem hxe]
    omega

theorem switchGraph_reverse {F : SimpleHypergraph V} {e : Finset V} {v w : V}
    (he : e ∈ F) (hv : v ∈ e) (hw : w ∉ e) (ha : switchedEdge e v w ∉ F) :
    switchGraph (switchGraph F e v w) (switchedEdge e v w) w v = F := by
  rw [switchGraph, switchedEdge_reverse hv hw]
  have hne : switchedEdge e v w ≠ e := by
    intro hh
    exact switchedEdge_not_mem hv hw (hh.symm ▸ hv)
  ext a
  simp only [switchGraph, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨_, rfl | ⟨_, h⟩⟩)
    · exact he
    · contradiction
    · exact h
  · intro h
    by_cases hh : a = e
    · exact Or.inl hh
    · exact Or.inr ⟨(fun hh' => ha (hh' ▸ h)), Or.inr ⟨hh, h⟩⟩

end LooseHamilton
