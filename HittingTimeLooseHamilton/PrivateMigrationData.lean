module

public import HittingTimeLooseHamilton.CompletionModels
public import HittingTimeLooseHamilton.CycleSurgery

public section

/-! # Labels for moving a distinguished private vertex

The pair in a label is unordered. All families count actual ordinary edge sets.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

structure PrivateMigrationLegal (r : ℕ) (markers host : Finset (Finset V))
    (D q : Finset V) (x : V) (R uv : Finset V) : Prop where
  rest_card : R.card = r - 3
  x_not_mem_rest : x ∉ R
  pair_card : uv.card = 2
  private_pair_disjoint : Disjoint (insert x R) uv
  forbidden_disjoint : Disjoint (uv ∪ insert x R)
    (D ∪ originalPorts (insert q markers))
  edge_mem : uv ∪ insert x R ∈ host

@[expose] def privateMigrationLabels (r : ℕ) (markers host : Finset (Finset V))
    (D q : Finset V) (x : V) : Finset (Finset V × Finset V) := by
  classical
  exact univ.filter fun a => PrivateMigrationLegal r markers host D q x a.1 a.2

@[simp] theorem mem_privateMigrationLabels (r : ℕ) (markers host : Finset (Finset V))
    (D q : Finset V) (x : V) (a : Finset V × Finset V) :
    a ∈ privateMigrationLabels r markers host D q x ↔
      PrivateMigrationLegal r markers host D q x a.1 a.2 := by
  classical
  simp [privateMigrationLabels]

@[expose] def privateMigrationInputFamily (r : ℕ) (markers host : Finset (Finset V))
    (D q : Finset V) (x : V) (R uv : Finset V) : Finset (Finset (Finset V)) :=
  cycleOnFamily r (univ \ (D ∪ insert x R)) (insert uv (insert q markers)) host

@[simp] theorem mem_privateMigrationInputFamily (r : ℕ)
    (markers host : Finset (Finset V)) (D q : Finset V) (x : V)
    (R uv : Finset V) (F : Finset (Finset V)) :
    F ∈ privateMigrationInputFamily r markers host D q x R uv ↔
      IsMixedCycleOn r (univ \ (D ∪ insert x R)) (insert uv (insert q markers)) F ∧
        F ⊆ host := mem_cycleOnFamily _ _ _ _ _

namespace PrivateMigrationLegal
variable {r : ℕ} {markers host : Finset (Finset V)} {D q : Finset V}
  {x : V} {R uv : Finset V}

theorem private_card (h : PrivateMigrationLegal r markers host D q x R uv)
    (hr : 3 ≤ r) : (insert x R).card = r - 2 := by
  rw [card_insert_of_notMem h.x_not_mem_rest, h.rest_card]
  omega

theorem private_deleted_disjoint (h : PrivateMigrationLegal r markers host D q x R uv) :
    Disjoint (insert x R) D :=
  h.forbidden_disjoint.mono subset_union_right subset_union_left

theorem pair_not_mem (h : PrivateMigrationLegal r markers host D q x R uv) :
    uv ∉ insert q markers := by
  intro hm
  have hd : Disjoint uv uv := h.forbidden_disjoint.mono subset_union_left (by
    intro y hy
    exact mem_union_right _ (mem_biUnion.mpr ⟨uv, hm, hy⟩))
  have := disjoint_self.mp hd
  have := h.pair_card
  simp_all

end PrivateMigrationLegal
end LooseHamilton
