module

public import HittingTimeLooseHamilton.KahnMatching
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod

public section

/-! Coordinates identifying each vertex with a matching block and a position in it. -/
namespace Kahn.PerfectMatching
variable {n r : ℕ} (M : Kahn.PerfectMatching n r)

/-- A matching block together with a vertex belonging to that block. -/
@[expose] noncomputable def vertexSigmaEquiv :
    Fin n ≃ (Σ B : {B // B ∈ M.val}, {v : Fin n // v ∈ B.val}) where
  toFun v := ⟨⟨M.edge v, M.edge_mem v⟩, ⟨v, M.mem_edge v⟩⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨B, hB⟩, ⟨v, hv⟩⟩
    have hE : M.edge v = B := (M.eq_edge_of_mem hB hv).symm
    cases hE
    rfl

/-- Coordinates by block and one of `r` positions, chosen using finite equivalences. -/
@[expose] noncomputable def vertexCoordinates :
    Fin n ≃ {B // B ∈ M.val} × Fin r :=
  M.vertexSigmaEquiv |>.trans
    ((Equiv.sigmaCongrRight (fun B : {B // B ∈ M.val} =>
      Finset.equivFinOfCardEq (M.property.1 B.val B.property))).trans
      (Equiv.sigmaEquivProd _ _))

/-- The block coordinate is precisely the matching edge containing the vertex. -/
@[simp] theorem vertexCoordinates_block (v : Fin n) :
    (M.vertexCoordinates v).1.val = M.edge v := rfl

/-- Two vertices have the same block coordinate exactly when their matching edges agree. -/
theorem vertexCoordinates_same_block (v w : Fin n) :
    (M.vertexCoordinates v).1 = (M.vertexCoordinates w).1 ↔ M.edge v = M.edge w := by
  exact Subtype.ext_iff

/-- The number of vertices equals the number of blocks times their common size. -/
theorem card_blocks_mul : n = M.val.card * r := by
  have h := Fintype.card_congr M.vertexCoordinates
  simpa using h

include M in
/-- Existence of a perfect matching forces the required divisibility. -/
theorem uniformity_dvd : r ∣ n := by
  rw [M.card_blocks_mul]
  exact dvd_mul_left r M.val.card

end Kahn.PerfectMatching
