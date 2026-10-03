module

public import HittingTimeLooseHamilton.MigrationMarkerBounds
public import HittingTimeLooseHamilton.Setup
public import Mathlib.Tactic

public section

noncomputable section
namespace LooseHamilton
namespace AuxiliaryFrame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Label slots record bounded changes, rather than an assumed bound on a frame family. -/
abbrev Code (r : ℕ) (V : Type*) :=
  (Fin (4*r) → Option V) × (Fin 2 → Option (V × V)) ×
    (Fin 2 → Option (V × V)) × (V × V) × Option (V × V)

@[expose] def labelledSet {a : ℕ} (f : Fin a → Option V) : Finset V :=
  univ.biUnion (fun i => (f i).toFinset)

omit [Fintype V] in
theorem labelledSet_card_le {a : ℕ} (f : Fin a → Option V) :
    (labelledSet f).card ≤ a := by
  apply (card_biUnion_le).trans
  calc
    ∑ i : Fin a, (f i).toFinset.card ≤ ∑ _i : Fin a, 1 := by
      apply sum_le_sum
      intro i _
      cases f i <;> simp
    _ = a := by simp

@[expose] def pairSet {a : ℕ} (f : Fin a → Option (V × V)) : Finset (Finset V) :=
  (labelledSet f).image (fun p => {p.1,p.2})

omit [Fintype V] in
theorem pairSet_card_le {a : ℕ} (f : Fin a → Option (V × V)) :
    (pairSet f).card ≤ a := (card_image_le).trans (labelledSet_card_le f)

@[expose] def Code.deleted {r : ℕ} (c : Code r V) := labelledSet c.1
@[expose] def Code.markers {r : ℕ} (c : Code r V) (original : Finset (Finset V)) :=
  (original \ pairSet c.2.1) ∪ pairSet c.2.2.1
@[expose] def Code.active {r : ℕ} (c : Code r V) : Finset V := univ \ c.deleted
@[expose] def Code.root {r : ℕ} (c : Code r V) := c.2.2.2.1
@[expose] def Code.relative {r : ℕ} (c : Code r V) := c.2.2.2.2

structure Legal {r : ℕ} (original : Finset (Finset V)) (c : Code r V) : Prop where
  matching : IsPairMatching (c.markers original)
  retained : ∀ e ∈ c.markers original, e ⊆ c.active
  root_mem : {c.root.1,c.root.2} ∈ c.markers original
  relative_mem : ∀ p ∈ c.relative, {p.1,p.2} ∈ c.markers original

abbrev Frame (r : ℕ) (original : Finset (Finset V)) := {c : Code r V // Legal original c}

@[expose] instance (r : ℕ) (original : Finset (Finset V)) : Fintype (Frame r original) :=
  Fintype.ofFinite _

omit [Fintype V] in
theorem Code.deleted_card_le {r : ℕ} (c : Code r V) : c.deleted.card ≤ 4*r :=
  labelledSet_card_le _
omit [Fintype V] in
theorem Code.marker_budget {r : ℕ} (c : Code r V) (original : Finset (Finset V)) :
    MarkerBudget original (c.markers original) :=
  markerBudget_of_changes _ _ _ (pairSet_card_le _) (pairSet_card_le _)
theorem Legal.nonempty {r : ℕ} {original : Finset (Finset V)} {c : Code r V}
    (h : Legal original c) : (c.markers original).Nonempty := ⟨_,h.root_mem⟩

omit [DecidableEq V] in
/-- An explicit polynomial bound for all label specifications, including unused slots. -/
theorem code_card_le (r : ℕ) :
    Fintype.card (Code r V) ≤ (Fintype.card V + 1) ^ (4*r+12) := by
  let n := Fintype.card V
  have hp : n*n+1 ≤ (n+1)^2 := by nlinarith
  have hn : n*n ≤ (n+1)^2 := by nlinarith
  simp only [Code, Fintype.card_prod, Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
  change (n+1)^(4*r) * ((n*n+1)^2 * ((n*n+1)^2 * ((n*n)*(n*n+1)))) ≤ _
  calc
    _ ≤ (n+1)^(4*r) * (((n+1)^2)^2 * (((n+1)^2)^2 * ((n+1)^2*(n+1)^2))) := by
      gcongr
    _ = (n+1)^(4*r+12) := by ring

theorem frame_card_le (r : ℕ) (original : Finset (Finset V)) :
    Fintype.card (Frame r original) ≤ (Fintype.card V+1)^(4*r+12) := by
  classical
  exact (Fintype.card_subtype_le _).trans (code_card_le r)

/-- The manuscript's polynomial-in-N form for every subfamily of generated frames. -/
theorem frame_family_card_le (r : ℕ) (original : Finset (Finset V))
    (A : Finset (Frame r original)) (hN : 2 ≤ Fintype.card V) :
    A.card ≤ (Fintype.card V)^(8*r+24) := by
  have hbase : Fintype.card V+1 ≤ (Fintype.card V)^2 := by nlinarith
  calc
    A.card ≤ Fintype.card (Frame r original) := card_le_univ _
    _ ≤ (Fintype.card V+1)^(4*r+12) := frame_card_le r original
    _ ≤ ((Fintype.card V)^2)^(4*r+12) := Nat.pow_le_pow_left hbase _
    _ = (Fintype.card V)^(8*r+24) := by rw [← pow_mul]; congr 1; ring

end AuxiliaryFrame
end LooseHamilton
