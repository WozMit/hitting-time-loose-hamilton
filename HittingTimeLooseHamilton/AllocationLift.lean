module

public import HittingTimeLooseHamilton.Allocation

public section
namespace LooseHamilton.Allocation
noncomputable section
open Finset
variable {V U B : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
  [Fintype B] [DecidableEq B] {k d : ℕ}
/-- Place an allocation on a vertex subset, and transport its block labels. -/
@[expose] def liftBlocks (P : Blocks U k d) (j : U ↪ V) (b : B ≃ Fin k) (i : B) : Finset V :=
  (P.val (b i)).map j
omit [Fintype U] [DecidableEq U] [DecidableEq V] [Fintype B] [DecidableEq B] in
@[simp] theorem liftBlocks_card (P : Blocks U k d) (j : U ↪ V) (b : B ≃ Fin k) (i : B) :
    (liftBlocks P j b i).card = d := by simp [liftBlocks, P.property.1]
omit [Fintype U] [DecidableEq U] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem liftBlocks_disjoint (P : Blocks U k d) (j : U ↪ V) (b : B ≃ Fin k) :
    Pairwise (fun i l => Disjoint (liftBlocks P j b i) (liftBlocks P j b l)) := by
  intro i l hil
  apply disjoint_left.mpr
  intro v hi hl
  obtain ⟨u, hu, rfl⟩ := mem_map.mp hi
  obtain ⟨w, hw, he⟩ := mem_map.mp hl
  have hwu : w = u := j.injective he
  subst w
  exact disjoint_left.mp (blocks_disjoint _ _ _ P (fun h => hil (b.injective h))) hu hw

omit [DecidableEq U] [DecidableEq B] in
theorem liftBlocks_union (P : Blocks U k d) (j : U ↪ V) (b : B ≃ Fin k) :
    univ.biUnion (liftBlocks P j b) = univ.map j := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
    obtain ⟨u, _, rfl⟩ := mem_map.mp hi
    exact mem_map.mpr ⟨u, mem_univ _, rfl⟩
  · intro hv
    obtain ⟨u, _, rfl⟩ := mem_map.mp hv
    obtain ⟨i, hi, _⟩ := P.property.2 u
    exact mem_biUnion.mpr ⟨b.symm i, mem_univ _, mem_map.mpr ⟨u, by simpa using hi, rfl⟩⟩

omit [DecidableEq U] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem liftBlocks_subset (P : Blocks U k d) (j : U ↪ V) (b : B ≃ Fin k) (i : B) :
    liftBlocks P j b i ⊆ univ.map j := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := mem_map.mp hv
  exact mem_map.mpr ⟨u, mem_univ _, rfl⟩
end
end LooseHamilton.Allocation
