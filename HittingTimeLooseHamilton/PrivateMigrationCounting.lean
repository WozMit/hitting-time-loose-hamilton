module

public import HittingTimeLooseHamilton.PrivateMigrationInjection

public section

/-! # Counting all disjoint images of private-coordinate migration -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The domain remembers both summation labels and the actual input edge set. -/
abbrev PrivateMigrationDomain (r : ℕ) (markers host : Finset (Finset V))
    (D q : Finset V) (x : V) :=
  Σ a : ↥(privateMigrationLabels r markers host D q x),
    ↥(privateMigrationInputFamily r markers host D q x a.val.1 a.val.2)

variable {r : ℕ} {markers host : Finset (Finset V)} {D q : Finset V} {x : V}

@[expose] def privateMigrationMap (hr : 3 ≤ r) :
    PrivateMigrationDomain r markers host D q x →
      ↥(completionFamily r markers host D q) := fun a =>
  ⟨insert (a.1.val.2 ∪ insert x a.1.val.1) a.2.val,
    privateMigration_expand_mem hr
      ((mem_privateMigrationLabels _ _ _ _ _ _ _).mp a.1.property) a.2.property⟩

theorem privateMigrationMap_injective (hr : 3 ≤ r) :
    Function.Injective (privateMigrationMap (markers := markers) (host := host)
      (D := D) (q := q) (x := x) hr) := by
  rintro ⟨⟨⟨R, uv⟩, ha⟩, ⟨F, hF⟩⟩ ⟨⟨⟨R', uv'⟩, ha'⟩, ⟨F', hF'⟩⟩ heq
  have h := privateMigration_joint_injective hr
    ((mem_privateMigrationLabels _ _ _ _ _ _ _).mp ha)
    ((mem_privateMigrationLabels _ _ _ _ _ _ _).mp ha') hF hF'
    (congrArg Subtype.val heq)
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- Every legal summand is counted once; the pair label is unordered. -/
theorem privateMigration_count_le (hr : 3 ≤ r) :
    ∑ a ∈ privateMigrationLabels r markers host D q x,
      (privateMigrationInputFamily r markers host D q x a.1 a.2).card ≤
        completionCount r markers host D q := by
  classical
  have h := Fintype.card_le_of_injective _ (privateMigrationMap_injective
    (markers := markers) (host := host) (D := D) (q := q) (x := x) hr)
  have hc : Fintype.card (PrivateMigrationDomain r markers host D q x) =
      ∑ a ∈ privateMigrationLabels r markers host D q x,
        (privateMigrationInputFamily r markers host D q x a.1 a.2).card := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    exact Finset.sum_coe_sort _ (fun a : Finset V × Finset V =>
      (privateMigrationInputFamily r markers host D q x a.1 a.2).card)
  rw [hc, Fintype.card_coe] at h
  exact h

end LooseHamilton
