module

public import HittingTimeLooseHamilton.KahnRandomOrder
public import Mathlib.Data.Fintype.EquivFin

public section

/-! Bridge between edge permutations and bijections to finite ranks. -/
noncomputable section
namespace LooseHamilton
/-- Edge permutations and rank bijections describe the same random ordering. -/
@[expose] def orderRankEquiv (A : Type*) [Fintype A] :
    Equiv.Perm A ≃ (A ≃ Fin (Fintype.card A)) where
  toFun σ := σ.trans (Fintype.equivFin A)
  invFun ρ := ρ.trans (Fintype.equivFin A).symm
  left_inv σ := by ext a; simp
  right_inv ρ := by ext a; simp
end LooseHamilton
