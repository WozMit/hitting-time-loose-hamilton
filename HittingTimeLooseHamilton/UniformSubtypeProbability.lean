module

public import HittingTimeLooseHamilton.KahnRandomOrder
public import HittingTimeLooseHamilton.KahnConditioning
public import Mathlib.Data.Fintype.Card

public section

/-! Exact uniform conditioning on a nonempty finite subtype. -/
noncomputable section
namespace FiniteEntropy.Law
open Finset

lemma uniform_product_eq {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (uniform : Law (A×B)) = (uniform : Law A).prod (uniform : Law B) := by
  apply ext_mass
  intro x
  simp [uniform,prod,Fintype.card_prod,mul_inv_rev,mul_comm]

lemma uniform_subtype_conditioning {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E P : Ω→Prop) [DecidablePred E] [Nonempty {ω // E ω}] :
    (uniform : Law Ω).event (fun ω=>E ω ∧ P ω) =
      (uniform : Law Ω).event E *
        (uniform : Law {ω // E ω}).event (fun ω=>P ω.val) := by
  classical
  have heq : Fintype.card {ω : Ω // E ω ∧ P ω} =
      Fintype.card {ω : {ω : Ω // E ω} // P ω.val} := by
    apply Fintype.card_congr
    exact ⟨(fun ω => ⟨⟨ω.val,ω.property.1⟩,ω.property.2⟩),
      (fun ω => ⟨ω.val.val,ω.val.property,ω.property⟩),
      (fun ω => rfl), (fun ω => rfl)⟩
  rw [uniform_event,uniform_event,uniform_event,
    ←Fintype.card_subtype,←Fintype.card_subtype,←Fintype.card_subtype,heq]
  have hE : (Fintype.card {ω // E ω}:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp <;> ring
end FiniteEntropy.Law

namespace LooseHamilton
export FiniteEntropy.Law (uniform_product_eq)
alias uniform_event_and_eq_mul_subtype := FiniteEntropy.Law.uniform_subtype_conditioning
end LooseHamilton
