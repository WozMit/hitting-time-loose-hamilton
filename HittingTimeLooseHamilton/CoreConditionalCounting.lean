module

public import HittingTimeLooseHamilton.KahnConditioning
public import HittingTimeLooseHamilton.DisjointEventSum

public section

/-! Conditional uniformity from equal unconditional masses of the fibres. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators

theorem condition_event_eq_joint {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (E A : Ω → Prop) (hE : 0 < p.event E) :
    (p.condition E hE).event A = p.event (fun ω => E ω ∧ A ω) / p.event E := by
  classical
  unfold FiniteEntropy.Law.event FiniteEntropy.Law.condition
  rw [sum_div]
  apply sum_congr rfl
  intro ω _
  by_cases he : E ω <;> by_cases ha : A ω <;> simp [he, ha, FiniteEntropy.Law.event]

/-- A positive event partitioned into equally likely finite fibres gives the
uniform law, including an explicit proof of its normalization. -/
theorem conditional_uniform_of_equal_fibres {Ω A : Type*}
    [Fintype Ω] [Fintype A] [DecidableEq A]
    (p : FiniteEntropy.Law Ω) (E : Ω → Prop) (f : Ω → A) (S : Finset A)
    (hE : 0 < p.event E) (hsupport : ∀ ω, E ω → f ω ∈ S)
    (w : ℝ) (hw : ∀ a ∈ S, p.event (fun ω => E ω ∧ f ω = a) = w)
    (a : A) (ha : a ∈ S) :
    (p.condition E hE).event (fun ω => f ω = a) = 1 / (S.card : ℝ) := by
  classical
  have hpartition : (fun ω => E ω) =
      (fun ω => ∃ b : ↥S, E ω ∧ f ω = b.val) := by
    funext ω
    apply propext
    constructor
    · intro he; exact ⟨⟨f ω, hsupport ω he⟩, he, rfl⟩
    · rintro ⟨b,he,_⟩; exact he
  have hsum : p.event E = (S.card : ℝ) * w := by
    change p.event (fun ω => E ω) = _
    rw [hpartition, event_exists_eq_sum p _ (by
      intro ω b c hb hc
      exact Subtype.ext (hb.2.symm.trans hc.2))]
    have hpoint (b : ↥S) : p.event (fun ω => E ω ∧ f ω = b.val) = w := hw b.val b.property
    simp only [hpoint, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hc : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (card_pos.mpr ⟨a,ha⟩).ne'
  rw [condition_event_eq_joint, hw a ha]
  apply (div_eq_div_iff hE.ne' hc).mpr
  rw [one_mul, hsum]
  ring
end LooseHamilton
