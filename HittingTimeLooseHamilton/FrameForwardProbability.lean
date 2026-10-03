module

public import HittingTimeLooseHamilton.FiniteMomentBounds
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! Finite probability assembly for the pointwise forward witness. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset

lemma event_not_and_le {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (A B : Ω → Prop) :
    p.event (fun x => ¬(A x ∧ B x)) ≤
      p.event (fun x => ¬A x)+p.event (fun x => ¬B x) := by
  classical
  unfold FiniteEntropy.Law.event
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha,hb,p.nonneg x]

/-- Four pointwise good events suffice without independence. -/
theorem forward_four_event_lower {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (A B C D Success : Ω → Prop)
    (ea eb ec ed : ℝ)
    (hA : p.event (fun x => ¬A x) ≤ ea)
    (hB : p.event (fun x => ¬B x) ≤ eb)
    (hC : p.event (fun x => ¬C x) ≤ ec)
    (hD : p.event (fun x => ¬D x) ≤ ed)
    (hs : ∀ x, A x → B x → C x → D x → Success x) :
    1-(ea+eb+ec+ed) ≤ p.event Success := by
  have h₁ := event_not_and_le p A (fun x => B x ∧ C x ∧ D x)
  have h₂ := event_not_and_le p B (fun x => C x ∧ D x)
  have h₃ := event_not_and_le p C D
  have hm : p.event (fun x => A x ∧ B x ∧ C x ∧ D x) ≤ p.event Success :=
    p.event_mono (fun x hx => hs x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2)
  rw [p.event_compl] at h₁
  linarith

end LooseHamilton.CandidateBalance
