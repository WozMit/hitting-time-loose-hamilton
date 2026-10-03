module

public import HittingTimeLooseHamilton.KahnEntropy

public section

open scoped BigOperators
noncomputable section
namespace FiniteEntropy
namespace Law
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Probability of an event in a finite probability space. -/
@[expose] noncomputable def event (p : Law A) (E : A → Prop) : ℝ := by
  classical
  exact ∑ a, if E a then p.mass a else 0

lemma event_nonneg (p : Law A) (E : A → Prop) : 0 ≤ p.event E := by
  classical
  unfold event
  exact Finset.sum_nonneg fun a _ => ite_nonneg (p.nonneg a) (le_refl 0)

lemma event_mono (p : Law A) {E F : A → Prop} (h : ∀ a, E a → F a) :
    p.event E ≤ p.event F := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases he : E a
  · simp [he, h a he]
  · simp only [he, ↓reduceIte]
    exact ite_nonneg (p.nonneg a) (le_refl 0)

@[simp] lemma event_true (p : Law A) : p.event (fun _ => True) = 1 := by
  classical
  simpa [event] using p.total

lemma event_le_one (p : Law A) (E : A → Prop) : p.event E ≤ 1 := by
  calc
    p.event E ≤ p.event (fun _ => True) := p.event_mono (fun _ _ => trivial)
    _ = 1 := p.event_true

/-- Pushforward of a finite law; the definition includes all zero-probability values. -/
@[expose] noncomputable def map (p : Law A) (f : A → B) : Law B where
  mass b := p.event (fun a => f a = b)
  nonneg b := p.event_nonneg _
  total := by
    classical
    simp only [event]
    rw [Finset.sum_comm]
    simpa using p.total

lemma event_eq_zero_of_false (p : Law A) {E : A → Prop} (h : ∀ a, ¬ E a) :
    p.event E = 0 := by
  classical
  simp [event, h]

end Law
end FiniteEntropy
