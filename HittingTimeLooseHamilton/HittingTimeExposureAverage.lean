module

public import HittingTimeLooseHamilton.CoreConditionalCounting
public import HittingTimeLooseHamilton.DisjointEventSum
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! Averaging over a finite exposed observation without a union bound over
its possible values or conditioning on a global good event. -/
noncomputable section
namespace LooseHamilton.HittingTimeExposure
open Finset
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

lemma joint_le_of_conditional (p : FiniteEntropy.Law Ω) (E B : Ω → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ hE : 0 < p.event E, (p.condition E hE).event B ≤ ε) :
    p.event (fun ω => E ω ∧ B ω) ≤ ε * p.event E := by
  by_cases he : 0 < p.event E
  · have hh := h he
    rw [condition_event_eq_joint] at hh
    exact (div_le_iff₀ he).mp hh
  · have hz : p.event E = 0 := le_antisymm (le_of_not_gt he) (p.event_nonneg _)
    rw [hz,mul_zero]
    exact (p.event_mono (fun _ h => h.1)).trans_eq hz

lemma good_joint_le (p : FiniteEntropy.Law Ω) (f : Ω → A)
    (Good : A → Prop) (Bad : Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (hcond : ∀ a, Good a → ∀ ha : 0 < p.event (fun ω => f ω = a),
      (p.condition (fun ω => f ω = a) ha).event Bad ≤ ε) :
    p.event (fun ω => Good (f ω) ∧ Bad ω) ≤ ε := by
  classical
  have he : (fun ω => Good (f ω) ∧ Bad ω) =
      (fun ω => ∃ a, f ω = a ∧ Good a ∧ Bad ω) := by
    funext ω
    exact propext ⟨fun h => ⟨f ω,rfl,h⟩,fun ⟨a,ha,hg,hb⟩ => ⟨ha.symm ▸ hg,hb⟩⟩
  rw [he,event_exists_eq_sum p _ (by intro ω a b ha hb; exact ha.1.symm.trans hb.1)]
  calc
    _ ≤ ∑ a, ε * p.event (fun ω => f ω = a) := by
      apply sum_le_sum
      intro a _
      by_cases hg : Good a
      · simpa only [hg,true_and] using joint_le_of_conditional p (fun ω => f ω=a) Bad ε hε (hcond a hg)
      · simp only [hg,false_and,and_false]
        rw [p.event_eq_zero_of_false (fun _ => id)]
        exact mul_nonneg hε (p.event_nonneg _)
    _ = ε := by
      rw [← mul_sum]
      change ε * (∑ a, (p.map f).mass a) = ε
      rw [(p.map f).total,mul_one]

/-- The failure probability is the probability of a bad exposed observation
plus one uniform conditional error. No cardinality factor occurs. -/
theorem average_failure (p : FiniteEntropy.Law Ω) (f : Ω → A)
    (Good : A → Prop) (Bad : Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (hcond : ∀ a, Good a → ∀ ha : 0 < p.event (fun ω => f ω = a),
      (p.condition (fun ω => f ω = a) ha).event Bad ≤ ε) :
    p.event Bad ≤ p.event (fun ω => ¬ Good (f ω)) + ε := by
  have hs : p.event Bad ≤ p.event (fun ω => ¬ Good (f ω)) +
      p.event (fun ω => Good (f ω) ∧ Bad ω) := by
    classical
    unfold FiniteEntropy.Law.event
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro ω _
    by_cases hg : Good (f ω) <;> by_cases hb : Bad ω <;> simp [hg,hb,p.nonneg ω]
  exact hs.trans (add_le_add_right (good_joint_le p f Good Bad ε hε hcond) _)

end LooseHamilton.HittingTimeExposure
