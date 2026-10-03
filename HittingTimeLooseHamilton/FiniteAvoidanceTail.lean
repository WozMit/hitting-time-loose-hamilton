module

public import HittingTimeLooseHamilton.KahnLaw
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

noncomputable section
open scoped BigOperators
open Finset
namespace LooseHamilton.Hypergeometric
variable {Ω A : Type*} [Fintype Ω] [DecidableEq A]

lemma product_absent_indicator (S T : Finset A) (z : ℝ) :
    (∏ a ∈ T, if a ∈ S then 0 else z) = if Disjoint S T then z ^ T.card else 0 := by
  classical
  by_cases h : Disjoint S T
  · rw [if_pos h]
    calc
      _ = ∏ _a ∈ T, z := by
        apply prod_congr rfl
        intro a ha
        rw [if_neg (fun hs => disjoint_left.mp h hs ha)]
      _ = _ := by simp
  · rw [if_neg h]
    obtain ⟨a,haS,haT⟩ := not_disjoint_iff.mp h
    exact prod_eq_zero haT (by simp [haS])

/-- Positive-coefficient expansion of a negative exponential of an intersection count. -/
lemma intersection_power_expansion (S D : Finset A) (q : ℝ) :
    q ^ (S ∩ D).card = ∑ T ∈ D.powerset,
      ((1 - q) ^ T.card * q ^ (D \ T).card) * (if Disjoint S T then 1 else 0) := by
  classical
  have hprod : (∏ a ∈ D, ((if a ∈ S then 0 else 1 - q) + q)) = q ^ (S ∩ D).card := by
    calc
      _ = ∏ a ∈ D, if a ∈ S then q else 1 := by
        apply prod_congr rfl
        intro a ha
        split_ifs <;> ring
      _ = q ^ (S ∩ D).card := by
        rw [Finset.prod_ite]
        have heq : D.filter (fun a => a ∈ S) = S ∩ D := by ext; simp [and_comm]
        simp [heq]
  rw [← hprod, prod_add]
  apply sum_congr rfl
  intro T hT
  rw [product_absent_indicator]
  simp only [prod_const]
  split_ifs <;> ring

/-- Joint-event version of the negative-Laplace bound: avoidance estimates
with a prefactor c retain that same prefactor after the powerset expansion. -/
theorem moment_le_of_avoidance (p : FiniteEntropy.Law Ω) (S : Ω → Finset A)
    (D : Finset A) (B : Ω → Prop) [DecidablePred B] (q a c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (_ha : 0 ≤ a)
    (havoid : ∀ T ⊆ D, p.event (fun ω => B ω ∧ Disjoint (S ω) T) ≤ c * a ^ T.card) :
    (∑ ω, if B ω then p.mass ω * q ^ (S ω ∩ D).card else 0) ≤
      c * (q + (1 - q) * a) ^ D.card := by
  classical
  let coeff : Finset A → ℝ := fun T => (1 - q) ^ T.card * q ^ (D \ T).card
  have hexp (ω : Ω) : (if B ω then p.mass ω * q ^ (S ω ∩ D).card else 0) =
      ∑ T ∈ D.powerset, coeff T * (if B ω ∧ Disjoint (S ω) T then p.mass ω else 0) := by
    by_cases hB : B ω
    · rw [if_pos hB, intersection_power_expansion, mul_sum]
      apply sum_congr rfl
      intro T hT
      simp only [hB, true_and]
      change p.mass ω * (coeff T * (if Disjoint (S ω) T then 1 else 0)) = _
      split_ifs <;> ring
    · simp [hB]
  have heq : (∑ ω, if B ω then p.mass ω * q ^ (S ω ∩ D).card else 0) =
      ∑ T ∈ D.powerset, coeff T * p.event (fun ω => B ω ∧ Disjoint (S ω) T) := by
    simp_rw [hexp]
    rw [sum_comm]
    apply sum_congr rfl
    intro T hT
    rw [← mul_sum]
    unfold FiniteEntropy.Law.event
    congr 1
    apply sum_congr rfl
    intro ω hω
    by_cases h : B ω ∧ Disjoint (S ω) T <;> simp [h]
  rw [heq]
  calc
    _ ≤ ∑ T ∈ D.powerset, coeff T * (c * a ^ T.card) := by
      apply sum_le_sum
      intro T hT
      apply mul_le_mul_of_nonneg_left (havoid T (mem_powerset.mp hT))
      exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hq1) _) (pow_nonneg hq0 _)
    _ = c * ∑ T ∈ D.powerset, (((1 - q) * a) ^ T.card * q ^ (D \ T).card) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro T hT
      dsimp [coeff]
      rw [mul_pow]
      ring
    _ = c * (q + (1 - q) * a) ^ D.card := by
      congr 1
      have h := prod_add (fun _a : A => (1 - q) * a) (fun _a : A => q) D
      simpa only [prod_const, add_comm] using h.symm

/-- Exponential Markov step, with a simultaneous auxiliary event B. -/
theorem lower_tail_le_of_avoidance (p : FiniteEntropy.Law Ω) (S : Ω → Finset A)
    (D : Finset A) (B : Ω → Prop) [DecidablePred B] (q a c : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (ha : 0 ≤ a) (k : ℕ)
    (havoid : ∀ T ⊆ D, p.event (fun ω => B ω ∧ Disjoint (S ω) T) ≤ c * a ^ T.card) :
    p.event (fun ω => B ω ∧ (S ω ∩ D).card ≤ k) ≤
      c * (q + (1 - q) * a) ^ D.card / q ^ k := by
  classical
  have hmarkov : q ^ k * p.event (fun ω => B ω ∧ (S ω ∩ D).card ≤ k) ≤
      ∑ ω, if B ω then p.mass ω * q ^ (S ω ∩ D).card else 0 := by
    unfold FiniteEntropy.Law.event
    rw [mul_sum]
    apply sum_le_sum
    intro ω hω
    by_cases hB : B ω
    · simp only [hB, true_and, ↓reduceIte]
      by_cases hk : (S ω ∩ D).card ≤ k
      · rw [if_pos hk]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hq0.le hq1 hk) (p.nonneg ω)
      · rw [if_neg hk, mul_zero]
        exact mul_nonneg (p.nonneg ω) (pow_nonneg hq0.le _)
    · simp [hB]
  apply (le_div_iff₀ (pow_pos hq0 _)).mpr
  rw [mul_comm]
  exact hmarkov.trans (moment_le_of_avoidance p S D B q a c hq0.le hq1 ha havoid)

/-- Exponential form of the finite avoidance-to-lower-tail estimate. -/
theorem lower_tail_exp_le_of_avoidance (p : FiniteEntropy.Law Ω) (S : Ω → Finset A)
    (D : Finset A) (B : Ω → Prop) [DecidablePred B] (q ρ c : ℝ)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (_hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hc : 0 ≤ c) (k : ℕ)
    (havoid : ∀ T ⊆ D, p.event (fun ω => B ω ∧ Disjoint (S ω) T) ≤ c * (1 - ρ) ^ T.card) :
    p.event (fun ω => B ω ∧ (S ω ∩ D).card ≤ k) ≤
      c * Real.exp (-ρ * D.card * (1 - q) - (k : ℝ) * Real.log q) := by
  have h := lower_tail_le_of_avoidance p S D B q (1 - ρ) c hq0 hq1 (sub_nonneg.mpr hρ1) k havoid
  have hbase0 : 0 ≤ q + (1 - q) * (1 - ρ) :=
    add_nonneg hq0.le (mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hρ1))
  have hbase : q + (1 - q) * (1 - ρ) ≤ Real.exp (-ρ * (1 - q)) := by
    have he := Real.add_one_le_exp (-ρ * (1 - q))
    nlinarith
  have hpow := pow_le_pow_left₀ hbase0 hbase D.card
  have hexp : Real.exp (-ρ * (1 - q)) ^ D.card = Real.exp (-ρ * D.card * (1 - q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hpow
  have hquot := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc) (pow_nonneg hq0.le k)
  apply h.trans (hquot.trans_eq _)
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hq0]
  ring

end LooseHamilton.Hypergeometric
