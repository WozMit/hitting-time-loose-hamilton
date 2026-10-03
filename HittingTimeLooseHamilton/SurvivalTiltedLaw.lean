module

public import HittingTimeLooseHamilton.BatchVarianceScalar
public import HittingTimeLooseHamilton.KahnConditioning

public section

/-! The survival tilt for indexed families: labels, not distinct support sets,
carry mass. This preserves multiplicity when different objects share a support. -/
noncomputable section
namespace LooseHamilton.SurvivalTilt
open Finset FiniteEntropy
open scoped BigOperators
variable {A : Type*} [Fintype A] [Nonempty A]

lemma sum_pos (q : A → ℝ) (hq : ∀ a, 0 < q a) : 0 < ∑ a, q a := by
  exact Finset.sum_pos (fun a _ => hq a) univ_nonempty

/-- Each object's mass is proportional to its individual survival probability. -/
@[expose] def law (q : A → ℝ) (hq : ∀ a, 0 < q a) : Law A where
  mass a := q a / ∑ b, q b
  nonneg a := div_nonneg (hq a).le (sum_pos q hq).le
  total := by rw [← sum_div]; exact div_self (sum_pos q hq).ne'

/-- The overlap of two independently sampled labels under the survival tilt. -/
@[expose] def pairMean (p : Law A) (I : A → A → ℝ) : ℝ :=
  ∑ a, ∑ b, p.mass a * p.mass b * I a b

lemma uniform_pairMean (I : A → A → ℝ) :
    pairMean (uniform : Law A) I =
      (∑ a, ∑ b, I a b) / (Fintype.card A : ℝ)^2 := by
  unfold pairMean
  simp only [uniform]
  simp_rw [mul_assoc, ← mul_sum]
  ring

lemma mass_le (q : A → ℝ) (hq : ∀ a, 0 < q a) (z L : ℝ)
    (hz : 0 < z) (hL : 0 ≤ L) (hlo : ∀ a, z ≤ q a) (hhi : ∀ a, q a ≤ L*z)
    (a : A) : (law q hq).mass a ≤ L / Fintype.card A := by
  have hn : (0:ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hs : (Fintype.card A:ℝ)*z ≤ ∑ a, q a := by
    simpa using (sum_le_sum (s:=univ) (fun a _ => hlo a))
  change q a / (∑ b, q b) ≤ _
  apply (div_le_iff₀ (sum_pos q hq)).2
  calc
    q a ≤ L*z := hhi a
    _ = (L/(Fintype.card A:ℝ))*((Fintype.card A:ℝ)*z)  := by field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (div_nonneg hL hn.le)

/-- Tilting by weights in [z,Lz] increases every nonnegative pair statistic by
at most L squared relative to independent uniform labels. -/
theorem pairMean_le (q : A → ℝ) (hq : ∀ a, 0 < q a) (z L : ℝ)
    (hz : 0 < z) (hL : 0 ≤ L) (hlo : ∀ a, z ≤ q a) (hhi : ∀ a, q a ≤ L*z)
    (I : A → A → ℝ) (hI : ∀ a b, 0 ≤ I a b) :
    pairMean (law q hq) I ≤ L^2 * pairMean (uniform : Law A) I := by
  have hn : (0:ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ ∑ a, ∑ b, (L/(Fintype.card A:ℝ))*(L/(Fintype.card A:ℝ))*I a b := by
      apply sum_le_sum; intro a _
      apply sum_le_sum; intro b _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mass_le q hq z L hz hL hlo hhi a)
          (mass_le q hq z L hz hL hlo hhi b) ((law q hq).nonneg b)
          (div_nonneg hL hn.le)) (hI a b)
    _ = _ := by
      rw [uniform_pairMean]
      simp_rw [← mul_sum]
      field_simp
      <;> ring

/-- The weights of the independent tilted pair sum to one. -/
lemma pair_mass_total (p : Law A) : ∑ a, ∑ b, p.mass a*p.mass b = 1 := by
  simp_rw [← mul_sum, p.total, mul_one]
  exact p.total

/-- Normalized second moment is exactly the pair-survival ratio averaged with
survival-tilted weights. This identity is why uniform weights cannot be used
at this step for supports of different sizes. -/
theorem normalized_secondMoment (q : A → ℝ) (hq : ∀ a, 0 < q a)
    (P : A → A → ℝ) :
    (∑ a, ∑ b, P a b) / (∑ a, q a)^2 =
      pairMean (law q hq) (fun a b => P a b/(q a*q b)) := by
  unfold pairMean
  rw [sum_div]
  apply sum_congr rfl; intro a _
  rw [sum_div]
  apply sum_congr rfl; intro b _
  simp only [law]
  field_simp [(hq a).ne', (hq b).ne', (sum_pos q hq).ne']
  <;> ring

/-- Subtracting one after the tilted ratio bound gives a pure overlap term. -/
theorem normalized_variance_le_tilt (q : A → ℝ) (hq : ∀ a, 0 < q a)
    (P I : A → A → ℝ) (C : ℝ)
    (hP : ∀ a b, P a b/(q a*q b) ≤ 1+C*I a b) :
    ((∑ a, ∑ b, P a b) - (∑ a, q a)^2)/(∑ a, q a)^2 ≤
      C*pairMean (law q hq) I := by
  have hs : (∑ a, q a)^2 ≠ 0 := pow_ne_zero _ (sum_pos q hq).ne'
  rw [sub_div, div_self hs, normalized_secondMoment q hq]
  have hp := sum_le_sum (s:=univ) (fun a _ =>
    sum_le_sum (s:=univ) (fun b _ => mul_le_mul_of_nonneg_left (hP a b)
      (mul_nonneg ((law q hq).nonneg a) ((law q hq).nonneg b))))
  change pairMean (law q hq) (fun a b => P a b/(q a*q b)) ≤
    ∑ a, ∑ b, (law q hq).mass a*(law q hq).mass b*(1+C*I a b) at hp
  have he : (∑ a, ∑ b, (law q hq).mass a*(law q hq).mass b*(1+C*I a b)) =
      1+C*pairMean (law q hq) I := by
    simp_rw [mul_add, mul_one, sum_add_distrib]
    rw [pair_mass_total]
    congr 1
    unfold pairMean
    simp_rw [mul_sum]
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    ring
  rw [he] at hp
  linarith

/-- Final abstract transfer used by item 30.6, with the uniform-label overlap. -/
theorem normalized_variance_le (q : A → ℝ) (hq : ∀ a, 0 < q a)
    (P I : A → A → ℝ) (C z L : ℝ) (hC : 0 ≤ C) (hz : 0 < z) (hL : 0 ≤ L)
    (hlo : ∀ a, z ≤ q a) (hhi : ∀ a, q a ≤ L*z)
    (hI : ∀ a b, 0 ≤ I a b)
    (hP : ∀ a b, P a b/(q a*q b) ≤ 1+C*I a b) :
    ((∑ a, ∑ b, P a b) - (∑ a, q a)^2)/(∑ a, q a)^2 ≤
      L^2*C*pairMean (uniform : Law A) I := by
  calc
    _ ≤ C*pairMean (law q hq) I := normalized_variance_le_tilt q hq P I C hP
    _ ≤ C*(L^2*pairMean (uniform : Law A) I) :=
      mul_le_mul_of_nonneg_left (pairMean_le q hq z L hz hL hlo hhi I hI) hC
    _ = _ := by ring

end LooseHamilton.SurvivalTilt
