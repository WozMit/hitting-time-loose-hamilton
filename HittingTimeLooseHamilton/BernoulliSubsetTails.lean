module

public import HittingTimeLooseHamilton.BernoulliSubsetLaw
public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics
public import HittingTimeLooseHamilton.NatLawAtoms

public section

/-! Elementary Chernoff and product lower bounds for independent subsets. -/
noncomputable section
open scoped BigOperators
open Finset
namespace LooseHamilton.BernoulliSubset
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma moment_quotient_le (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (D : Finset A) (k : ℕ) :
    (law (A := A) p hp0 hp1).finiteMean (fun S => q ^ (S ∩ D).card) / q ^ k ≤
      Real.exp (p * D.card * (q-1) - k * Real.log q) := by
  rw [intersection_moment]
  have hb : 0 ≤ 1-p+p*q := add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp0 hq.le)
  have he : 1-p+p*q ≤ Real.exp (p*(q-1)) := by
    have := Real.add_one_le_exp (p*(q-1)); linarith
  have hh := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ hb he D.card) (pow_nonneg hq.le k)
  apply hh.trans_eq
  rw [Real.exp_sub,Real.exp_nat_mul (Real.log q),Real.exp_log hq,← Real.exp_nat_mul]
  congr 1
  congr 1
  ring

theorem lower_tail (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (D : Finset A) (k : ℕ) :
    (law (A := A) p hp0 hp1).event (fun S => (S ∩ D).card ≤ k) ≤
      Real.exp (p * D.card * (q-1) - k * Real.log q) := by
  have hm := (law (A := A) p hp0 hp1).finite_markov
    (fun S => pow_nonneg hq0.le (S ∩ D).card) (pow_pos hq0 k)
  have hmono := (law (A := A) p hp0 hp1).event_mono (fun S (hS : (S ∩ D).card ≤ k) =>
    pow_le_pow_of_le_one hq0.le hq1 hS)
  exact hmono.trans (hm.trans (moment_quotient_le p q hp0 hp1 hq0 D k))

theorem upper_tail (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 1 ≤ q) (D : Finset A) (k : ℕ) :
    (law (A := A) p hp0 hp1).event (fun S => k ≤ (S ∩ D).card) ≤
      Real.exp (p * D.card * (q-1) - k * Real.log q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hm := (law (A := A) p hp0 hp1).finite_markov
    (fun S => pow_nonneg hq0.le (S ∩ D).card) (pow_pos hq0 k)
  have hmono := (law (A := A) p hp0 hp1).event_mono (fun S (hS : k ≤ (S ∩ D).card) =>
    pow_le_pow_right₀ hq hS)
  exact hmono.trans (hm.trans (moment_quotient_le p q hp0 hp1 hq0 D k))

/-- A convenient coarse lower-tail exponent; there is room above 0.9. -/
theorem degree_failure_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset A) (ell n : ℕ) (hn : 1 ≤ n)
    (hmean : (98/100:ℝ) * Real.log n ≤ p * D.card)
    (hell : (ell:ℝ) ≤ (11/1000:ℝ) * Real.log n) :
    (law (A := A) p hp0 hp1).event (fun S => (S ∩ D).card < ell) ≤
      (n:ℝ) ^ (-91/100:ℝ) := by
  have hm := (law (A := A) p hp0 hp1).event_mono
    (fun S (h : (S ∩ D).card < ell) => h.le)
  have htail := lower_tail p (1/100) hp0 hp1 (by norm_num) (by norm_num) D ell
  have hlog : Real.log (1/100:ℝ) = -Real.log 100 := by
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  rw [hlog] at htail
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hl : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have he : p * D.card * ((1/100:ℝ)-1) - (ell:ℝ)*(-Real.log 100) ≤
      Real.log n * (-91/100:ℝ) := by
    have h100 := log_hundred_lt_five
    have hmul : (ell:ℝ)*Real.log 100 ≤ (ell:ℝ)*5 :=
      mul_le_mul_of_nonneg_left h100.le (Nat.cast_nonneg _)
    nlinarith
  exact (hm.trans htail).trans ((Real.exp_le_exp.mpr he).trans_eq
    (Real.rpow_def_of_pos hn0 _).symm)

/-- A deliberately coarse upper tail at one percent above the mean. -/
theorem size_overflow_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (M : ℕ)
    (hmean : p * Fintype.card A = (99/100:ℝ) * M) :
    (law (A := A) p hp0 hp1).event (fun S => M < S.card) ≤ Real.exp (-(M:ℝ)/1010000) := by
  have ht := upper_tail p (101/100) hp0 hp1 (by norm_num) (univ : Finset A) M
  simp only [inter_univ,card_univ] at ht
  rw [hmean] at ht
  have hl : (1/101:ℝ) ≤ Real.log (101/100:ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<101/100)
    norm_num at h ⊢
    exact h
  have hb : (99/100:ℝ)*M*(101/100-1) - M*Real.log (101/100) ≤ -(M:ℝ)/1010000 := by
    have := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg M)
    nlinarith
  exact ((law (A := A) p hp0 hp1).event_mono (fun S (h : M < S.card) => h.le)).trans
    (ht.trans (Real.exp_le_exp.mpr hb))

lemma exp_neg_two_le_one_sub {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) :
    Real.exp (-2*u) ≤ 1-u := by
  have hp : 0 < 1-u := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hi : 1-(1-u)⁻¹ ≥ -2*u := by
    have he : (1-u)*(1-u)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hp)
    have hnon : 0 ≤ u*(1-2*u) := mul_nonneg hu0 (by linarith)
    nlinarith
  exact (Real.exp_le_exp.mpr (hi.trans hl)).trans_eq (Real.exp_log hp)

/-- Converts individual failure bounds into an exponential bound for their intersection. -/
theorem all_events_lower_bound {I : Type*} [Fintype I]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : I → Finset A → Prop)
    (hE : ∀ i, Monotone (E i)) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hfail : ∀ i, (law (A := A) p hp0 hp1).event (fun S => ¬E i S) ≤ u) :
    Real.exp (-2 * u * Fintype.card I) ≤ (law (A := A) p hp0 hp1).event (fun S => ∀ i, E i S) := by
  have hsingle (i : I) : Real.exp (-2*u) ≤ (law (A := A) p hp0 hp1).event (E i) := by
    have hh := hfail i
    rw [FiniteEntropy.Law.event_compl] at hh
    exact (exp_neg_two_le_one_sub hu0 hu1).trans (by linarith)
  have hprod := Finset.prod_le_prod₀ (s := (univ : Finset I))
    (fun i _ => (Real.exp_pos (-2*u)).le) (fun i _ => hsingle i)
  have hi := intersection_lower_bound (univ : Finset I) p hp0 hp1 E hE
  simp only [mem_univ,forall_const] at hi
  have he : (∏ _i : I, Real.exp (-2*u)) = Real.exp (-2*u*Fintype.card I) := by
    rw [prod_const,card_univ,← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hprod
  exact hprod.trans hi
end LooseHamilton.BernoulliSubset
