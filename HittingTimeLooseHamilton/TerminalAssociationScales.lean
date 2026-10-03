module

public import HittingTimeLooseHamilton.AssociationModels
public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics

public section

noncomputable section
namespace LooseHamilton
open Filter Finset
open scoped BigOperators

lemma degreeOn_le_card_mul_maximum {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (B : Finset V) : degreeOn d B ≤ B.card * degreeMaximum d := by
  unfold degreeOn
  calc
    _ ≤ ∑ _v ∈ B, degreeMaximum d := sum_le_sum (fun v _ => degree_le_maximum d v)
    _ = _ := by simp

/-- The error terms in association switching are uniformly smaller than half the total degree. -/
theorem eventually_association_budget (r : ℕ) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 1 ≤ Real.log (n:ℝ) ∧
      C*(n:ℝ)^(1/4:ℝ)+(r:ℝ)^2*C+2*C^2*Real.log n ≤ (n:ℝ)/2 := by
  have hpow := tendsto_nat_rpow_ratio (by norm_num : (1/4:ℝ)<1)
  simp only [Real.rpow_one] at hpow
  have hconst : Tendsto (fun n : ℕ => (r:ℝ)^2*C/(n:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hsum := ((hpow.const_mul C).add hconst).add (hlog.const_mul (2*C^2))
  simp only [mul_zero,add_zero] at hsum
  filter_upwards [eventually_ge_atTop (1:ℕ),
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually
      (eventually_ge_atTop 1),
    (tendsto_order.mp hsum).2 (1/2) (by norm_num)] with n hn hl hs
  refine ⟨hn,hl,?_⟩
  have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have he : C*((n:ℝ)^(1/4:ℝ)/(n:ℝ))+(r:ℝ)^2*C/(n:ℝ)+
      (2*C^2)*(Real.log n/(n:ℝ)) =
      (C*(n:ℝ)^(1/4:ℝ)+(r:ℝ)^2*C+2*C^2*Real.log n)/(n:ℝ) := by ring
  rw [he] at hs
  linarith [(div_lt_iff₀ hn0).mp hs]

lemma associationSlack_lower {V : Type*} [Fintype V] [DecidableEq V]
    {n r : ℕ} {C : ℝ} {d : V → ℕ} {B : Finset V}
    (hC : 0 ≤ C) (hl : 1 ≤ Real.log (n:ℝ))
    (hsum : (99/100:ℝ)*(n:ℝ)*Real.log n ≤ degreeSum d)
    (hmax : (degreeMaximum d:ℝ) ≤ C*Real.log n)
    (hcard : (B.card:ℝ) ≤ (n:ℝ)^(1/4:ℝ))
    (hbudget : C*(n:ℝ)^(1/4:ℝ)+(r:ℝ)^2*C+2*C^2*Real.log n ≤ (n:ℝ)/2) :
    (n:ℝ)*Real.log n/4 ≤ associationSlack r d B := by
  have hl0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hB : (degreeOn d B:ℝ) ≤ (n:ℝ)^(1/4:ℝ)*(C*Real.log n) := by
    have hb : (degreeOn d B:ℝ) ≤ (B.card:ℝ)*(degreeMaximum d:ℝ) := by
      exact_mod_cast degreeOn_le_card_mul_maximum d B
    exact hb.trans (mul_le_mul hcard hmax (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hr : (r:ℝ)^2*(degreeMaximum d:ℝ) ≤ (r:ℝ)^2*(C*Real.log n) := by gcongr
  have hsq : (degreeMaximum d:ℝ)^2 ≤ (C*Real.log n)^2 := by gcongr
  have hb := mul_le_mul_of_nonneg_right hbudget hl0
  unfold associationSlack
  nlinarith [mul_nonneg (show (0:ℝ) ≤ n by positivity) hl0]

lemma associationRate_upper {V : Type*} [Fintype V] [DecidableEq V]
    {n r : ℕ} {C b : ℝ} {d : V → ℕ} {B : Finset V} {y : V}
    (hn : 0 < n) (hl : 0 < Real.log (n:ℝ)) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hmax : (degreeMaximum d:ℝ) ≤ C*Real.log n)
    (hB : (degreeOn d B:ℝ) ≤ C*Real.log n*b)
    (hslack : (n:ℝ)*Real.log n/4 ≤ associationSlack r d B) :
    associationRate r d y B ≤ 4*(r:ℝ)*C^2*Real.log n*b/(n:ℝ) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hA : 0 < associationSlack r d B := lt_of_lt_of_le (by positivity) hslack
  have hy : (d y:ℝ) ≤ C*Real.log n :=
    (show (d y:ℝ) ≤ degreeMaximum d by exact_mod_cast degree_le_maximum d y).trans hmax
  have hr : ((r-1:ℕ):ℝ) ≤ (r:ℝ) := by exact_mod_cast Nat.sub_le r 1
  have hnum : (associationNumerator r d y B:ℝ) ≤ (r:ℝ)*(C*Real.log n)*(C*Real.log n*b) := by
    unfold associationNumerator
    push_cast
    gcongr
  unfold associationRate
  calc
    _ ≤ ((r:ℝ)*(C*Real.log n)*(C*Real.log n*b))/((n:ℝ)*Real.log n/4) := by
      exact div_le_div₀ (by positivity) hnum (by positivity) hslack
    _ = _ := by field_simp <;> ring

lemma degreeOn_real_upper {V : Type*} [Fintype V] [DecidableEq V]
    {C L b : ℝ} {d : V → ℕ} {B : Finset V}
    (hmax : (degreeMaximum d:ℝ) ≤ C*L) (hcard : (B.card:ℝ) ≤ b) :
    (degreeOn d B:ℝ) ≤ C*L*b := by
  have hb : (degreeOn d B:ℝ) ≤ (B.card:ℝ)*(degreeMaximum d:ℝ) := by
    exact_mod_cast degreeOn_le_card_mul_maximum d B
  have hb0 : 0 ≤ b := (Nat.cast_nonneg B.card).trans hcard
  calc
    _ ≤ (B.card:ℝ)*(degreeMaximum d:ℝ) := hb
    _ ≤ b*(C*L) := mul_le_mul hcard hmax (Nat.cast_nonneg _) hb0
    _ = _ := by ring

/-- Uniformly in the degree sequence and test set, the switching rate has its expected scale. -/
theorem eventually_association_rate_bounds (r : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < Real.log (n:ℝ) ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (d : V → ℕ),
      (99/100:ℝ)*(n:ℝ)*Real.log n ≤ degreeSum d →
      (degreeMaximum d:ℝ) ≤ C*Real.log n →
      ∀ (B : Finset V), (B.card:ℝ) ≤ (n:ℝ)^(1/4:ℝ) →
      0 < associationSlack r d B ∧
      ∀ (y : V) (b : ℝ), 0 ≤ b → (B.card:ℝ) ≤ b →
        associationRate r d y B ≤ 4*(r:ℝ)*C^2*Real.log n*b/(n:ℝ) := by
  filter_upwards [eventually_association_budget r C] with n hn
  obtain ⟨hn,hl,hbudget⟩ := hn
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnreal : (0:ℝ)<n := by exact_mod_cast hn0
  have hl0 : 0 < Real.log (n:ℝ) := by linarith
  refine ⟨hn0,hl0,?_⟩
  intro V _ _ d hsum hmax B hcard
  have hslack := associationSlack_lower hC hl hsum hmax hcard hbudget
  refine ⟨lt_of_lt_of_le (by positivity) hslack,?_⟩
  intro y b hb hbcard
  exact associationRate_upper hn0 hl0 hC hb hmax (degreeOn_real_upper hmax hbcard) hslack

/-- The union bounds for pairs and associations to a set of size n^(1/4) vanish. -/
theorem terminal_association_errors_tendsto_zero (K : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)^2*(K*Real.log n/(n:ℝ))^3/6) atTop (nhds 0) ∧
    Tendsto (fun n : ℕ => (n:ℝ)*(K*Real.log n*(n:ℝ)^(1/4:ℝ)/(n:ℝ))^2/2)
      atTop (nhds 0) := by
  constructor
  · have h := (tendsto_nat_rpow_mul_log_pow (by norm_num : (-1:ℝ)<0) 3).const_mul (K^3/6)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [Real.rpow_neg_one]
    field_simp <;> ring
  · have h := (tendsto_nat_rpow_mul_log_pow (by norm_num : (-1/2:ℝ)<0) 2).const_mul (K^2/2)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hp : ((n:ℝ)^(1/4:ℝ))^2 = (n:ℝ)^(1/2:ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      norm_num
    have he : (n:ℝ)^(-1/2:ℝ)*(n:ℝ) = (n:ℝ)^(1/2:ℝ) := by
      calc
        _ = (n:ℝ)^(-1/2:ℝ)*(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hn0]; norm_num
    simp only [mul_pow,div_pow]
    rw [hp]
    field_simp
    rw [←he]
    ring
end LooseHamilton
