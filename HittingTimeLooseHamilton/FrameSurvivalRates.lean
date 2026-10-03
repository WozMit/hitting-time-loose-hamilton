module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic

public section

noncomputable section
open Filter
namespace LooseHamilton

/-- Uniform denominator control for the two completion survival ratios. -/
lemma frame_survival_denominator (m k t : ℝ) (hm : 0 < m)
    (hk4 : 4*k ≤ m) (ht4 : 4*t ≤ m) :
    0 < m-k-t+1 ∧ m/2 ≤ m-k-t+1 := by constructor <;> linarith

lemma frame_survival_ratio_error (m k t : ℝ) (hm : 0 < m)
    (ht : 0 ≤ t) (hk4 : 4*k ≤ m) (ht4 : 4*t ≤ m) :
    |(m-k+1)/(m-k-t+1)-1| ≤ 2*t/m := by
  have hd := frame_survival_denominator m k t hm hk4 ht4
  have he : (m-k+1)/(m-k-t+1)-1 = t/(m-k-t+1) := by
    field_simp [ne_of_gt hd.1] <;> ring
  rw [he, abs_of_nonneg (div_nonneg ht hd.1.le)]
  apply (div_le_div_iff₀ hd.1 hm).2
  nlinarith [mul_nonneg ht (show 0 ≤ 2*(m-k-t+1)-m by linarith [hd.2])]

lemma frame_deleted_survival_ratio_error (m k t : ℝ) (hm : 0 < m)
    (hk : 1 ≤ k) (ht : 0 ≤ t) (hk4 : 4*k ≤ m) (ht4 : 4*t ≤ m) :
    |m/(m-k-t+1)-1| ≤ 2*(k+t)/m := by
  have hd := frame_survival_denominator m k t hm hk4 ht4
  have he : m/(m-k-t+1)-1 = (k+t-1)/(m-k-t+1) := by
    field_simp [ne_of_gt hd.1]; ring
  rw [he, abs_of_nonneg (div_nonneg (by linarith) hd.1.le)]
  apply (div_le_div_iff₀ hd.1 hm).2
  nlinarith [mul_nonneg (show 0 ≤ k+t by linarith)
    (show 0 ≤ 2*(m-k-t+1)-m by linarith [hd.2])]

/-- The batch-size bound and the lower comparison of k with N yield the first rate. -/
lemma frame_survival_ratio_rate (m k t N ν a : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hN : 0 < N) (_hν : 0 ≤ ν)
    (ht : 0 ≤ t) (hk4 : 4*k ≤ m) (ht4 : 4*t ≤ m)
    (htν : t ≤ ν*m/k) (hNk : N ≤ a*k) :
    |(m-k+1)/(m-k-t+1)-1| ≤ (2*a)*(ν/N) := by
  have htk : t*k ≤ ν*m := (le_div_iff₀ hk).mp htν
  have hb : t*N ≤ a*(ν*m) := by
    have h1 := mul_le_mul_of_nonneg_left hNk ht
    have ha : 0 ≤ a := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left htk ha
    nlinarith
  apply (frame_survival_ratio_error m k t hm ht hk4 ht4).trans
  apply (div_le_iff₀ hm).2
  apply (mul_le_mul_iff_left₀ hN).mp
  field_simp
  nlinarith

/-- The known-deleted-edge correction contains both the density and batch-size errors. -/
lemma frame_deleted_survival_ratio_rate (m k t N ν a b r μ : ℝ)
    (hm : 0 < m) (hk : 1 ≤ k) (hN : 0 < N) (_hν : 0 ≤ ν)
    (ht : 0 ≤ t) (hk4 : 4*k ≤ m) (ht4 : 4*t ≤ m)
    (htν : t ≤ ν*m/k) (hNk : N ≤ a*k) (hkN : k ≤ b*N)
    (hμ : 0 < μ) (hmean : μ = r*m/N) :
    |m/(m-k-t+1)-1| ≤ 2*b*r/μ + (2*a)*(ν/N) := by
  have hkpos : 0 < k := by linarith
  have htbound : 2*t/m ≤ (2*a)*(ν/N) := by
    have htk := (le_div_iff₀ hkpos).mp htν
    have ha : 0 ≤ a := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hNk ht
    have h2 := mul_le_mul_of_nonneg_left htk ha
    apply (div_le_iff₀ hm).2
    apply (mul_le_mul_iff_left₀ hN).mp
    field_simp
    nlinarith
  have hr : 0 < r := by
    have := (div_pos_iff.mp (hmean ▸ hμ))
    rcases this with h | h
    · exact pos_of_mul_pos_left h.1 hm.le
    · linarith [h.2]
  have hid : 2*b*r/μ = 2*b*N/m := by rw [hmean]; field_simp <;> ring
  rw [hid]
  have hkbound : 2*k/m ≤ 2*b*N/m := by
    exact div_le_div_of_nonneg_right (by linarith) hm.le
  have he := frame_deleted_survival_ratio_error m k t hm hk ht hk4 ht4
  rw [mul_add, add_div] at he
  linarith

/-- Uniform finite estimates imply the claimed first asymptotic error, without
any unmentioned positivity restriction on the batch parameter. -/
theorem frame_survival_ratio_isBigO {ι : Type*} (l : Filter ι)
    (m k t N ν : ι → ℝ) (a : ℝ)
    (h : ∀ᶠ i in l, 0 < m i ∧ 0 < k i ∧ 0 < N i ∧ 0 ≤ ν i ∧
      0 ≤ t i ∧ 4*k i ≤ m i ∧ 4*t i ≤ m i ∧
      t i ≤ ν i*m i/k i ∧ N i ≤ a*k i) :
    Asymptotics.IsBigO l (fun i => (m i-k i+1)/(m i-k i-t i+1)-1)
      (fun i => ν i/N i) := by
  apply Asymptotics.IsBigO.of_bound (2*a)
  filter_upwards [h] with i hi
  rcases hi with ⟨hm,hk,hN,hν,ht,hk4,ht4,htν,hNk⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hν hN.le)] using
    frame_survival_ratio_rate (m i) (k i) (t i) (N i) (ν i) a
      hm hk hN hν ht hk4 ht4 htν hNk

/-- Uniform finite estimates give the additional inverse-density term for a
candidate known to be in the deleted batch. -/
theorem frame_deleted_survival_ratio_isBigO {ι : Type*} (l : Filter ι)
    (m k t N ν μ : ι → ℝ) (a b r : ℝ) (ha : 0 ≤ a) (hbr : 0 ≤ b*r)
    (h : ∀ᶠ i in l, 0 < m i ∧ 1 ≤ k i ∧ 0 < N i ∧ 0 ≤ ν i ∧
      0 ≤ t i ∧ 4*k i ≤ m i ∧ 4*t i ≤ m i ∧
      t i ≤ ν i*m i/k i ∧ N i ≤ a*k i ∧ k i ≤ b*N i ∧
      0 < μ i ∧ μ i = r*m i/N i) :
    Asymptotics.IsBigO l (fun i => m i/(m i-k i-t i+1)-1)
      (fun i => 1/μ i+ν i/N i) := by
  apply Asymptotics.IsBigO.of_bound (2*b*r+2*a)
  filter_upwards [h] with i hi
  rcases hi with ⟨hm,hk,hN,hν,ht,hk4,ht4,htν,hNk,hkN,hμ,hmean⟩
  have he := frame_deleted_survival_ratio_rate (m i) (k i) (t i) (N i) (ν i)
    a b r (μ i) hm hk hN hν ht hk4 ht4 htν hNk hkN hμ hmean
  have hq : 0 ≤ ν i/N i := div_nonneg hν hN.le
  have hp : 0 ≤ 1/μ i := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hp hq)]
  have heq : 2*b*r/μ i = (2*b*r)*(1/μ i) := by ring
  rw [heq] at he
  nlinarith [mul_nonneg (show 0 ≤ 2*b*r by nlinarith) hq,
    mul_nonneg (show 0 ≤ 2*a by linarith) hp]

end LooseHamilton
