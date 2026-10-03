module

public import HittingTimeLooseHamilton.KahnEntropy

public section

/-! Quantitative finite algebra for transporting a candidate's normalized count. -/
noncomputable section
namespace LooseHamilton

lemma normalization_product_error (a b u v : ℝ)
    (ha : |a-1|≤u) (hb : |b-1|≤v) (hu : u≤1) :
    |a*b-1|≤2*v+u := by
  have habs : |a|≤2 := by
    calc
      |a| = |(a-1)+1| := by congr 1; ring
      _ ≤ |a-1|+|1| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  calc
    |a*b-1| = |a*(b-1)+(a-1)| := by congr 1; ring
    _ ≤ |a*(b-1)|+|a-1| := abs_add_le _ _
    _ = |a| *|b-1|+|a-1| := by rw [abs_mul]
    _ ≤ 2*v+u := add_le_add (mul_le_mul habs hb (abs_nonneg _) (by norm_num)) ha

/-- Three numerator factors and one denominator factor with small errors. -/
lemma normalization_four_factor_error (a b c d h : ℝ)
    (h0 : 0≤h) (hsmall : h≤1/10)
    (ha : |a-1|≤h) (hb : |b-1|≤h) (hc : |c-1|≤h) (hd : |d-1|≤h) :
    |a*b*c/d-1|≤16*h := by
  have hdI := abs_le.mp hd
  have hdpos : 0<d := by linarith
  have hab := normalization_product_error a b h h ha hb (by linarith)
  have habc := normalization_product_error (a*b) c (3*h) h (by linarith) hc (by linarith)
  have hnum : |a*b*c-d|≤6*h := by
    calc
      |a*b*c-d| = |(a*b*c-1)-(d-1)| := by congr 1; ring
      _ ≤ |a*b*c-1|+|d-1| := abs_sub _ _
      _ ≤ 6*h := by linarith
  have he : a*b*c/d-1=(a*b*c-d)/d := by field_simp
  rw [he,abs_div,abs_of_pos hdpos]
  apply (div_le_iff₀ hdpos).2
  have hh : 0≤h*(d-1/2) := mul_nonneg h0 (by linarith)
  nlinarith

/-- A nonnegative value abnormal at α cannot become normal at α/2 under
an α/8 multiplicative perturbation. -/
lemma normalization_abnormal_transfer (x q α : ℝ)
    (hx : 0≤x) (hα : 0<α) (hα1 : α≤1)
    (hq : |q-1|≤α/8) (habnormal : α< |x-1|) :
    α/2< |q*x-1| := by
  have hqi := abs_le.mp hq
  have hqp : 0<q := by linarith
  by_contra hh
  have hh' := abs_le.mp (le_of_not_gt hh)
  have hxbound : x≤2 := by
    have hp := mul_le_mul_of_nonneg_right hqi.1 hx
    nlinarith
  have hclose : |q*x-x|≤α/4 := by
    have he : q*x-x=(q-1)*x := by ring
    rw [he,abs_mul,abs_of_nonneg hx]
    calc
      |q-1| *x ≤ (α/8)*2 := mul_le_mul hq hxbound hx (by positivity)
      _ = α/4 := by ring
  have ht : |x-1|≤|x-q*x|+|q*x-1| := by
    convert abs_add_le (x-q*x) (q*x-1) using 1 <;> ring
  rw [abs_sub_comm x (q*x)] at ht
  linarith

end LooseHamilton
