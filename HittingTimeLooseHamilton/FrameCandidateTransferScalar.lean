module

public import HittingTimeLooseHamilton.CandidateNormalizationTransfer

public section

/-! Finite transfer using the combined exact survival and raw-density factor. -/
noncomputable section
namespace LooseHamilton

lemma normalization_normal_transfer (x q α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hq : |q-1| ≤ α/16)
    (hnormal : |x-1| ≤ α/100) : |q*x-1| ≤ α/4 := by
  have hx : |x| ≤ 2 := by
    calc
      |x| = |(x-1)+1| := by congr 1; ring
      _ ≤ |x-1|+|1| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  calc
    |q*x-1| = |(q-1)*x+(x-1)| := by congr 1; ring
    _ ≤ |(q-1)*x|+|x-1| := abs_add_le _ _
    _ = |q-1| * |x|+|x-1| := by rw [abs_mul]
    _ ≤ (α/16)*2+α/100 := add_le_add
      (mul_le_mul hq hx (abs_nonneg _) (by positivity)) hnormal
    _ ≤ α/4 := by linarith

/-- Absolute concentration around a positive center yields a positive count
and the literal relative error used by the normalization identity. -/
lemma positive_relative_of_survival (x z h : ℝ) (hz : 0 < z)
    (hh : h < 1) (hs : |x-z| ≤ h*z) :
    0 < x ∧ |x/z-1| ≤ h := by
  have hb := abs_le.mp hs
  constructor
  · nlinarith
  · rw [show x/z-1 = (x-z)/z by field_simp, abs_div, abs_of_pos hz]
    exact (div_le_iff₀ hz).mpr hs

/-- Perturbation of the normalized count. The middle factor combines exact
hypergeometric survival and the raw-host mean-degree change. -/
lemma candidate_combined_perturbation (XJ XF YJ YF μJ μF z0 z1 b α : ℝ)
    (hXJ : 0 < XJ) (hYJ : 0 < YJ) (hμJ : 0 < μJ)
    (hz0 : 0 < z0) (hz1 : 0 < z1) (hα : 0 < α) (hα1 : α ≤ 1)
    (hcycle : |XF-z0*XJ| ≤ (α/100000)*(z0*XJ))
    (hcompletion : |YF-z1*YJ| ≤ (α/100000)*(z1*YJ))
    (hratio : |(z1/z0)*(μF/μJ)-1| ≤ α/100000) :
    ∃ q : ℝ, |q-1| ≤ α/16 ∧
      candidateNormalizedCount XF YF μF b = q*candidateNormalizedCount XJ YJ μJ b := by
  have h0 : 0 ≤ α/100000 := by positivity
  have hsmall : α/100000 < 1 := by linarith
  have hx := positive_relative_of_survival XF (z0*XJ) (α/100000) (by positivity) hsmall hcycle
  have hy := positive_relative_of_survival YF (z1*YJ) (α/100000) (by positivity) hsmall hcompletion
  let q := (YF/(z1*YJ))*((z1/z0)*(μF/μJ))/(XF/(z0*XJ))
  refine ⟨q, ?_, ?_⟩
  · have hh := normalization_four_factor_error (YF/(z1*YJ))
      ((z1/z0)*(μF/μJ)) 1 (XF/(z0*XJ)) (α/100000) h0 (by linarith)
      hy.2 hratio (by simpa using h0) hx.2
    dsimp [q]
    simpa only [mul_one] using hh.trans (show 16*(α/100000) ≤ α/16 by linarith)
  · rw [candidate_normalized_transfer_identity XJ XF YJ YF μJ μF z0 z1 b
      hXJ.ne' hx.1.ne' hYJ.ne' hμJ.ne' hz0.ne' hz1.ne']
    dsimp [q]
    ring

/-- Abnormality persists under the actual combined normalization factor. -/
theorem candidate_abnormality_combined (XJ XF YJ YF μJ μF z0 z1 b α : ℝ)
    (hXJ : 0 < XJ) (hYJ : 0 < YJ) (hμJ : 0 < μJ)
    (hz0 : 0 < z0) (hz1 : 0 < z1) (hb : 0 ≤ b)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hcycle : |XF-z0*XJ| ≤ (α/100000)*(z0*XJ))
    (hcompletion : |YF-z1*YJ| ≤ (α/100000)*(z1*YJ))
    (hratio : |(z1/z0)*(μF/μJ)-1| ≤ α/100000)
    (habnormal : α < |candidateNormalizedCount XJ YJ μJ b-1|) :
    α/2 < |candidateNormalizedCount XF YF μF b-1| := by
  obtain ⟨q,hq,heq⟩ := candidate_combined_perturbation XJ XF YJ YF μJ μF z0 z1 b α
    hXJ hYJ hμJ hz0 hz1 hα hα1 hcycle hcompletion hratio
  rw [heq]
  exact normalization_abnormal_transfer _ q α (by unfold candidateNormalizedCount; positivity)
    hα hα1 (hq.trans (by linarith)) habnormal

/-- Normality transfers with the candidate-conditioned survival factor. -/
theorem candidate_normality_combined (XJ XF YJ YF μJ μF z0 z1 b α : ℝ)
    (hXJ : 0 < XJ) (hYJ : 0 < YJ) (hμJ : 0 < μJ)
    (hz0 : 0 < z0) (hz1 : 0 < z1) (hα : 0 < α) (hα1 : α ≤ 1)
    (hcycle : |XF-z0*XJ| ≤ (α/100000)*(z0*XJ))
    (hcompletion : |YF-z1*YJ| ≤ (α/100000)*(z1*YJ))
    (hratio : |(z1/z0)*(μF/μJ)-1| ≤ α/100000)
    (hnormal : |candidateNormalizedCount XJ YJ μJ b-1| ≤ α/100) :
    |candidateNormalizedCount XF YF μF b-1| ≤ α/4 := by
  obtain ⟨q,hq,heq⟩ := candidate_combined_perturbation XJ XF YJ YF μJ μF z0 z1 b α
    hXJ hYJ hμJ hz0 hz1 hα hα1 hcycle hcompletion hratio
  rw [heq]
  exact normalization_normal_transfer _ q α hα hα1 hq hnormal

end LooseHamilton
