module

public import HittingTimeLooseHamilton.CandidateNormalizationTransferScalar

public section

/-! Finite transfer of candidate abnormality through deletion. No independence
or relative-error assertion is hidden in the normalized conclusion. -/
noncomputable section
namespace LooseHamilton

/-- Completion count divided by its directed-candidate benchmark. -/
@[expose] def candidateNormalizedCount (X Y μ b : ℝ) : ℝ := Y/(X/(b*μ))

/-- The exact quotient of normalized completion counts is the product of the
completion survival, survival-ratio and density factors, divided by cycle survival. -/
lemma candidate_normalized_transfer_identity (XJ XF YJ YF μJ μF z0 z1 b : ℝ)
    (hXJ : XJ≠0) (hXF : XF≠0) (hYJ : YJ≠0) (hμJ : μJ≠0)
    (hz0 : z0≠0) (hz1 : z1≠0) :
    candidateNormalizedCount XF YF μF b =
      ((YF/(z1*YJ))*(z1/z0)*(μF/μJ)/(XF/(z0*XJ))) *
        candidateNormalizedCount XJ YJ μJ b := by
  unfold candidateNormalizedCount
  simp only [div_div,div_eq_mul_inv,mul_inv_rev,inv_inv]
  field_simp
  <;> ring

/-- Stable non-tiny completions retain their abnormality. The scale factor b is
(r−1)^2 in the mixed-cycle application; z0 and z1 are the exact k and k−1
survival probabilities. -/
theorem candidate_abnormality_survives
    (XJ XF YJ YF μJ μF z0 z1 b α h : ℝ)
    (hXJ : 0<XJ) (hXF : 0<XF) (hYJ : 0<YJ) (hμJ : 0<μJ)
    (hz0 : 0<z0) (hz1 : 0<z1) (hb : 0≤b)
    (hα : 0<α) (hα1 : α≤1) (h0 : 0≤h) (hsmall : h≤α/100000)
    (hcycle : |XF/(z0*XJ)-1|≤h)
    (hcompletion : |YF/(z1*YJ)-1|≤h)
    (hratio : |z1/z0-1|≤h)
    (hdensity : |μF/μJ-1|≤h)
    (habnormal : α< |candidateNormalizedCount XJ YJ μJ b-1|) :
    α/2< |candidateNormalizedCount XF YF μF b-1| := by
  let q := (YF/(z1*YJ))*(z1/z0)*(μF/μJ)/(XF/(z0*XJ))
  have hq : |q-1|≤α/8 := by
    have hh := normalization_four_factor_error (YF/(z1*YJ)) (z1/z0)
      (μF/μJ) (XF/(z0*XJ)) h h0 (by linarith)
      hcompletion hratio hdensity hcycle
    dsimp [q]
    linarith
  have hx : 0≤candidateNormalizedCount XJ YJ μJ b := by
    unfold candidateNormalizedCount
    positivity
  rw [candidate_normalized_transfer_identity XJ XF YJ YF μJ μF z0 z1 b
    hXJ.ne' hXF.ne' hYJ.ne' hμJ.ne' hz0.ne' hz1.ne']
  exact normalization_abnormal_transfer _ q α hx hα hα1 hq habnormal

/-- Tiny completions require no relative concentration estimate: deletion
monotonicity and a bound relative to the surviving benchmark suffice. -/
theorem tiny_candidate_abnormality_survives
    (XJ XF YJ YF μF z0 b α : ℝ)
    (hXJ : 0<XJ) (hXF : 0<XF) (hz0 : 0<z0) (hμF : 0<μF)
    (hb : 0<b) (hα : 0<α) (hα1 : α≤1)
    (hmono : YF≤YJ) (htiny : YJ≤z0*XJ/(8*b*μF))
    (hcycle : z0*XJ/2≤XF) :
    α/2< |candidateNormalizedCount XF YF μF b-1| := by
  have hden : 0<b*μF := mul_pos hb hμF
  have hY : YF*(b*μF)≤XF/4 := by
    have hy := (le_div_iff₀ (by positivity : 0<8*b*μF)).mp htiny
    have hm := mul_le_mul_of_nonneg_right hmono hden.le
    nlinarith
  have hn : candidateNormalizedCount XF YF μF b≤1/4 := by
    unfold candidateNormalizedCount
    rw [div_div_eq_mul_div]
    exact (div_le_iff₀ hXF).2 (by nlinarith)
  have ha : 3/4≤|candidateNormalizedCount XF YF μF b-1| := by
    have hh := neg_le_abs (candidateNormalizedCount XF YF μF b-1)
    linarith
  linarith

end LooseHamilton
