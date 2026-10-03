module

public import HittingTimeLooseHamilton.FrameSurvivalConcentrationCenter
public import HittingTimeLooseHamilton.FrameConcentrationScales

public section

/-! Uniform asymptotic concentration at the prescribed small tolerance.
The threshold is chosen before the sampling host, labelled family, support
map, density, and batch parameters. -/
noncomputable section
namespace LooseHamilton.IndexedSurvival
open Finset FrameSurvival CandidateLogSurvival Filter FrameScales
universe u v

/-- Entropy-scale overlap control gives the exact power `L₂^(-24/25)`.
Variable support sizes and retained boundary edges contribute only an absorbed
bias; distinct labels with the same support remain distinct. -/
theorem eventually_interval_concentration (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ N in atTop, ∀ (α : Type u) (ι : Type v) [DecidableEq α] [DecidableEq ι],
    ∀ (H : Finset α) (F : Finset ι) (support : ι → Finset α)
      (k d τ : ℕ) (μ : ℝ),
    0 < H.card → 0 < k → 4*k ≤ H.card → 4*τ ≤ H.card → F.Nonempty →
    (∀ i ∈ F, support i ⊆ H) →
    (∀ i ∈ F, k-d ≤ (support i).card ∧ (support i).card ≤ k) →
    L1 N/2 ≤ μ → (τ:ℝ)*k/H.card ≤ nu N →
    (d:ℝ)*τ/H.card ≤ A*(nu N/(N:ℝ)) →
    uniformOverlap F support / k ≤ B/Real.log μ →
    ∀ hτ : τ ≤ H.card,
    (hostBatchLaw hτ).event (fun T =>
      (alpha N/100000) * (CandidateLogSurvival.zeta H.card k τ * F.card) <
        |(count F support T.val:ℝ) - CandidateLogSurvival.zeta H.card k τ * F.card|) ≤
      (64*B) * (L2 N)^(-24/25:ℝ) / (alpha N/100000)^2 := by
  filter_upwards [eventually_boundary_bias_alpha A hA,
    eventually_survival_variance A B hA hB, eventual_range]
    with N hb hv hR α ι instα instι H F support k d τ μ hm hk hk4 ht4 hne hsub hsize hμ hx hy hO hτ
  have hh : 0 < alpha N/100000 := div_pos hR.2.2.2.1 (by norm_num)
  have hquarter : 0 < (alpha N/100000)/4 := by positivity
  have hmean : 0 ≤ CandidateLogSurvival.zeta H.card k τ * (F.card:ℝ) :=
    mul_nonneg (zeta_pos (by omega)).le (Nat.cast_nonneg _)
  have hconc := interval_relative_concentration hm hk hk4 ht4 F support hne hsub hsize hquarter
  have hbias := hb ((d:ℝ)*τ/H.card) (by positivity) hy
  have hbias' : Real.exp (2*(d:ℝ)*τ/H.card)-1 ≤ (alpha N/100000)/4 ∧
      Real.exp (2*(d:ℝ)*τ/H.card) ≤ 2 := by
    convert hbias using 1 <;> congr 2 <;> ring
  have habs := (hostBatchLaw hτ).absorb_relative_bias
    (fun T => (count F support T.val:ℝ)) hmean hh hbias'.1 hbias'.2 hconc
  have hvar := hv μ H.card k τ d (uniformOverlap F support) (alpha N/100000)
    hμ (by exact_mod_cast hm) (by exact_mod_cast hk) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hx hy hO hh
  have hid :
      (Real.exp (4*(d:ℝ)*τ/H.card)*(Real.exp (4*(τ:ℝ)*k/H.card)-1)*
        uniformOverlap F support / k) / (alpha N/100000)^2 =
      Real.exp (4*(d:ℝ)*τ/H.card)*(Real.exp (4*(τ:ℝ)*k/H.card)-1)*
        (uniformOverlap F support / k) / (alpha N/100000)^2 := by ring
  calc
    _ ≤ 16 * Real.exp (4*(d:ℝ)*τ/H.card)*(Real.exp (4*(τ:ℝ)*k/H.card)-1)*
        (uniformOverlap F support / k) / (alpha N/100000)^2 := by
      convert habs using 1 <;> ring
    _ ≤ 16*((4*B)*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2) := by
      convert mul_le_mul_of_nonneg_left hvar (by norm_num : (0:ℝ)≤16) using 1 <;> ring
    _ = _ := by ring

end LooseHamilton.IndexedSurvival
