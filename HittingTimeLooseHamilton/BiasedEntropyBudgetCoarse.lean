module

public import HittingTimeLooseHamilton.BiasedEntropyBudgetFinite
public import HittingTimeLooseHamilton.BiasedEntropyDegree
public import HittingTimeLooseHamilton.BiasedRoleErrorBounds

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy
variable {r : ℕ}

@[expose] def coarseDeficitConstant (r : ℕ) (C C₁ C₂ : ℝ) : ℝ :=
  2*Real.log ((r:ℝ)^2*C+1)+(r:ℝ)+2*(r:ℝ)*Real.log 2+2*(r:ℝ)*C₁+2*(r:ℝ)*C₂

lemma coarseDeficitConstant_nonneg (r : ℕ) {C C₁ C₂ : ℝ}
    (hC : 0≤C) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂) : 0≤coarseDeficitConstant r C C₁ C₂ := by
  have hl : 0≤Real.log ((r:ℝ)^2*C+1) := Real.log_nonneg (by nlinarith [sq_nonneg (r:ℝ)])
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  unfold coarseDeficitConstant
  positivity

lemma log_auxDegree_gap (D : BiasedRoleInstance r) (hr : 3≤r) (C : ℝ) (hC : 0<C)
    (hμ : 1≤D.μ) :
    Real.log (D.auxDegree C)-Real.log (((r:ℝ)-1)*D.μ) ≤ Real.log ((r:ℝ)^2*C+1) := by
  have haux : (0:ℝ)<D.auxDegree C := by exact_mod_cast D.auxDegree_pos hr C hC
  have hm := D.μ_pos hr
  have hK : 0<(r:ℝ)^2*C+1 := by nlinarith [sq_nonneg (r:ℝ)]
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hlog := Real.log_le_log haux (D.auxDegree_le C hC.le hμ)
  rw [Real.log_mul hK.ne' hm.ne'] at hlog
  rw [Real.log_mul (by linarith : (r:ℝ)-1≠0) hm.ne']
  have hnon : 0≤Real.log ((r:ℝ)-1) := Real.log_nonneg (by linarith)
  linarith

/-- A uniform O(N) bound for the averaged padded deficit, proved using only a
single total entropy lower bound and coarse Kahn control. -/
lemma actual_padded_deficit_coarse (D : BiasedRoleInstance r) (hr : 3≤r)
    (C ξ C₁ C₂ : ℝ) (hC : 0<C) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hμ : 1≤D.μ) (hsk : D.s<D.k) (hξ : ξ≤1)
    (hent : D.entropyBound ξ) (hK : D.KahnBounds hr C₁ C₂) :
    averageKahnPaddedDeficit D.ensembleLaw (D.ensembleHost hr) (D.ensembleMatchingLaw hr)
      (D.auxDegree C) ≤ coarseDeficitConstant r C C₁ C₂*(D.N:ℝ) := by
  let n : ℝ := (r*D.k:ℕ)
  have h := kahn_role_padded_budget D.ensembleLaw (D.ensembleHost hr) (D.ensembleMatchingLaw hr)
    (by omega) (D := (D.auxDegree C:ℝ)) hC₁ hK (D.ensemble_entropy_chain hr)
    (D.roleEntropy_le_roleSupport hr) hent
  have hcorr := kahn_correction_eq (show 0<r by omega) (show r*D.k=r*D.k from rfl)
  rw [hcorr] at h
  have heq : n*Real.log (D.auxDegree C)-(r:ℝ)*
      ((D.k:ℝ)*Real.log (((r:ℝ)-1)*D.μ)-((r:ℝ)-1)*D.k-ξ*D.N-D.roleSupport)-
      (r:ℝ)*(((r:ℝ)-1)*D.k)+(r:ℝ)*C₁*n+(r:ℝ)*C₂*Real.log n =
      n*(Real.log (D.auxDegree C)-Real.log (((r:ℝ)-1)*D.μ))+
      (r:ℝ)*ξ*D.N+(r:ℝ)*D.roleSupport+(r:ℝ)*C₁*n+(r:ℝ)*C₂*Real.log n := by
    dsimp [n]
    push_cast
    ring
  change _ ≤ n*Real.log (D.auxDegree C)-(r:ℝ)*
      ((D.k:ℝ)*Real.log (((r:ℝ)-1)*D.μ)-((r:ℝ)-1)*D.k-ξ*D.N-D.roleSupport)-
      (r:ℝ)*(((r:ℝ)-1)*D.k)+(r:ℝ)*C₁*n+(r:ℝ)*C₂*Real.log n at h
  rw [heq] at h
  have hn0 : 0<n := by dsimp [n]; exact_mod_cast Nat.mul_pos (by omega : 0<r) (D.k_pos hr)
  have hn : n≤2*(D.N:ℝ) := by dsimp [n]; exact_mod_cast D.rk_le_two_N hr
  have hlogn : Real.log n≤2*(D.N:ℝ) := by
    have hh := Real.log_le_sub_one_of_pos hn0
    linarith
  have hloggap := D.log_auxDegree_gap hr C hC hμ
  have hl : 0≤Real.log ((r:ℝ)^2*C+1) := Real.log_nonneg (by nlinarith [sq_nonneg (r:ℝ)])
  have hterm1 : n*(Real.log (D.auxDegree C)-Real.log (((r:ℝ)-1)*D.μ)) ≤
      2*(D.N:ℝ)*Real.log ((r:ℝ)^2*C+1) :=
    (mul_le_mul_of_nonneg_left hloggap hn0.le).trans (mul_le_mul_of_nonneg_right hn hl)
  have hterm2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξ
    (Nat.cast_nonneg r : (0:ℝ)≤r)) (Nat.cast_nonneg D.N : (0:ℝ)≤D.N)
  have hterm3 := mul_le_mul_of_nonneg_left (D.roleSupport_coarse hr hsk)
    (Nat.cast_nonneg r : (0:ℝ)≤r)
  have hterm4 := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (Nat.cast_nonneg r : (0:ℝ)≤r) hC₁)
  have hterm5 := mul_le_mul_of_nonneg_left hlogn
    (mul_nonneg (Nat.cast_nonneg r : (0:ℝ)≤r) hC₂)
  unfold coarseDeficitConstant
  nlinarith

end LooseHamilton.BiasedRoleInstance
