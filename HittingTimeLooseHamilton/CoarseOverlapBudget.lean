module

public import HittingTimeLooseHamilton.CoarseOverlapAtoms
public import HittingTimeLooseHamilton.BiasedEntropyBudgetCoarse

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy
variable {r : ℕ}

/-- The elementary role-support estimate does not require sparse markers. -/
lemma coarse_roleSupport_le (D : BiasedRoleInstance r) (hr : 3 ≤ r) :
    D.roleSupport ≤ 2*(D.N : ℝ)*Real.log 2 := by
  have hchoose : ((D.N-2*D.s).choose (D.k-D.s) : ℝ) ≤ (2:ℝ)^(D.N-2*D.s) := by
    by_cases hn : D.N-2*D.s=0
    · simp only [hn, pow_zero]
      exact_mod_cast (show (0:ℕ).choose (D.k-D.s) ≤ 1 by
        cases D.k-D.s <;> simp)
    · exact_mod_cast (Nat.choose_le_two_pow (D.N-2*D.s) (D.k-D.s))
  have hs : D.s ≤ D.N := by have := D.vertex_bookkeeping hr; omega
  have hx : (((D.N-2*D.s).choose (D.k-D.s) : ℝ)*2^(D.s-1)) ≤
      (2:ℝ)^((D.N-2*D.s)+(D.s-1)) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right hchoose (by positivity)
  unfold roleSupport
  by_cases hzero : (((D.N-2*D.s).choose (D.k-D.s) : ℝ)*2^(D.s-1))=0
  · rw [hzero, Real.log_zero]
    positivity
  · have hp : 0<(((D.N-2*D.s).choose (D.k-D.s) : ℝ)*2^(D.s-1)) :=
      lt_of_le_of_ne (by positivity) (Ne.symm hzero)
    have hh := Real.log_le_log hp hx
    rw [Real.log_pow] at hh
    have hn : (((D.N-2*D.s)+(D.s-1):ℕ):ℝ) ≤ 2*(D.N:ℝ) := by
      exact_mod_cast (show D.N-2*D.s+(D.s-1) ≤ 2*D.N by omega)
    exact hh.trans (mul_le_mul_of_nonneg_right hn (Real.log_nonneg (by norm_num)))

@[expose] def coarseOverlapConstant (r : ℕ) (C B C₁ C₂ : ℝ) : ℝ :=
  2*Real.log ((r:ℝ)^2*C+1)+(r:ℝ)*B+2*(r:ℝ)*Real.log 2+
    2*(r:ℝ)*C₁+2*(r:ℝ)*C₂+2*Real.log 2

lemma coarseOverlapConstant_nonneg (r : ℕ) {C B C₁ C₂ : ℝ}
    (hC : 0≤C) (hB : 0≤B) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂) :
    0≤coarseOverlapConstant r C B C₁ C₂ := by
  have hl : 0≤Real.log ((r:ℝ)^2*C+1) := Real.log_nonneg (by nlinarith [mul_nonneg (sq_nonneg (r:ℝ)) hC])
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  unfold coarseOverlapConstant
  positivity

/-- Coarse deficit bound from the actual total cycle entropy. This uses no
partition quasirandomness, no codegree hypothesis, and no sparse-marker limit. -/
lemma coarse_actual_padded_budget (D : BiasedRoleInstance r) (hr : 3 ≤ r)
    (C B C₁ C₂ : ℝ) (hC : 0<C) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hμ : 1≤D.μ)
    (hent : (D.k:ℝ)*Real.log D.μ-B*D.N ≤ entropy D.cycleLaw.mass)
    (hK : D.KahnBounds hr C₁ C₂) :
    averageKahnPaddedDeficit D.ensembleLaw (D.ensembleHost hr)
      (D.ensembleMatchingLaw hr) (D.auxDegree C)+(r*D.k:ℕ)*Real.log 2 ≤
      coarseOverlapConstant r C B C₁ C₂*(D.N:ℝ) := by
  let n : ℝ := (r*D.k:ℕ)
  have h := average_kahn_padded_deficit_coarse D.ensembleLaw
    (D.ensembleHost hr) (D.ensembleMatchingLaw hr) (by omega)
    (D := (D.auxDegree C:ℝ)) hC₁ hK
  have hchain := D.ensemble_entropy_chain hr
  have hrole := D.roleEntropy_le_roleSupport hr
  have hrpos : 0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have havg : (D.k:ℝ)*Real.log D.μ-B*D.N-D.roleSupport ≤
      ∑ i, D.ensembleLaw.mass i*entropy (D.ensembleMatchingLaw hr i).mass := by linarith
  have hmul := mul_le_mul_of_nonneg_left havg hrpos.le
  have hcorr := kahn_correction_eq (show 0<r by omega) (show r*D.k=r*D.k from rfl)
  rw [hcorr] at h
  have hc0 : 0≤(r:ℝ)*(((r:ℝ)-1)*D.k) := by
    have hrR : (3:ℝ)≤r := by exact_mod_cast hr
    exact mul_nonneg hrpos.le (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have haux : (0:ℝ)<D.auxDegree C := by exact_mod_cast D.auxDegree_pos hr C hC
  have hm := D.μ_pos hr
  have hLpos : 0<(r:ℝ)^2*C+1 := by positivity
  have hgap : Real.log (D.auxDegree C)-Real.log D.μ ≤ Real.log ((r:ℝ)^2*C+1) := by
    have hg := Real.log_le_log haux (D.auxDegree_le C hC.le hμ)
    rwa [Real.log_mul hLpos.ne' hm.ne', ← sub_le_iff_le_add] at hg
  have hn0 : 0<n := by dsimp [n]; exact_mod_cast Nat.mul_pos (by omega : 0<r) (D.k_pos hr)
  have hn : n≤2*(D.N:ℝ) := by dsimp [n]; exact_mod_cast D.rk_le_two_N hr
  have hlogn : Real.log n≤2*(D.N:ℝ) := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hl : 0≤Real.log ((r:ℝ)^2*C+1) := Real.log_nonneg (by nlinarith [sq_nonneg (r:ℝ)])
  have ht1 : n*(Real.log (D.auxDegree C)-Real.log D.μ) ≤
      2*(D.N:ℝ)*Real.log ((r:ℝ)^2*C+1) :=
    (mul_le_mul_of_nonneg_left hgap hn0.le).trans (mul_le_mul_of_nonneg_right hn hl)
  have ht3 := mul_le_mul_of_nonneg_left (D.coarse_roleSupport_le hr) hrpos.le
  have ht4 := mul_le_mul_of_nonneg_left hn (mul_nonneg hrpos.le hC₁)
  have ht5 := mul_le_mul_of_nonneg_left hlogn (mul_nonneg hrpos.le hC₂)
  have ht6 := mul_le_mul_of_nonneg_right hn (Real.log_nonneg (show (1:ℝ)≤2 by norm_num))
  change _ ≤ n*Real.log ↑(D.auxDegree C)-(r:ℝ)*
    (∑ i, D.ensembleLaw.mass i*entropy (D.ensembleMatchingLaw hr i).mass)-
    (r:ℝ)*(((r:ℝ)-1)*D.k)+(r:ℝ)*C₁*n+(r:ℝ)*C₂*Real.log n at h
  change _+n*Real.log 2 ≤ _
  have hnk : n=(r:ℝ)*D.k := by dsimp [n]; push_cast; rfl
  simp only [hnk] at h ht1 ht4 ht5 ht6 ⊢
  unfold coarseOverlapConstant
  nlinarith only [h, hmul, hc0, ht1, ht3, ht4, ht5, ht6]

/-- The actual role-averaged incidence collision estimate appearing in the
coarse-overlap proof, with a fixed explicit constant. -/
lemma coarse_actual_incidence_bound (D : BiasedRoleInstance r) (hr : 3 ≤ r)
    (C B C₁ C₂ : ℝ) (hC : 1≤C) (hB : 0≤B) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hμ : 1<D.μ) (hdeg : ∀v, (vertexDegree D.host v:ℝ)≤C*D.μ)
    (hent : (D.k:ℝ)*Real.log D.μ-B*D.N ≤ entropy D.cycleLaw.mass)
    (hK : D.KahnBounds hr C₁ C₂) :
    (∑ i, D.ensembleLaw.mass i * ∑ v, ∑ e : KahnIncident (D.ensembleHost hr i) v,
      ((kahnIncidentLaw (D.ensembleMatchingLaw hr i) v).mass e)^2) ≤
      coarseOverlapConstant r C B C₁ C₂*(D.N:ℝ)/Real.log D.μ := by
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hC0 : 0<C := by linarith
  have hμD : D.μ ≤ (D.auxDegree C:ℝ) := by
    have hh := Nat.le_ceil ((r:ℝ)^2*C*D.μ)
    change D.μ ≤ (⌈(r:ℝ)^2*C*D.μ⌉₊:ℝ)
    have hfactor : 1≤(r:ℝ)^2*C := by nlinarith [sq_nonneg (r:ℝ), mul_le_mul_of_nonneg_left hC (sq_nonneg (r:ℝ))]
    exact (le_mul_of_one_le_left (by linarith : 0≤D.μ) hfactor).trans hh
  have hD2 : 2≤D.auxDegree C := by
    have : (1:ℝ)<D.auxDegree C := hμ.trans_le hμD
    exact_mod_cast (show (1:ℝ)<D.auxDegree C from this)
  have hi := coarse_ensemble_incidence_collision_bound D.ensembleLaw
    (D.ensembleHost hr) (D.ensembleMatchingLaw hr) hD2
    (D.ensemble_degree_le_auxDegree hr C hdeg)
  have hb := D.coarse_actual_padded_budget hr C B C₁ C₂ hC0 hC₁ hC₂ hμ.le hent hK
  have hlog : Real.log D.μ ≤ Real.log (D.auxDegree C) := Real.log_le_log (by linarith) hμD
  have hlpos : 0<Real.log D.μ := Real.log_pos hμ
  have hb0 : 0≤coarseOverlapConstant r C B C₁ C₂*(D.N:ℝ) :=
    mul_nonneg (coarseOverlapConstant_nonneg r hC0.le hB hC₁ hC₂) (Nat.cast_nonneg _)
  exact hi.trans ((div_le_div_of_nonneg_right hb (hlpos.trans_le hlog).le).trans
    (div_le_div_of_nonneg_left hb0 hlpos hlog))

end LooseHamilton.BiasedRoleInstance
