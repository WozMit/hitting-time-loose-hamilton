module

public import HittingTimeLooseHamilton.BiasedEntropyBudgetRate
public import HittingTimeLooseHamilton.BiasedEntropyMeanConstants
public import HittingTimeLooseHamilton.BiasedEntropyRateAbsorption

public section

/-! Finite absorption into the six-term error of Theorem 6.1. -/
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy

/-- One fixed constant bounds all three actual entropy deficits by N times the
printed error, in the eventual finite range of the theorem. -/
theorem finite_entropy_deficit_rate (r : ℕ) (hr : 3≤r) (C : ℝ) (hC : 0<C)
    (C₁ C₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂) :
    ∃ B : ℝ, 0<B ∧ ∀ (D : BiasedRoleInstance r) (ξ δ : ℝ),
      1≤D.μ → D.s<D.k → 3*D.s≤D.N → 0≤ξ → ξ≤1 →
      (∀v,(vertexDegree D.host v:ℝ)≤C*D.μ) → D.partitionBound δ →
      D.entropyBound ξ → D.KahnBounds hr C₁ C₂ → D.η<1 →
      D.cloneCollisionRate C<1 →
      1/Real.log (1/D.cloneCollisionRate C)≤2/Real.log (1/D.η) →
      1≤Real.log (D.N:ℝ) →
      D.entropyDeficit hr ≤ B*(D.N:ℝ)*biasedRoleError r D.N D.s ξ δ D.η := by
  obtain ⟨A,hA,hfinite⟩ := actual_entropy_deficit_bound r hr
  let L := 1+Real.log (r:ℝ)/Real.log 2
  let T := 4*A+cloneRelativeConstant r C+1+
    C₁*collisionBudgetConstant r C C₁ C₂+C₂*L
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hrel := cloneRelativeConstant_pos hr C hC.le
  have hcol := collisionBudgetConstant_nonneg r hC hC₁ hC₂
  have hlogr : 0≤Real.log (r:ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0≤L := by dsimp [L]; positivity
  have hT : 0≤T := by dsimp [T]; positivity
  refine ⟨(r:ℝ)*T+1, by positivity, ?_⟩
  intro D ξ δ hμ hsk hsN hξ0 hξ1 hdeg hpart hent hK hη hζ hlog hlogN
  let E := biasedRoleError r D.N D.s ξ δ D.η
  have hterms := D.error_term_bounds hr hξ0 hpart hη
  have hE : 0≤E := hterms.1
  have hN : (0:ℝ)<D.N := Nat.cast_pos.mpr D.N_pos
  have hδ := D.partitionBound_nonneg hr hpart
  have hkN : (D.k:ℝ)≤D.N := by exact_mod_cast D.k_le_N hr
  have hN2 : (2:ℝ)≤D.N := by
    have hn2 : 2≤D.N := by
      by_contra h
      have he : D.N=1 := by have := D.N_pos; omega
      simp only [he,Nat.cast_one,Real.log_one] at hlogN
      linarith
    exact_mod_cast hn2
  have hround : A*((D.s:ℝ)+Real.log ((D.N:ℝ)+1)+1)≤4*A*(D.N:ℝ)*E := by
    have hh := mul_le_mul_of_nonneg_left
      (error_controls_rounding hr D hξ0 hpart hη hlogN) hA
    dsimp [E]
    nlinarith only [hh]
  have hmean : (D.k:ℝ)*cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N) ≤
      cloneRelativeConstant r C*(D.N:ℝ)*E := by
    have ht : δ+(D.s:ℝ)/D.N≤E := hterms.2.2.2.2.2.2.2
    have ht0 : 0≤δ+(D.s:ℝ)/D.N := by positivity
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul hkN ht ht0 hN.le) hrel.le
    nlinarith only [hh]
  have hxi : ξ*(D.N:ℝ)≤(D.N:ℝ)*E := by
    have hh := mul_le_mul_of_nonneg_right hterms.2.1 hN.le
    nlinarith only [hh]
  have hcoll : C₁*D.meanCollision hr≤
      C₁*collisionBudgetConstant r C C₁ C₂*(D.N:ℝ)*E := by
    have hh := mul_le_mul_of_nonneg_left
      (D.actual_collision_budget_rate hr C ξ δ C₁ C₂ hC hC₁ hC₂ hμ hsk hξ0 hξ1
        hdeg hpart hent hK hη hζ hlog) hC₁
    nlinarith only [hh]
  have hlogNE : Real.log (D.N:ℝ)≤(D.N:ℝ)*E := by
    have hh := (div_le_iff₀ hN).mp hterms.2.2.2.2.2.2.1
    nlinarith only [hh]
  have hlogs : C₂*Real.log (r*D.k:ℕ)≤C₂*L*(D.N:ℝ)*E := by
    have hh := log_uniformity_size_le (r := (r:ℝ)) (k := (D.k:ℝ)) (N := (D.N:ℝ))
      (by linarith) (Nat.cast_pos.mpr (D.k_pos hr)) hN2 hkN
    have hh' : Real.log (r*D.k:ℕ)≤L*((D.N:ℝ)*E) := by
      rw [Nat.cast_mul]
      exact hh.trans (mul_le_mul_of_nonneg_left hlogNE hL)
    have hfinal := mul_le_mul_of_nonneg_left hh' hC₂
    nlinarith only [hfinal]
  have hstart := hfinite D C δ ξ C₁ C₂ hC.le hμ hsk hsN hdeg hpart hent hK
  have hsum : A*((D.s:ℝ)+Real.log ((D.N:ℝ)+1)+1)+
      (D.k:ℝ)*cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N)+ξ*D.N+
      C₁*D.meanCollision hr+C₂*Real.log (r*D.k:ℕ) ≤ T*(D.N:ℝ)*E := by
    have hh := add_le_add (add_le_add (add_le_add (add_le_add hround hmean) hxi) hcoll) hlogs
    convert hh using 1
    dsimp [T]
    ring
  have hfinal := hstart.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg r))
  have hNE : 0≤(D.N:ℝ)*E := mul_nonneg hN.le hE
  dsimp [E] at hfinal hNE ⊢
  nlinarith only [hfinal,hNE]

end LooseHamilton.BiasedRoleInstance
