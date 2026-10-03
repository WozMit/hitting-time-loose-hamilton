module

public import HittingTimeLooseHamilton.BiasedEntropyBudgetCoarse
public import HittingTimeLooseHamilton.BiasedEntropyRates

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy
variable {r : ℕ}

@[expose] def collisionBudgetConstant (r : ℕ) (C C₁ C₂ : ℝ) : ℝ :=
  2*((r.choose 2:ℝ)/C)^(1/(2*((r:ℝ)-1)))+
    4*(coarseDeficitConstant r C C₁ C₂+2*Real.log 2)

lemma collisionBudgetConstant_nonneg (r : ℕ) {C C₁ C₂ : ℝ}
    (hC : 0<C) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂) : 0≤collisionBudgetConstant r C C₁ C₂ := by
  have ha := coarseDeficitConstant_nonneg r hC.le hC₁ hC₂
  have hp : 0≤((r.choose 2:ℝ)/C)^(1/(2*((r:ℝ)-1))) :=
    Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hC.le) _
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  unfold collisionBudgetConstant
  positivity

/-- Finite absorption of the actual collision correction into the exact error
printed in Theorem 6.1. All constants depend only on fixed r,C and Kahn constants. -/
lemma actual_collision_budget_rate (D : BiasedRoleInstance r) (hr : 3≤r)
    (C ξ δ C₁ C₂ : ℝ) (hC : 0<C) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hμ : 1≤D.μ) (hsk : D.s<D.k) (hξ0 : 0≤ξ) (hξ1 : ξ≤1)
    (hdeg : ∀v,(vertexDegree D.host v:ℝ)≤C*D.μ)
    (hpart : D.partitionBound δ) (hent : D.entropyBound ξ) (hK : D.KahnBounds hr C₁ C₂)
    (hη : D.η<1) (hζ : D.cloneCollisionRate C<1)
    (hlog : 1/Real.log (1/D.cloneCollisionRate C)≤2/Real.log (1/D.η)) :
    D.meanCollision hr ≤ collisionBudgetConstant r C C₁ C₂*(D.N:ℝ)*
      biasedRoleError r D.N D.s ξ δ D.η := by
  let A := coarseDeficitConstant r C C₁ C₂
  let α : ℝ := 1/(2*((r:ℝ)-1))
  let K : ℝ := (r.choose 2:ℝ)/C
  let N : ℝ := D.N
  let n : ℝ := (r*D.k:ℕ)
  let E := biasedRoleError r D.N D.s ξ δ D.η
  have hA : 0≤A := coarseDeficitConstant_nonneg r hC.le hC₁ hC₂
  have hN : 0≤N := Nat.cast_nonneg _
  have hn : n≤2*N := by dsimp [n,N]; exact_mod_cast D.rk_le_two_N hr
  have hn0 : 0≤n := Nat.cast_nonneg _
  have hα : 0≤α := by
    have : (3:ℝ)≤r := by exact_mod_cast hr
    dsimp [α]
    exact div_nonneg zero_le_one (by linarith)
  have hK0 : 0≤K := div_nonneg (Nat.cast_nonneg _) hC.le
  have hζ0 := D.cloneCollisionRate_pos hr C hC
  have hη0 := D.η_pos hr
  have hzlog : 0<Real.log (1/D.cloneCollisionRate C) :=
    Real.log_pos ((lt_div_iff₀ hζ0).mpr (by simpa using hζ))
  have helog : 0<Real.log (1/D.η) :=
    Real.log_pos ((lt_div_iff₀ hη0).mpr (by simpa using hη))
  have hterms := D.error_term_bounds hr hξ0 hpart hη
  have hpE : D.η^α≤E := hterms.2.2.2.2.1
  have hiE : 1/Real.log (1/D.η)≤E := hterms.2.2.2.2.2.1
  have hp := comparable_rpow_bound hη0.le hζ0.le hK0 hα (D.cloneCollisionRate_le hr C hC)
  have hp0 : 0≤K^α := Real.rpow_nonneg hK0 _
  have hzpow0 : 0≤(D.cloneCollisionRate C)^α := Real.rpow_nonneg hζ0.le _
  have hfirst : n*(D.cloneCollisionRate C)^α≤2*K^α*N*E := by
    calc
      _ ≤ 2*N*(D.cloneCollisionRate C)^α := mul_le_mul_of_nonneg_right hn hzpow0
      _ ≤ 2*N*(K^α*D.η^α) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ 2*N*(K^α*E) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpE hp0) (by positivity)
      _ = _ := by ring
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hB : 0≤A+2*Real.log 2 := by positivity
  have hnum : A*N+n*Real.log 2≤(A+2*Real.log 2)*N := by
    have := mul_le_mul_of_nonneg_right hn hlog2
    nlinarith
  have hsecond : 2*(A*N+n*Real.log 2)/Real.log (1/D.cloneCollisionRate C) ≤
      4*(A+2*Real.log 2)*N*E := by
    calc
      _ = 2*(A*N+n*Real.log 2)*(1/Real.log (1/D.cloneCollisionRate C)) := by ring
      _ ≤ 2*((A+2*Real.log 2)*N)*(1/Real.log (1/D.cloneCollisionRate C)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg zero_le_one hzlog.le)
      _ ≤ 2*((A+2*Real.log 2)*N)*(2/Real.log (1/D.η)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 4*(A+2*Real.log 2)*N*(1/Real.log (1/D.η)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hiE (by positivity)
  have hbudget := D.actual_padded_deficit_coarse hr C ξ C₁ C₂ hC hC₁ hC₂ hμ hsk hξ1 hent hK
  have hcollision := kahn_role_collision_budget D.ensembleLaw (D.ensembleHost hr)
    (D.ensembleMatchingLaw hr) (Nat.mul_pos (by omega) (D.k_pos hr))
    (D.auxDegree_pos hr C hC) (by omega) (D.ensemble_degree_le_auxDegree hr C hdeg)
    D.clonePairBound (D.ensemble_pair_bound hr) hζ0 hζ hbudget
  change D.meanCollision hr ≤ n*(D.cloneCollisionRate C)^α+
    2*(A*N+n*Real.log 2)/Real.log (1/D.cloneCollisionRate C) at hcollision
  change D.meanCollision hr ≤ (2*K^α+4*(A+2*Real.log 2))*N*E
  nlinarith

end LooseHamilton.BiasedRoleInstance
