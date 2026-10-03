module

public import HittingTimeLooseHamilton.BiasedEntropyRates
public import HittingTimeLooseHamilton.BiasedRoleAveraging

public section

noncomputable section
namespace FiniteEntropy

lemma clone_radical_budget {v L A N E : ℝ}
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hL0 : 0 ≤ L) (hv : v ≤ A * N) (hL : L ≤ A * N * E) :
    Real.sqrt (2 * v * L) ≤ 2 * A * N * Real.sqrt E := by
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ 2 * (A * N) * (A * N * E) := by gcongr
    _ ≤ 4 * (A * N) * (A * N * E) := by gcongr; norm_num
    _ = _ := by simp only [mul_pow, Real.sq_sqrt hE]; ring

lemma compatibility_radical_budget {m D B A N mu E : ℝ}
    (hA : 1 ≤ A) (hN : 0 ≤ N) (hmu : 0 ≤ mu) (hE : 0 ≤ E)
    (hD0 : 0 ≤ D) (hB0 : 0 ≤ B)
    (hm : m ≤ A * N * mu) (hD : D ≤ A * mu) (hB : B ≤ A * N * E) :
    Real.sqrt (4 * m * D * B) ≤ 2 * A^2 * N * mu * Real.sqrt E := by
  have hA0 : 0 ≤ A := by linarith
  have hA34 : A^3 ≤ A^4 := by
    have h := mul_le_mul_of_nonneg_left hA (pow_nonneg hA0 3)
    nlinarith only [h]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ 4 * (A * N * mu) * (A * mu) * (A * N * E) := by gcongr
    _ = 4 * A^3 * N^2 * mu^2 * E := by ring
    _ ≤ 4 * A^4 * N^2 * mu^2 * E := by gcongr
    _ = _ := by simp only [mul_pow, Real.sq_sqrt hE]; ring

/-- Explicit scalar accounting for the final projection estimate. The inputs
are the two independently proved L1 bounds and upper budgets on their genuine
entropy, degree, and role quantities. -/
theorem entropy_projection_budget {x y dev r v L t D B m lam A N mu E : ℝ}
    (hA : 1 ≤ A) (hr : 1 ≤ r) (hN : 0 < N) (hmu : 0 < mu)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hv0 : 0 ≤ v) (hL0 : 0 ≤ L) (ht0 : 0 ≤ t)
    (hD0 : 0 ≤ D) (hB0 : 0 ≤ B)
    (hv : v ≤ A * N) (hL : L ≤ A * N * E) (ht : t ≤ A * E)
    (hD : D ≤ A * mu) (hB : B ≤ A * N * E) (hm : m ≤ A * N * mu)
    (hlam : mu / A ≤ lam)
    (hx : x ≤ (2 / r) * Real.sqrt (2 * v * L) + (v / r) * t)
    (hy : y ≤ (r * (r - 1) / lam) * Real.sqrt (4 * m * D * B))
    (hdev : dev ≤ x + y) :
    dev ≤ (4 * A + A^2 + 2 * r * (r - 1) * A^3) * N * Real.sqrt E := by
  have hApos : 0 < A := by linarith
  have hrpos : 0 < r := by linarith
  have hlampos : 0 < lam := (div_pos hmu hApos).trans_le hlam
  have hrminus : 0 ≤ r - 1 := by linarith
  have hroot := clone_radical_budget hApos.le hN.le hE0 hL0 hv hL
  have hcompat := compatibility_radical_budget hA hN.le hmu.le hE0 hD0 hB0 hm hD hB
  have hsqrt : E ≤ Real.sqrt E := by
    have hs := Real.sq_sqrt hE0
    have hs0 := Real.sqrt_nonneg E
    nlinarith
  have htwo : 2 / r ≤ 2 := (div_le_iff₀ hrpos).2 (by linarith)
  have hvdiv : v / r ≤ v := (div_le_iff₀ hrpos).2 (by nlinarith)
  have hfirst : (2 / r) * Real.sqrt (2 * v * L) ≤ 4 * A * N * Real.sqrt E := by
    calc
      _ ≤ 2 * (2 * A * N * Real.sqrt E) :=
        mul_le_mul htwo hroot (Real.sqrt_nonneg _) (by norm_num)
      _ = _ := by ring
  have hsecond : (v / r) * t ≤ A^2 * N * Real.sqrt E := by
    calc
      _ ≤ v * t := mul_le_mul_of_nonneg_right hvdiv ht0
      _ ≤ (A * N) * (A * E) := mul_le_mul hv ht ht0 (by positivity)
      _ = A^2 * N * E := by ring
      _ ≤ A^2 * N * Real.sqrt E := mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hratio : mu / lam ≤ A := by
    apply (div_le_iff₀ hlampos).2
    have h := (div_le_iff₀ hApos).1 hlam
    nlinarith only [h]
  have hthird : (r * (r - 1) / lam) * Real.sqrt (4 * m * D * B) ≤
      2 * r * (r - 1) * A^3 * N * Real.sqrt E := by
    calc
      _ ≤ (r * (r - 1) / lam) * (2 * A^2 * N * mu * Real.sqrt E) :=
        mul_le_mul_of_nonneg_left hcompat (by positivity)
      _ = (2 * r * (r - 1) * A^2 * N * Real.sqrt E) * (mu / lam) := by ring
      _ ≤ (2 * r * (r - 1) * A^2 * N * Real.sqrt E) * A :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  nlinarith only [hx, hy, hdev, hfirst, hsecond, hthird]

end FiniteEntropy
