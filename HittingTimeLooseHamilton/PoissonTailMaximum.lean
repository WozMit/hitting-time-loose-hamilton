module

public import HittingTimeLooseHamilton.PoissonTailExponential
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

noncomputable section
namespace LooseHamilton

/-- A uniform logarithmic degree constant; it does not depend on the bounded
additive offsets in the terminal model. -/
@[expose] def poissonMaximumConstant (A : ℝ) : ℝ := 2 * Real.exp 1 + |A| + 5

/-- Finite union-bound consequence of coordinatewise shifted Poisson domination. -/
theorem maximum_tail_of_poisson_domination
    {Ω V : Type*} [Fintype Ω] [Fintype V]
    (p : FiniteEntropy.Law Ω) (degree : Ω → V → ℕ) (h : V → ℕ)
    (μ A : ℝ) (hμ : 0 ≤ μ)
    (hn : 1 ≤ Real.log (Fintype.card V : ℝ))
    (hm : μ ≤ 2 * Real.log (Fintype.card V : ℝ))
    (hh : ∀ v, (h v : ℝ) ≤ 3 * Real.log (Fintype.card V : ℝ))
    (hdom : ∀ v k, p.event (fun ω => k ≤ degree ω v - h v) ≤
      1 - Real.exp (-μ) * ∑ j ∈ Finset.range k, μ ^ j / (j.factorial : ℝ)) :
    p.event (fun ω => ∃ v, poissonMaximumConstant A *
        Real.log (Fintype.card V : ℝ) < (degree ω v : ℝ)) ≤
      Real.rpow (Fintype.card V : ℝ) (-A) := by
  classical
  let n : ℝ := Fintype.card V
  let L : ℝ := 2 * Real.exp 1 + |A| + 1
  let k : ℕ := Nat.ceil (L * Real.log n)
  have hnlog : 0 < Real.log n := lt_of_lt_of_le zero_lt_one hn
  have hnpos : 0 < n := by
    have hnn : 0 ≤ n := Nat.cast_nonneg _
    by_contra H
    have hz : n = 0 := le_antisymm (le_of_not_gt H) hnn
    simp [hz] at hnlog
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hklo : L * Real.log n ≤ (k : ℝ) := Nat.le_ceil _
  have hkhi : (k : ℝ) ≤ L * Real.log n + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hL hnlog.le)).le
  have hcover (ω : Ω) (v : V)
      (hd : poissonMaximumConstant A * Real.log n < (degree ω v : ℝ)) :
      k ≤ degree ω v - h v := by
    have hb := hh v
    have he : (h v : ℝ) + (k : ℝ) ≤ poissonMaximumConstant A * Real.log n := by
      dsimp [poissonMaximumConstant, L] at *
      nlinarith
    have hd' : h v + k ≤ degree ω v := by exact_mod_cast (le_of_lt (he.trans_lt hd))
    omega
  have htail (v : V) : p.event (fun ω => k ≤ degree ω v - h v) ≤
      Real.exp ((-|A| - 3) * Real.log n) := by
    refine (hdom v k).trans ((poisson_tail_exponential μ hμ k).trans ?_)
    apply Real.exp_le_exp.mpr
    have he : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
    have hm' := mul_le_mul_of_nonneg_right hm he
    dsimp [L] at hklo
    dsimp [n] at *
    nlinarith
  calc
    _ ≤ p.event (fun ω => ∃ v, k ≤ degree ω v - h v) :=
      p.event_mono (fun ω ⟨v,hv⟩ => ⟨v,hcover ω v hv⟩)
    _ ≤ ∑ v, p.event (fun ω => k ≤ degree ω v - h v) := p.finite_union_bound _
    _ ≤ ∑ _v : V, Real.exp ((-|A| - 3) * Real.log n) :=
      Finset.sum_le_sum (fun v _ => htail v)
    _ = n * Real.exp ((-|A| - 3) * Real.log n) := by simp [n]
    _ = Real.exp ((-|A| - 2) * Real.log n) := by
      rw [← Real.exp_log hnpos, ← Real.exp_add]
      congr 1
      rw [Real.log_exp]
      ring
    _ ≤ Real.exp (-A * Real.log n) := by
      apply Real.exp_le_exp.mpr
      have habs := le_abs_self A
      nlinarith
    _ = Real.rpow n (-A) := by change Real.exp (-A * Real.log n) = n ^ (-A); rw [Real.rpow_def_of_pos hnpos]; congr 1; ring
end LooseHamilton
