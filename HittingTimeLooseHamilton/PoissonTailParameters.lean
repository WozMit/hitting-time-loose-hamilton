module

public import HittingTimeLooseHamilton.PoissonTailMaximum
public import HittingTimeLooseHamilton.TightWindowScales

public section

noncomputable section
namespace LooseHamilton
open Filter

/-- The admissible density window and a fixed bounded offset uniformly imply
the elementary estimates needed for the maximum-degree tail. -/
theorem eventually_poisson_parameters (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) ∧
      ∀ (μ : ℝ) (ell : ℕ), 0 ≤ μ →
        |μ - Real.log n| ≤ 3 * Real.log (Real.log n) →
        |(ell : ℝ) - Nat.floor (epsilon * Real.log n)| ≤ B →
        μ ≤ 2 * Real.log n ∧
          ((max ell (Nat.ceil μ) : ℕ) : ℝ) ≤ 3 * Real.log n := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n)
      atTop (nhds 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  filter_upwards [hlog.eventually (eventually_ge_atTop (max 1 B)),
    (tendsto_order.mp hratio).2 (1/3) (by norm_num)] with n hn hr
  have hn1 : 1 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hn
  have hnB : B ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hn
  refine ⟨hn1, ?_⟩
  intro μ ell hμ hm hell
  have hlpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hll : 3 * Real.log (Real.log (n : ℝ)) ≤ Real.log n := by
    have := (div_lt_iff₀ hlpos).mp hr
    linarith
  have hm2 : μ ≤ 2 * Real.log n := by have := (abs_le.mp hm).2; linarith
  refine ⟨hm2, ?_⟩
  rw [Nat.cast_max]
  apply max_le
  · have hf : (Nat.floor (epsilon * Real.log (n : ℝ)) : ℝ) ≤
        epsilon * Real.log n := Nat.floor_le (by unfold epsilon; positivity)
    have ho := (abs_le.mp hell).2
    unfold epsilon at hf ho
    nlinarith
  · have hc := Nat.ceil_lt_add_one hμ
    linarith

/-- Uniform finite-parameter application, for every vertex type of a sufficiently
large cardinality and every admissible core on that type. -/
theorem eventually_core_poisson_parameters (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = n → ∀ (r M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
      CoreAdmissible r M ell markers B →
      1 ≤ Real.log (Fintype.card V : ℝ) ∧
      meanDegree (V := V) r M ≤ 2 * Real.log (Fintype.card V : ℝ) ∧
      ∀ v, ((max (ell v) (Nat.ceil (meanDegree (V := V) r M)) : ℕ) : ℝ) ≤
        3 * Real.log (Fintype.card V : ℝ) := by
  filter_upwards [eventually_poisson_parameters B] with n hn
  intro V _ _ hcard r M ell markers hadm
  have hμ : 0 ≤ meanDegree (V := V) r M := by unfold meanDegree; positivity
  have hp (v : V) := hn.2 (meanDegree (V := V) r M) (ell v) hμ
    (by simpa [hcard] using hadm.density_window)
    (by simpa [lowerDegreeBase, hcard] using hadm.offsets v)
  have hM : meanDegree (V := V) r M ≤ 2 * Real.log (n : ℝ) := by
    have hbound := hn.2 (meanDegree (V := V) r M) (Nat.floor (epsilon * Real.log n)) hμ
      (by simpa [hcard] using hadm.density_window)
      (by simpa using hadm.offset_nonneg)
    exact hbound.1
  exact ⟨by simpa [hcard] using hn.1, by simpa [hcard] using hM,
    fun v => by simpa [hcard] using (hp v).2⟩
end LooseHamilton
