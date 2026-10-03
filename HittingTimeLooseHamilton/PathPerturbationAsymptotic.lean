module

public import HittingTimeLooseHamilton.PathDeletionAsymptotic
public import HittingTimeLooseHamilton.PathPortAsymptotic

public section

/-! Uniform composition of bounded deletion and the original port prohibition. -/
noncomputable section
namespace LooseHamilton
open Finset Filter

lemma tenth_power_le_twice {n k : ℝ} (hk : 0 ≤ k) (hn : 0 ≤ n) (h : n ≤ 2*k) :
    n^(1/10:ℝ) ≤ 2*k^(1/10:ℝ) := by
  have hh : n^(1/10:ℝ) ≤ (2*k)^(1/10:ℝ) := Real.rpow_le_rpow hn h (by norm_num)
  rw [Real.mul_rpow (by norm_num) hk] at hh
  have htwo : (2:ℝ)^(1/10:ℝ) ≤ 2 := by
    calc
      _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  exact hh.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hk _))

lemma restrictedPorts_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (S U : Finset V) : (restrictedPorts S U).card ≤ U.card := by
  apply card_le_card_of_injOn (fun v : ↥S => v.val)
  · intro v hv
    exact (mem_filter.mp hv).2
  · intro x hx y hy he
    exact Subtype.ext he

/-- A single cutoff works for every graph, every bounded deletion and every
original port set of the required size. All means use the resulting graph. -/
theorem eventually_path_regular_perturbations (r h : ℕ) (c C L : ℝ)
    (hr : 2 ≤ r) (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type*) [Fintype V] [DecidableEq V],
      Fintype.card V = n → ∀ F : SimpleHypergraph V,
      PathGraphRegular r c C (L+1) F → ∀ U : Finset V,
      (U.card:ℝ) ≤ 2*(n:ℝ)^(1/10:ℝ) → ∀ Z : Finset V, Z.card ≤ h →
      PathGraphRegular r (c/4) (8*C) L (deleteVertices Z F) ∧
      PathGraphUpperRegular r (32*C) L
        (fixedPortHost (deleteVertices Z F) (restrictedPorts (univ \ Z) U)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (eventually_path_upper_regular_ports r (8*C) L 4 hr (by positivity) (by norm_num))
  filter_upwards [eventually_path_regular_deletion r h c C L hr hc hC hL,
    eventually_ge_atTop (N₀+h),eventually_ge_atTop (2*h)] with n hdel hn₀ hn₂
  intro V _ _ hV F hF U hU Z hZ
  have hd := hdel V hV F hF Z hZ
  refine ⟨hd,?_⟩
  let k := Fintype.card ↥(univ \ Z)
  have hk : k = n-Z.card := by
    simp only [k,Fintype.card_coe,card_sdiff_of_subset (subset_univ Z),card_univ,hV]
  have hzN : Z.card ≤ n := by rw [← hV]; exact card_le_univ _
  have hNk : N₀ ≤ k := by rw [hk]; omega
  have hn2k : (n:ℝ) ≤ 2*(k:ℝ) := by
    exact_mod_cast (show n ≤ 2*k by rw [hk]; omega)
  have hpow := tenth_power_le_twice (Nat.cast_nonneg k) (Nat.cast_nonneg n) hn2k
  have hports : ((restrictedPorts (univ \ Z) U).card:ℝ) ≤ 4*(k:ℝ)^(1/10:ℝ) := by
    have hsize : ((restrictedPorts (univ \ Z) U).card:ℝ) ≤ U.card := by
      exact_mod_cast restrictedPorts_card_le (univ \ Z) U
    linarith
  have ht := hN₀ k hNk ↥(univ \ Z) rfl (deleteVertices Z F)
    hd.toPathGraphUpperRegular (restrictedPorts (univ \ Z) U) hports
  convert ht using 1; ring
end LooseHamilton
