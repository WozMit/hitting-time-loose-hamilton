module

public import HittingTimeLooseHamilton.StoppedCountingPath
public import HittingTimeLooseHamilton.StoppedCountingLog
public import HittingTimeLooseHamilton.StoppedCountingVariance

public section
noncomputable section
open scoped BigOperators
namespace LooseHamilton.StoppedCounting
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]
theorem sum_deletion_range (K t : ℕ) (ht : t ≤ K) (f : ℕ → ℝ) :
    ∑ u ∈ range t, f (K-u) = ∑ j ∈ Ioc (K-t) K, f j := by
  apply sum_bij (fun u _ => K-u)
  · intro u hu; have hu := mem_range.mp hu; exact mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro u hu v hv he; have hu := mem_range.mp hu; have hv := mem_range.mp hv; omega
  · intro j hj; rcases mem_Ioc.mp hj with ⟨hlo,hhi⟩
    exact ⟨K-j, mem_range.mpr (by omega), by omega⟩
  · intros; rfl

theorem sum_drift (k t : ℕ) (ht : t ≤ Fintype.card A) :
    ∑ u ∈ range t, (k:ℝ)/(Fintype.card A-u : ℕ) =
      k * deletionHarmonic (Fintype.card A-t) (Fintype.card A) := by
  rw [sum_deletion_range _ _ ht (fun j => (k:ℝ)/(j:ℝ))]
  simp only [deletionHarmonic, mul_sum, div_eq_mul_inv]

theorem log_state_lower {C : Finset (Finset A)} {C0 : ℝ} {k M t : ℕ} {σ : FiniteOrder A}
    (hM : 0<M) (hMK : M≤Fintype.card A) (hC0 : 0≤C0)
    (hsmall : C0*k/M ≤ (1/2:ℝ)) (ht : Reached C C0 k M σ t) :
    Real.log (familyCount C univ) - k*deletionHarmonic (Fintype.card A-t) (Fintype.card A)
      - (∑ u ∈ range t, increment C C0 k M σ u) - variance C0 k M (Fintype.card A) ≤
      Real.log (familyCount C (state σ t)) := by
  have htK : t≤Fintype.card A := ht.1.trans (Nat.sub_le _ _)
  have hstep (u : ℕ) (hu : u ∈ range t) :
      -(loss C σ u) - (cap A C0 k u)^2 ≤ Real.log (1-loss C σ u) := by
    have hut := mem_range.mp hu
    have huK : u<Fintype.card A := by omega
    have hgood := ht.2 u hut
    have hcap := loss_le_cap hgood huK
    have hhalf := hcap.trans (cap_le_half hM hC0 hsmall (by have := ht.1; omega) hMK)
    have hlog := neg_log_one_sub_le (loss_nonneg C σ u) hhalf
    have hs : (loss C σ u)^2 ≤ (cap A C0 k u)^2 :=
      sq_le_sq₀ (loss_nonneg C σ u) ((loss_nonneg C σ u).trans hcap) |>.mpr hcap
    linarith
  have hsum := sum_le_sum hstep
  have hv : ∑ u ∈ range t, (cap A C0 k u)^2 ≤ variance C0 k M (Fintype.card A) := by
    rw [variance_eq_sum_steps C0 k M (Fintype.card A) hMK]
    change (∑ u ∈ range t, (cap A C0 k u)^2) ≤ ∑ u ∈ range (Fintype.card A-M), (cap A C0 k u)^2
    exact sum_le_sum_of_subset_of_nonneg (range_mono ht.1) (by intros; positivity)
  have hi : ∑ u ∈ range t, increment C C0 k M σ u =
      (∑ u ∈ range t, loss C σ u) -
      (∑ u ∈ range t, (k:ℝ)/(Fintype.card A-u : ℕ)) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro u hu
    simp only [increment, if_pos (reached_active_before ht (mem_range.mp hu))]
  rw [sum_drift k t htK] at hi
  rw [log_state_telescope hM hMK hC0 hsmall ht]
  simp only [sum_sub_distrib, sum_neg_distrib] at hsum
  linarith

theorem deficit_implies_stopped_sum {C : Finset (Finset A)} {C0 a : ℝ} {k M t : ℕ}
    {σ : FiniteOrder A} (hM : 0<M) (hMK : M≤Fintype.card A) (hC0 : 0≤C0)
    (hsmall : C0*k/M ≤ (1/2:ℝ)) (ht : Reached C C0 k M σ t)
    (hdeficit : Real.log (familyCount C (state σ t)) <
      Real.log (familyCount C univ) - k*deletionHarmonic (Fintype.card A-t) (Fintype.card A)
        - a - variance C0 k M (Fintype.card A)) :
    a < ∑ u ∈ range t, increment C C0 k M σ u := by
  have hh := log_state_lower hM hMK hC0 hsmall ht
  linarith
end LooseHamilton.StoppedCounting
