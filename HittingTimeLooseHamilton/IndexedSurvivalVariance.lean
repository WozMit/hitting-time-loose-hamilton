module

public import HittingTimeLooseHamilton.IndexedSurvivalBounds
public import HittingTimeLooseHamilton.SurvivalTiltedFinset

public section

/-! Variable-support variance bound, preserving all labels and multiplicities. -/
noncomputable section
namespace LooseHamilton.IndexedSurvival
open Finset FrameSurvival CandidateLogSurvival
open scoped BigOperators
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-- Expected overlap of two independent uniform labels (diagonal included). -/
@[expose] def uniformOverlap (F : Finset ι) (support : ι → Finset α) : ℝ :=
  (∑ i ∈ F, ∑ j ∈ F, ((support i ∩ support j).card : ℝ)) / (F.card : ℝ)^2

/-- A multiplicative support-size error, with no additive zero-overlap error. -/
theorem normalized_variance_bound {H : Finset α} {k d τ : ℕ}
    (hm : 0 < H.card) (hk : 0 < k) (hk4 : 4*k ≤ H.card) (ht4 : 4*τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α) (hne : F.Nonempty)
    (hsub : ∀ i ∈ F, support i ⊆ H)
    (hsize : ∀ i ∈ F, k-d ≤ (support i).card ∧ (support i).card ≤ k) :
    variance (by omega : τ ≤ H.card) F support /
        (mean (by omega : τ ≤ H.card) F support)^2 ≤
      Real.exp (4*(d:ℝ)*τ/H.card) * (Real.exp (4*(τ:ℝ)*k/H.card)-1) *
        uniformOverlap F support / k := by
  classical
  let q : ι → ℝ := fun i => zeta H.card (support i).card τ
  let P : ι → ι → ℝ := fun i j => zeta H.card (support i ∪ support j).card τ
  let I : ι → ι → ℝ := fun i j => (support i ∩ support j).card / (k:ℝ)
  let C : ℝ := Real.exp (4*(τ:ℝ)*k/H.card)-1
  let L : ℝ := Real.exp (2*(d:ℝ)*τ/H.card)
  have hq : ∀ i ∈ F, 0 < q i := by
    intro i hi
    exact zeta_pos (by have := (hsize i hi).2; omega)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hI : ∀ i ∈ F, ∀ j ∈ F, 0 ≤ I i j := by intros; dsimp [I]; positivity
  have hP : ∀ i ∈ F, ∀ j ∈ F,
      P i j / (q i*q j) ≤ 1+C*I i j := by
    intro i hi j hj
    have hcard := card_union_add_card_inter (support i) (support j)
    have hinter : (support i ∩ support j).card ≤ k :=
      (card_le_card inter_subset_left).trans (hsize i hi).2
    have hsum : (support i ∩ support j).card ≤
        (support i).card + (support j).card := by omega
    have hb := variable_zeta_joint_le_chord H.card k (support i).card (support j).card
      τ (support i ∩ support j).card hm hk hk4 ht4
      (hsize i hi).2 (hsize j hj).2 hsum hinter
    have hu : (support i).card+(support j).card-(support i ∩ support j).card =
        (support i ∪ support j).card := by omega
    rw [hu] at hb
    apply (div_le_iff₀ (mul_pos (hq i hi) (hq j hj))).2
    simpa only [P, q, I, C, mul_comm] using hb
  have hb (i : ι) (hi : i ∈ F) :=
    variable_zeta_bounds H.card k (support i).card d τ hm hk4 ht4
      (hsize i hi).2 (hsize i hi).1
  have h := SurvivalTilt.normalized_variance_finset F hne q hq P I C
    (zeta H.card k τ) L hC (zeta_pos (by omega)) (Real.exp_pos _).le
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2) hI hP
  rw [variance_eq, secondMoment_eq _ F support hsub, mean_eq _ F support hsub]
  change ((∑ i ∈ F, ∑ j ∈ F, P i j) - (∑ i ∈ F, q i)^2) /
    (∑ i ∈ F, q i)^2 ≤ _
  calc
    _ ≤ L^2*C*((∑ i ∈ F, ∑ j ∈ F, I i j)/(F.card:ℝ)^2) := h
    _ = _ := by
      dsimp [L, C, I, uniformOverlap]
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      have he : 2 * (2*(d:ℝ)*τ/H.card) = 4*(d:ℝ)*τ/H.card := by ring
      rw [he]
      simp_rw [← sum_div]
      ring

end LooseHamilton.IndexedSurvival
