module

public import HittingTimeLooseHamilton.PathDeletionRegularity
public import HittingTimeLooseHamilton.PathPerturbationScalars

public section

noncomputable section
namespace LooseHamilton
open Finset Filter

/-- Uniform deterministic preservation of all path bounds after bounded vertex
deletions, with the actual new vertex and edge counts in every parameter. -/
theorem eventually_path_regular_deletion (r h : ℕ) (c C L : ℝ)
    (hr : 2 ≤ r) (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type*) [Fintype V] [DecidableEq V],
      Fintype.card V = n → ∀ F : SimpleHypergraph V,
      PathGraphRegular r c C (L+1) F → ∀ Z : Finset V, Z.card ≤ h →
      PathGraphRegular r (c/4) (8*C) L (deleteVertices Z F) := by
  have hp : Tendsto (fun n : ℕ => (n:ℝ)^(1/10:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_sublinear_budget (h*C*r) 0,
    eventually_sublinear_budget h 0, eventually_ge_atTop (4:ℕ),
    eventually_log_error_small (h*C) (by linarith : 0<c/2),
    eventually_partition_loss_budget ((1+partitionDensity r)*h) 0,
    hp.eventually (eventually_ge_atTop (junctionFraction r*h))] with n hnM hnZ hn4 hnD hnP hnW
  intro V _ _ hV F hF Z hZ
  have hzr : (Z.card:ℝ) ≤ h := by exact_mod_cast hZ
  have hnc : Fintype.card ↥(univ \ Z) = n-Z.card := by
    rw [Fintype.card_coe, card_sdiff_of_subset (subset_univ _), card_univ,hV]
  have hzN : Z.card ≤ n := by rw [← hV]; exact card_le_univ Z
  have hnr : (Fintype.card ↥(univ \ Z):ℝ) = (n:ℝ)-Z.card := by
    rw [hnc,Nat.cast_sub hzN]
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn4r : (4:ℝ)≤n := by exact_mod_cast hn4
  simp only [zero_mul,add_zero] at hnM hnZ hnP
  have hnn : (Fintype.card ↥(univ \ Z):ℝ) ≤ (n:ℝ) := by rw [hnr]; have hz0 : (0:ℝ)≤Z.card := Nat.cast_nonneg _; linarith
  have hnnhalf : (n:ℝ)/2 ≤ Fintype.card ↥(univ \ Z) := by rw [hnr]; linarith [hnZ.2]
  have hnnpos : (1:ℝ)<Fintype.card ↥(univ \ Z) := by linarith
  have hmcard : ((deleteVertices Z F).card:ℝ) ≤ F.card := by
    rw [deleteVertices_card]; exact_mod_cast card_le_card (filter_subset (fun e => Disjoint e Z) F)
  have hbudget : (Z.card:ℝ)*C*r ≤ (n:ℝ)/2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hzr hC) (Nat.cast_nonneg r)).trans hnM.2
  have hloss := deleteVertices_edge_loss_real F Z (C*meanDegree (V:=V) r F.card) hF.upper_degree
  have hmeans := mean_degree_perturbation hnpos hnnhalf hnn (Nat.cast_nonneg F.card)
    hmcard (Nat.cast_nonneg r) (b:=(Z.card:ℝ)*C)
    (by simpa only [meanDegree,hV,mul_assoc] using hloss) hbudget
  apply path_regular_deletion_transport hc.le hC hr hF Z
  · simpa only [meanDegree,hV] using (show (r:ℝ)*F.card/n ≤
      2*((r:ℝ)*(deleteVertices Z F).card/Fintype.card ↥(univ \ Z)) by linarith [hmeans.1])
  · simpa only [meanDegree,hV] using hmeans.2
  · rw [hV]; linarith
  · rw [hV]; exact log_rpow_deletion_mono hnnpos hnn (by norm_num)
  · rw [hV]; exact log_rpow_deletion_mono hnnpos hnn (by norm_num)
  · rw [hV]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hzr hC)
      (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)).trans hnD
  · rw [hV]
    exact (mul_le_mul_of_nonneg_left hzr (by have := partitionDensity_nonneg hr; linarith)).trans hnP
  · intro A hA
    rw [hV]
    have ha : 0 ≤ junctionFraction r := by
      unfold junctionFraction; have hr' : (2:ℝ)≤r := by exact_mod_cast hr
      have : 0 ≤ (r:ℝ)-1 := by linarith
      positivity
    exact balanced_window_deletion (Nat.cast_nonneg _) hnn ha hL
      (by rw [hnr]; ring) ((mul_le_mul_of_nonneg_left hzr ha).trans hnW) hA

end LooseHamilton
