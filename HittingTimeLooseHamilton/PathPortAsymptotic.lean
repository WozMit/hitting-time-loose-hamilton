module

public import HittingTimeLooseHamilton.PathPortRegularity
public import HittingTimeLooseHamilton.PathPerturbationScalars

public section

noncomputable section
namespace LooseHamilton
open Finset Filter

/-- Uniform deterministic preservation of upper degrees, codegrees and partition
counts under a port prohibition of sublinear size. -/
theorem eventually_path_upper_regular_ports (r : ℕ) (C L K : ℝ)
    (hr : 2 ≤ r) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type*) [Fintype V] [DecidableEq V],
      Fintype.card V = n → ∀ F : SimpleHypergraph V,
      PathGraphUpperRegular r C L F → ∀ U : Finset V,
      (U.card:ℝ) ≤ K*(n:ℝ)^(1/10:ℝ) →
      PathGraphUpperRegular r (4*C) L (fixedPortHost F U) := by
  filter_upwards [eventually_sublinear_budget 0 (K*C*r),
    eventually_partition_loss_budget 0 ((1+partitionDensity r)*K)] with n hnM hnP
  intro V _ _ hV F hF U hU
  simp only [zero_add] at hnM hnP
  have hnpos : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnM.1)
  have hn0 : (0:ℝ)≤n := hnpos.le
  have hμ : 0 ≤ meanDegree (V:=V) r F.card := by unfold meanDegree; positivity
  have hcard : ((fixedPortHost F U).card:ℝ) ≤ F.card := by
    exact_mod_cast card_le_card (portFilteredHost_subset U F)
  have hbudget : (U.card:ℝ)*C*r ≤ (n:ℝ)/2 := by
    have hu := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hU hC) (Nat.cast_nonneg r)
    nlinarith only [hu,hnM.2]
  have hloss := port_filter_edge_loss_real F U (C*meanDegree (V:=V) r F.card) hF.upper_degree
  have hmeans := mean_degree_perturbation hnpos (show (n:ℝ)/2≤n by linarith)
    (le_refl (n:ℝ)) (Nat.cast_nonneg F.card) hcard (Nat.cast_nonneg r)
    (b:=(U.card:ℝ)*C) (by simpa only [fixedPortHost, portFilteredHost, meanDegree,hV,mul_assoc] using hloss) hbudget
  apply path_upper_regular_port_transport hC hr hF U
  · simpa only [meanDegree,hV] using (show (r:ℝ)*F.card/n ≤
      2*((r:ℝ)*(fixedPortHost F U).card/n) by linarith [hmeans.1])
  · rw [hV]
    have hθ := partitionDensity_nonneg hr
    have hu := mul_le_mul_of_nonneg_left hU (by linarith : 0≤1+partitionDensity r)
    have hb : (1+partitionDensity r)*(U.card:ℝ) ≤
        (n:ℝ)*(Real.log (n:ℝ))^(-1/8:ℝ) := by nlinarith only [hu,hnP]
    have hh := mul_le_mul_of_nonneg_right hb hC
    nlinarith only [hh]

end LooseHamilton
