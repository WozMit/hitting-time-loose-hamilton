module

public import HittingTimeLooseHamilton.PathPerturbationBounds
public import HittingTimeLooseHamilton.PathRegularityModels

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma partitionDensity_nonneg {r : ℕ} (hr : 2 ≤ r) : 0 ≤ partitionDensity r := by
  unfold partitionDensity privateFraction junctionFraction
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h2 : 0 ≤ (r:ℝ)-2 := by linarith
  have h1 : 0 ≤ (r:ℝ)-1 := by linarith
  positivity

/-- Finite transport for the port prohibition. Its two scalar hypotheses say
that the new mean retains at least half the old mean and that the loss of edges
is below the partition tolerance; neither is a probabilistic assumption. -/
theorem path_upper_regular_port_transport {r : ℕ} {C L : ℝ} {F : SimpleHypergraph V}
    (hC : 0 ≤ C) (hr : 2 ≤ r) (hF : PathGraphUpperRegular r C L F)
    (U : Finset V)
    (hmean : meanDegree (V:=V) r F.card ≤ 2*meanDegree (V:=V) r (fixedPortHost F U).card)
    (hloss : (1+partitionDensity r)*(U.card:ℝ)*C ≤
      C*Fintype.card V*(Real.log (Fintype.card V:ℝ))^(-1/8:ℝ)) :
    PathGraphUpperRegular r (4*C) L (fixedPortHost F U) := by
  let μ := meanDegree (V:=V) r F.card
  let ν := meanDegree (V:=V) r (fixedPortHost F U).card
  have hμ : 0 ≤ μ := by unfold μ meanDegree; positivity
  have hν : 0 ≤ ν := by unfold ν meanDegree; positivity
  have hmean' : μ ≤ 2*ν := hmean
  have hcmean : C*μ ≤ 4*C*ν := by nlinarith
  constructor
  · intro v
    exact (Nat.cast_le.mpr (port_filter_vertex_degree_le U F v)).trans
      ((hF.upper_degree v).trans hcmean)
  · intro v w hvw
    exact (Nat.cast_le.mpr (port_filter_pair_degree_le U F v w)).trans
      ((hF.codegree v w hvw).trans
        (mul_le_mul_of_nonneg_right hcmean (Real.rpow_nonneg (Real.log_nonneg
          (by have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩; exact_mod_cast this)) _)))
  · intro A hA
    have hbase := hF.partitions A hA
    have ht := filter_discrepancy_transfer (portFilteredHost_subset U F)
      (fun e => (e∩A).card=2) (partitionDensity r)
      (C*Fintype.card V*μ*(Real.log (Fintype.card V:ℝ))^(-1/8:ℝ))
      (partitionDensity_nonneg hr) hbase
    have hcard : (fixedPortHost F U).card ≤ F.card := card_le_card (portFilteredHost_subset U F)
    have hports := port_filter_edge_loss_real F U (C*μ) hF.upper_degree
    change (F.card:ℝ) - (fixedPortHost F U).card ≤ (U.card:ℝ)*(C*μ) at hports
    have ht' : |(partitionCount (fixedPortHost F U) A:ℝ)-partitionDensity r*(fixedPortHost F U).card| ≤
      C*Fintype.card V*μ*(Real.log (Fintype.card V:ℝ))^(-1/8:ℝ)+
      (1+partitionDensity r)*((F.card:ℝ)-(fixedPortHost F U).card) := by
      change |(partitionCount (fixedPortHost F U) A:ℝ)-partitionDensity r*(fixedPortHost F U).card| ≤
        C*Fintype.card V*μ*(Real.log (Fintype.card V:ℝ))^(-1/8:ℝ)+
        (1+partitionDensity r)*((F.card-(fixedPortHost F U).card:ℕ):ℝ) at ht
      rwa [Nat.cast_sub hcard] at ht
    have hθ := partitionDensity_nonneg hr
    have hn : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hf : 0 ≤ (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ) := Real.rpow_nonneg (Real.log_natCast_nonneg _) _
    have hl := mul_le_mul_of_nonneg_right hloss hμ
    have he := mul_le_mul_of_nonneg_left hports (by linarith : 0 ≤ 1+partitionDensity r)
    have hm := mul_le_mul_of_nonneg_right hcmean (mul_nonneg hn hf)
    have hm2 := mul_le_mul_of_nonneg_right hmean' (mul_nonneg (mul_nonneg hC hn) hf)
    dsimp [μ,ν] at *
    nlinarith

end LooseHamilton
