module

public import HittingTimeLooseHamilton.EndpointLowDegreeTail
public import HittingTimeLooseHamilton.ProcessMixedPrefix
public import HittingTimeLooseHamilton.HypergeometricInclusionBounds

public section

/-! Joint presence and low-degree estimates in the original edge-order process. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A prescribed path-edge event and two low endpoint degrees have the expected
multiplicative upper bound, with the finite correction of deleting those edges
from both the sample size and incidence supports. -/
theorem process_endpoint_low_degree_bound {r : ℕ} (hr : 1 ≤ r)
    (K : SimpleHypergraph V) (hK : K ⊆ completeEdges V r)
    {u v : V} (huv : u ≠ v) (a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ (completeEdges V r).card)
    (hk : K.card ≤ a) (hkN : K.card < (completeEdges V r).card)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (h : ℕ) :
    (processLaw V r).event (fun σ => K ⊆ processState σ b ∧
      vertexDegree (processState σ a) u ≤ h ∧ vertexDegree (processState σ a) v ≤ h) ≤
      ((b : ℝ) / (completeEdges V r).card)^K.card *
        Real.exp (-(((a-K.card : ℕ) : ℝ) / ((completeEdges V r).card-K.card : ℕ)) *
          ((2 * (Fintype.card V-2).choose (r-1) - K.card : ℕ) : ℝ) * (1-q)
          - ((2*h : ℕ) : ℝ) * Real.log q) := by
  classical
  let N := (completeEdges V r).card
  let ρ : ℝ := ((a-K.card : ℕ) : ℝ) / ((N-K.card : ℕ) : ℝ)
  let B : EdgeOrder V r → Prop := fun σ => K ⊆ processState σ b
  let c := (processLaw V r).event B
  have ha : a ≤ N := hab.trans hb
  have hden : (0 : ℝ) < ((N-K.card : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N-K.card)
  have hρ0 : 0 ≤ ρ := div_nonneg (Nat.cast_nonneg _) hden.le
  have hρ1 : ρ ≤ 1 := (div_le_one hden).mpr (Nat.cast_le.mpr (Nat.sub_le_sub_right ha _))
  have hc : 0 ≤ c := (processLaw V r).event_nonneg B
  have havoid (T : SimpleHypergraph V) (hT : T ⊆ endpointDegreeTest r u v K) :
      (processLaw V r).event (fun σ => B σ ∧ Disjoint (processState σ a) T) ≤ c * (1-ρ)^T.card := by
    have hTc : T ⊆ completeEdges V r := hT.trans (endpointDegreeTest_subset r u v K)
    have hKT : Disjoint K T := (endpointDegreeTest_disjoint r u v K).symm.mono_right hT
    have hsize : T.card ≤ N-K.card := by
      have hh := card_le_card (union_subset hK hTc)
      rw [card_union_of_disjoint hKT] at hh
      omega
    have hh := process_mixed_prefix_bound K T hK hTc a b ha hk hKT
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hc
    have hn : 0 < N-K.card := by omega
    have hd := Hypergeometric.avoidance_ratio_le (Nat.sub_le_sub_right ha K.card) hn hsize
    simpa only [N, completeEdges_card, ρ] using hd
  have htail := endpoint_low_degree_tail_of_mixed_avoidance (processLaw V r)
    (fun σ => processState σ a) B hr huv K q ρ c hq0 hq1 hρ0 hρ1 hc h havoid
  apply htail.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact process_contains_probability_le hb (by omega) K hK (hk.trans hab)
end LooseHamilton
