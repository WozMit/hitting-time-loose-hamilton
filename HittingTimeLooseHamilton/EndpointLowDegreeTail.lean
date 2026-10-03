module

public import HittingTimeLooseHamilton.EndpointLowDegreeTestSet
public import HittingTimeLooseHamilton.FiniteAvoidanceTail

public section

/-! A joint two-endpoint lower-tail estimate retaining a prescribed-edge event.
The mixed avoidance premise is quantitative and is supplied by the uniform
permutation calculation; no conditioning or independence is assumed here. -/
noncomputable section
namespace LooseHamilton
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

theorem endpoint_low_degree_tail_of_mixed_avoidance
    (p : FiniteEntropy.Law Ω) (H : Ω → SimpleHypergraph V)
    (B : Ω → Prop) [DecidablePred B] {r : ℕ} (hr : 1 ≤ r)
    {u v : V} (huv : u ≠ v) (K : SimpleHypergraph V)
    (q ρ c : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hc : 0 ≤ c) (h : ℕ)
    (havoid : ∀ T ⊆ endpointDegreeTest r u v K,
      p.event (fun ω => B ω ∧ Disjoint (H ω) T) ≤ c * (1-ρ)^T.card) :
    p.event (fun ω => B ω ∧ vertexDegree (H ω) u ≤ h ∧ vertexDegree (H ω) v ≤ h) ≤
      c * Real.exp (-ρ * ((2 * (Fintype.card V-2).choose (r-1) - K.card : ℕ) : ℝ) * (1-q)
        - ((2*h : ℕ) : ℝ) * Real.log q) := by
  have hevent : p.event (fun ω => B ω ∧ vertexDegree (H ω) u ≤ h ∧ vertexDegree (H ω) v ≤ h) ≤
      p.event (fun ω => B ω ∧ (H ω ∩ endpointDegreeTest r u v K).card ≤ 2*h) := by
    apply FiniteEntropy.Law.event_mono
    intro ω hh
    refine ⟨hh.1, (endpointDegreeTest_inter_card_le r u v K (H ω)).trans ?_⟩
    omega
  apply hevent.trans
  apply (Hypergeometric.lower_tail_exp_le_of_avoidance p H (endpointDegreeTest r u v K)
    B q ρ c hq0 hq1 hρ0 hρ1 hc (2*h) havoid).trans
  apply mul_le_mul_of_nonneg_left _ hc
  apply Real.exp_le_exp.mpr
  have hd : (((2 * (Fintype.card V-2).choose (r-1) - K.card : ℕ) : ℝ)) ≤
      ((endpointDegreeTest r u v K).card : ℝ) :=
    Nat.cast_le.mpr (endpointDegreeTest_card_lower hr huv K)
  have ha : 0 ≤ ρ * (1-q) := mul_nonneg hρ0 (sub_nonneg.mpr hq1)
  have hh := mul_le_mul_of_nonneg_right hd ha
  nlinarith
end LooseHamilton
