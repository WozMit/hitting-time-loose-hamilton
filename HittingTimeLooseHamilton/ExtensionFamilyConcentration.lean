module

public import HittingTimeLooseHamilton.HypergeometricFamilyConcentration
public import HittingTimeLooseHamilton.ExtensionConditioning

public section

/-! A simultaneous finite-family sampling estimate under the genuine extension law Q. -/
noncomputable section
open scoped BigOperators
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- The union ranges over every test and every time after the conditioned start. -/
theorem extension_test_family_concentration {I : Type*} [Fintype I]
    (D : I → SimpleHypergraph V) (hD : ∀ i, D i ⊆ completeEdges V r)
    (M : ℕ) (ell : V → ℕ) [Nonempty (TerminalState V r M ell)]
    (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ)
    (hb : 0 < terminalFeasibilityProbability r M ell) :
    (extensionLaw r M ell).event (fun ω => ∃ i, ∃ m : ℕ, M ≤ m ∧ m ≤ (completeEdges V r).card ∧
      δ*m  ≤  |((extensionState ω.1 ω.2 m ∩ D i).card:ℝ)-
        (m:ℝ)/(completeEdges V r).card*(D i).card|)  ≤ 
      (Fintype.card I:ℝ)*((completeEdges V r).card+1)*2*Real.exp (-δ^2*M/4) /
        terminalFeasibilityProbability r M ell := by
  let J := I × Fin ((completeEdges V r).card+1)
  let E : J → TerminalState V r M ell × MissingOrder V r M → Prop := fun j ω => M ≤ j.2.val ∧
      δ*j.2.val  ≤  |((extensionState ω.1 ω.2 j.2.val ∩ D j.1).card:ℝ)-
        (j.2.val:ℝ)/(completeEdges V r).card*(D j.1).card|
  have hm_event := (extensionLaw r M ell).event_mono
    (E:=fun ω => ∃ i, ∃ m : ℕ, M ≤ m ∧ m ≤ (completeEdges V r).card ∧
      δ*m  ≤  |((extensionState ω.1 ω.2 m ∩ D i).card:ℝ)-
        (m:ℝ)/(completeEdges V r).card*(D i).card|)
    (F:=fun ω => ∃ j : J, E j ω) (by
      rintro ω ⟨i,m,hMm,hm,hω⟩
      exact ⟨⟨i,⟨m,by omega⟩⟩,hMm,hω⟩)
  apply (hm_event.trans ((extensionLaw r M ell).finite_union_bound E)).trans
  calc
    _  ≤  ∑ j : J, 2*Real.exp (-δ^2*M/4)/terminalFeasibilityProbability r M ell := by
      apply sum_le_sum
      intro j _
      by_cases hMm : M ≤ j.2.val
      · let P : SimpleHypergraph V → Prop := fun F => δ*j.2.val  ≤ 
          |((F ∩ D j.1).card:ℝ)-(j.2.val:ℝ)/(completeEdges V r).card*(D j.1).card|
        have hm_event' := (extensionLaw r M ell).event_mono (E:=E j)
          (F:=fun ω => P (extensionState ω.1 ω.2 j.2.val)) (fun _ h => h.2)
        have hj : j.2.val ≤ (completeEdges V r).card := by have := j.2.isLt; omega
        apply (hm_event'.trans (extension_event_le_process_div r M ell j.2.val hMm hj P hb)).trans
        apply div_le_div_of_nonneg_right _ hb.le
        exact process_intersection_relative_concentration M j.2.val hM hMm hj (D j.1) (hD j.1) δ hδ
      · simp [E,hMm,FiniteEntropy.Law.event]
        positivity
    _ = _ := by simp [J]; ring
end LooseHamilton
