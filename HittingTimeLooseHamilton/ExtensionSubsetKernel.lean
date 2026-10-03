module

public import HittingTimeLooseHamilton.TerminalConditioning

public section
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At a fixed time, uniformly ordering missing edges gives the exact uniform
subset kernel; the initial terminal graph remains fixed. -/
theorem extension_subset_kernel {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card) (P : SimpleHypergraph V → Prop) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => P (extensionState F σ j)) =
    ((((completeEdges V r \ F.val).powersetCard (j-M)).filter
      (fun S => P (F.val ∪ S))).card : ℝ) /
      (((completeEdges V r).card-M).choose (j-M) : ℝ) := by
  classical
  let val : MissingEdge F ↪ Finset V := ⟨Subtype.val,Subtype.val_injective⟩
  let Q : Finset (MissingEdge F) → Prop := fun S => P (F.val ∪ S.map val)
  let e : MissingOrder V r M ≃ FiniteOrder (MissingEdge F) :=
    (missingOrderEquiv F).trans (Equiv.equivCongr (Equiv.refl _)
      (finCongr (missing_card F).symm))
  have ht := FiniteEntropy.Law.uniform_event_equiv e
    (fun σ => Q (orderPrefix σ (j-M)))
  have he (σ : MissingOrder V r M) : Q (orderPrefix (e σ) (j-M)) =
      P (extensionState F σ j) := by
    simp only [Q,orderPrefix,e,Equiv.trans_apply,Equiv.refl_symm,
      Equiv.refl_apply,missingOrderEquiv,finCongr_apply,extensionState,val,map_eq_image]
    rfl
  simp_rw [he] at ht
  rw [ht]
  change BernoulliSubset.prefixProbability (j-M) Q = _
  rw [BernoulliSubset.prefixProbability_eq _ (by rw [missing_card F]; omega)]
  have hmap : (univ : Finset (MissingEdge F)).map val = completeEdges V r \ F.val := by
    ext x
    simp only [mem_map,mem_univ,true_and,val,Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a,rfl⟩; exact a.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  have hc : (((univ : Finset (MissingEdge F)).powersetCard (j-M)).filter Q).card =
      (((completeEdges V r \ F.val).powersetCard (j-M)).filter
        (fun S => P (F.val ∪ S))).card := by
    have hh := congrArg (fun S : Finset (Finset V) =>
      ((S.powersetCard (j-M)).filter (fun T => P (F.val ∪ T))).card) hmap
    rw [powersetCard_map,filter_map,card_map] at hh
    exact hh
  rw [hc,missing_card F]
end LooseHamilton
