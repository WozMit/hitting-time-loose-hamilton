module

public import HittingTimeLooseHamilton.EdgeComplementEquiv

public section

/-! Exact conditioning of the actual extension law on an arbitrary fixed edge
complement. No residual bounded-offset or new feasibility assumption occurs. -/
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The terminal and current restrictions are uniformly distributed among all
nested residual pairs of the recorded sizes satisfying the original lower
bounds after adjoining the exposed terminal edges. -/
theorem edgeComplement_conditional_uniform (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j U A0 B0)) :
    ∃ hne : Nonempty (EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card)),
      letI := hne
      ∀ P : SimpleHypergraph V × SimpleHypergraph V → Prop,
        ((extensionLaw r M ell).condition
          (EdgeComplementEvent r M ell j U A0 B0) hb).event
            (fun ω => P (ω.1.val ∩ U, extensionState ω.1 ω.2 j ∩ U)) =
        (FiniteEntropy.uniform : FiniteEntropy.Law
          (EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card))).event
            (fun p => P p.val) := by
  let f := extensionNestedState r M ell j hMj hj
  let E : NestedState V r M ell j → Prop := fun p =>
    p.val.1.val \ U = A0 ∧ p.val.2 \ U = B0
  obtain ⟨ω,hω⟩ := exists_of_event_pos (extensionLaw r M ell)
    (EdgeComplementEvent r M ell j U A0 B0) hb
  let w : EdgeComplementFiber r M ell j U A0 B0 := ⟨f ω,hω⟩
  let e := edgeComplementEquiv r M ell j U A0 B0 hU w
  letI : Nonempty (NestedState V r M ell j) := ⟨w.val⟩
  letI : Nonempty {p : NestedState V r M ell j // E p} := ⟨w⟩
  let hne : Nonempty (EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card)) := ⟨e w⟩
  letI := hne
  refine ⟨hne,?_⟩
  intro P
  exact uniform_pushforward_conditioned_equiv (extensionLaw r M ell) f
    (extension_nested_law_uniform r M ell j hMj hj) E
    (fun p => P (p.val.1.val ∩ U,p.val.2 ∩ U)) e (fun p => P p.val)
    (fun p => Iff.rfl) hb

/-- Positive-probability complement data automatically give feasible residual
sizes. In particular this is not a hypothesis about a fresh shifted model. -/
theorem edgeComplement_sizes_of_positive (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j U A0 B0)) :
    M-A0.card ≤ j-B0.card ∧ j-B0.card ≤ U.card := by
  obtain ⟨hne,_⟩ := edgeComplement_conditional_uniform r M ell j hMj hj U A0 B0 hU hb
  obtain ⟨p⟩ := hne
  constructor
  · simpa only [p.property.2.2.1,p.property.2.2.2.1] using card_le_card p.property.1
  · simpa only [p.property.2.2.2.1] using card_le_card p.property.2.1
/-- Every positively observed record is nested, avoids the sampling universe,
and has sizes bounded by the original terminal/current times. -/
theorem edgeComplement_record_of_positive (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card) (U A0 B0 : SimpleHypergraph V)
    (hb : 0 < (extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j U A0 B0)) :
    A0 ⊆ B0 ∧ B0 ⊆ completeEdges V r ∧ Disjoint A0 U ∧ Disjoint B0 U ∧
      A0.card ≤ M ∧ B0.card ≤ j := by
  obtain ⟨ω,hω⟩ := exists_of_event_pos (extensionLaw r M ell)
    (EdgeComplementEvent r M ell j U A0 B0) hb
  let w : EdgeComplementFiber r M ell j U A0 B0 :=
    ⟨extensionNestedState r M ell j hMj hj ω,hω⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [w.property.1,w.property.2] using
      (sdiff_subset_sdiff w.val.property.1 (Subset.refl U))
  · have hs : w.val.val.2 \ U ⊆ completeEdges V r :=
      sdiff_subset.trans w.val.property.2.1
    simpa only [w.property.2] using hs
  · have hd : Disjoint (w.val.val.1.val \ U) U := sdiff_disjoint
    simpa only [w.property.1] using hd
  · have hd : Disjoint (w.val.val.2 \ U) U := sdiff_disjoint
    simpa only [w.property.2] using hd
  · simpa only [w.property.1,w.val.val.1.property.2.1] using
      (card_le_card (sdiff_subset : w.val.val.1.val \ U ⊆ w.val.val.1.val))
  · simpa only [w.property.2,w.val.property.2.2] using
      (card_le_card (sdiff_subset : w.val.val.2 \ U ⊆ w.val.val.2))
end LooseHamilton
