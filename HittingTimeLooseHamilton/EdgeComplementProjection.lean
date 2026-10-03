module

public import HittingTimeLooseHamilton.EdgeComplementConditionalLaw

public section

/-! A total observed residual-pair map for the actual conditioned Q law.
Its arbitrary value off the conditioning event has zero conditional mass. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

@[expose] def edgeComplementObserved (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V)
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (he : EdgeComplementEvent r M ell j U A0 B0 ω) :
    EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card) := by
  refine ⟨(ω.1.val ∩ U, extensionState ω.1 ω.2 j ∩ U),
    inter_subset_inter subset_union_left (Subset.refl U), inter_subset_right, ?_, ?_, ?_⟩
  · rw [edgeComplement_card, ω.1.property.2.1, he.1]
  · rw [edgeComplement_card, extensionState_card _ _ _ hMj hj, he.2]
  · have hr : A0 ∪ (ω.1.val ∩ U) = ω.1.val := by
      rw [← he.1]; exact edgeComplement_reconstruct _ _
    rw [hr]
    exact ω.1.property.2.2

@[expose] def edgeComplementProjection (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V)
    [Nonempty (EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card))]
    (ω : TerminalState V r M ell × MissingOrder V r M) :
    EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card) :=
  if he : EdgeComplementEvent r M ell j U A0 B0 ω then
    edgeComplementObserved r M ell j hMj hj U A0 B0 ω he
  else Classical.choice inferInstance

lemma edgeComplementProjection_val (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V)
    [Nonempty (EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card))]
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (he : EdgeComplementEvent r M ell j U A0 B0 ω) :
    (edgeComplementProjection r M ell j hMj hj U A0 B0 ω).val =
      (ω.1.val ∩ U, extensionState ω.1 ω.2 j ∩ U) := by
  simp only [edgeComplementProjection, dif_pos he]
  rfl

/-- Totalization outside the exposed record does not change the law: its
pushforward under the genuine conditional Q distribution is exactly uniform. -/
theorem edgeComplement_projection_uniform (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    [Nonempty (EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card))]
    (hb : 0 < (extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j U A0 B0)) :
    ((extensionLaw r M ell).condition
      (EdgeComplementEvent r M ell j U A0 B0) hb).map
        (edgeComplementProjection r M ell j hMj hj U A0 B0) = FiniteEntropy.uniform := by
  classical
  obtain ⟨hne, hlaw⟩ := edgeComplement_conditional_uniform r M ell j hMj hj U A0 B0 hU hb
  apply FiniteEntropy.Law.ext_mass
  intro a
  change ((extensionLaw r M ell).condition
    (EdgeComplementEvent r M ell j U A0 B0) hb).event
    (fun ω => edgeComplementProjection r M ell j hMj hj U A0 B0 ω = a) = _
  have he : ((extensionLaw r M ell).condition
      (EdgeComplementEvent r M ell j U A0 B0) hb).event
      (fun ω => edgeComplementProjection r M ell j hMj hj U A0 B0 ω = a) =
    ((extensionLaw r M ell).condition
      (EdgeComplementEvent r M ell j U A0 B0) hb).event
      (fun ω => (ω.1.val ∩ U, extensionState ω.1 ω.2 j ∩ U) = a.val) := by
    rw [condition_event_eq_joint, condition_event_eq_joint]
    congr 1
    apply congrArg (fun E => (extensionLaw r M ell).event E)
    funext ω
    apply propext
    apply and_congr_right
    intro hω
    rw [← edgeComplementProjection_val r M ell j hMj hj U A0 B0 ω hω]
    exact Subtype.ext_iff
  rw [he, hlaw (fun z => z = a.val)]
  simp only [FiniteEntropy.Law.event, Subtype.val_inj]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have hv : b.val ≠ a.val := fun h => hba (Subtype.ext h)
    simp [hv]
  · simp

end LooseHamilton
