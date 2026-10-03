module

public import HittingTimeLooseHamilton.RootLinkFiberEquiv

public section

/-! Conditional root links under the actual Q law, including exposed prescribed edges. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact conditional law after fixing the complementary terminal and current data.
Taking U to be all root edges gives the root-free observation. Removing prescribed
root edges from U exposes their inner/outer status in the complementary data. -/
theorem root_link_conditional_law (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (m : ℕ) (hMm : M ≤ m)
    (hm : m ≤ (completeEdges V r).card) (U A B : SimpleHypergraph V)
    (hU : U ⊆ completeEdges V r)
    (hobs : 0 < (extensionLaw r M ell).event (fun ω =>
      RootLinkObservation U A B ω.1.val (extensionState ω.1 ω.2 m))) :
    ∃ hne : Nonempty (RootLinkFeasibleState U A ell (M-A.card) (m-B.card)),
      letI := hne
      ∀ P : SimpleHypergraph V × SimpleHypergraph V → Prop,
      ((extensionLaw r M ell).condition (fun ω =>
        RootLinkObservation U A B ω.1.val (extensionState ω.1 ω.2 m)) hobs).event
          (fun ω => P (ω.1.val∩U,extensionState ω.1 ω.2 m∩U)) =
        (FiniteEntropy.uniform : FiniteEntropy.Law
          (RootLinkFeasibleState U A ell (M-A.card) (m-B.card))).event (fun p => P p.val.val) := by
  classical
  let f := extensionNestedState r M ell m hMm hm
  let E : NestedState V r M ell m → Prop := fun p => RootLinkObservation U A B p.val.1.val p.val.2
  obtain ⟨ω,hω⟩ := exists_of_event_pos (extensionLaw r M ell) _ hobs
  let W : RootLinkFiber r M ell m U A B := ⟨f ω,hω⟩
  let e := rootLinkFiberEquiv r M ell m U A B hU W
  letI : Nonempty (NestedState V r M ell m) := ⟨W.val⟩
  letI : Nonempty {p : NestedState V r M ell m // E p} := ⟨W⟩
  let hne : Nonempty (RootLinkFeasibleState U A ell (M-A.card) (m-B.card)) := ⟨e W⟩
  letI := hne
  refine ⟨hne,?_⟩
  intro P
  exact uniform_pushforward_conditioned_equiv (extensionLaw r M ell) f
    (extension_nested_law_uniform r M ell m hMm hm) E
    (fun p => P (p.val.1.val∩U,p.val.2∩U)) e (fun p => P p.val.val)
    (fun p => Iff.rfl) hobs
end LooseHamilton
