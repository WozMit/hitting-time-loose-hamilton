module

public import HittingTimeLooseHamilton.NestedPairLaw
public import HittingTimeLooseHamilton.UniformConditionalEquivalence

public section

/-! Fixed edge-complement exposure leaves the original degree constraint intact. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def EdgeComplementPair (U A0 : SimpleHypergraph V) (ell : V → ℕ) (s t : ℕ) :=
  {p : SimpleHypergraph V × SimpleHypergraph V //
    p.1 ⊆ p.2 ∧ p.2 ⊆ U ∧ p.1.card = s ∧ p.2.card = t ∧
      ∀ v, ell v ≤ vertexDegree (A0 ∪ p.1) v}
@[expose] instance (U A0 : SimpleHypergraph V) (ell : V → ℕ) (s t : ℕ) :
    Fintype (EdgeComplementPair U A0 ell s t) := by
  classical
  unfold EdgeComplementPair
  infer_instance
@[expose] instance (U A0 : SimpleHypergraph V) (ell : V → ℕ) (s t : ℕ) :
    DecidableEq (EdgeComplementPair U A0 ell s t) := Classical.decEq _

@[expose] def EdgeComplementEvent (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (U A0 B0 : SimpleHypergraph V)
    (ω : TerminalState V r M ell × MissingOrder V r M) : Prop :=
  ω.1.val \ U = A0 ∧ extensionState ω.1 ω.2 j \ U = B0

@[expose] def EdgeComplementFiber (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (U A0 B0 : SimpleHypergraph V) :=
  {p : NestedState V r M ell j // p.val.1.val \ U = A0 ∧ p.val.2 \ U = B0}
@[expose] instance (r M : ℕ) (ell : V → ℕ) (j : ℕ) (U A0 B0 : SimpleHypergraph V) :
    Fintype (EdgeComplementFiber r M ell j U A0 B0) := by
  classical
  unfold EdgeComplementFiber
  infer_instance

lemma edgeComplement_reconstruct (H U : SimpleHypergraph V) :
    (H \ U) ∪ (H ∩ U) = H := by ext e; simp; tauto

lemma edgeComplement_card (H U : SimpleHypergraph V) :
    (H ∩ U).card = H.card - (H \ U).card := by
  have hd : Disjoint (H \ U) (H ∩ U) := by
    apply disjoint_left.mpr
    intro e he hf
    exact (mem_sdiff.mp he).2 (mem_inter.mp hf).2
  have h := card_union_of_disjoint hd
  rw [edgeComplement_reconstruct] at h
  omega
end LooseHamilton
