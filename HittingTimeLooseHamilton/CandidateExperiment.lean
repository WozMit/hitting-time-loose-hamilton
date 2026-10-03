module

public import HittingTimeLooseHamilton.AuxiliaryFrameEntropy
public import HittingTimeLooseHamilton.BoundaryModels
public import HittingTimeLooseHamilton.CoreConditionalCounting

public section

/-! Item 30.2: the genuine Q experiment and the allowed-universe decomposition.
No conditional uniformity or reverse resampling law is asserted in this module. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ} {original : Finset (Finset V)}
attribute [local instance] Classical.propDecidable

abbrev Outcome (V : Type) [Fintype V] [DecidableEq V] (r M : ℕ) (ell : V → ℕ) :=
  TerminalState V r M ell × MissingOrder V r M

/-- Fixed labelled observations, not a randomly chosen boundary. Vertices in D
may still belong to the frame. Feasibility below means positive Q probability. -/
structure BoundaryRecord (V : Type) [DecidableEq V] where
  vertices : Finset V
  terminal : SimpleHypergraph V
  current : SimpleHypergraph V

@[expose] def BoundaryRecord.event (b : BoundaryRecord V) (j : ℕ) : Outcome V r M ell → Prop :=
  BoundaryEvent r M ell j b.vertices b.terminal b.current

@[expose] def BoundaryRecord.Feasible [Nonempty (TerminalState V r M ell)]
    (b : BoundaryRecord V) (j : ℕ) : Prop :=
  0 < (extensionLaw r M ell).event (b.event j)

@[expose] def BoundaryRecord.law [Nonempty (TerminalState V r M ell)]
    (b : BoundaryRecord V) (j : ℕ) (hb : b.Feasible (r:=r) (M:=M) (ell:=ell) j) :=
  (extensionLaw r M ell).condition (b.event j) hb

/-- Only boundary data are conditioned upon; regularity and entropy stay inside E. -/
theorem boundary_probability [Nonempty (TerminalState V r M ell)]
    (b : BoundaryRecord V) (j : ℕ) (hb : b.Feasible (r:=r) (M:=M) (ell:=ell) j)
    (E : Outcome V r M ell → Prop) :
    (b.law j hb).event E =
      (extensionLaw r M ell).event (fun ω => b.event j ω ∧ E ω) /
        (extensionLaw r M ell).event (b.event j) := by
  exact condition_event_eq_joint _ _ _ _

/-- All allowed frame edges, with the original port prohibition. -/
@[expose] def allowedUniverse (f : Frame r original) : SimpleHypergraph V :=
  (allowedEdges r (originalPorts original)).filter (fun e => e ⊆ f.active)

/-- The only edges available for the repaired random batch. -/
@[expose] def samplingUniverse (f : Frame r original) (D : Finset V) : SimpleHypergraph V :=
  (allowedUniverse f).filter (fun e => Disjoint e D)

/-- Deterministic edge-set decomposition, applied to both original terminal and
current graphs. The complement includes forbidden and deleted-vertex edges. -/
@[expose] def unexposed (f : Frame r original) (D : Finset V) (H : SimpleHypergraph V) :=
  H ∩ samplingUniverse f D

@[expose] def exposed (f : Frame r original) (D : Finset V) (H : SimpleHypergraph V) :=
  H \ samplingUniverse f D

@[expose] def fixedAllowed (f : Frame r original) (D : Finset V) (H : SimpleHypergraph V) :=
  exposed f D H ∩ allowedUniverse f

@[simp] theorem rawHost_eq_inter (f : Frame r original) (H : SimpleHypergraph V) :
    f.rawHost H = H ∩ allowedUniverse f := by
  ext e
  simp [Frame.rawHost, allowedUniverse, and_assoc]

theorem unexposed_union_exposed (f : Frame r original) (D : Finset V)
    (H : SimpleHypergraph V) : unexposed f D H ∪ exposed f D H = H := by
  ext e
  simp [unexposed, exposed]
  tauto

/-- J = J0 union Bcirc. In particular the fixed boundary edges are NOT discarded. -/
theorem rawHost_decomposition (f : Frame r original) (D : Finset V)
    (H : SimpleHypergraph V) :
    f.rawHost H = unexposed f D H ∪ fixedAllowed f D H := by
  ext e
  simp [rawHost_eq_inter, unexposed, fixedAllowed, exposed, samplingUniverse]
  tauto

theorem decomposition_disjoint (f : Frame r original) (D : Finset V)
    (H : SimpleHypergraph V) : Disjoint (unexposed f D H) (fixedAllowed f D H) := by
  rw [Finset.disjoint_left]
  intro e he hf
  exact (mem_sdiff.mp (mem_inter.mp hf).1).2 (mem_inter.mp he).2

/-- S*,H refer to the original Q pair; S,J0 and A0,B0 to its restrictions.
This record exposes deterministic observables only, without an assumed law. -/
@[expose] def pairData (f : Frame r original) (D : Finset V) (j : ℕ)
    (ω : Outcome V r M ell) :
    (SimpleHypergraph V × SimpleHypergraph V) ×
      (SimpleHypergraph V × SimpleHypergraph V) :=
  ((unexposed f D ω.1.val, unexposed f D (extensionState ω.1 ω.2 j)),
   (exposed f D ω.1.val, exposed f D (extensionState ω.1 ω.2 j)))

/-- The repaired batch size uses |J0|, while frame counts still use raw J. -/
@[expose] def batchSize (f : Frame r original) (D : Finset V) (H : SimpleHypergraph V) : ℕ :=
  Nat.floor (FrameScales.nu (Fintype.card V) * (unexposed f D H).card / (f.k:ℝ))

/-- The raw remainder restores the fixed allowed boundary edges. -/
@[expose] def rawRemainder (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) : SimpleHypergraph V :=
  (unexposed f D H \ T) ∪ fixedAllowed f D H

theorem rawRemainder_eq (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T ⊆ unexposed f D H) :
    rawRemainder f D H T = f.rawHost H \ T := by
  rw [rawHost_decomposition]
  ext e
  simp only [rawRemainder, mem_union, mem_sdiff]
  constructor
  · rintro (⟨he, hn⟩ | he)
    · exact ⟨Or.inl he, hn⟩
    · refine ⟨Or.inr he, fun ht => ?_⟩
      exact Finset.disjoint_left.mp (decomposition_disjoint f D H) (hT ht) he
  · rintro ⟨he | he, hn⟩
    · exact Or.inl ⟨he, hn⟩
    · exact Or.inr he

end LooseHamilton.CandidateBalance
