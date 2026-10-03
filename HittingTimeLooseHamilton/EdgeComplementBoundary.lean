module

public import HittingTimeLooseHamilton.EdgeComplementConditionalLaw
public import HittingTimeLooseHamilton.CandidateExperiment

public section

/-! Edge-complement exposure refines the fixed vertex-boundary observation,
including when boundary vertices remain active in the frame. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

lemma boundaryEdges_sdiff_of_avoids (D : Finset V) (H U : SimpleHypergraph V)
    (hU : ∀ e ∈ U, Disjoint e D) :
    boundaryEdges D (H \ U) = boundaryEdges D H := by
  ext e
  simp only [boundaryEdges, mem_traceOn, mem_sdiff]
  constructor
  · rintro ⟨⟨hH,_⟩,hD⟩; exact ⟨hH,hD⟩
  · rintro ⟨hH,hD⟩; exact ⟨⟨hH,fun he => hD (hU e he)⟩,hD⟩

/-- The observed edge complement determines both vertex-boundary traces. -/
theorem edgeComplementEvent_refines_boundary (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (D : Finset V) (U A0 B0 : SimpleHypergraph V)
    (hU : ∀ e ∈ U, Disjoint e D)
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (hω : EdgeComplementEvent r M ell j U A0 B0 ω) :
    BoundaryEvent r M ell j D (boundaryEdges D A0) (boundaryEdges D B0) ω := by
  constructor
  · have h := boundaryEdges_sdiff_of_avoids D ω.1.val U hU
    rw [hω.1] at h
    exact h.symm
  · have h := boundaryEdges_sdiff_of_avoids D (extensionState ω.1 ω.2 j) U hU
    rw [hω.2] at h
    exact h.symm

namespace CandidateBalance
open AuxiliaryFrame
variable {r : ℕ} {original : Finset (Finset V)}

lemma samplingUniverse_subset_complete (f : Frame r original) (D : Finset V) :
    samplingUniverse f D ⊆ completeEdges V r := by
  intro e he
  exact (mem_filter.mp (mem_filter.mp (mem_filter.mp he).1).1).1

lemma samplingUniverse_avoids_boundary (f : Frame r original) (D : Finset V) :
    ∀ e ∈ samplingUniverse f D, Disjoint e D := by
  intro e he
  exact (mem_filter.mp he).2

/-- A complement record from a boundary-conditioned outcome refines that very
record. There is no assumption that the frame deleted its boundary vertices. -/
theorem samplingComplement_refines_record (M : ℕ) (ell : V → ℕ) (j : ℕ)
    (f : Frame r original) (b : BoundaryRecord V)
    (A0 B0 : SimpleHypergraph V)
    (ω₀ : Outcome V r M ell) (hb : b.event j ω₀)
    (h₀ : EdgeComplementEvent r M ell j (samplingUniverse f b.vertices) A0 B0 ω₀)
    (ω : Outcome V r M ell)
    (hω : EdgeComplementEvent r M ell j (samplingUniverse f b.vertices) A0 B0 ω) :
    b.event j ω := by
  have hfirst := edgeComplementEvent_refines_boundary r M ell j b.vertices
    (samplingUniverse f b.vertices) A0 B0 (samplingUniverse_avoids_boundary f b.vertices) ω₀ h₀
  have hsecond := edgeComplementEvent_refines_boundary r M ell j b.vertices
    (samplingUniverse f b.vertices) A0 B0 (samplingUniverse_avoids_boundary f b.vertices) ω hω
  exact ⟨hsecond.1.trans (hfirst.1.symm.trans hb.1),
    hsecond.2.trans (hfirst.2.symm.trans hb.2)⟩
end CandidateBalance
end LooseHamilton
