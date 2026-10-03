module

public import HittingTimeLooseHamilton.EdgeComplementBoundary
public import HittingTimeLooseHamilton.RootConditionalMixture

public section

/-! Exact averaging over complement records, with no union bound and no cost
proportional to the reciprocal probability of a boundary record. -/
noncomputable section
namespace LooseHamilton

/-- A uniform bound on refined fibres survives conditioning on any coarser
observation. Only positive-probability refined fibres are used. -/
theorem conditional_event_le_of_refining_fibres
    {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : FiniteEntropy.Law Ω) (E Bad : Ω→Prop) (obs : Ω→I)
    (hE : 0 < p.event E) (q : ℝ)
    (hstable : ∀ ω₀ ω, E ω₀ → obs ω=obs ω₀ → E ω)
    (hbound : ∀ i, ∀ hi : 0 < p.event (fun ω => obs ω=i),
      (p.condition (fun ω => obs ω=i) hi).event Bad ≤ q) :
    (p.condition E hE).event Bad ≤ q := by
  apply conditional_event_le_of_fibre_bounds p E Bad obs hE q
  intro i hi
  obtain ⟨ω₀,hω₀⟩ := exists_of_event_pos p _ hi
  have he : (fun ω => E ω ∧ obs ω=i)=(fun ω => obs ω=i) := by
    funext ω
    apply propext
    exact ⟨And.right,fun hω => ⟨hstable ω₀ ω hω₀.1 (hω.trans hω₀.2.symm),hω⟩⟩
  have hi' : 0 < p.event (fun ω => obs ω=i) := by rwa [he] at hi
  have hb := hbound i hi'
  rw [condition_event_eq_joint] at hb ⊢
  have hnum := congrArg (fun Q : Ω→Prop => p.event (fun ω => Q ω ∧ Bad ω)) he
  rw [hnum,he]
  exact hb

namespace CandidateBalance
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V→ℕ} {original : Finset (Finset V)}

/-- Forgetting the complete fixed edge-complement record preserves its uniform
bound. The source event may include regularity and entropy intersections. -/
theorem complement_bounds_unconditional [Nonempty (TerminalState V r M ell)]
    (j : ℕ) (f : Frame r original) (D : Finset V)
    (Bad : Outcome V r M ell→Prop) (q : ℝ)
    (hbound : ∀ A0 B0 : SimpleHypergraph V,
      ∀ hb : 0 < (extensionLaw r M ell).event
        (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0),
      ((extensionLaw r M ell).condition
        (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0) hb).event Bad ≤ q) :
    (extensionLaw r M ell).event Bad ≤ q := by
  apply event_le_of_observation_conditional_bounds (extensionLaw r M ell) Bad
    (fun ω => (ω.1.val\samplingUniverse f D,
      extensionState ω.1 ω.2 j\samplingUniverse f D)) q
  rintro ⟨A0,B0⟩ hb
  simp only [Prod.mk.injEq] at hb ⊢
  exact hbound A0 B0 hb

/-- The same averaging works within any fixed positive-probability vertex
boundary record, including boundary vertices retained by the frame. -/
theorem complement_bounds_boundary [Nonempty (TerminalState V r M ell)]
    (j : ℕ) (f : Frame r original) (b : BoundaryRecord V)
    (hb : b.Feasible (r:=r) (M:=M) (ell:=ell) j)
    (Bad : Outcome V r M ell→Prop) (q : ℝ)
    (hbound : ∀ A0 B0 : SimpleHypergraph V,
      ∀ he : 0 < (extensionLaw r M ell).event
        (EdgeComplementEvent r M ell j (samplingUniverse f b.vertices) A0 B0),
      ((extensionLaw r M ell).condition
        (EdgeComplementEvent r M ell j (samplingUniverse f b.vertices) A0 B0) he).event Bad ≤ q) :
    (b.law j hb).event Bad ≤ q := by
  apply conditional_event_le_of_refining_fibres (extensionLaw r M ell) (b.event j) Bad
    (fun ω => (ω.1.val\samplingUniverse f b.vertices,
      extensionState ω.1 ω.2 j\samplingUniverse f b.vertices)) hb q
  · intro ω₀ ω hω₀ heq
    exact samplingComplement_refines_record M ell j f b _ _ ω₀ hω₀ ⟨rfl,rfl⟩ ω
      (Prod.mk.inj heq)
  · rintro ⟨A0,B0⟩ he
    simp only [Prod.mk.injEq] at he ⊢
    exact hbound A0 B0 he
end CandidateBalance
end LooseHamilton
