module

public import HittingTimeLooseHamilton.AuxiliaryFrameLabels
public import HittingTimeLooseHamilton.ActiveDirectedCounting
public import HittingTimeLooseHamilton.CompletionModels

public section

noncomputable section
namespace LooseHamilton
namespace AuxiliaryFrame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A prescribed start in the same cycle witness used for all directions. -/
@[expose] def Starts {r : ℕ} {S : Finset V} {M E : Finset (Finset V)}
    (C : MixedCycleOnWitness r S M E) (p : V × V) : Prop :=
  ∃ m : ↥M, m.val = {p.1,p.2} ∧ C.junction (C.slot.symm (.inl m)) = p.1

namespace Frame
variable {r : ℕ} {original : Finset (Finset V)}
@[expose] def active (F : Frame r original) := F.val.active
@[expose] def markers (F : Frame r original) := F.val.markers original
/-- The prohibition is the original port set, never the changing marker ports. -/
@[expose] def rawHost (F : Frame r original) (host : Finset (Finset V)) : Finset (Finset V) :=
  (host ∩ allowedEdges r (originalPorts original)).filter (fun e => e ⊆ F.active)

@[expose] def Directed (F : Frame r original) {S : Finset V} {M E : Finset (Finset V)}
    (C : MixedCycleOnWitness r S M E) : Prop :=
  Starts C F.val.root ∧ ∀ p ∈ F.val.relative, Starts C p

/-- Actual connected ordinary edge sets; relative directions use a single orientation. -/
@[expose] def cycleFamily (F : Frame r original) (host : Finset (Finset V)) :
    Finset (Finset (Finset V)) := by
  classical
  exact (F.rawHost host).powerset.filter (fun E =>
    ∃ C : MixedCycleOnWitness r F.active F.markers E, F.Directed C)
@[expose] def cycleCount (F : Frame r original) (host : Finset (Finset V)) : ℕ :=
  (F.cycleFamily host).card
@[expose] def n (F : Frame r original) : ℕ := F.active.card
@[expose] def s (F : Frame r original) : ℕ := F.markers.card
@[expose] def k (F : Frame r original) : ℕ := (F.n-F.s)/(r-1)
@[expose] def m (F : Frame r original) (host : Finset (Finset V)) : ℕ := (F.rawHost host).card
@[expose] def mu (F : Frame r original) (host : Finset (Finset V)) : ℝ :=
  (r:ℝ)*F.m host/F.n

@[simp] theorem mem_cycleFamily (F : Frame r original) (host E : Finset (Finset V)) :
    E ∈ F.cycleFamily host ↔ E ⊆ F.rawHost host ∧
      ∃ C : MixedCycleOnWitness r F.active F.markers E, F.Directed C := by
  classical
  simp [cycleFamily]

theorem markers_nonempty (F : Frame r original) : F.markers.Nonempty := F.property.nonempty
theorem marker_budget (F : Frame r original) : MarkerBudget original F.markers :=
  F.val.marker_budget original

theorem rawHost_original_prohibition (F : Frame r original) (host : Finset (Finset V)) :
    F.rawHost host ⊆ allowedEdges r (originalPorts original) := by
  intro e he
  exact (mem_inter.mp (mem_filter.mp he).1).2

/-- Legal candidates are not required to be edges currently present in the raw host. -/
@[expose] def LegalCandidate (F : Frame r original) (c : Finset V × V × V) : Prop :=
  LegalPrivateCompletion r F.markers c.1 {c.2.1,c.2.2} ∧
  c.1 ∪ {c.2.1,c.2.2} ⊆ F.active ∧
  c.1 ∪ {c.2.1,c.2.2} ∈ allowedEdges r (originalPorts original)

@[expose] def candidates (F : Frame r original) : Finset (Finset V × V × V) := by
  classical
  exact univ.filter F.LegalCandidate

/-- Directed completions preserve all frame directions and prescribe the fresh pair start. -/
@[expose] def completionFamily (F : Frame r original) (host : Finset (Finset V))
    (c : Finset V × V × V) : Finset (Finset (Finset V)) := by
  classical
  exact (F.rawHost host).powerset.filter (fun E =>
    ∃ C : MixedCycleOnWitness r (F.active \ c.1) (insert {c.2.1,c.2.2} F.markers) E,
      F.Directed C ∧ Starts C c.2)
@[expose] def completionCount (F : Frame r original) (host : Finset (Finset V))
    (c : Finset V × V × V) : ℕ := (F.completionFamily host c).card

@[expose] def candidateBad (F : Frame r original) (host : Finset (Finset V)) (alpha : ℝ) : Prop :=
  alpha * (F.candidates.card : ℝ) <
    ((F.candidates.filter (fun c =>
      |(F.completionCount host c : ℝ) /
        ((F.cycleCount host : ℝ) / (((r:ℝ)-1)^2 * F.mu host)) - 1| > alpha)).card : ℝ)

end Frame
end AuxiliaryFrame
end LooseHamilton
