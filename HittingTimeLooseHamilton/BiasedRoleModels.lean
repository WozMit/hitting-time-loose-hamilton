module

public import HittingTimeLooseHamilton.DirectedCompletions
public import HittingTimeLooseHamilton.EdgeRoles
public import HittingTimeLooseHamilton.PathRegularityModels
public import HittingTimeLooseHamilton.BenchmarkAlgebra

public section

/-! Actual rooted directed roles for Theorem 6.1. Private vertices are determined
by the host edge and its ordered endpoints; no artificial private colours occur. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The role `(e \ {u,v}; u → v)` occurs in the connected cycle oriented by the
specified initial endpoint of the fixed root marker. -/
@[expose] def rootedOrdinaryRole (r : ℕ) (markers edges : SimpleHypergraph V)
    (root : ↥markers) (a : ↥root.val) (e : Finset V) (u v : V) : Prop :=
  ∃ C : MixedCycleWitness r markers edges, C.markerStart root = a ∧
    ∃ he : e ∈ edges,
      C.junction (C.slot.symm (.inr ⟨e,he⟩)) = u ∧
      C.junction (finRotate C.length (C.slot.symm (.inr ⟨e,he⟩))) = v

lemma rootedOrdinaryRole_unique {r : ℕ} {markers edges : SimpleHypergraph V}
    (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val) (e : Finset V)
    {u v u' v' : V}
    (h : rootedOrdinaryRole r markers edges root a e u v)
    (h' : rootedOrdinaryRole r markers edges root a e u' v') : u=u' ∧ v=v' := by
  obtain ⟨C,hC,he,hu,hv⟩ := h
  obtain ⟨D,hD,he',hu',hv'⟩ := h'
  constructor
  · exact hu.symm.trans ((C.slot_start_eq_of_root D hr root (hC.trans hD.symm)
      (.inr ⟨e,he⟩)).trans hu')
  · exact hv.symm.trans ((C.slot_end_eq_of_root D hr root (hC.trans hD.symm)
      (.inr ⟨e,he⟩)).trans hv')

lemma rootedOrdinaryRole_mem {r : ℕ} {markers edges : SimpleHypergraph V}
    {root : ↥markers} {a : ↥root.val} {e : Finset V} {u v : V}
    (h : rootedOrdinaryRole r markers edges root a e u v) :
    e ∈ edges ∧ (u,v) ∈ e.offDiag := by
  obtain ⟨C,hC,he,hu,hv⟩ := h
  have hs := C.endpoint_mem_slotSet (C.slot.symm (.inr ⟨e,he⟩))
  simp only [MixedCycleWitness.slotSet, Equiv.apply_symm_apply, Sum.elim_inr] at hs
  refine ⟨he, mem_offDiag.mpr ⟨?_,?_,?_⟩⟩
  · simpa only [hu] using hs.1
  · simpa only [hv] using hs.2
  · intro huv
    exact C.junction_next_ne _ (hu.trans (huv.trans hv.symm))

lemma rootedOrdinaryRole_exists {r : ℕ} {markers edges : SimpleHypergraph V}
    (root : ↥markers) (a : ↥root.val) (hC : IsMixedCycle r markers edges)
    {e : Finset V} (he : e ∈ edges) :
    ∃ u v, rootedOrdinaryRole r markers edges root a e u v := by
  obtain ⟨C⟩ := hC
  let D := C.normalize root a
  exact ⟨_,_,D,C.normalize_markerStart root a,he,rfl,rfl⟩

/-- There are exactly r(r-1) directed roles on every r-edge. -/
lemma directedRole_card {r : ℕ} {e : Finset V} (he : e.card=r) :
    e.offDiag.card = r*(r-1) := by rw [offDiag_card,he, Nat.mul_sub_left_distrib, Nat.mul_one]

/-- The actual finite sample space of connected spanning mixed cycles. -/
abbrev BiasedCycleState (r : ℕ) (markers host : SimpleHypergraph V) :=
  ↥(cycleFamily r markers host ∅)

/-- Probability of a directed role under an arbitrary cycle law. -/
@[expose] def directedRoleProbability (r : ℕ) (markers host : SimpleHypergraph V)
    (root : ↥markers) (a : ↥root.val)
    (p : FiniteEntropy.Law (BiasedCycleState r markers host))
    (e : Finset V) (u v : V) : ℝ :=
  p.event (fun E => rootedOrdinaryRole r markers E.val root a e u v)

/-- Left side of the printed entropy-balance conclusion, on existing edges
avoiding all original marked ports. -/
@[expose] def biasedRoleDeviation (r : ℕ) (markers host : SimpleHypergraph V)
    (root : ↥markers) (a : ↥root.val)
    (p : FiniteEntropy.Law (BiasedCycleState r markers host)) : ℝ :=
  ∑ e ∈ host.filter (fun e => Disjoint e (originalPorts markers)),
    ∑ uv ∈ e.offDiag,
      |directedRoleProbability r markers host root a p e uv.1 uv.2 -
        1/(((r:ℝ)-1)^2*meanDegree (V:=V) r host.card)|

/-- The exact six error terms of Theorem 6.1. -/
@[expose] def biasedRoleError (r N s : ℕ) (ξ δ η : ℝ) : ℝ :=
  ξ + δ + (s:ℝ)/N + η^(1/(2*((r:ℝ)-1))) +
    1/Real.log (1/η) + Real.log (N:ℝ)/N
end LooseHamilton
