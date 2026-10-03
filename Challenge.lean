module

public import Mathlib

public section

/-!
# The hitting time for loose Hamilton cycles in r-graphs

Fix r >= 3. Order all r-element subsets of n labelled vertices
uniformly at random, and reveal them one at a time. As n tends to
infinity through multiples of r − 1, with probability tending to one,
a loose Hamilton cycle first appears exactly when the last isolated
vertex disappears. That is, the first time the minimum degree of the
hypergraph is 1.  -/

noncomputable section
namespace LooseHamilton
open Finset

section
variable {State : Type*}

/-- First time in 0,...,K at which P holds; infinity if the set is
empty. -/
@[expose] def firstTime (K : ℕ) (H : ℕ → State) (P : State → Prop) : WithTop ℕ := by
  classical
  exact ((Finset.range (K + 1)).filter fun t => P (H t)).min

end

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A simple hypergraph is a finite set of vertex subsets. -/
abbrev SimpleHypergraph (V : Type*) := Finset (Finset V)

/-- All r-element subsets of the vertex set. -/
@[expose] def completeEdges (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :
    SimpleHypergraph V := Finset.univ.filter (fun e => e.card = r)

/-- An edge of the complete r-uniform hypergraph. -/
abbrev Edge (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :=
  ↥(completeEdges V r)

/-- A permutation of all possible edges; uniform permutations give the
random process. -/
abbrev EdgeOrder (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :=
  Equiv.Perm (Edge V r)

/-- Zero-based rank of an edge in the chosen order. -/
@[expose] def edgeRank {r : ℕ} (σ : EdgeOrder V r) (e : Edge V r) : ℕ :=
  (Fintype.equivFin (Edge V r) (σ e)).val

/-- The hypergraph after the first t edges have appeared. -/
@[expose] def processState {r : ℕ} (σ : EdgeOrder V r) (t : ℕ) : SimpleHypergraph V :=
  ((Finset.univ : Finset (Edge V r)).filter (fun e => edgeRank σ e < t)).image
    Subtype.val

/-- Number of edges incident to a vertex. -/
@[expose] def vertexDegree (G : SimpleHypergraph V) (v : V) : ℕ :=
  (G.filter fun e => v ∈ e).card

/-- Minimum degree at least one, equivalently no isolated vertices. -/
@[expose] def NoIsolated (host : SimpleHypergraph V) : Prop :=
  ∀ v : V, 1 ≤ vertexDegree host v

/-- A cyclic presentation of a spanning loose cycle, allowing marked
pairs.  Distinct junctions occur in cyclic order. Each ordinary edge
consists of its two consecutive junctions and r - 2 private
vertices. Private blocks are pairwise disjoint, avoid the junctions,
and cover all remaining vertices.  Slots enumerate the edges exactly
once. The main theorem uses no marked pairs; the more general
presentation is needed inside the proof. -/
structure MixedCycleWitness (r : ℕ) (markers edges : Finset (Finset V)) where
  length : ℕ
  length_ge : 3 ≤ length
  junction : Fin length → V
  junction_injective : Function.Injective junction
  junction_next_ne : ∀ i, junction i ≠ junction (finRotate length i)
  slot : Fin length ≃ ({e // e ∈ markers} ⊕ {e // e ∈ edges})
  privateBlock : {e // e ∈ edges} → Finset V
  private_card : ∀ e, (privateBlock e).card = r - 2
  private_disjoint : Pairwise (fun e f => Disjoint (privateBlock e) (privateBlock f))
  junction_private_disjoint : ∀ e, Disjoint (univ.image junction) (privateBlock e)
  cover : univ = univ.image junction ∪ univ.biUnion privateBlock
  marked_matching : (markers : Set (Finset V)).PairwiseDisjoint id
  slot_edge : ∀ i, match slot i with
    | Sum.inl e => e.val = {junction i, junction (finRotate length i)}
    | Sum.inr e => e.val = {junction i, junction (finRotate length i)} ∪ privateBlock e

/-- Existence of the cyclic presentation above. -/
@[expose] def IsMixedCycle (r : ℕ) (markers edges : Finset (Finset V)) : Prop :=
  Nonempty (MixedCycleWitness r markers edges)

/-- A spanning loose Hamilton cycle contained in the host, with no marked pairs. -/
@[expose] def HasLooseHamiltonCycle (r : ℕ) (host : SimpleHypergraph V) : Prop :=
  ∃ edges : Finset (Finset V), edges ⊆ host ∧ IsMixedCycle r ∅ edges

/-- First time the minimum degree is at least one. -/
@[expose] def tauOne {r : ℕ} (σ : EdgeOrder V r) : WithTop ℕ :=
  firstTime (completeEdges V r).card (processState σ) NoIsolated

/-- First time a spanning loose Hamilton cycle exists. -/
@[expose] def tauLooseHamilton {r : ℕ} (σ : EdgeOrder V r) : WithTop ℕ :=
  firstTime (completeEdges V r).card (processState σ) (HasLooseHamiltonCycle r)

end LooseHamilton

namespace HittingTimeLooseHamilton

/-- Proportion of complete edge orders for which the two hitting times
are equal. -/
@[expose] def hittingTimeProbability (n r : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun σ : LooseHamilton.EdgeOrder (Fin n) r =>
    LooseHamilton.tauLooseHamilton σ = LooseHamilton.tauOne σ)).card : ℝ) /
      Fintype.card (LooseHamilton.EdgeOrder (Fin n) r)

/-- For every fixed r >= 3, with probability tending to 1, a loose
Hamilton cycle appears exactly when the last isolated vertex
disappears. Writing n=(r-1)q parametrises all vertex counts satisfying
the necessary divisibility condition. -/
theorem main_result (r : ℕ) (hr : 3 ≤ r) :
    Filter.Tendsto (fun q : ℕ => hittingTimeProbability ((r - 1) * q) r)
      Filter.atTop (nhds 1) := by
  sorry

end HittingTimeLooseHamilton
