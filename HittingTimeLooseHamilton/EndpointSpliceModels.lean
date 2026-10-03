module

public import HittingTimeLooseHamilton.EndpointCutModels
public import HittingTimeLooseHamilton.ActiveDirectedCompletions

public section

/-! Independent labels and actual directed completion families for endpoint splicing.
The host remains fixed throughout: only the surviving vertex set changes. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A private block and the endpoint of the edge incident to the deleted vertex. -/
abbrev EndpointSpliceInnerLabel (V : Type*) := Finset V × V

/-- Freshness conditions for a single inner summand. `D` is the cut's deleted set
and `a` its remaining endpoint. These conditions only concern labels and host
membership; no existence or injectivity assertion is included. -/
structure EndpointSpliceLegal (r : ℕ) (M G : Finset (Finset V))
    (P D : Finset V) (y z a t : V) (Q : Finset V) (v : V) : Prop where
  private_card : Q.card = r - 2
  newEndpoint_fresh : v ∉ P ∪ D ∪ originalPorts M ∪ {y, z, a, t}
  target_fresh : t ∉ P ∪ D ∪ originalPorts M ∪ {y, z, a}
  private_disjoint : Disjoint Q (P ∪ D ∪ originalPorts M ∪ {a, z, v, t})
  edge_mem : {y, v} ∪ Q ∈ G

abbrev EndpointSpliceLegalI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelI V) (b : EndpointSpliceInnerLabel V) :=
  EndpointSpliceLegal r M G P (l.deleted y) y z l.1 t b.1 b.2
abbrev EndpointSpliceLegalII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelII V) (b : EndpointSpliceInnerLabel V) :=
  EndpointSpliceLegal r M G P (l.deleted y) y z l.2.2.1 t b.1 b.2

@[expose] def endpointSpliceLabelsI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelI V) : Finset (EndpointSpliceInnerLabel V) := by
  classical
  exact univ.filter (EndpointSpliceLegalI r M G P y z t l)
@[expose] def endpointSpliceLabelsII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelII V) : Finset (EndpointSpliceInnerLabel V) := by
  classical
  exact univ.filter (EndpointSpliceLegalII r M G P y z t l)

@[simp] theorem mem_endpointSpliceLabelsI (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z t : V) (l : EndpointCutLabelI V) (b : EndpointSpliceInnerLabel V) :
    b ∈ endpointSpliceLabelsI r M G P y z t l ↔ EndpointSpliceLegalI r M G P y z t l b := by
  simp [endpointSpliceLabelsI]
@[simp] theorem mem_endpointSpliceLabelsII (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z t : V) (l : EndpointCutLabelII V) (b : EndpointSpliceInnerLabel V) :
    b ∈ endpointSpliceLabelsII r M G P y z t l ↔ EndpointSpliceLegalII r M G P y z t l b := by
  simp [endpointSpliceLabelsII]

@[expose] def endpointSpliceInputFamilyI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelI V) (b : EndpointSpliceInnerLabel V) :
    Finset (Finset (Finset V)) :=
  directedCycleOnFamily r (univ \ (P ∪ l.deleted y ∪ b.1))
    (insert {b.2, t} (l.markers M z)) G
    ⟨{l.1, z}, mem_insert_of_mem (mem_insert_self _ _)⟩
    ⟨{b.2, t}, mem_insert_self _ _⟩ l.1 b.2

@[expose] def endpointSpliceInputFamilyII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelII V) (b : EndpointSpliceInnerLabel V) :
    Finset (Finset (Finset V)) :=
  directedCycleOnFamily r (univ \ (P ∪ l.deleted y ∪ b.1))
    (insert {b.2, t} (l.markers M z)) G
    ⟨{l.2.2.1, z}, mem_insert_of_mem (mem_insert_self _ _)⟩
    ⟨{b.2, t}, mem_insert_self _ _⟩ l.2.2.1 b.2

end LooseHamilton
