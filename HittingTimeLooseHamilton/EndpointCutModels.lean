module

public import HittingTimeLooseHamilton.CompletionModels

public section

/-! # Independent labelled endpoint-cut cores

The labels remember actual vertices and private blocks, not a cycle witness.
Every core family is the unrestricted actual-edge-set cycle family in the fixed
host restricted to its surviving vertices.
-/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Type I: the new endpoint and the private block of the removed edge. -/
abbrev EndpointCutLabelI (V : Type*) := V × Finset V
/-- Type II: the oriented old marker, new endpoint, and two private blocks. -/
abbrev EndpointCutLabelII (V : Type*) := V × V × V × Finset V × Finset V

namespace EndpointCutLabelI
variable (l : EndpointCutLabelI V)
@[expose] def edge (y : V) : Finset V := {y, l.1} ∪ l.2
@[expose] def deleted (y : V) : Finset V := insert y l.2
@[expose] def markers (M : Finset (Finset V)) (z : V) : Finset (Finset V) := insert {l.1, z} M
end EndpointCutLabelI

namespace EndpointCutLabelII
variable (l : EndpointCutLabelII V)
@[expose] def oldMarker : Finset V := {l.1, l.2.1}
@[expose] def firstEdge (y : V) : Finset V := {y, l.1} ∪ l.2.2.2.1
@[expose] def secondEdge : Finset V := {l.2.1, l.2.2.1} ∪ l.2.2.2.2
@[expose] def deleted (y : V) : Finset V := {y, l.1, l.2.1} ∪ l.2.2.2.1 ∪ l.2.2.2.2
@[expose] def markers (M : Finset (Finset V)) (z : V) : Finset (Finset V) :=
  insert {l.2.2.1, z} (M.erase l.oldMarker)
end EndpointCutLabelII

/-- Precisely the legal Type I labels: the far endpoint is ordinary and all
private vertices avoid the old ports, the deleted block and the named endpoints. -/
structure EndpointCutLegalI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelI V) : Prop where
  endpoint_fresh : l.1 ∉ P ∪ originalPorts M ∪ {y, z}
  private_card : l.2.card = r - 2
  private_disjoint : Disjoint l.2 (P ∪ originalPorts M ∪ {y, z, l.1})
  edge_mem : l.edge y ∈ G

/-- Legal Type II labels additionally remember the orientation of an old marker
and the two disjoint private blocks on either side of it. -/
structure EndpointCutLegalII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelII V) : Prop where
  oldMarker_mem : l.oldMarker ∈ M
  ports_ne : l.1 ≠ l.2.1
  endpoint_fresh : l.2.2.1 ∉ P ∪ originalPorts M ∪ {y, z}
  first_private_card : l.2.2.2.1.card = r - 2
  second_private_card : l.2.2.2.2.card = r - 2
  private_disjoint : Disjoint l.2.2.2.1 l.2.2.2.2
  first_private_disjoint : Disjoint l.2.2.2.1 (P ∪ originalPorts M ∪ {y, z, l.2.2.1})
  second_private_disjoint : Disjoint l.2.2.2.2 (P ∪ originalPorts M ∪ {y, z, l.2.2.1})
  firstEdge_mem : l.firstEdge y ∈ G
  secondEdge_mem : l.secondEdge ∈ G

@[expose] def endpointCutLabelsI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V) (y z : V) :
    Finset (EndpointCutLabelI V) := by
  classical
  exact univ.filter (EndpointCutLegalI r M G P y z)
@[expose] def endpointCutLabelsII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V) (y z : V) :
    Finset (EndpointCutLabelII V) := by
  classical
  exact univ.filter (EndpointCutLegalII r M G P y z)

@[simp] theorem mem_endpointCutLabelsI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelI V) :
    l ∈ endpointCutLabelsI r M G P y z ↔ EndpointCutLegalI r M G P y z l := by
  simp [endpointCutLabelsI]
@[simp] theorem mem_endpointCutLabelsII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelII V) :
    l ∈ endpointCutLabelsII r M G P y z ↔ EndpointCutLegalII r M G P y z l := by
  simp [endpointCutLabelsII]

@[expose] def endpointCutCoreFamilyI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelI V) : Finset (Finset (Finset V)) :=
  cycleOnFamily r (univ \ (P ∪ l.deleted y)) (l.markers M z) G

@[expose] def endpointCutCoreFamilyII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelII V) : Finset (Finset (Finset V)) :=
  cycleOnFamily r (univ \ (P ∪ l.deleted y)) (l.markers M z) G

@[simp] theorem mem_endpointCutCoreFamilyI (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z : V) (l : EndpointCutLabelI V) (F : Finset (Finset V)) :
    F ∈ endpointCutCoreFamilyI r M G P y z l ↔
      IsMixedCycleOn r (univ \ (P ∪ l.deleted y)) (l.markers M z) F ∧ F ⊆ G :=
  mem_cycleOnFamily _ _ _ _ _
@[simp] theorem mem_endpointCutCoreFamilyII (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z : V) (l : EndpointCutLabelII V) (F : Finset (Finset V)) :
    F ∈ endpointCutCoreFamilyII r M G P y z l ↔
      IsMixedCycleOn r (univ \ (P ∪ l.deleted y)) (l.markers M z) F ∧ F ⊆ G :=
  mem_cycleOnFamily _ _ _ _ _

end LooseHamilton
