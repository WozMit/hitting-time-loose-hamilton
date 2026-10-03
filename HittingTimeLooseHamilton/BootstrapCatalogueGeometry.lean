module

public import HittingTimeLooseHamilton.BootstrapCatalogueCounts

public section

/-! Geometry-only gates for the fixed raw catalogue. Gates never inspect a host.
In particular, registering a cut does not require its edges to be present.
Additional geometry conditions may be supplied when actual tests are constructed.
Invalid geometry is sent to a fixed dummy value, without removing its index. -/
noncomputable section
namespace LooseHamilton.BootstrapCatalogue
open Finset RootFreeTestIndexing
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex named by a residual label must survive the base deletion. -/
@[expose] def support {r : ℕ} : BaseLabel r V → Finset V
  | .inl (S,x,y,z,t) => S.val ∪ {x,y,z,t}
  | .inr (.inl (P,y,z,t,a,R)) => P.val ∪ R.val ∪ {y,z,t,a}
  | .inr (.inr (P,y,z,t,u,v,a,R,Q)) => P.val ∪ R.val ∪ Q.val ∪ {y,z,t,u,v,a}

/-- Only source-endpoint geometry is tested here; cut and target coincidences
are deliberately not ruled out by a blanket distinctness requirement. -/
@[expose] def sourceDistinct {r : ℕ} : BaseLabel r V → Prop
  | .inl (S,x,y,z,_t) => x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ Disjoint S.val {x,y,z}
  | .inr (.inl (P,y,z,_t,_a,_R)) => y ≠ z ∧ Disjoint P.val {y,z}
  | .inr (.inr (P,y,z,_t,_u,_v,_a,_R,_Q)) => y ≠ z ∧ Disjoint P.val {y,z}

@[expose] def portSourceDistinct {r : ℕ} (l : PortLabel r V) : Prop :=
  l.2.1 ≠ l.2.2.1 ∧ Disjoint l.1.val {l.2.1,l.2.2.1}

/-- Static survival and source distinctness, determined by the original
matching and raw label alone. The original-port family is on all of V. -/
@[expose] def admissible {r : ℕ} {M : Finset (Finset V)} : Geometry r M → Prop
  | .inl (b,l) => support l ⊆ BootstrapBases.active b ∧ sourceDistinct l
  | .inr l => portSourceDistinct l

@[expose] def root {r : ℕ} {M : Finset (Finset V)} : Geometry r M → V
  | .inl (_, .inl l) => l.2.1
  | .inl (_, .inr (.inl l)) => l.2.1
  | .inl (_, .inr (.inr l)) => l.2.1
  | .inr l => l.2.1

/-- Raw labels are never filtered out of the catalogue by eligibility. -/
@[expose] def baseIndex {r : ℕ} {M : Finset (Finset V)} (b : BootstrapBases.Base M)
    (l : BaseLabel r V) (j : Fin ((Fintype.card V)^r+1)) : Index r M :=
  (.inl (b,l),j)

@[expose] def portIndex {r : ℕ} {M : Finset (Finset V)} (l : PortLabel r V)
    (j : Fin ((Fintype.card V)^r+1)) : Index r M := (.inr l,j)

@[simp] theorem baseIndex_geometry {r : ℕ} {M : Finset (Finset V)}
    (b : BootstrapBases.Base M) (l : BaseLabel r V) (j) :
    (baseIndex b l j).1 = Sum.inl (b,l) := rfl

@[simp] theorem portIndex_geometry {r : ℕ} {M : Finset (Finset V)}
    (l : PortLabel r V) (j) : (portIndex (M := M) l j).1 = Sum.inr l := rfl

theorem baseIndex_injective {r : ℕ} {M : Finset (Finset V)}
    {b c : BootstrapBases.Base M} {l k : BaseLabel r V} {i j}
    (h : baseIndex b l i = baseIndex c k j) : b = c ∧ l = k ∧ i = j := by
  simpa [baseIndex, Prod.mk.injEq, and_assoc] using h

theorem portIndex_injective {r : ℕ} {M : Finset (Finset V)}
    {l k : PortLabel r V} {i j}
    (h : portIndex (M := M) l i = portIndex k j) : l = k ∧ i = j := by
  simpa [portIndex] using h

theorem baseIndex_ne_portIndex {r : ℕ} {M : Finset (Finset V)}
    (b : BootstrapBases.Base M) (l : BaseLabel r V) (p : PortLabel r V) (i j) :
    baseIndex b l i ≠ portIndex p j := by simp [baseIndex, portIndex]

/-- Every catalogue entry is a base label or a full-space original-port label,
with its ambient time. No observation is involved in this exhaustive split. -/
theorem index_cases {r : ℕ} {M : Finset (Finset V)} (i : Index r M) :
    (∃ b l j, i = baseIndex b l j) ∨ (∃ l j, i = portIndex l j) := by
  rcases i with ⟨⟨b,l⟩ | l,j⟩
  · exact Or.inl ⟨b,l,j,rfl⟩
  · exact Or.inr ⟨l,j,rfl⟩

theorem root_mem_support {r : ℕ} {M : Finset (Finset V)}
    (b : BootstrapBases.Base M) (l : BaseLabel r V) : root (.inl (b,l)) ∈ support l := by
  rcases l with l | (l | l) <;> simp [root, support]

theorem admissible_root_survives {r : ℕ} {M : Finset (Finset V)}
    {b : BootstrapBases.Base M} {l : BaseLabel r V}
    (h : admissible (.inl (b,l))) : root (.inl (b,l)) ∈ BootstrapBases.active b :=
  h.1 (root_mem_support b l)

theorem not_admissible_of_deleted {r : ℕ} {M : Finset (Finset V)}
    {b : BootstrapBases.Base M} {l : BaseLabel r V} {v : V}
    (hv : v ∈ support l) (hd : v ∈ BootstrapBases.deleted b) :
    ¬ admissible (.inl (b,l)) := by
  intro h
  have := h.1 hv
  exact (mem_sdiff.mp this).2 hd

theorem private_repeated_root_invalid {r : ℕ} {M : Finset (Finset V)}
    (b : BootstrapBases.Base M) (S : Block (r-3) V) (x z t : V) :
    ¬ admissible (.inl (b,.inl (S,x,x,z,t))) := by
  simp [admissible, sourceDistinct]

theorem endpointI_repeated_endpoint_invalid {r : ℕ} {M : Finset (Finset V)}
    (b : BootstrapBases.Base M) (P R : Block (r-2) V) (y t a : V) :
    ¬ admissible (.inl (b,.inr (.inl (P,y,y,t,a,R)))) := by
  simp [admissible, sourceDistinct]

theorem endpointII_repeated_endpoint_invalid {r : ℕ} {M : Finset (Finset V)}
    (b : BootstrapBases.Base M) (P R Q : Block (r-2) V) (y t u v a : V) :
    ¬ admissible (.inl (b,.inr (.inr (P,y,y,t,u,v,a,R,Q)))) := by
  simp [admissible, sourceDistinct]

theorem port_repeated_endpoint_invalid {r : ℕ} {M : Finset (Finset V)}
    (P : Block (r-2) V) (a u : V) :
    ¬ admissible (M := M) (.inr (P,a,a,u)) := by
  simp [admissible, portSourceDistinct]

/-- A fixed dummy assignment at the geometry level. Actual test constructors
will instantiate α in the next item. Neither gate takes an observed graph. -/
@[expose] def assign {r : ℕ} {M : Finset (Finset V)} {α : Type*}
    (extraGeometry : Geometry r M → Prop) (dummy : Geometry r M → α)
    (make : Geometry r M → α) (g : Geometry r M) : α := by
  classical
  exact if admissible g ∧ extraGeometry g then make g else dummy g

theorem assign_of_admissible {r : ℕ} {M : Finset (Finset V)} {α : Type*}
    (extraGeometry : Geometry r M → Prop) (dummy make : Geometry r M → α)
    {g : Geometry r M} (h : admissible g) (he : extraGeometry g) :
    assign extraGeometry dummy make g = make g := by simp [assign,h,he]

theorem assign_of_invalid {r : ℕ} {M : Finset (Finset V)} {α : Type*}
    (extraGeometry : Geometry r M → Prop) (dummy make : Geometry r M → α)
    {g : Geometry r M} (h : ¬ admissible g) :
    assign extraGeometry dummy make g = dummy g := by simp [assign,h]

theorem assign_of_extra_invalid {r : ℕ} {M : Finset (Finset V)} {α : Type*}
    (extraGeometry : Geometry r M → Prop) (dummy make : Geometry r M → α)
    {g : Geometry r M} (h : ¬ extraGeometry g) :
    assign extraGeometry dummy make g = dummy g := by simp [assign,h]

end LooseHamilton.BootstrapCatalogue
