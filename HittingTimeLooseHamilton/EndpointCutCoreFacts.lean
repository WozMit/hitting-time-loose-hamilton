module

public import HittingTimeLooseHamilton.EndpointCutModels

public section

/-! # Actual surviving-host interpretation and erasure recovery for endpoint cuts -/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An independent Type I core cannot contain the removed edge: it omits `y`. -/
theorem endpointCutCoreI_edge_not_mem {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z : V} {l : EndpointCutLabelI V} {F : Finset (Finset V)}
    (hF : F ∈ endpointCutCoreFamilyI r M G P y z l) : l.edge y ∉ F := by
  obtain ⟨⟨C⟩, _⟩ := mem_endpointCutCoreFamilyI _ _ _ _ _ _ _ _ |>.mp hF
  intro he
  have hy : y ∈ l.edge y := by simp [EndpointCutLabelI.edge]
  have hs := C.edge_subset_active he hy
  simpa [EndpointCutLabelI.deleted] using hs

/-- Hence inserting and then erasing the remembered edge recovers every core. -/
theorem endpointCutCoreI_erase_insert {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z : V} {l : EndpointCutLabelI V} {F : Finset (Finset V)}
    (hF : F ∈ endpointCutCoreFamilyI r M G P y z l) :
    (insert (l.edge y) F).erase (l.edge y) = F :=
  erase_insert (endpointCutCoreI_edge_not_mem hF)

/-- Both remembered Type II edges meet vertices deleted from the independent core. -/
theorem endpointCutCoreII_edges_not_mem {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z : V} {l : EndpointCutLabelII V} {F : Finset (Finset V)}
    (hF : F ∈ endpointCutCoreFamilyII r M G P y z l) :
    l.firstEdge y ∉ F ∧ l.secondEdge ∉ F := by
  obtain ⟨⟨C⟩, _⟩ := mem_endpointCutCoreFamilyII _ _ _ _ _ _ _ _ |>.mp hF
  constructor
  · intro he
    have hy : y ∈ l.firstEdge y := by simp [EndpointCutLabelII.firstEdge]
    have hs := C.edge_subset_active he hy
    simpa [EndpointCutLabelII.deleted] using hs
  · intro he
    have hu : l.2.1 ∈ l.secondEdge := by simp [EndpointCutLabelII.secondEdge]
    have hs := C.edge_subset_active he hu
    simpa [EndpointCutLabelII.deleted] using hs

/-- Type II expansion remembers enough to recover its core by two erasures. -/
theorem endpointCutCoreII_erase_insert {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z : V} {l : EndpointCutLabelII V} {F : Finset (Finset V)}
    (hF : F ∈ endpointCutCoreFamilyII r M G P y z l) :
    ((insert (l.firstEdge y) (insert l.secondEdge F)).erase (l.firstEdge y)).erase
      l.secondEdge = F := by
  obtain ⟨h₁, h₂⟩ := endpointCutCoreII_edges_not_mem hF
  by_cases he : l.firstEdge y = l.secondEdge
  · simp [he, h₂]
  · rw [erase_insert (by simp [he, h₁]), erase_insert h₂]

end LooseHamilton
