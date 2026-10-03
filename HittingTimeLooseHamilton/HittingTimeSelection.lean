module

public import HittingTimeLooseHamilton.CoreSeparatedBlocks
public import HittingTimeLooseHamilton.CoreExposureProbability

public section

/-! A trace-only choice of exceptional blocks. The choice is defined on every
trace and does not condition on separation or on goodness of the unexposed host. -/
noncomputable section
namespace LooseHamilton.HittingTimeSelection
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def Valid (r : ℕ) (B : Finset V) (T : SimpleHypergraph V) : Prop :=
  Nonempty (CoreBlockFamily r T B)

@[expose] def blocks {r : ℕ} {B : Finset V} {T : SimpleHypergraph V} (h : Valid r B T) :
    CoreBlockFamily r T B := Classical.choice h

@[expose] def chooseD (r : ℕ) (B : Finset V) (T : SimpleHypergraph V) : Finset V :=
  by classical
     exact if h : Valid r B T then (blocks h).deleted else B

theorem chooseD_eq {r : ℕ} {B : Finset V} {T : SimpleHypergraph V} (h : Valid r B T) :
    chooseD r B T = (blocks h).deleted := by simp [chooseD,h]

theorem subset_chooseD (r : ℕ) (B : Finset V) (T : SimpleHypergraph V) :
    B ⊆ chooseD r B T := by
  classical
  unfold chooseD
  split
  · exact (blocks _).anchors_deleted
  · exact subset_refl _

/-- Change only the host of a block family; its selected edges and ports stay fixed. -/
@[expose] def enlarge {r : ℕ} {B : Finset V} {T F : SimpleHypergraph V}
    (C : CoreBlockFamily r T B) (hTF : T ⊆ F) : CoreBlockFamily r F B :=
  { C with edge_mem := fun v => hTF (C.edge_mem v) }

theorem traceOn_eq_exceptionalTrace (B : Finset V) (F : SimpleHypergraph V) :
    traceOn B F = exceptionalTrace B F := by
  ext e
  simp only [mem_traceOn,mem_exceptionalTrace]
  constructor
  · rintro ⟨he,h⟩
    obtain ⟨v,hv⟩ := not_disjoint_iff.mp h
    exact ⟨he,v,hv.2,hv.1⟩
  · rintro ⟨he,v,hvB,hve⟩
    exact ⟨he,not_disjoint_iff.mpr ⟨v,hve,hvB⟩⟩

/-- Every block family is already supported by the exposed exceptional trace. -/
@[expose] def restrictTrace {r : ℕ} {B : Finset V} {F : SimpleHypergraph V}
    (C : CoreBlockFamily r F B) : CoreBlockFamily r (traceOn B F) B :=
  by
    refine { C with edge_mem := ?_ }
    intro v
    rw [traceOn_eq_exceptionalTrace]
    exact mem_exceptionalTrace.mpr ⟨C.edge_mem v,v.val,v.property,C.anchor_mem v⟩

theorem valid_of_separated {r : ℕ} (hr : 3 ≤ r) {F : SimpleHypergraph V} {B : Finset V}
    (hF : F ⊆ completeEdges V r) (hpos : ∀ v ∈ B, 0 < vertexDegree F v)
    (hsep : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → ¬ shortBergeConnected F u v) :
    Valid r B (traceOn B F) :=
  ⟨restrictTrace (CoreBlockFamily.ofSeparated hr hF hpos hsep)⟩

/-- The actual chosen blocks in a full host inspect its exceptional trace only. -/
@[expose] def selected {r : ℕ} {B : Finset V} {F : SimpleHypergraph V}
    (h : Valid r B (traceOn B F)) : CoreBlockFamily r F B :=
  enlarge (blocks h) (filter_subset _ _)

theorem selected_deleted {r : ℕ} {B : Finset V} {F : SimpleHypergraph V}
    (h : Valid r B (traceOn B F)) :
    (selected h).deleted = chooseD r B (traceOn B F) := by
  rw [chooseD_eq h]; rfl

/-- Recover the chosen deletion from a full stopped exposure, without any
further condition on the host in that exposure fibre. -/
theorem choice_on_exposure {r m : ℕ} {B D : Finset V} {T : SimpleHypergraph V}
    (hBD : B ⊆ D) (hD : chooseD r B (traceOn B T) = D)
    (σ : EdgeOrder V r) (hσ : coreExposureEvent r m B D T σ) :
    chooseD r B (traceOn B (processState σ m)) = D :=
  exposure_deterministic_deletion hBD (chooseD r) hD σ hσ

end LooseHamilton.HittingTimeSelection
