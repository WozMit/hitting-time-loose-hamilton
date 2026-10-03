module

public import HittingTimeLooseHamilton.CoreExposureData
public import HittingTimeLooseHamilton.CoreRestrictionDegrees

public section

/-! The ambient surviving-core family is exactly the existing degree-conditioned
terminal family on the surviving vertex subtype. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges in an ambient core family have all their vertices in the surviving set. -/
theorem coreCompletion_supported {r m : ℕ} {D : Finset V} {T G : SimpleHypergraph V}
    (hG : G ∈ coreCompletionFamily r m D T) : ∀ e ∈ G, e ⊆ univ \ D := by
  have hg := (mem_coreCompletionFamily _ _ _ _ _).mp hG
  intro e he v hv
  exact mem_sdiff.mpr ⟨mem_univ _,fun hd => disjoint_left.mp (hg.2.1 e he) hv hd⟩

/-- Re-express a surviving core on its own vertex subtype. -/
@[expose] def coreCompletionToTerminal (r m : ℕ) (D : Finset V) (T : SimpleHypergraph V)
    (G : ↥(coreCompletionFamily r m D T)) :
    TerminalState ↥(univ \ D) r (m-T.card) (fun v => coreLowerBound D T v.val) := by
  have hg := (mem_coreCompletionFamily _ _ _ _ _).mp G.property
  have hs := coreCompletion_supported G.property
  refine ⟨restrictEdges (univ \ D) G.val, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    apply (mem_completeEdges _ _).mpr
    rw [← liftEdge_card (univ \ D),lift_restrictEdge _ _ (hs f hf)]
    exact (mem_completeEdges _ _).mp (hg.1 hf)
  · rw [restrictEdges_card_of_supported _ _ hs]
    exact hg.2.2.1
  · intro v
    rw [vertexDegree_restrictEdges _ _ hs]
    exact hg.2.2.2 v.val (mem_sdiff.mp v.property).2

/-- Embed a terminal state of the surviving vertex subtype into the original vertices. -/
@[expose] def terminalToCoreCompletion (r m : ℕ) (D : Finset V) (T : SimpleHypergraph V)
    (G : TerminalState ↥(univ \ D) r (m-T.card) (fun v => coreLowerBound D T v.val)) :
    ↥(coreCompletionFamily r m D T) := by
  refine ⟨G.val.image (liftEdge (univ \ D)), (mem_coreCompletionFamily _ _ _ _ _).mpr ?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    apply (mem_completeEdges _ _).mpr
    rw [liftEdge_card]
    exact (mem_completeEdges _ _).mp (G.property.1 hf)
  · intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    apply disjoint_left.mpr
    intro v hv hd
    exact (mem_sdiff.mp (liftEdge_subset _ _ hv)).2 hd
  · rw [card_image_of_injective _ (liftEdge_injective _)]
    exact G.property.2.1
  · intro v hv
    let w : ↥(univ \ D) := ⟨v,mem_sdiff.mpr ⟨mem_univ _,hv⟩⟩
    have h := vertexDegree_liftEdges (univ \ D) G.val w
    rw [h]
    exact G.property.2.2 w

/-- Exact identification of all ambient completions with Omega on the surviving vertices. -/
@[expose] def coreCompletionEquiv (r m : ℕ) (D : Finset V) (T : SimpleHypergraph V) :
    ↥(coreCompletionFamily r m D T) ≃
      TerminalState ↥(univ \ D) r (m-T.card) (fun v => coreLowerBound D T v.val) where
  toFun := coreCompletionToTerminal r m D T
  invFun := terminalToCoreCompletion r m D T
  left_inv G := by
    apply Subtype.ext
    exact liftEdges_restrictEdges _ _ (coreCompletion_supported G.property)
  right_inv G := by
    apply Subtype.ext
    exact restrictEdges_liftEdges _ _

@[simp] theorem coreCompletionEquiv_val (r m : ℕ) (D : Finset V) (T : SimpleHypergraph V)
    (G : ↥(coreCompletionFamily r m D T)) :
    (coreCompletionEquiv r m D T G).val = restrictEdges (univ \ D) G.val := rfl

@[simp] theorem coreCompletionEquiv_symm_val (r m : ℕ) (D : Finset V) (T : SimpleHypergraph V)
    (G : TerminalState ↥(univ \ D) r (m-T.card) (fun v => coreLowerBound D T v.val)) :
    ((coreCompletionEquiv r m D T).symm G).val = G.val.image (liftEdge (univ \ D)) := rfl
end LooseHamilton
