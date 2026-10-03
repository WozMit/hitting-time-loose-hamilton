module

public import HittingTimeLooseHamilton.VertexEquivInvariants
public import HittingTimeLooseHamilton.UniformConditionalEquivalence

public section

/-! Vertex relabelling of the degree-conditioned terminal law and its parameters. -/
noncomputable section
namespace LooseHamilton.HittingTimeCore
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Relabel a terminal state and the degree threshold at the same time. -/
@[expose] def terminalMap (σ : V ≃ W) (r m : ℕ) (ell : V → ℕ)
    (F : TerminalState V r m ell) : TerminalState W r m (fun w => ell (σ.symm w)) := by
  refine ⟨vertexEdges σ F.val, ?_, by simpa using F.property.2.1, ?_⟩
  · intro e he
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    rw [mem_completeEdges,card_image_of_injective _ σ.injective]
    exact (mem_completeEdges _ _).mp (F.property.1 ha)
  · intro w
    obtain ⟨v,rfl⟩ := σ.surjective w
    simpa using F.property.2.2 v

/-- Exact equivalence of the finite conditioned families. -/
@[expose] def terminalEquiv (σ : V ≃ W) (r m : ℕ) (ell : V → ℕ) :
    TerminalState V r m ell ≃ TerminalState W r m (fun w => ell (σ.symm w)) where
  toFun := terminalMap σ r m ell
  invFun := fun F => by
    have G := terminalMap σ.symm r m (fun w => ell (σ.symm w)) F
    exact ⟨G.val,G.property.1,G.property.2.1,by simpa using G.property.2.2⟩
  left_inv := by
    intro F
    apply Subtype.ext
    simp [terminalMap,vertexEdges,image_image,Function.comp_def]
  right_inv := by
    intro F
    apply Subtype.ext
    simp [terminalMap,vertexEdges,image_image,Function.comp_def]

@[simp] theorem terminalEquiv_val (σ : V ≃ W) (r m : ℕ) (ell : V → ℕ)
    (F : TerminalState V r m ell) : (terminalEquiv σ r m ell F).val = vertexEdges σ F.val := rfl

/-- Uniform terminal probabilities are invariant under the concrete equivalence. -/
theorem terminal_event_relabel (σ : V ≃ W) (r m : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r m ell)]
    [Nonempty (TerminalState W r m (fun w => ell (σ.symm w)))]
    (P : TerminalState W r m (fun w => ell (σ.symm w)) → Prop) :
    (terminalLaw r m ell).event (fun F => P (terminalEquiv σ r m ell F)) =
      (terminalLaw r m (fun w => ell (σ.symm w))).event P := by
  exact FiniteEntropy.Law.uniform_event_equiv (terminalEquiv σ r m ell) P

/-- Every admissibility condition, including feasibility, survives relabelling. -/
theorem admissible_relabel (σ : V ≃ W) {r m : ℕ} {ell : V → ℕ}
    {M : Finset (Finset V)} {offset : ℝ} (h : CoreAdmissible r m ell M offset) :
    CoreAdmissible r m (fun w => ell (σ.symm w)) (vertexEdges σ M) offset := by
  have hn := Fintype.card_congr σ
  refine ⟨h.uniformity,h.marker_matching.vertexEdges σ,?_,?_,?_,?_,h.offset_nonneg,?_,?_⟩
  · simpa using h.markers_nonempty
  · simpa [hn] using h.markers_small
  · simpa [hn] using h.divisibility
  · simpa [meanDegree,hn] using h.density_window
  · intro w
    simpa [lowerDegreeBase,hn] using h.offsets (σ.symm w)
  · obtain ⟨F⟩ := h.feasible
    exact ⟨terminalEquiv σ r m ell F⟩

end LooseHamilton.HittingTimeCore
