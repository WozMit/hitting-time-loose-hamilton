module

public import HittingTimeLooseHamilton.OrderedPathKernel
public import HittingTimeLooseHamilton.ExtensionPathCoordinates

public section
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
local instance {A : Type*} [Fintype A] : Nonempty (FiniteOrder A) := ⟨Fintype.equivFin A⟩
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact full-path kernel conditional on a specified terminal graph. -/
theorem process_extension_path_kernel {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (P : (ℕ → SimpleHypergraph V) → Prop) :
    (processLaw V r).event (fun σ => processState σ M = F.val ∧
      P (fun j => processState σ (max M j))) =
    (1 / (((Fintype.card V).choose r).choose M : ℝ)) *
      (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
        (fun σ => P (extensionState F σ)) := by
  classical
  let K := liftEdges r F.val
  let Q : (ℕ → Finset (Edge V r)) → Prop := fun S => P (fun j => (S j).image Subtype.val)
  have hK : K.card = M := (liftEdges_card F.property.1).trans F.property.2.1
  have he : (fun σ : EdgeOrder V r => processState σ M = F.val ∧
      P (fun j => processState σ (max M j))) =
      (fun σ => orderPrefix (orderRankEquiv (Edge V r) σ) K.card = K ∧
        Q (fun j => orderPrefix (orderRankEquiv (Edge V r) σ) (max K.card j))) := by
    funext σ
    apply propext
    rw [hK]
    apply and_congr (processState_eq_iff_rank_prefix F.property.1 σ M)
    rfl
  change (FiniteEntropy.uniform : FiniteEntropy.Law (EdgeOrder V r)).event _ = _
  rw [he,FiniteEntropy.Law.uniform_event_equiv (orderRankEquiv (Edge V r))
    (fun σ => orderPrefix σ K.card = K ∧ Q (fun j => orderPrefix σ (max K.card j))),ordered_path_kernel]
  have ht := FiniteEntropy.Law.uniform_event_equiv (outsideRankEquiv F)
    (fun τ => Q (outsideExtensionPath K τ))
  have hext (σ : MissingOrder V r M) : Q (outsideExtensionPath K (outsideRankEquiv F σ)) =
      P (extensionState F σ) := by
    unfold Q
    congr 1
    funext j
    exact outsideExtensionPath_eq_extensionState F σ j
  simp_rw [hext] at ht
  rw [← ht,hK]
  congr 1
  simp only [Fintype.card_coe,completeEdges_card]
end LooseHamilton
