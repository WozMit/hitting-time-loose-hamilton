module

public import HittingTimeLooseHamilton.FrameCompletionInstanceBiased
public import HittingTimeLooseHamilton.CoreRestrictionDegrees

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

@[simp] theorem completionEntropyInstance_host_card (F : Frame r original)
    (H : SimpleHypergraph V) (c : Finset V × V × V) (hc : F.LegalCandidate c)
    (hY : (F.completionFamily H c).Nonempty) :
    (F.completionEntropyInstance H c hc hY).host.card=(F.completionRawHost H c).card :=
  F.completionNumberedEdges_card c _ (fun _ he => (mem_filter.mp he).2)

@[simp] theorem completionEntropyInstance_degree (F : Frame r original)
    (H : SimpleHypergraph V) (c : Finset V × V × V) (hc : F.LegalCandidate c)
    (hY : (F.completionFamily H c).Nonempty) (v : ↥(F.completionActive c)) :
    vertexDegree (F.completionEntropyInstance H c hc hY).host (F.completionNumbering c v) =
      vertexDegree (F.completionRawHost H c) v.val := by
  change vertexDegree (vertexEdges (F.completionNumbering c) _) _ = _
  rw [vertexEdges_vertexDegree]
  exact vertexDegree_restrictEdges _ _ (fun _ he => (mem_filter.mp he).2) v

/-- Host maximum-degree bounds transport to every numbered contracted vertex. -/
theorem completionEntropyInstance_degree_le (F : Frame r original)
    (H : SimpleHypergraph V) (c : Finset V × V × V) (hc : F.LegalCandidate c)
    (hY : (F.completionFamily H c).Nonempty) (d : ℝ)
    (hd : ∀v, (vertexDegree (F.completionRawHost H c) v:ℝ) ≤ d) :
    ∀v, (vertexDegree (F.completionEntropyInstance H c hc hY).host v:ℝ) ≤ d := by
  intro v
  obtain ⟨u,rfl⟩ := (F.completionNumbering c).surjective v
  rw [F.completionEntropyInstance_degree H c hc hY u]
  exact hd u.val
end LooseHamilton.AuxiliaryFrame.Frame
