module

public import HittingTimeLooseHamilton.PrivateBadRootCounting

public section

/-! Reconstruction turns image coverage into an actual injection after
colliding edges are removed. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_private_reconstruction_injection (x t : V)
    (Γ collisions : SimpleHypergraph V) (B : Finset (Finset V × V × V))
    (hsub : Γ ⊆ B.image (privateCandidateRootEdge x t) ∪ collisions) :
    ∃ f : ↥(Γ \ collisions) → ↥B,
      Function.Injective f ∧ ∀ e, privateCandidateRootEdge x t (f e).val = e.val := by
  classical
  have hex : ∀ e : ↥(Γ \ collisions),
      ∃ a : ↥B, privateCandidateRootEdge x t a.val = e.val := by
    intro e
    have hi := hsub (mem_sdiff.mp e.property).1
    have hb : e.val ∈ B.image (privateCandidateRootEdge x t) :=
      (mem_union.mp hi).resolve_right (mem_sdiff.mp e.property).2
    obtain ⟨a,ha,he⟩ := mem_image.mp hb
    exact ⟨⟨a,ha⟩,he⟩
  choose f hf using hex
  refine ⟨f,?_,hf⟩
  intro e e' he
  apply Subtype.ext
  rw [← hf e, ← hf e', he]

end LooseHamilton
