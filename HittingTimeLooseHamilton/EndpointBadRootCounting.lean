module

public import HittingTimeLooseHamilton.RootTestRegistrations
public import HittingTimeLooseHamilton.PrivateReconstructionInjection

public section

/-! Endpoint root reconstruction preserves both directions: the candidate is
(Q,v,t), rooted at the cut marker a→z with relative direction v→t. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Endpoint candidates whose second directed endpoint is the selected target. -/
@[expose] def endpointBadCandidateFiber (bad : Finset (Finset V × V × V)) (t : V) :=
  bad.filter fun a => a.2.2 = t

/-- A directed endpoint candidate determines its proposed root edge exactly. -/
@[expose] def endpointCandidateRootEdge (y : V) (a : Finset V × V × V) : Finset V :=
  {y,a.2.1} ∪ a.1

/-- Forbidden edges and edges admitting no structural endpoint split. -/
@[expose] def endpointRootInvalidEdges (r : ℕ) (markers G : SimpleHypergraph V)
    (P U : Finset V) (y z t : V) (l : RootFreeEndpointLabel V) : SimpleHypergraph V :=
  (rootEdgeUniverse r y).filter fun e => e ∉ allowedEdges r U ∨
    ¬ ∃ q, RootFreeEndpointSplit r markers G P y z t e l q

/-- Low-summand capture accounts for every bad edge except the explicitly
structurally invalid ones. There is no assumption of an injective choice. -/
theorem endpoint_bad_root_subset (r : ℕ) (markers G : SimpleHypergraph V)
    (P U : Finset V) (y z t : V) (l : RootFreeEndpointLabel V) (c μ : ℝ)
    (bad : Finset (Finset V × V × V))
    (hcapture : ∀ e q, RootFreeEndpointSplit r markers G P y z t e l q →
      (rootFreeEndpointY r markers G P y z t l q : ℝ) <
        c * rootFreeEndpointX r markers G P y z l / μ → (q.1,q.2,t) ∈ bad) :
    rootFreeEndpointBadSet r markers G P U y z t l c μ ⊆
      (endpointBadCandidateFiber bad t).image (endpointCandidateRootEdge y) ∪
        endpointRootInvalidEdges r markers G P U y z t l := by
  intro e he
  obtain ⟨heroot,hbad⟩ := mem_filter.mp he
  by_cases hi : e ∈ endpointRootInvalidEdges r markers G P U y z t l
  · exact mem_union_right _ hi
  have hvalid : e ∈ allowedEdges r U ∧
      ∃ q, RootFreeEndpointSplit r markers G P y z t e l q := by
    simpa only [endpointRootInvalidEdges,mem_filter,heroot,true_and,not_or,not_not] using hi
  obtain ⟨q,hq⟩ := hvalid.2
  have hlow := (hbad.resolve_left (not_not.mpr hvalid.1)) q hq
  have hcap := hcapture e q hq hlow
  have hre : endpointCandidateRootEdge y (q.1,q.2,t) = e := by
    cases l <;> exact hq.1
  exact mem_union_left _ (mem_image.mpr ⟨_,mem_filter.mpr ⟨hcap,rfl⟩,hre⟩)

/-- Reconstruction supplies an actual injection on the noncolliding bad edges. -/
theorem exists_endpoint_reconstruction_injection (y : V)
    (Γ collisions : SimpleHypergraph V) (bad : Finset (Finset V × V × V))
    (hsub : Γ ⊆ bad.image (endpointCandidateRootEdge y) ∪ collisions) :
    ∃ f : ↥(Γ \ collisions) → ↥bad,
      Function.Injective f ∧ ∀ e, endpointCandidateRootEdge y (f e).val = e.val := by
  have hex : ∀ e : ↥(Γ \ collisions),
      ∃ a : ↥bad, endpointCandidateRootEdge y a.val = e.val := by
    intro e
    have hi := hsub (mem_sdiff.mp e.property).1
    have hb := (mem_union.mp hi).resolve_right (mem_sdiff.mp e.property).2
    obtain ⟨a,ha,he⟩ := mem_image.mp hb
    exact ⟨⟨a,ha⟩,he⟩
  choose f hf using hex
  refine ⟨f,?_,hf⟩
  intro e e' he
  apply Subtype.ext
  rw [← hf e,← hf e',he]

theorem endpoint_bad_root_edges_card_le (r : ℕ) (markers G : SimpleHypergraph V)
    (P U : Finset V) (y z t : V) (l : RootFreeEndpointLabel V) (c μ : ℝ)
    (bad : Finset (Finset V × V × V))
    (hcapture : ∀ e q, RootFreeEndpointSplit r markers G P y z t e l q →
      (rootFreeEndpointY r markers G P y z t l q : ℝ) <
        c * rootFreeEndpointX r markers G P y z l / μ → (q.1,q.2,t) ∈ bad) :
    (rootFreeEndpointBadSet r markers G P U y z t l c μ).card ≤
      (endpointBadCandidateFiber bad t).card +
        (endpointRootInvalidEdges r markers G P U y z t l).card := by
  have hs := endpoint_bad_root_subset r markers G P U y z t l c μ bad hcapture
  exact (card_le_card hs).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right card_image_le _))

/-- Residual reconstruction recovers the original ambient edge, including all
vertices lost by neither the base deletion nor the cut. -/
theorem endpoint_reconstruct_lift (B : Finset V) (y t : ↥B)
    (q : EndpointSpliceInnerLabel ↥B) (e : Finset V) (he : e ⊆ B)
    (hq : {y,q.2} ∪ q.1 = restrictEdge B e) :
    endpointCandidateRootEdge y.val (liftEdge B q.1,q.2.val,t.val) = e := by
  have h := congrArg (liftEdge B) hq
  simpa only [liftEdge_union,liftEdge_pair,lift_restrictEdge _ _ he,
    endpointCandidateRootEdge] using h

end LooseHamilton
