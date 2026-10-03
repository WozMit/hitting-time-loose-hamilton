module

public import HittingTimeLooseHamilton.RootEventGoodLinks
public import HittingTimeLooseHamilton.EndpointMigrationFamilies

public section

/-! A fixed endpoint cut receives actual directed completions from the sampled
root link. One split is chosen per good edge, and its endpoints/private block
reconstruct that edge, so the selected labels are distinct. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Forget only the proofs of geometric legality in an actual cut label. -/
@[expose] def endpointMigrationRawLabel {r : ℕ} {M G : SimpleHypergraph V} {P : Finset V}
    {y z : V} : EndpointMigrationCut r M G P y z → RootFreeEndpointLabel V
  | .inl l => .inl l.val
  | .inr l => .inr l.val

theorem endpointMigration_rootFree_X {r : ℕ} {M G : SimpleHypergraph V}
    {P : Finset V} {y z : V} (b : EndpointMigrationCut r M G P y z) :
    (rootFreeEndpointX r M G P y z (endpointMigrationRawLabel b) : ℝ) =
      endpointMigrationWeight b := by
  cases b with
  | inl l =>
    simp only [endpointMigrationRawLabel,endpointMigrationWeight]
    exact_mod_cast rootFreeEndpointX_I_eq r M G P y z l.val
  | inr l =>
    simp only [endpointMigrationRawLabel,endpointMigrationWeight]
    exact_mod_cast rootFreeEndpointX_II_eq r M G P y z l.val

theorem endpointMigration_rootFree_Y {r : ℕ} {M G : SimpleHypergraph V}
    {P : Finset V} {y z : V} (b : EndpointMigrationCut r M G P y z)
    (t : V) (q : EndpointSpliceInnerLabel V) :
    (rootFreeEndpointY r M G P y z t (endpointMigrationRawLabel b) q : ℝ) =
      endpointMigrationY t b q := by
  cases b with
  | inl l =>
    simp only [endpointMigrationRawLabel,endpointMigrationY]
    exact_mod_cast rootFreeEndpointY_I_eq r M G P y z t l.val q
  | inr l =>
    simp only [endpointMigrationRawLabel,endpointMigrationY]
    exact_mod_cast rootFreeEndpointY_II_eq r M G P y z t l.val q

/-- A counterfactual split passing the registered test becomes an actual legal
summation label when its root edge is present. -/
theorem endpointMigration_split_actual {r : ℕ} {M G : SimpleHypergraph V}
    {P : Finset V} {y z : V} (b : EndpointMigrationCut r M G P y z)
    (t : V) (e : Finset V) (q : EndpointSpliceInnerLabel V) (he : e ∈ G)
    (hq : RootFreeEndpointSplit r M G P y z t e (endpointMigrationRawLabel b) q) :
    q ∈ endpointMigrationLabels t b ∧ {y,q.2} ∪ q.1 = e := by
  cases b with
  | inl l =>
    exact ⟨(mem_endpointSpliceLabelsI _ _ _ _ _ _ _ _ _).mpr
      (rootFreeEndpointSplit_I_actual r M G P y z t e l.val q he hq), hq.1⟩
  | inr l =>
    exact ⟨(mem_endpointSpliceLabelsII _ _ _ _ _ _ _ _ _).mpr
      (rootFreeEndpointSplit_II_actual r M G P y z t e l.val q he hq), hq.1⟩

/-- Root-test nonfailure supplies the degree-over-mean contribution of a fixed
actual cut. The prescribed direction is the existing `v→t` direction rooted
at `a→z`; it is never replaced by an undirected or half-count assumption. -/
theorem endpoint_cut_mobility_of_root_test (r : ℕ)
    (M F H : SimpleHypergraph V) (P U : Finset V) (y z t : V)
    (b : EndpointMigrationCut r M (fixedPortHost H U) P y z)
    (c μ : ℝ) (hc : 0 ≤ c) (hμ : 0 < μ)
    (hH : H ⊆ completeEdges V r)
    (hn : ¬ RootLinkBad
      (rootFreeEndpointBadSet r M (fixedPortHost H U) P U y z t
        (endpointMigrationRawLabel b) c μ) (vertexDegree H y) (F,H)) :
    (c/3) * (vertexDegree H y : ℝ) / μ * endpointMigrationWeight b ≤
      ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q := by
  classical
  let G := fixedPortHost H U
  let Γ := rootFreeEndpointBadSet r M G P U y z t (endpointMigrationRawLabel b) c μ
  let E := rootGoodEdges H Γ y
  have hΓ : Γ ⊆ rootEdgeUniverse r y := filter_subset _ _
  have hex : ∀ e : ↥E, ∃ q : EndpointSpliceInnerLabel V,
      q ∈ endpointMigrationLabels t b ∧
      c * endpointMigrationWeight b / μ ≤ endpointMigrationY t b q ∧
      {y,q.2} ∪ q.1 = e.val := by
    intro e
    obtain ⟨he,hnot⟩ := mem_sdiff.mp e.property
    obtain ⟨heH,hye⟩ := mem_filter.mp he
    have heU : e.val ∈ rootEdgeUniverse r y :=
      (mem_rootEdgeUniverse _ _ _).mpr ⟨(mem_completeEdges _ _).mp (hH heH),hye⟩
    obtain ⟨hallowed,q,hq,hbound⟩ := rootFreeEndpoint_good_split r M G P U y z t
      (endpointMigrationRawLabel b) c μ e.val heU hnot
    have heG : e.val ∈ G := mem_filter.mpr
      ⟨heH,((mem_allowedEdges _ _ _).mp hallowed).2⟩
    obtain ⟨hlegal,hedge⟩ := endpointMigration_split_actual b t e.val q heG hq
    refine ⟨q,hlegal,?_,hedge⟩
    rw [endpointMigration_rootFree_X b,endpointMigration_rootFree_Y b t q] at hbound
    exact hbound
  choose chooseLabel hchoose using hex
  have hinj : Function.Injective chooseLabel := by
    intro e f hef
    apply Subtype.ext
    exact (hchoose e).2.2.symm.trans ((congrArg
      (fun q : EndpointSpliceInnerLabel V => {y,q.2} ∪ q.1) hef).trans (hchoose f).2.2)
  let good := univ.image chooseLabel
  have hcard : good.card = E.card := by
    rw [show good = univ.image chooseLabel from rfl,card_image_of_injective _ hinj,
      card_univ,Fintype.card_coe]
  have hlegal : good ⊆ endpointMigrationLabels t b := by
    intro q hq
    obtain ⟨e,_,rfl⟩ := mem_image.mp hq
    exact (hchoose e).1
  have hbound : ∀ q ∈ good,
      c * endpointMigrationWeight b / μ ≤ endpointMigrationY t b q := by
    intro q hq
    obtain ⟨e,_,rfl⟩ := mem_image.mp hq
    exact (hchoose e).2.1
  have hdegree : (vertexDegree H y : ℝ)/3 ≤ (good.card : ℝ) := by
    rw [hcard]
    exact rootGoodEdges_card_lower r F H Γ y hΓ hn
  have hscale : 0 ≤ c * endpointMigrationWeight b / μ :=
    div_nonneg (mul_nonneg hc (endpointMigrationWeight_nonneg b)) hμ.le
  calc
    _ = ((vertexDegree H y : ℝ)/3) * (c * endpointMigrationWeight b / μ) := by ring
    _ ≤ (good.card : ℝ) * (c * endpointMigrationWeight b / μ) :=
      mul_le_mul_of_nonneg_right hdegree hscale
    _ = ∑ _q ∈ good, c * endpointMigrationWeight b / μ := by simp
    _ ≤ ∑ q ∈ good, endpointMigrationY t b q := sum_le_sum hbound
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hlegal (fun q _ _ => endpointMigrationY_nonneg t b q)

/-- The same inequality directly from the concrete registered endpoint test,
with its actual root-free surviving-host mean. -/
theorem endpoint_cut_mobility_of_registered_test (r h time : ℕ)
    (M F H : SimpleHypergraph V) (P U : Finset V) (y z t : V)
    (b : EndpointMigrationCut r M (fixedPortHost H U) P y z)
    (c : ℝ) (hc : 0 ≤ c)
    (hμ : 0 < rootFreeEndpointMean r H P y (endpointMigrationRawLabel b))
    (hH : H ⊆ completeEdges V r)
    (R : SimpleHypergraph V) (hR : R ⊆ rootEdgeUniverse r y) (hRh : R.card ≤ h)
    (hn : ¬ RootLinkBad
      ((registerEndpointRootTest r h time M P U y z t (endpointMigrationRawLabel b)
        c R hR hRh).badSet (F,H)) (vertexDegree H y) (F,H)) :
    (c/3) * (vertexDegree H y : ℝ) /
        rootFreeEndpointMean r H P y (endpointMigrationRawLabel b) * endpointMigrationWeight b ≤
      ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q :=
  endpoint_cut_mobility_of_root_test r M F H P U y z t b c _ hc hμ hH hn

end LooseHamilton
