module

public import HittingTimeLooseHamilton.EndpointRootEventMobility

public section

/-! Actual directed endpoint contributions from any certified good-edge count. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each good edge supplies one legal directed label, and the label reconstructs
its edge. Thus an arbitrary real lower bound for the good-edge count suffices. -/
theorem endpoint_cut_mobility_of_good_edge_count (r : ℕ)
    (M H : SimpleHypergraph V) (P U : Finset V) (y z t : V)
    (b : EndpointMigrationCut r M (fixedPortHost H U) P y z)
    (c μ : ℝ) (hc : 0 ≤ c) (hμ : 0 < μ)
    (hH : H ⊆ completeEdges V r)
    (d : ℝ)
    (hgood : d ≤ (rootGoodEdges H
      (rootFreeEndpointBadSet r M (fixedPortHost H U) P U y z t
        (endpointMigrationRawLabel b) c μ) y).card) :
    d * (c * endpointMigrationWeight b / μ) ≤
      ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q := by
  classical
  let G := fixedPortHost H U
  let Γ := rootFreeEndpointBadSet r M G P U y z t (endpointMigrationRawLabel b) c μ
  let E := rootGoodEdges H Γ y
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
  have hdegree : d ≤ (good.card : ℝ) := by
    rw [hcard]
    exact hgood
  have hscale : 0 ≤ c * endpointMigrationWeight b / μ :=
    div_nonneg (mul_nonneg hc (endpointMigrationWeight_nonneg b)) hμ.le
  calc
    _ ≤ (good.card : ℝ) * (c * endpointMigrationWeight b / μ) :=
      mul_le_mul_of_nonneg_right hdegree hscale
    _ = ∑ _q ∈ good, c * endpointMigrationWeight b / μ := by simp
    _ ≤ ∑ q ∈ good, endpointMigrationY t b q := sum_le_sum hbound
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hlegal (fun q _ _ => endpointMigrationY_nonneg t b q)


end LooseHamilton
