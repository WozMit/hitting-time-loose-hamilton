module

public import HittingTimeLooseHamilton.EndpointGoodEdgeMobility
public import HittingTimeLooseHamilton.LiftedRootGoodEdgeCount
public import HittingTimeLooseHamilton.BootstrapMobilityConstants

public section

/-! Lifted endpoint tests control actual directed residual cut contributions
using the ambient root degree, without assuming residual sampling. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The injected good residual edges retain the ambient occupancy lower bound. -/
theorem endpoint_cut_mobility_of_lifted_root_test (r h time : ℕ) (D : Finset V)
    (M : SimpleHypergraph ↥(univ \ D)) (F H : SimpleHypergraph V)
    (P U : Finset ↥(univ \ D)) (y z t : ↥(univ \ D))
    (b : EndpointMigrationCut r M (fixedPortHost (inducedHost (univ \ D) H) U) P y z)
    (c : ℝ) (hc : 0 ≤ c)
    (hμ : 0 < rootFreeEndpointMean r (inducedHost (univ \ D) H) P y
      (endpointMigrationRawLabel b))
    (hH : H ⊆ completeEdges V r)
    (R : SimpleHypergraph ↥(univ \ D))
    (hR : R ⊆ rootEdgeUniverse r y) (hRh : R.card ≤ h)
    (hn : ¬ RootLinkBad
      (((registerEndpointRootTest r h time M P U y z t (endpointMigrationRawLabel b)
        c R hR hRh).liftDeleted D).badSet (F,H)) (vertexDegree H y.val) (F,H)) :
    (c/3) * (vertexDegree H y.val : ℝ) /
        rootFreeEndpointMean r (inducedHost (univ \ D) H) P y
          (endpointMigrationRawLabel b) * endpointMigrationWeight b ≤
      ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q := by
  have hg := (registerEndpointRootTest r h time M P U y z t
    (endpointMigrationRawLabel b) c R hR hRh).liftDeleted_good_card_lower D F H hH hn
  have houter : inducedHost (univ \ D) H ⊆ completeEdges ↥(univ \ D) r := by
    intro e he
    apply (mem_completeEdges _ _).mpr
    have h := (mem_completeEdges _ _).mp (hH ((mem_inducedHost _ _ _).mp he))
    simpa only [ambientEdge_card] using h
  have hm := endpoint_cut_mobility_of_good_edge_count r M
    (inducedHost (univ \ D) H) P U y z t b c _ hc hμ
    houter ((vertexDegree H y.val : ℝ)/3) hg
  convert hm using 1; ring

/-- The common lower regularity factor and the endpoint source-mean comparison
turn literal lifted-test nonfailure into the fixed per-cut coefficient. -/
theorem endpoint_cut_fixed_factor_of_lifted_root_test (r h time : ℕ) (D : Finset V)
    (M : SimpleHypergraph ↥(univ \ D)) (F H : SimpleHypergraph V)
    (P U : Finset ↥(univ \ D)) (y z t : ↥(univ \ D))
    (b : EndpointMigrationCut r M (fixedPortHost (inducedHost (univ \ D) H) U) P y z)
    (c : ℝ) (hr : 3 ≤ r)
    (hμ : 0 < rootFreeEndpointMean r (inducedHost (univ \ D) H) P y
      (endpointMigrationRawLabel b))
    (hH : H ⊆ completeEdges V r)
    (hratio : c/2 ≤ (vertexDegree H y.val : ℝ) /
      rootFreeEndpointMean r (inducedHost (univ \ D) H) P y
        (endpointMigrationRawLabel b))
    (R : SimpleHypergraph ↥(univ \ D))
    (hR : R ⊆ rootEdgeUniverse r y) (hRh : R.card ≤ h)
    (hn : ¬ RootLinkBad
      (((registerEndpointRootTest r h time M P U y z t (endpointMigrationRawLabel b)
        (BootstrapConstants.rootThreshold r) R hR hRh).liftDeleted D).badSet (F,H))
      (vertexDegree H y.val) (F,H)) :
    BootstrapConstants.privateFactor r c * endpointMigrationWeight b ≤
      ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q := by
  have hcoef := BootstrapConstants.privateFactor_le_root_ratio hr hratio
  have hm := endpoint_cut_mobility_of_lifted_root_test r h time D M F H P U y z t b
    (BootstrapConstants.rootThreshold r) (BootstrapConstants.rootThreshold_pos hr).le
    hμ hH R hR hRh hn
  have hmul := mul_le_mul_of_nonneg_right hcoef (endpointMigrationWeight_nonneg b)
  exact hmul.trans (by convert hm using 1; ring)

end LooseHamilton
