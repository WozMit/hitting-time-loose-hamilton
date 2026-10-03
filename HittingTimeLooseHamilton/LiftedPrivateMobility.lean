module

public import HittingTimeLooseHamilton.LiftedRootGoodEdgeCount
public import HittingTimeLooseHamilton.PrivateGoodEdgeMobility
public import HittingTimeLooseHamilton.BootstrapMobilityConstants

public section

/-! The actual private migration injection after deleting vertices. All
sampling bounds retain the ambient root degree. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem private_mobility_of_lifted_root_test (r h time : ℕ) (D : Finset V)
    (markers : SimpleHypergraph ↥(univ \ D)) (F H : SimpleHypergraph V)
    (S q U : Finset ↥(univ \ D)) (x t : ↥(univ \ D))
    (c : ℝ) (hr : 3 ≤ r) (hc : 0 ≤ c)
    (hH : H ⊆ completeEdges V r)
    (htarget : LegalPrivateCompletion r markers (insert t S) q)
    (hμ : 0 < privateRootSourceMean r (inducedHost (univ \ D) H) S x)
    (hn : ¬ RootLinkBad
      (((registerPrivateRootTest r h time markers S q U x t c).liftDeleted D).badSet (F,H))
      (vertexDegree H x.val) (F,H)) :
    (c/3) * (vertexDegree H x.val : ℝ) /
        privateRootSourceMean r (inducedHost (univ \ D) H) S x *
        (completionCount r markers (fixedPortHost (inducedHost (univ \ D) H) U)
          (insert x S) q : ℝ) ≤
      completionCount r markers (fixedPortHost (inducedHost (univ \ D) H) U)
        (insert t S) q := by
  have hg := (registerPrivateRootTest r h time markers S q U x t c).liftDeleted_good_card_lower
    D F H hH hn
  have houter : inducedHost (univ \ D) H ⊆ completeEdges ↥(univ \ D) r := by
    intro e he
    apply (mem_completeEdges _ _).mpr
    have h := (mem_completeEdges _ _).mp (hH ((mem_inducedHost _ _ _).mp he))
    simpa only [ambientEdge_card] using h
  have hm := private_mobility_of_good_edge_count r h time markers
    (inducedHost (univ \ D) F) (inducedHost (univ \ D) H) S q U x t c
    hr hc houter htarget hμ ((vertexDegree H x.val : ℝ)/3) hg
  convert hm using 1 <;> ring

/-- The fixed private factor follows from the actual lifted test and the
ambient degree-to-source-mean comparison proved in item 33.13. -/
theorem private_fixed_factor_of_lifted_root_test (r h time : ℕ) (D : Finset V)
    (markers : SimpleHypergraph ↥(univ \ D)) (F H : SimpleHypergraph V)
    (S q U : Finset ↥(univ \ D)) (x t : ↥(univ \ D))
    (c : ℝ) (hr : 3 ≤ r) (hH : H ⊆ completeEdges V r)
    (htarget : LegalPrivateCompletion r markers (insert t S) q)
    (hμ : 0 < privateRootSourceMean r (inducedHost (univ \ D) H) S x)
    (hratio : c/2 ≤ (vertexDegree H x.val : ℝ) /
      privateRootSourceMean r (inducedHost (univ \ D) H) S x)
    (hn : ¬ RootLinkBad
      (((registerPrivateRootTest r h time markers S q U x t
        (BootstrapConstants.rootThreshold r)).liftDeleted D).badSet (F,H))
      (vertexDegree H x.val) (F,H)) :
    BootstrapConstants.privateFactor r c *
        (completionCount r markers (fixedPortHost (inducedHost (univ \ D) H) U)
          (insert x S) q : ℝ) ≤
      completionCount r markers (fixedPortHost (inducedHost (univ \ D) H) U)
        (insert t S) q := by
  have hcoef := BootstrapConstants.privateFactor_le_root_ratio hr hratio
  have hm := private_mobility_of_lifted_root_test r h time D markers F H S q U x t
    (BootstrapConstants.rootThreshold r) hr (BootstrapConstants.rootThreshold_pos hr).le
    hH htarget hμ hn
  have hmul := mul_le_mul_of_nonneg_right hcoef
    (Nat.cast_nonneg (completionCount r markers
      (fixedPortHost (inducedHost (univ \ D) H) U) (insert x S) q) : (0 : ℝ) ≤ _)
  exact hmul.trans (by convert hm using 1 <;> ring)

end LooseHamilton
