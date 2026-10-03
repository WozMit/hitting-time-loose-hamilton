module

public import HittingTimeLooseHamilton.BootstrapPrivateSourceNormalization
public import HittingTimeLooseHamilton.BootstrapSourceMeanRatios

public section

/-! Construct the actual ambient source frame once from legal supported labels;
its source-count and normalization dictionaries hold for every uniform host. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateSourceNormalization
open Finset BootstrapBases BootstrapMeans
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

/-- Frame selection depends only on labels. Neither an entropy budget nor a
count/mean identification is assumed of the chosen frame. -/
theorem exists_normalized_source (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    (S : Finset ↥(active b)) (x y z : ↥(active b))
    (hs : LegalPrivateCompletion r (markers hM b)
      (liftEdge (active b) (insert x S)) {y.val,z.val}) :
    ∃ F : AuxiliaryFrame.Frame r M,
      F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S) ∧
      F.markers = insert {y.val,z.val} (markers hM b) ∧
      F.val.root = (y.val,z.val) ∧ F.val.relative = none ∧
      ∀ (H : SimpleHypergraph V), H ⊆ completeEdges V r →
        F.cycleCount H = completionCount r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) {y,z} ∧
        F.mu H = privateRootSourceMean r
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) S x ∧
        F.mu H ≤ privateRootSourceMean r (inducedHost (active b) H) S x ∧
        (0 < completionCount r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) {y,z} →
          0 < F.mu H ∧ 0 < privateRootSourceMean r (inducedHost (active b) H) S x) := by
  have hp : ({y.val,z.val} : Finset V) ⊆ active b := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact y.property
    · have he := mem_singleton.mp hv
      exact he ▸ z.property
  obtain ⟨F,hd,hm,hroot,hrel⟩ := BootstrapActualSourceFrames.exists_source hM b hr
    (liftEdge (active b) (insert x S)) y.val z.val hs hp
  refine ⟨F,hd,hm,hroot,hrel,?_⟩
  intro H hH
  have hm' : F.markers = insert (liftEdge (active b) {y,z}) (markers hM b) := by
    simpa only [liftEdge_pair] using hm
  refine ⟨frame_source_count hM b F H hH S {y,z} x hd hm' hrel,
    frame_mu_eq_filtered_source b F H hH S x hd,
    frame_mu_le_outer_source b F H S x hd,?_⟩
  intro hW
  have hn := positive_source_normalization hM b F hr H hH S {y,z} x hd hm' hrel hW
  exact ⟨hn.1,hn.2.2⟩

/-- The same literal normalization interfaces with the cached ambient degree
bound. The fixed original-port filter is retained in the source count. -/
theorem normalized_source_bounds (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (hS : S.card = r-3) (hN : 8*r ≤ Fintype.card V)
    {c C L : ℝ} (hc : 0 ≤ c) (hreg : PathGraphRegular r c C L H) :
    0 < F.mu H ∧
      F.mu H ≤ privateRootSourceMean r (inducedHost (active b) H) S x ∧
      0 < privateRootSourceMean r (inducedHost (active b) H) S x ∧
      privateRootSourceMean r (inducedHost (active b) H) S x ≤
        2*meanDegree (V := V) r H.card ∧
      c/2 ≤ (vertexDegree H x.val : ℝ) /
        privateRootSourceMean r (inducedHost (active b) H) S x := by
  have hn := positive_source_normalization hM b F hr H hH S q x hd hm hrel hW
  have hb := private_mean_bounds hr b H S x hS hN
  have hsub : fixedPortHost (inducedHost (active b) H) (fixedPorts b) ⊆
      inducedHost (active b) H := by
    intro e he
    exact (mem_filter.mp he).1
  exact ⟨hn.1,hn.2.1,hn.2.2,hb.1.trans hb.2,
    private_degree_mean_ratio hr b H S x q (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) hS hN hsub hW hc hreg⟩

end LooseHamilton.BootstrapPrivateSourceNormalization
