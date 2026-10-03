module

public import HittingTimeLooseHamilton.BootstrapRootMeanBounds

public section

/-! Fixed lower degree/mean ratios for the actual private and endpoint source
means. Source positivity discharges the denominator condition.
-/
noncomputable section
namespace LooseHamilton.BootstrapMeans
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem private_degree_mean_ratio {r : ℕ} (hr : 3 ≤ r)
    {M : Finset (Finset V)} (b : BootstrapBases.Base M) (H : SimpleHypergraph V)
    (S : Finset ↥(BootstrapBases.active b)) (x : ↥(BootstrapBases.active b))
    (q : Finset ↥(BootstrapBases.active b))
    (markers G : SimpleHypergraph ↥(BootstrapBases.active b))
    (hS : S.card = r-3) (hN : 8*r ≤ Fintype.card V)
    (hGH : G ⊆ inducedHost (BootstrapBases.active b) H)
    (hX : 0 < completionCount r markers G (insert x S) q)
    {c C L : ℝ} (hc : 0 ≤ c) (hreg : PathGraphRegular r c C L H) :
    c/2 ≤ (vertexDegree H x.val : ℝ) /
      privateRootSourceMean r (inducedHost (BootstrapBases.active b) H) S x := by
  have hp := privateRootSourceMean_pos_of_completionCount (by omega : 0 < r) hGH hX
  have hb := private_mean_bounds hr b H S x hS hN
  have hm := hb.1.trans hb.2
  have hd := hreg.lower_degree x.val
  apply (le_div_iff₀ hp).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm hc]

theorem endpoint_degree_mean_ratio {r : ℕ} (hr : 3 ≤ r)
    {M : Finset (Finset V)} (b : BootstrapBases.Base M) (H : SimpleHypergraph V)
    (P : Finset ↥(BootstrapBases.active b)) (y z : ↥(BootstrapBases.active b))
    (l : RootFreeEndpointLabel ↥(BootstrapBases.active b))
    (markers G : SimpleHypergraph ↥(BootstrapBases.active b))
    (hP : P.card = r-2)
    (hl : match l with
      | .inl l => l.2.card = r-2
      | .inr l => l.2.2.2.1.card = r-2 ∧ l.2.2.2.2.card = r-2)
    (hN : 8*r ≤ Fintype.card V)
    (hGH : G ⊆ inducedHost (BootstrapBases.active b) H)
    (hX : 0 < rootFreeEndpointX r markers G P y z l)
    {c C L : ℝ} (hc : 0 ≤ c) (hreg : PathGraphRegular r c C L H) :
    c/2 ≤ (vertexDegree H y.val : ℝ) /
      rootFreeEndpointMean r (inducedHost (BootstrapBases.active b) H) P y l := by
  have hp := rootFreeEndpointMean_pos_of_source l (by omega : 0 < r) hGH hX
  have hb := endpoint_mean_bounds hr b H P y l hP hl hN
  have hm := hb.1.trans hb.2
  have hd := hreg.lower_degree y.val
  apply (le_div_iff₀ hp).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm hc]

end LooseHamilton.BootstrapMeans
