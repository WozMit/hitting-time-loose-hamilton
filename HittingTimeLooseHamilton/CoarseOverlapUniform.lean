module

public import HittingTimeLooseHamilton.CoarseOverlapMarkers
public import HittingTimeLooseHamilton.EntropySubfamilyCycles

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy Filter

/-- Coarse overlap for arbitrary laws; the marker condition is the standing
polynomial marker budget of the manuscript. The constant is independent of L. -/
theorem eventual_mixed_overlap_bound (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃K : ℝ, 0<K ∧ ∀(D : ℕ→BiasedRoleInstance r) (L : ℝ),
      Tendsto (fun n => (D n).μ) atTop atTop →
      (∀ᶠn in atTop,((D n).s:ℝ)≤L*((D n).N:ℝ)^(1/10:ℝ)) →
      (∀ᶠn in atTop,∀v,(vertexDegree (D n).host v:ℝ)≤C*(D n).μ) →
      (∀ᶠn in atTop,((D n).k:ℝ)*Real.log (D n).μ-B*(D n).N≤entropy (D n).cycleLaw.mass) →
      ∀ᶠn in atTop,(D n).mixedOverlap≤K*(D n).N/Real.log (D n).μ := by
  obtain ⟨K,hK,h⟩ := eventual_ordinary_overlap_bound r hr C B hC hB
  refine ⟨K+1,by linarith,?_⟩
  intro D L hμ hs hd he
  filter_upwards [h D hμ hd he,eventually_markers_le_overlap_scale hr L D hμ hs] with n hn hm
  calc
    _ ≤ (D n).ordinaryOverlap+(D n).s := (D n).mixedOverlap_le
    _ ≤ K*(D n).N/Real.log (D n).μ+(D n).N/Real.log (D n).μ := add_le_add hn hm
    _ = _ := by ring

/-- Exact uniform-family form: the entropy hypothesis is log of its actual
cardinality, and the overlap includes the prescribed marker edges. -/
theorem eventual_uniform_mixed_overlap (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃K : ℝ, 0<K ∧ ∀(D : ℕ→BiasedRoleInstance r)
      (F : ∀n,Finset (BiasedCycleState r (D n).markers (D n).host))
      (hF : ∀n,(F n).Nonempty) (L : ℝ),
      Tendsto (fun n => (D n).μ) atTop atTop →
      (∀ᶠn in atTop,((D n).s:ℝ)≤L*((D n).N:ℝ)^(1/10:ℝ)) →
      (∀ᶠn in atTop,∀v,(vertexDegree (D n).host v:ℝ)≤C*(D n).μ) →
      (∀ᶠn in atTop,((D n).k:ℝ)*Real.log (D n).μ-B*(D n).N≤Real.log (F n).card) →
      ∀ᶠn in atTop,
        (uniformSubfamily (F n) (hF n)).independentOverlap
          (fun A => A.val∪(D n).markers) ≤ K*(D n).N/Real.log (D n).μ := by
  obtain ⟨K,hK,h⟩ := eventual_mixed_overlap_bound r hr C B hC hB
  refine ⟨K,hK,?_⟩
  intro D F hF L hμ hs hd he
  apply h (fun n => (D n).withUniformSubfamily (F n) (hF n)) L hμ hs hd
  filter_upwards [he] with n hn
  change (D n).k * Real.log (D n).μ - B*(D n).N ≤
    entropy (uniformSubfamily (F n) (hF n)).mass
  rw [entropy_uniformSubfamily]
  exact hn
end LooseHamilton.BiasedRoleInstance
