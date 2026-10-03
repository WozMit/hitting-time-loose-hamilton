module

public import HittingTimeLooseHamilton.BootstrapNestedMeans
public import HittingTimeLooseHamilton.BootstrapBases
public import HittingTimeLooseHamilton.RootSourceMeanPositive

public section

/-! Uniform ambient estimates for the actual means on every residual base. -/
noncomputable section
namespace LooseHamilton.BootstrapMeans
open Finset Filter
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Flattening the residual active set loses exactly the base deletion plus
its own residual complement. No temporary deletions are counted twice. -/
theorem base_active_card {M : Finset (Finset V)} (b : BootstrapBases.Base M)
    (T : Finset ↥(BootstrapBases.active b)) :
    (BootstrapBases.deleted b).card + (univ \ T).card +
      (ambientEdge (BootstrapBases.active b) T).card = Fintype.card V := by
  have hA := card_sdiff_add_card_eq_card (subset_univ (BootstrapBases.deleted b))
  have hT := card_sdiff_add_card_eq_card (subset_univ T)
  simp only [card_univ, Fintype.card_coe] at hA hT
  rw [ambientEdge_card]
  change _ + _ + T.card = _
  change (BootstrapBases.active b).card + (BootstrapBases.deleted b).card = _ at hA
  omega

/-- The exact actual residual mean obeys the manuscript's two upper bounds. -/
theorem base_mean_bounds {M : Finset (Finset V)} (b : BootstrapBases.Base M)
    (r k : ℕ) (H : SimpleHypergraph V) (T : Finset ↥(BootstrapBases.active b))
    (hN : 0 < Fintype.card V) (hkN : 2*k ≤ Fintype.card V)
    (hdel : (BootstrapBases.deleted b).card + (univ \ T).card ≤ k) :
    inducedMean r (inducedHost (BootstrapBases.active b) H) T ≤
      (r : ℝ)*H.card/T.card ∧
    (r : ℝ)*H.card/T.card ≤ 2*meanDegree (V := V) r H.card := by
  have hc := base_active_card b T
  have hhalf : Fintype.card V ≤ 2*(ambientEdge (BootstrapBases.active b) T).card := by omega
  rw [inducedMean_nested]
  simpa only [ambientEdge_card] using
    And.intro (inducedMean_le r H (ambientEdge (BootstrapBases.active b) T))
      (ambient_over_active_le r H (ambientEdge (BootstrapBases.active b) T) hN hhalf)

/-- Uniform in all base labels and actual active sets with the proved frame
budget; the threshold depends only on r. -/
theorem eventually_base_mean_bounds (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : Finset (Finset (Fin N))) (b : BootstrapBases.Base M)
      (H : SimpleHypergraph (Fin N)) (T : Finset ↥(BootstrapBases.active b)),
      (BootstrapBases.deleted b).card + (univ \ T).card ≤ 4*r →
      inducedMean r (inducedHost (BootstrapBases.active b) H) T ≤
        (r : ℝ)*H.card/T.card ∧
      (r : ℝ)*H.card/T.card ≤ 2*meanDegree (V := Fin N) r H.card := by
  filter_upwards [eventually_ge_atTop (max 1 (8*r))] with N hN M b H T hdel
  exact base_mean_bounds b r (4*r) H T (by simp only [Fintype.card_fin]; omega)
    (by simp only [Fintype.card_fin]; omega) hdel

/-- Common lower degree gives the fixed c/2 ratio for every positive actual
residual mean with the bounded-deletion budget. -/
theorem base_degree_mean_ratio {M : Finset (Finset V)} (b : BootstrapBases.Base M)
    (r k : ℕ) (H : SimpleHypergraph V) (T : Finset ↥(BootstrapBases.active b))
    (hN : 0 < Fintype.card V) (hkN : 2*k ≤ Fintype.card V)
    (hdel : (BootstrapBases.deleted b).card + (univ \ T).card ≤ k)
    {c : ℝ} (hc : 0 ≤ c) (x : V)
    (hdegree : c*meanDegree (V := V) r H.card ≤ (vertexDegree H x : ℝ))
    (hpos : 0 < inducedMean r (inducedHost (BootstrapBases.active b) H) T) :
    c/2 ≤ (vertexDegree H x : ℝ)/inducedMean r (inducedHost (BootstrapBases.active b) H) T := by
  have hb := base_mean_bounds b r k H T hN hkN hdel
  apply (le_div_iff₀ hpos).mpr
  have hm := hb.1.trans hb.2
  nlinarith [mul_le_mul_of_nonneg_left hm hc]

end LooseHamilton.BootstrapMeans
