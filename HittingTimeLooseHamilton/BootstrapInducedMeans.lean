module

public import HittingTimeLooseHamilton.Setup
public import HittingTimeLooseHamilton.Operations
public import HittingTimeLooseHamilton.PathRegularityModels

public section

/-! Uniform upper bounds for actual induced outer-host means. These estimates
use ambient edge count and vertex count, without a new residual sampling law.
-/
noncomputable section
namespace LooseHamilton.BootstrapMeans
open Finset Filter
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem induced_card_le (T : Finset V) (H : SimpleHypergraph V) :
    (inducedHost T H).card ≤ H.card := by
  calc
    _ = ((inducedHost T H).image (ambientEdge T)).card :=
      (card_image_of_injective _ (Finset.map_injective _)).symm
    _ ≤ _ := card_le_card (by
      intro e he
      obtain ⟨a,ha,rfl⟩ := mem_image.mp he
      exact (mem_inducedHost _ _ _).mp ha)

@[expose] def inducedMean (r : ℕ) (H : SimpleHypergraph V) (T : Finset V) : ℝ :=
  meanDegree (V := ↥T) r (inducedHost T H).card

/-- The actual induced mean is bounded by the ambient edge count divided by
its own actual vertex count, including empty sets under Lean's division convention. -/
theorem inducedMean_le (r : ℕ) (H : SimpleHypergraph V) (T : Finset V) :
    inducedMean r H T ≤ (r : ℝ)*H.card/T.card := by
  unfold inducedMean meanDegree
  rw [Fintype.card_coe]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (by exact_mod_cast induced_card_le T H) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

omit [DecidableEq V] in
/-- Keeping at least half the ambient vertices yields the factor two bound. -/
theorem ambient_over_active_le (r : ℕ) (H : SimpleHypergraph V) (T : Finset V)
    (hN : 0 < Fintype.card V) (hT : Fintype.card V ≤ 2*T.card) :
    (r : ℝ)*H.card/T.card ≤ 2*meanDegree (V := V) r H.card := by
  have ht : (0 : ℝ) < T.card := by exact_mod_cast (show 0 < T.card by omega)
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  have hb : (Fintype.card V : ℝ) ≤ 2*(T.card : ℝ) := by exact_mod_cast hT
  unfold meanDegree
  apply (div_le_iff₀ ht).mpr
  apply (mul_le_mul_iff_left₀ hn).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ (r : ℝ)*H.card by positivity)]

theorem inducedMean_le_twice (r : ℕ) (H : SimpleHypergraph V) (T : Finset V)
    (hN : 0 < Fintype.card V) (hT : Fintype.card V ≤ 2*T.card) :
    inducedMean r H T ≤ 2*meanDegree (V := V) r H.card :=
  (inducedMean_le r H T).trans (ambient_over_active_le r H T hN hT)

/-- One size bound works for every active set with bounded complement. -/
theorem half_size_of_complement_bound (T : Finset V) (k : ℕ)
    (hk : (univ \ T).card ≤ k) (hN : 2*k ≤ Fintype.card V) :
    Fintype.card V ≤ 2*T.card := by
  have hc := card_sdiff_add_card_eq_card (subset_univ T)
  simp only [card_univ] at hc
  omega

/-- Uniform eventual form for all bounded-deletion means. -/
theorem eventually_inducedMean_bounds (r k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (H : SimpleHypergraph (Fin N)) (T : Finset (Fin N)),
      (univ \ T).card ≤ k →
      inducedMean r H T ≤ (r : ℝ)*H.card/T.card ∧
      (r : ℝ)*H.card/T.card ≤ 2*meanDegree (V := Fin N) r H.card := by
  filter_upwards [eventually_ge_atTop (max 1 (2*k))] with N hN H T hT
  refine ⟨inducedMean_le r H T, ambient_over_active_le r H T ?_ ?_⟩
  · simp only [Fintype.card_fin]; omega
  · exact half_size_of_complement_bound T k hT (by simp only [Fintype.card_fin]; omega)

/-- Ambient lower degree and the factor-two upper mean imply a fixed ratio.
Positivity of the actual source mean is the only division requirement. -/
theorem degree_div_inducedMean_lower {r : ℕ} {H : SimpleHypergraph V}
    {T : Finset V} {c : ℝ} (hc : 0 ≤ c) (x : V)
    (hdeg : c*meanDegree (V := V) r H.card ≤ (vertexDegree H x : ℝ))
    (hmean : inducedMean r H T ≤ 2*meanDegree (V := V) r H.card)
    (hpos : 0 < inducedMean r H T) :
    c/2 ≤ (vertexDegree H x : ℝ)/inducedMean r H T := by
  apply (le_div_iff₀ hpos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hmean hc]

end LooseHamilton.BootstrapMeans
