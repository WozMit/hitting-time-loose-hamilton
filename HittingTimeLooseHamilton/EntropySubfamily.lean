module

public import HittingTimeLooseHamilton.KahnConditioning
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! Exact entropy cost of passing to a polynomial-size subfamily.
The cardinality hypothesis is essential, including when the subset is selected
by prescribing relative marker directions. -/
noncomputable section
namespace FiniteEntropy
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- Uniform sampling on a nonempty subfamily, as a law on the original space. -/
@[expose] def uniformSubfamily (S : Finset Ω) (hS : S.Nonempty) : Law Ω := by
  letI : Nonempty ↥S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  exact (uniform (A := ↥S)).map (Subtype.val : ↥S → Ω)

/-- The subfamily law has precisely the logarithm of its cardinality as entropy. -/
theorem entropy_uniformSubfamily (S : Finset Ω) (hS : S.Nonempty) :
    entropy (uniformSubfamily S hS).mass = Real.log S.card := by
  letI : Nonempty ↥S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  change entropy (uniform.map (Subtype.val : ↥S → Ω)).mass = _
  rw [Law.entropy_map_of_injective _ _ Subtype.val_injective, entropy_uniform]
  simp

omit [Fintype Ω] in
/-- The exact logarithmic loss estimate. No symmetry of the host or of the
selection rule is assumed. -/
theorem log_card_subfamily_ge (F S : Finset Ω) (hF : F.Nonempty)
    (hS : S.Nonempty) (N A : ℝ) (hN : 0 < N)
    (hsize : N ^ (-A) ≤ (S.card : ℝ) / F.card) :
    Real.log F.card - A * Real.log N ≤ Real.log S.card := by
  have hf : (0 : ℝ) < F.card := Nat.cast_pos.mpr hF.card_pos
  have hs : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have h := Real.strictMonoOn_log.monotoneOn
    (Real.rpow_pos_of_pos hN (-A)) (div_pos hs hf) hsize
  rw [Real.log_rpow hN, Real.log_div (ne_of_gt hs) (ne_of_gt hf)] at h
  nlinarith

/-- Uniform laws on a family and on a subfamily lose at most `A log N` in
entropy when the retained fraction is at least `N^(-A)`. -/
theorem entropy_uniformSubfamily_ge (F S : Finset Ω) (hF : F.Nonempty)
    (hS : S.Nonempty) (N A : ℝ) (hN : 0 < N)
    (hsize : N ^ (-A) ≤ (S.card : ℝ) / F.card) :
    entropy (uniformSubfamily F hF).mass - A * Real.log N ≤
      entropy (uniformSubfamily S hS).mass := by
  simpa only [entropy_uniformSubfamily] using
    log_card_subfamily_ge F S hF hS N A hN hsize

/-- A lower bound for the original log count transfers with precisely the
normalised additional loss `A log N / N`. -/
theorem entropy_uniformSubfamily_lower_bound (F S : Finset Ω)
    (hF : F.Nonempty) (hS : S.Nonempty) (N A base ξ : ℝ) (hN : 0 < N)
    (hsize : N ^ (-A) ≤ (S.card : ℝ) / F.card)
    (hbase : base - ξ * N ≤ Real.log F.card) :
    base - (ξ + A * Real.log N / N) * N ≤
      entropy (uniformSubfamily S hS).mass := by
  rw [entropy_uniformSubfamily]
  have h := log_card_subfamily_ge F S hF hS N A hN hsize
  have he : (ξ + A * Real.log N / N) * N = ξ * N + A * Real.log N := by
    field_simp [ne_of_gt hN]
  rw [he]
  linarith

end FiniteEntropy
