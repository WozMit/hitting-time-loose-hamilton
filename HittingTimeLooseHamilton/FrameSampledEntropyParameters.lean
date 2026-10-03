module

public import HittingTimeLooseHamilton.FrameSamplingParameters

public section

/-! Uniform raw-to-sampling host comparison for weighting source entropy counts. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame Filter

/-- The sampling host retains at least half the raw edges, with the threshold
chosen before every frame, bounded boundary and source outcome. -/
theorem inherited_raw_le_twice_unexposed_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N→ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
        M ≤ j → j ≤ (completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
      let H := extensionState ω.1 ω.2 j
      0 < (unexposed f D H).card ∧ (f.m H:ℝ) ≤ 2*(unexposed f D H).card := by
  have hsize : ∀ᶠ N : ℕ in atTop, 4*(b:ℝ)*C*r ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [inherited_sampling_parameters_eventually r b hr C hC,
    hsize,eventually_ge_atTop (1:ℕ)] with N hp hsize hN
  intro M ell original offset hadm f D hD j h c L ω hMj hj hreg H
  obtain ⟨_,_,_,hratio,hm0,_⟩ :=
    hp M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hsub : (unexposed f D H).card ≤ f.m H := by
    rw [unexposed_eq_surviving]
    exact card_le_card (filter_subset _ _)
  have hm : (0:ℝ) < f.m H := Nat.cast_pos.mpr (lt_of_lt_of_le hm0 hsub)
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsmall : 2*(b:ℝ)*C*r/N ≤ 1/2 := by
    apply (div_le_iff₀ hNp).mpr
    nlinarith only [hsize]
  have hhalf : (1/2:ℝ) ≤ (unexposed f D H).card/(f.m H:ℝ) := by
    have hh := hratio.2.trans hsmall
    linarith only [hh]
  have hh := (le_div_iff₀ hm).mp hhalf
  exact ⟨hm0,by linarith only [hh]⟩

/-- Multiplication by the exact inclusion probability τ/m0 costs no reciprocal
conditioning probability. A raw entropy count and mraw ≤ 2m0 suffice. -/
lemma source_entropy_sampling_weight (mraw m0 τ E K α s : ℝ)
    (hm0 : 0 < m0) (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hα : 0 < α) (hs : 0 < s)
    (hm : mraw ≤ 2*m0) (hE : E ≤ K*mraw/((α/100)*s)) :
    (τ/m0)*E ≤ (200*K)*τ/(α*s) := by
  have hEs : E ≤ 100*K*mraw/(α*s) := by
    convert hE using 1  <;>  ring
  have hw := mul_le_mul_of_nonneg_left hEs (div_nonneg hτ hm0.le)
  have hraw := mul_le_mul_of_nonneg_left hm (show 0 ≤ 100*K*τ by positivity)
  apply hw.trans
  have he : (τ/m0)*(100*K*mraw/(α*s))=(100*K*τ*mraw)/(m0*(α*s)) := by ring
  rw [he]
  apply (div_le_div_iff₀ (mul_pos hm0 (mul_pos hα hs)) (mul_pos hα hs)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hraw (mul_pos hα hs).le]

end LooseHamilton.CandidateBalance
