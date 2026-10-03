module

public import HittingTimeLooseHamilton.FrameRestrictedNormalization
public import HittingTimeLooseHamilton.FramePreservationScales

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame Filter FrameSurvival

/-- Uniform finite-rate normalization estimates on the original inherited event.
The raw retention factor uses m_raw; every zeta uses m0. -/
theorem inherited_normalization_rates (r b : ℕ) (hr : 3≤r) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
      M≤j → j≤(completeEdges (Fin N) r).card →
      InheritedRegularity original j h c C L ω →
      let H := extensionState ω.1 ω.2 j
      let m0 := (unexposed f D H).card
      let τ := CandidateBalance.batchSize f D H
      |(zeta m0 τ (f.k-1)/zeta m0 τ f.k)*rawRetention (f.m H) τ-1| ≤
        24*((r:ℝ)-1)*(FrameScales.nu N/N) ∧
      |(conditionedZeta m0 τ f.k/zeta m0 τ f.k)*rawRetention (f.m H) τ-1| ≤
        4*(r:ℝ)/Real.log N+24*((r:ℝ)-1)*(FrameScales.nu N/N) := by
  filter_upwards [inherited_sampling_parameters_eventually r b hr C hC,
    inherited_frame_density_eventually r b C hC,
    FrameScales.eventual_range, eventually_ge_atTop (1:ℕ)] with N hs hd hscale hN
  intro M ell original offset hadm f D hD j h c L ω hMj hj hreg
  let H := extensionState ω.1 ω.2 j
  let m0 := (unexposed f D H).card
  let τ := CandidateBalance.batchSize f D H
  have hp := hs M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hd' := hd M ell original offset hadm f D hD j h c L ω hMj hj hreg
  rcases hp with ⟨_,hNk,hkN,_,hm0,hk,ht,hk4,ht4,_⟩
  have hν : 0≤FrameScales.nu N := hscale.2.2.2.2.2.1.le
  have hτ : (τ:ℝ)≤FrameScales.nu N*m0/f.k := by
    simp only [τ,CandidateBalance.batchSize,Fintype.card_fin]
    exact Nat.floor_le (show 0 ≤ FrameScales.nu N * ((unexposed f D H).card:ℝ) / f.k by positivity)
  have hsub : m0≤f.m H := by
    dsimp [m0]
    rw [unexposed_eq_surviving]
    exact card_le_card (filter_subset _ _)
  have hh := restricted_normalization_finite (f.m H) m0 f.k τ N
    (FrameScales.nu N) (8*((r:ℝ)-1)) r
    (by exact_mod_cast (show 0<N by omega)) hm0 hsub hk ht hk4 ht4 hν
    (by
      have hh : (3:ℝ)≤r := by exact_mod_cast hr
      linarith)
    (by exact_mod_cast (show 0<r by omega)) hscale.1 hNk hkN hτ hd'.2.1
  dsimp only [H,m0,τ] at hh
  constructor
  · convert hh.2.2.2.1 using 1 <;> ring
  · convert hh.2.2.2.2 using 1 <;> ring
theorem inherited_normalization_alpha (r b : ℕ) (hr : 3≤r) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
      M≤j → j≤(completeEdges (Fin N) r).card →
      InheritedRegularity original j h c C L ω →
      let H := extensionState ω.1 ω.2 j
      let m0 := (unexposed f D H).card
      let τ := CandidateBalance.batchSize f D H
      |(zeta m0 τ (f.k-1)/zeta m0 τ f.k)*rawRetention (f.m H) τ-1| ≤
        FrameScales.alpha N/100000 ∧
      |(conditionedZeta m0 τ f.k/zeta m0 τ f.k)*rawRetention (f.m H) τ-1| ≤
        FrameScales.alpha N/100000 := by
  filter_upwards [inherited_normalization_rates r b hr C hC,
    FrameScales.eventually_normalization_error (4*(r:ℝ)+24*((r:ℝ)-1)) (1/100000) (by norm_num),
    FrameScales.eventual_range] with N hrate herr hscale
  intro M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hh := hrate M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hn : 0≤FrameScales.nu N/(N:ℝ) := div_nonneg hscale.2.2.2.2.2.1.le (Nat.cast_nonneg _)
  have hl : 0≤1/Real.log (N:ℝ) := div_nonneg (by norm_num) hscale.1.le
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg _
  have hr1 : 0≤(r:ℝ)-1 := by
    have hh : (3:ℝ)≤r := by exact_mod_cast hr
    linarith
  have hb : 4*(r:ℝ)/Real.log N+24*((r:ℝ)-1)*(FrameScales.nu N/N) ≤ FrameScales.alpha N/100000 := by
    have he : (4*(r:ℝ)+24*((r:ℝ)-1))*(FrameScales.nu N/N+1/FrameScales.L1 N) ≤ FrameScales.alpha N/100000 := by
      convert herr using 1 <;> ring
    change (4*(r:ℝ)+24*((r:ℝ)-1))*(FrameScales.nu N/N+1/Real.log N) ≤ _ at he
    have h0 := mul_nonneg hr0 hn
    have h1 := mul_nonneg hr1 hl
    simp only [div_eq_mul_inv] at he h0 h1 ⊢
    nlinarith only [he,h0,h1]
  have hnon : 0 ≤ 4*(r:ℝ)/Real.log N := div_nonneg (mul_nonneg (by norm_num) hr0) hscale.1.le
  exact ⟨hh.1.trans (by linarith only [hb,hnon]),hh.2.trans hb⟩

end LooseHamilton.CandidateBalance
