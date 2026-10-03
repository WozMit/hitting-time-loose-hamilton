module

public import HittingTimeLooseHamilton.FrameMissingEntropyParameters
public import HittingTimeLooseHamilton.FrameCandidateTransferActual

public section

/-! Actual remainder exceptional existing roles occupy a negligible part of
all legal candidates, before the missing-edge set is formed. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame Filter FrameScales FrameSurvival

/-- Uniform subtraction bound for existing abnormal roles on main survival.
Both the complete active r-set scale and the full legal-candidate denominator
are retained. No existing-exceptional-count premise is imposed. -/
theorem inherited_remainder_existing_negligible_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C B L : ℝ) (hC : 0 < C) (hB : 0 ≤ B) (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r ≤ h → M ≤ j → j ≤ (completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      ∀ T : HostBatch (unexposed f D H) (batchSize f D H),
        MainCountSurvives f D H T.val →
      let G := rawRemainder f D H T.val
      ((f.existingExceptional G (alpha N/4)).card:ℝ) ≤
        alpha N*(f.n.choose r:ℝ)*(r*(r-1):ℕ)/8 ∧
      ((f.existingExceptional G (alpha N/4)).card:ℝ) ≤
        alpha N*(f.candidates.card:ℝ)/4 := by
  obtain ⟨K,hK,hstatic⟩ := inherited_remainder_static_entropy_eventually r b hr C B L hC hB hL
  obtain ⟨N₀,hcount⟩ := Frame.uniform_candidate_counts r (by omega)
  have hroles : (0:ℝ)<(r*(r-1):ℕ) := by
    exact_mod_cast (Nat.mul_pos (by omega : 0<r) (by omega : 0<r-1))
  filter_upwards [hstatic,eventually_remainder_entropy_factor K (r*(r-1):ℕ) hroles,
    eventually_ge_atTop N₀,eventual_range] with N hs hf hN hR
  intro M ell original offset hadm f D hD j h c ω hh hMj hj hreg hb H T hmain
  let G := rawRemainder f D H T.val
  have hstate := hs M ell original offset hadm f D hD j h c ω hh hMj hj hreg hb T hmain
  have he := hstate.2.2.2.2 (alpha N/4) (div_pos hR.2.2.2.1 (by norm_num))
  change ((f.existingExceptional G (alpha N/4)).card:ℝ) ≤
    K*(f.m G:ℝ)/((alpha N/4)*Real.sqrt (L2 N)) at he
  have hraw : (f.m G:ℝ) ≤ f.n.choose r := Nat.cast_le.mpr (f.raw_card_le_active_choose G)
  have hfactor : 0 ≤ K/((alpha N/4)*Real.sqrt (L2 N)) :=
    div_nonneg hK.le (mul_nonneg (div_nonneg hR.2.2.2.1.le (by norm_num)) (Real.sqrt_nonneg _))
  have hsmall : ((f.existingExceptional G (alpha N/4)).card:ℝ) ≤
      alpha N*(f.n.choose r:ℝ)*(r*(r-1):ℕ)/8 := by
    calc
      _ ≤ K*(f.m G:ℝ)/((alpha N/4)*Real.sqrt (L2 N)) := he
      _ = (K/((alpha N/4)*Real.sqrt (L2 N)))*(f.m G:ℝ) := by ring
      _ ≤ (K/((alpha N/4)*Real.sqrt (L2 N)))*(f.n.choose r:ℝ) :=
        mul_le_mul_of_nonneg_left hraw hfactor
      _ ≤ (alpha N*(r*(r-1):ℕ)/8)*(f.n.choose r:ℝ) :=
        mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg _)
      _ = _ := by ring
  have hc := (hcount (Fin N) original (by simpa using hN) hadm.marker_matching
    (by simpa using hadm.markers_small) f).1
  have hα4 : 0 ≤ alpha N/4 := div_nonneg hR.2.2.2.1.le (by norm_num)
  have hcm := mul_le_mul_of_nonneg_left hc hα4
  refine ⟨hsmall,?_⟩
  apply hsmall.trans
  convert hcm using 1 <;> ring
end LooseHamilton.CandidateBalance
