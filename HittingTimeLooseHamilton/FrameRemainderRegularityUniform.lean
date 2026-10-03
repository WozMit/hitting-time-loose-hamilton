module

public import HittingTimeLooseHamilton.FrameRemainderRegularityFinite
public import HittingTimeLooseHamilton.FramePreservationScales

public section

/-! Actual batch deletion preserves all upper and partition regularity estimates.
Every size and loss condition is discharged before the batch is selected. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame Filter FrameScales FrameSurvival

/-- Upper degrees, codegrees and every current-frame junction partition set
remain controlled with the same window L. The mean remains at least log N/4.
The assertion is deterministic for every possible actual deletion batch. -/
theorem inherited_remainder_regular_eventually (r b : ℕ) (hr : 3≤r)
    (C : ℝ) (hC : 0<C) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r≤h → M≤j → j≤(completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
      let H := extensionState ω.1 ω.2 j
      ∀ T : HostBatch (unexposed f D H) (batchSize f D H),
        Real.log N/4≤f.mu (rawRemainder f D H T.val) ∧
        PathGraphUpperRegular r (4*C) L
          (f.numberedEdges (f.rawHost (rawRemainder f D H T.val))) := by
  let a : ℝ := 8*((r:ℝ)-1)
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have ha : 0≤a := by dsimp [a]; linarith
  have hrpos : 0<(r:ℝ) := by linarith
  have hp : 0≤1+partitionDensity r := by
    have := partitionDensity_nonneg (r:=r) (by omega : 2≤r)
    linarith
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (L1_tendsto.eventually (eventually_ge_atTop 1))
  filter_upwards [inherited_sampling_parameters_eventually r b hr C hC.le,
    eventually_partition_loss_envelope ((1+partitionDensity r)*a) (C*r) (mul_pos hC hrpos),
    eventually_ge_atTop (4*r+n₀+1),eventual_range]
    with N hparam hsmall hN hR
  intro M ell original offset hadm f D hD j h c L ω hh hMj hj hreg H T
  obtain ⟨hmu,hNk,hkN,hratio,hm,hk,ht,hk4,ht4,hrest⟩ :=
    hparam M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hT := (mem_powersetCard.mp T.property).1
  have hcard := (mem_powersetCard.mp T.property).2
  have hquarter : 4*T.val.card≤(unexposed f D H).card := by rw [hcard]; exact ht4
  have hhalf := rawRemainder_mu_half f D H T.val hT hquarter
  refine ⟨by linarith,?_⟩
  apply rawRemainder_upper_regular_of_loss f (by omega) D H T.val C L hC.le
    (f.numbered_rawHost_inherited_regular j h c C L ω hh hreg) hT hquarter
  have hn := f.n_add_deleted
  have hd := f.val.deleted_card_le
  simp only [Fintype.card_fin] at hn
  have hnN : f.n≤N := by omega
  have hlog : 1≤Real.log (f.n:ℝ) := hn₀ f.n (by omega)
  have hscalar := hsmall f.n hnN hlog
  have hkpos : (0:ℝ)<f.k := by exact_mod_cast (show 0<f.k by omega)
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hf := actual_batch_le_raw f D H (by simpa only [Fintype.card_fin] using hR.2.2.2.2.2.1.le)
  simp only [Fintype.card_fin] at hf
  have htk := (le_div_iff₀ hkpos).mp hf
  have htn : (batchSize f D H:ℝ)*(N:ℝ)≤a*(nu N*(f.m H:ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hNk (Nat.cast_nonneg (batchSize f D H) : (0:ℝ)≤batchSize f D H)
    have h2 := mul_le_mul_of_nonneg_left htk ha
    change (batchSize f D H:ℝ)*(N:ℝ)≤(batchSize f D H:ℝ)*(a*(f.k:ℝ)) at h1
    nlinarith only [h1,h2]
  have htb : (batchSize f D H:ℝ)≤a*nu N*(f.m H:ℝ)/(N:ℝ) := by
    apply (le_div_iff₀ hNpos).mpr
    convert htn using 1 <;> ring
  rw [hcard]
  calc
    _ ≤ (1+partitionDensity r)*(a*nu N*(f.m H:ℝ)/(N:ℝ)) :=
      mul_le_mul_of_nonneg_left htb hp
    _ = (((1+partitionDensity r)*a)*nu N/(N:ℝ))*(f.m H:ℝ) := by ring
    _ ≤ (C*(r:ℝ)*(Real.log (f.n:ℝ))^(-1/8:ℝ))*(f.m H:ℝ) :=
      mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg _)
    _ = _ := by ring

end LooseHamilton.CandidateBalance
