module

public import HittingTimeLooseHamilton.FrameCoarseMainUniform
public import HittingTimeLooseHamilton.FrameSamplingRefined
public import HittingTimeLooseHamilton.IndexedOverlapMonotone
public import HittingTimeLooseHamilton.FrameSurvivalConcentrationRate
public import HittingTimeLooseHamilton.CandidateIndexedSurvival

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Filter AuxiliaryFrame Finset FrameScales FrameSurvival

/-- The boundary exponent is controlled by the original-size sampling scale. -/
lemma boundary_exponent_le {N k m t d : ℝ} (hN : 0<N) (hk : 0<k)
    (hm : 0 < m) (ht : 0≤t) {a b ν : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hν : 0≤ν) (hNk : N≤a*k) (hdb : d≤b) (hd : 0≤d)
    (hratio : t/m≤ν/k) : d*t/m≤(b*a)*(ν/N) := by
  have h1 : d*(t/m) ≤ b*(ν/k) :=
    mul_le_mul hdb hratio (by positivity) hb
  have h2 : b*(ν/k) ≤ (b*a)*(ν/N) := by
    apply (mul_le_mul_iff_left₀ hN).mp
    apply (mul_le_mul_iff_left₀ hk).mp
    have hh := mul_le_mul_of_nonneg_left hNk (mul_nonneg hb hν)
    field_simp
    nlinarith
  convert h1.trans h2 using 1 <;> ring

/-- Actual main-frame counts concentrate about ζ_k X, uniformly in the frame,
time, source outcome and bounded boundary. The overlap premise is discharged
by the imposed entropy budget and inherited regularity. -/
theorem inherited_main_concentration_eventually (r b : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r≤h → M≤j → j≤(completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      ∀ hτ : batchSize f D H ≤ (unexposed f D H).card,
      (hostBatchLaw hτ).event (fun T =>
        (alpha N/100000) * (CandidateLogSurvival.zeta (unexposed f D H).card
          f.k (batchSize f D H) * f.cycleCount H) <
        |(f.cycleCount (H \ T.val):ℝ) -
          CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H) *
            f.cycleCount H|) ≤
          K*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2 := by
  obtain ⟨K,hK,ho⟩ := inherited_main_overlap_eventually r hr C B hC hB
  let a : ℝ := 8*((r:ℝ)-1)
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have ha : 0<a := by dsimp [a]; linarith
  refine ⟨64*(a*K),by positivity,?_⟩
  filter_upwards [ho,inherited_sampling_parameters_eventually r b hr C hC.le,
    IndexedSurvival.eventually_interval_concentration (2*b*a) (a*K)
      (by positivity) (by positivity), FrameScales.eventually_log_density_lower,
    FrameScales.eventual_range, eventually_gt_atTop 0]
    with N ho hp hc hlog hR hN
  intro M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget H hτ
  have hpar := hp M ell original offset hadm f D hD j h c L ω hMj hj hreg
  obtain ⟨hμ,hNk,hkN,hratio,hm,hk,ht,hk4,ht4,hrest⟩ := hpar
  have hkpos : 0<f.k := by omega
  have hx := actual_batch_ratio_bounds f D H hkpos hm
    (by simpa only [Fintype.card_fin] using hR.2.2.2.2.2.1.le)
  simp only [Fintype.card_fin] at hx
  have hfull := ho M ell original offset hadm f j h c L ω hh hMj hj hreg hbudget
  have hO := (IndexedSurvival.uniformOverlap_inter_le (f.cycleFamily H)
    (unexposed f D H)).trans hfull
  have hnO := normalized_overlap_bound N f.k
    (IndexedSurvival.uniformOverlap (f.cycleFamily H) (fun E => E∩unexposed f D H))
    (f.mu H) a K (by exact_mod_cast hkpos) (hlog _ hμ).1 hK.le hNk hO
  have hy : ((2*D.card:ℕ):ℝ)*(batchSize f D H:ℝ)/(unexposed f D H).card ≤
      (2*b*a)*(nu N/(N:ℝ)) := by
    apply boundary_exponent_le (by exact_mod_cast hN) (by exact_mod_cast hkpos)
      (by exact_mod_cast hm) (Nat.cast_nonneg _) ha.le (by positivity)
      hR.2.2.2.2.2.1.le hNk _ (Nat.cast_nonneg _) hx.1
    exact_mod_cast (Nat.mul_le_mul_left 2 hD)
  have hhconc := hc (Finset (Fin N)) (Finset (Finset (Fin N))) (unexposed f D H) (f.cycleFamily H)
    (fun E => E∩unexposed f D H) f.k (2*D.card) (batchSize f D H) (f.mu H)
    hm hkpos hk4 ht4 hbudget.1 (fun _ _ => inter_subset_right)
    (fun E hE => cycle_restricted_support_card f hr D H E hE) hμ hx.2 hy hnO hτ
  have he (T : HostBatch (unexposed f D H) (batchSize f D H)) :
      f.cycleCount (H \ T.val) = IndexedSurvival.count (f.cycleFamily H)
        (fun E => E∩unexposed f D H) T.val :=
    cycleCount_eq_indexed f D H T.val (mem_powersetCard.mp T.property).1
  simp only [he]
  exact hhconc
end LooseHamilton.CandidateBalance
