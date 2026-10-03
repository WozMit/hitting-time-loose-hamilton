module

public import HittingTimeLooseHamilton.FrameCompletionConcentrationParameters
public import HittingTimeLooseHamilton.FrameSurvivalConcentrationRate

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

/-- Uniform completion concentration, simultaneously in the actual batch and
in its conditional law after requiring deletion of the candidate. -/
theorem eventually_actual_completion_concentration (r b : ℕ) (hr : 3 ≤ r)
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ (original : Finset (Finset (Fin N)))
      (f : Frame r original) (D : Finset (Fin N)) (H : SimpleHypergraph (Fin N))
      (c : Finset (Fin N) × Fin N × Fin N),
    D.card ≤ b → (f.cycleFamily H).Nonempty → f.LegalCandidate c →
    (f.completionFamily H c).Nonempty →
    L1 N/2 ≤ f.mu H →
    4*f.k ≤ (unexposed f D H).card →
    4*batchSize f D H ≤ (unexposed f D H).card →
    ∀ htpos : 1 ≤ batchSize f D H,
    IndexedSurvival.uniformOverlap (f.completionFamily H c) id ≤ K*N/Real.log (f.mu H) →
    ∀ hτ : batchSize f D H ≤ (unexposed f D H).card,
    ((hostBatchLaw hτ).event (fun T =>
      (alpha N/100000) * (CandidateLogSurvival.zeta (unexposed f D H).card
        (f.k-1) (batchSize f D H) * f.completionCount H c) <
      |(f.completionCount (rawRemainder f D H T.val) c : ℝ) -
        CandidateLogSurvival.zeta (unexposed f D H).card
          (f.k-1) (batchSize f D H) * f.completionCount H c|) ≤
      (64*((16*((r:ℝ)-1))*K)) * (L2 N)^(-24/25:ℝ)/(alpha N/100000)^2) ∧
    (∀ he : c.1 ∪ {c.2.1,c.2.2} ∈ unexposed f D H,
      ((hostBatchLaw hτ).condition (fun T => c.1 ∪ {c.2.1,c.2.2} ∈ T.val)
        (candidate_batch_event_pos he htpos hτ)).event (fun T =>
      (alpha N/100000) * (conditionedZeta (unexposed f D H).card
        (batchSize f D H) f.k * f.completionCount H c) <
      |(f.completionCount (rawRemainder f D H T.val) c : ℝ) -
        conditionedZeta (unexposed f D H).card
          (batchSize f D H) f.k * f.completionCount H c|) ≤
      (64*((16*((r:ℝ)-1))*K)) * (L2 N)^(-24/25:ℝ)/(alpha N/100000)^2) := by
  let a : ℝ := 16*((r:ℝ)-1)
  have ha : 0 ≤ a := by
    dsimp [a]
    have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  filter_upwards [IndexedSurvival.eventually_interval_concentration
    ((2*(b:ℝ))*a) (a*K) (by positivity) (by positivity),
    eventually_ge_atTop (32*r), eventually_log_density_lower, eventual_range]
    with N hconc hN hlog hR
  intro original f D H c hD hmain hc hcomp hmu hk4 ht4 htpos hO hτ
  have hNk := completion_k_comparison f hr (by simpa using hN)
  simp only [Fintype.card_fin] at hNk
  have hk : 0 < f.k := by omega
  have hm : 0 < (unexposed f D H).card := by omega
  have hNpos : 0 < (N:ℝ) := by
    have hNp : 0 < N := by omega
    exact_mod_cast hNp
  have hnu : 0 ≤ nu N := hR.2.2.2.2.2.1.le
  have hratio := actual_batch_ratio_bounds f D H hk hm (by simpa using hnu)
  simp only [Fintype.card_fin] at hratio
  have hratioq : (batchSize f D H:ℝ)/(unexposed f D H).card ≤ nu N/(f.k-1:ℕ) :=
    hratio.1.trans (div_le_div_of_nonneg_left hnu (by exact_mod_cast hNk.1)
      (by exact_mod_cast (Nat.sub_le f.k 1)))
  have hqd : ((2*D.card:ℕ):ℝ) ≤ 2*(b:ℝ) := by exact_mod_cast (Nat.mul_le_mul_left 2 hD)
  have hb := boundary_batch_exponent_bound (N:ℝ) (f.k-1:ℕ) (2*D.card:ℕ)
    (batchSize f D H) (unexposed f D H).card a (2*b) (nu N)
    hNpos (by exact_mod_cast hNk.1) (by positivity) (by positivity) hnu hNk.2 hqd hratioq
  have hx : (batchSize f D H:ℝ)*(f.k-1:ℕ)/(unexposed f D H).card ≤ nu N := by
    apply le_trans _ hratio.2
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.sub_le f.k 1)) (by positivity))
      (by positivity)
  have hOrestrict := IndexedSurvival.uniformOverlap_mono (f.completionFamily H c)
    (fun E => E ∩ unexposed f D H) id (fun _ _ => inter_subset_left)
  have hOnorm := normalized_overlap_bound (N:ℝ) (f.k-1:ℕ)
    (IndexedSurvival.uniformOverlap (f.completionFamily H c) (fun E => E ∩ unexposed f D H))
    (f.mu H) a K (by exact_mod_cast hNk.1) (hlog _ hmu).1 hK hNk.2
    (hOrestrict.trans hO)
  have hu := hconc (Finset (Fin N)) (Finset (Finset (Fin N)))
    (unexposed f D H) (f.completionFamily H c) (fun E => E ∩ unexposed f D H)
    (f.k-1) (2*D.card) (batchSize f D H) (f.mu H) hm hNk.1 (by omega) ht4 hcomp
    (fun _ _ => inter_subset_right)
    (fun E hE => completion_restricted_support_card f hr D H E hmain c hc hE)
    hmu hx hb hOnorm hτ
  constructor
  · have heq (T : HostBatch (unexposed f D H) (batchSize f D H)) :
        f.completionCount (rawRemainder f D H T.val) c =
          IndexedSurvival.count (f.completionFamily H c) (fun E => E ∩ unexposed f D H) T.val := by
      rw [rawRemainder_completionCount f D H _ c (mem_powersetCard.mp T.property).1]
      exact completionCount_eq_indexed f D H _ c (mem_powersetCard.mp T.property).1
    simp only [heq]
    simpa only [Frame.completionCount, a] using hu
  · intro he
    have hers := erased_quarter_parameters (unexposed f D H).card f.k (batchSize f D H)
      (by omega) hk4 ht4
    have hrats := erased_batch_ratio_le (unexposed f D H).card (batchSize f D H)
      (by omega) htpos hτ
    have hratioqs := hrats.trans hratioq
    have hbs := boundary_batch_exponent_bound (N:ℝ) (f.k-1:ℕ) (2*D.card:ℕ)
      (batchSize f D H-1:ℕ) ((unexposed f D H).card-1:ℕ) a (2*b) (nu N)
      hNpos (by exact_mod_cast hNk.1) (by positivity) (by positivity) hnu hNk.2 hqd hratioqs
    have hxs : (batchSize f D H-1:ℕ)*(f.k-1:ℕ)/((unexposed f D H).card-1:ℕ) ≤ nu N := by
      calc
        _ = ((batchSize f D H-1:ℕ)/((unexposed f D H).card-1:ℕ):ℝ)*(f.k-1:ℕ) := by ring
        _ ≤ ((batchSize f D H:ℝ)/(unexposed f D H).card)*(f.k-1:ℕ) :=
          mul_le_mul_of_nonneg_right hrats (by positivity)
        _ = (batchSize f D H:ℝ)*(f.k-1:ℕ)/(unexposed f D H).card := by ring
        _ ≤ nu N := hx
    have hts : batchSize f D H-1 ≤ ((unexposed f D H).erase (c.1 ∪ {c.2.1,c.2.2})).card := by
      rw [card_erase_of_mem he]; omega
    have hs := hconc (Finset (Fin N)) (Finset (Finset (Fin N)))
      ((unexposed f D H).erase (c.1 ∪ {c.2.1,c.2.2}))
      (f.completionFamily H c) (fun E => E ∩ unexposed f D H)
      (f.k-1) (2*D.card) (batchSize f D H-1) (f.mu H)
      (by simpa only [card_erase_of_mem he] using hers.1) hNk.1
      (by simpa only [card_erase_of_mem he] using hers.2.1)
      (by simpa only [card_erase_of_mem he] using hers.2.2) hcomp
      (fun _ hE => completion_support_subset_erased f hr D H c hc hE)
      (fun E hE => completion_restricted_support_card f hr D H E hmain c hc hE)
      hmu (by simpa only [card_erase_of_mem he] using hxs)
      (by simpa only [card_erase_of_mem he] using hbs) hOnorm hts
    rw [candidate_batch_conditional_law he htpos hτ (fun T =>
      (alpha N/100000) * (conditionedZeta (unexposed f D H).card
        (batchSize f D H) f.k * f.completionCount H c) <
      |(f.completionCount (rawRemainder f D H T) c : ℝ) -
        conditionedZeta (unexposed f D H).card
          (batchSize f D H) f.k * f.completionCount H c|)]
    have heq (T : HostBatch ((unexposed f D H).erase (c.1 ∪ {c.2.1,c.2.2}))
        (batchSize f D H-1)) :
        f.completionCount (rawRemainder f D H (insert (c.1 ∪ {c.2.1,c.2.2}) T.val)) c =
          IndexedSurvival.count (f.completionFamily H c) (fun E => E ∩ unexposed f D H) T.val := by
      have hT := (mem_powersetCard.mp T.property).1
      rw [rawRemainder_completionCount f D H _ c (insert_subset he (hT.trans (erase_subset _ _)))]
      exact completionCount_conditioned_eq_indexed f hr D H _ c hc hT
    simp only [heq]
    simpa only [Frame.completionCount, a, card_erase_of_mem he,
      conditioned_zeta_eq _ _ _ (by omega : 1 ≤ f.k)] using hs

end LooseHamilton.CandidateBalance
