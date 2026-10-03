module

public import HittingTimeLooseHamilton.CandidateRestrictedNoDeficit
public import HittingTimeLooseHamilton.RestrictedHostBatchLaw
public import HittingTimeLooseHamilton.FrameRestrictedKParameters
public import HittingTimeLooseHamilton.FrameScales

public section

/-! Terminal feasibility for the actual restricted frame batch, with the
original demand function at every original vertex. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

/-- Cached restricted no-deficit control applies to the actual uniform host
batch. The offset is fixed before the threshold; the terminal graph and original
lower demands are preserved explicitly. -/
theorem inherited_terminal_feasibility_eventually (r : ℕ) (hr : 3≤r)
    (C : ℝ) (hC : 0<C) (offset : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))),
    CoreAdmissible r M ell original offset →
    ∀ (ω : Outcome (Fin N) r M ell), TerminalRegular C ω.1.val →
    ∀ (f : Frame r original) (D : Finset (Fin N)) (j : ℕ),
    let H := extensionState ω.1 ω.2 j
    ∃ hτ : batchSize f D H≤(unexposed f D H).card,
      (hostBatchLaw hτ).event (fun T => ¬BatchRetainsLower ω.1.val ell T.val) ≤
        noDeficitError (C*(8*((r:ℝ)-1))) (epsilon/8) N (nu N) := by
  have hK : 0<8*((r:ℝ)-1) := by
    have hrR : (3:ℝ)≤r := by exact_mod_cast hr
    linarith
  filter_upwards [eventually_restricted_terminal_no_deficit hC hK offset,
    nu_tendsto.eventually (eventually_ge_atTop 1),eventual_range,eventually_ge_atTop (16*r)]
    with N ht hnu hR hN
  intro M ell original hadm ω hterminal f D j
  let H := extensionState ω.1 ω.2 j
  have hk := (frame_k_comparison_unconditional f hr (by simpa using hN)).1
  simp only [Fintype.card_fin] at hk
  have hlog : nu N≤Real.log N := by
    have h21 := Real.log_le_sub_one_of_pos hR.1
    have h32 := Real.log_le_sub_one_of_pos hR.2.1
    change L2 N≤L1 N-1 at h21
    change L3 N≤L2 N-1 at h32
    change nu N≤L1 N
    dsimp [nu]
    linarith [hR.2.2.1]
  have he := ht (Fin N) (Fintype.card_fin N) r M ell original hadm ω.1 hterminal
    (unexposed f D H) f.k (nu N) hk hnu hlog
  have hbatch : noDeficitBatchSize (unexposed f D H).card f.k (nu N)=batchSize f D H := by
    simp only [noDeficitBatchSize,batchSize,Fintype.card_fin]
  simp only [NoDeficitEstimate,Fintype.card_fin,hbatch] at he
  obtain ⟨hτ,hsuccess⟩ := he
  refine ⟨hτ,?_⟩
  have hl : 1-noDeficitError (C*(8*((r:ℝ)-1))) (epsilon/8) N (nu N) ≤
      (hostBatchLaw hτ).event (fun T => BatchRetainsLower ω.1.val ell T.val) := by
    rw [←selectedHostBatch_event (unexposed f D H) (batchSize f D H) hτ
      (BatchRetainsLower ω.1.val ell)]
    simpa only [Fintype.card_fin] using hsuccess
  rw [FiniteEntropy.Law.event_compl]
  linarith

end LooseHamilton.CandidateBalance
