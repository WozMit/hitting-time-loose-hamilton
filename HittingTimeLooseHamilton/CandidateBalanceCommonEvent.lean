module

public import HittingTimeLooseHamilton.FrameUniformCandidateBalance
public import HittingTimeLooseHamilton.FiniteMomentBounds
public import HittingTimeLooseHamilton.CommonEventScales

public section

/-! A single event for every labelled frame and every eligible extension time.
The family is fixed before the random outcome; regularity and the entropy budget
remain inside the bad event, exactly as in Proposition 8.1. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
open scoped BigOperators
variable {N r M : ℕ} {ell : Fin N → ℕ}
variable {original : Finset (Finset (Fin N))}

/-- Simultaneous candidate balance. No regularity or entropy-budget event is
conditioned upon: these are antecedents of each pointwise implication. -/
@[expose] def CommonCandidateBalance (original : Finset (Finset (Fin N)))
    (h : ℕ) (c C L B : ℝ) (ω : Outcome (Fin N) r M ell) : Prop :=
  ∀ f : Frame r original, ∀ j : ℕ, M ≤ j →
    j ≤ (completeEdges (Fin N) r).card →
    InheritedRegularity original j h c C L ω →
    f.entropyBudget (extensionState ω.1 ω.2 j) B →
    ¬ f.candidateBadAtScale (extensionState ω.1 ω.2 j)

/-- Finite union bound over all labelled frames and all times. -/
theorem common_candidate_failure_le [Nonempty (TerminalState (Fin N) r M ell)]
    (h : ℕ) (c C L B rate : ℝ) (hN : 2 ≤ N)
    (hb : ∀ f : Frame r original, ∀ j : ℕ, M ≤ j →
      j ≤ (completeEdges (Fin N) r).card →
      (extensionLaw r M ell).event (BadSource f j h c C L B) ≤ errorBound N rate) :
    (extensionLaw r M ell).event (fun ω =>
      ¬ CommonCandidateBalance original h c C L B ω) ≤
        (N : ℝ)^(9*r+25) * errorBound N rate := by
  classical
  let I := Frame r original × Fin (N^r+1)
  let E : I → Outcome (Fin N) r M ell → Prop := fun i ω =>
    M ≤ i.2.val ∧ i.2.val ≤ (completeEdges (Fin N) r).card ∧
      BadSource i.1 i.2.val h c C L B ω
  have hcover : ∀ ω, ¬ CommonCandidateBalance original h c C L B ω → ∃ i, E i ω := by
    intro ω hω
    simp only [CommonCandidateBalance, not_forall, Classical.not_imp, not_not] at hω
    obtain ⟨f,j,hMj,hj,hr,hb,hbad⟩ := hω
    have hjpow : j ≤ N^r := hj.trans (by
      simpa only [completeEdges_card, Fintype.card_fin] using Nat.choose_le_pow N r)
    exact ⟨(f,⟨j,by omega⟩),hMj,hj,hr,hb,hbad⟩
  have he (i : I) : (extensionLaw r M ell).event (E i) ≤ errorBound N rate := by
    by_cases hi : M ≤ i.2.val ∧ i.2.val ≤ (completeEdges (Fin N) r).card
    · exact ((extensionLaw r M ell).event_mono (fun _ hω => hω.2.2)).trans
        (hb i.1 i.2.val hi.1 hi.2)
    · have hz : (extensionLaw r M ell).event (E i) = 0 :=
        (extensionLaw r M ell).event_eq_zero_of_false (fun _ hω => hi ⟨hω.1,hω.2.1⟩)
      rw [hz]
      exact (Real.exp_pos _).le
  calc
    _ ≤ (extensionLaw r M ell).event (fun ω => ∃ i, E i ω) :=
      (extensionLaw r M ell).event_mono hcover
    _ ≤ ∑ i, (extensionLaw r M ell).event (E i) :=
      (extensionLaw r M ell).finite_union_bound E
    _ ≤ ∑ _ : I, errorBound N rate := Finset.sum_le_sum (fun i _ => he i)
    _ = (Fintype.card I : ℝ) * errorBound N rate := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      have hf : Fintype.card (Frame r original) ≤ N^(8*r+24) := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          frame_family_card_le r original Finset.univ (by simpa using hN)
      have ht : N^r+1 ≤ N^(r+1) := by
        have hp : 1 ≤ N^r := Nat.one_le_pow r N (by omega)
        rw [pow_succ]
        nlinarith
      have hi : Fintype.card I ≤ N^(9*r+25) := by
        change Fintype.card (Frame r original × Fin (N^r+1)) ≤ _
        rw [Fintype.card_prod, Fintype.card_fin]
        calc
          _ ≤ N^(8*r+24) * N^(r+1) := Nat.mul_le_mul hf ht
          _ = _ := by rw [←pow_add]; congr 1; omega
      exact_mod_cast hi)
      (Real.exp_pos _).le

/-- Proposition 8.1 supplies all pointwise estimates with one threshold, before
terminal data, frames and times. Thus candidate balance holds simultaneously
outside an explicit polynomial multiple of its stretched-exponential error. -/
theorem uniform_common_candidate_bound (r : ℕ) (hr : 3 ≤ r) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ B offset c C L : ℝ, 0 ≤ B → 0 ≤ offset → 0 < c → 0 < C → 0 < L →
      ∀ h : ℕ, 4*r ≤ h → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, ∀ ell : Fin N → ℕ,
      ∀ original : Finset (Finset (Fin N)),
      ∀ admissible : CoreAdmissible r M ell original offset,
      @FiniteEntropy.Law.event _ _ (@extensionLaw (Fin N) _ _ r M ell admissible.feasible)
        (fun ω => ¬ CommonCandidateBalance original h c C L B ω) ≤
          (N : ℝ)^(9*r+25) * errorBound N rate := by
  obtain ⟨rate,hrate,hbound⟩ := proposition81 r hr
  refine ⟨rate,hrate,?_⟩
  intro B offset c C L hB hoff hc hC hL h hh
  obtain ⟨N₀,hN₀⟩ := hbound B offset c C L hB hoff hc hC hL h 0 hh
  refine ⟨max N₀ 2,?_⟩
  intro N hN M ell original admissible
  letI := admissible.feasible
  exact common_candidate_failure_le h c C L B rate (le_trans (le_max_right _ _) hN)
    (fun f j hMj hj => by simpa only [Fintype.card_fin] using
      (hN₀ N (le_trans (le_max_left _ _) hN) M ell original admissible f j hMj hj).1)

/-- Uniform high probability for the simultaneous event, with a threshold
chosen before every admissible terminal instance. -/
theorem uniform_common_candidate_whp (r : ℕ) (hr : 3 ≤ r)
    (B offset c C L : ℝ) (hB : 0 ≤ B) (hoff : 0 ≤ offset)
    (hc : 0 < c) (hC : 0 < C) (hL : 0 < L) (h : ℕ) (hh : 4*r ≤ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, ∀ ell : Fin N → ℕ,
      ∀ original : Finset (Finset (Fin N)),
      ∀ admissible : CoreAdmissible r M ell original offset,
      @FiniteEntropy.Law.event _ _ (@extensionLaw (Fin N) _ _ r M ell admissible.feasible)
        (fun ω => ¬ CommonCandidateBalance original h c C L B ω) ≤ ε := by
  obtain ⟨rate,hrate,hbound⟩ := uniform_common_candidate_bound r hr
  obtain ⟨N₁,hN₁⟩ := hbound B offset c C L hB hoff hc hC hL h hh
  have he := (FrameScales.candidate_tail_tendsto_zero (9*r+25) hrate).eventually
    (gt_mem_nhds hε)
  obtain ⟨N₂,hN₂⟩ := Filter.eventually_atTop.mp he
  refine ⟨max N₁ N₂,?_⟩
  intro N hN M ell original admissible
  exact (hN₁ N (le_trans (le_max_left _ _) hN) M ell original admissible).trans
    (hN₂ N (le_trans (le_max_right _ _) hN)).le

end LooseHamilton.CandidateBalance
