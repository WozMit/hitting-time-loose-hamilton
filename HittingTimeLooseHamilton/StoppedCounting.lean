module

public import HittingTimeLooseHamilton.StoppedCountingStatement
public import HittingTimeLooseHamilton.StoppedCountingTelescope
public import HittingTimeLooseHamilton.StoppedCountingMartingale
public import HittingTimeLooseHamilton.StoppedExponentialZero

public section

/-! Conditional stopped counting under the actual uniform deletion path law. -/
noncomputable section
namespace LooseHamilton.StoppedCounting
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E]

theorem stopped_differences (C : Finset (Finset E)) (C0 : ℝ) (k M : ℕ)
    (hC : UniformFamily C k) :
    StoppedExponential.Differences (deletionLaw E)
      (fun t σ => increment C C0 k M σ t)
      (fun t σ τ => StoppedDeletion.History (Fintype.card E-t) σ =
        StoppedDeletion.History (Fintype.card E-t) τ) (Fintype.card E-M) := by
  constructor
  · intro t _ σ τ h u hu
    exact increment_history C C0 k M hu h
  · intro t _ f _ hf
    apply increment_centering C C0 k M t hC
    intro σ τ h
    simp only [deletionLaw, FiniteEntropy.uniform, hf σ τ h]

theorem failure_subset_crossing (C : Finset (Finset E)) (C0 : ℝ) (k M : ℕ)
    (hM : 0 < M) (hMK : M ≤ Fintype.card E) (hC0 : 0 ≤ C0)
    (hsmall : C0*k/M ≤ (1/2:ℝ)) (a : ℝ) (σ : FiniteOrder E)
    (hf : Failure C C0 k M a σ) :
    ∃ t ≤ Fintype.card E-M,
      a < StoppedExponential.partialSum (fun u τ => increment C C0 k M τ u) t σ := by
  obtain ⟨t, ht, hd⟩ := hf
  refine ⟨t, ht.1, ?_⟩
  apply deficit_implies_stopped_sum hM hMK hC0 hsmall ht
  dsimp [baseline] at hd
  linarith

theorem unconditional_stopped_counting (C : Finset (Finset E)) (k M : ℕ) (C0 : ℝ)
    (hC : UniformFamily C k) (hM : 0 < M) (hMK : M ≤ Fintype.card E)
    (hC0 : 0 ≤ C0) (hsmall : C0*k/M ≤ (1/2:ℝ)) (a : ℝ) (ha : 0 < a) :
    (deletionLaw E).event (Failure C C0 k M a) ≤
      Real.exp (-a^2 / (2 * variance C0 k M (Fintype.card E))) := by
  have hb : ∀ t < Fintype.card E-M, 0 ≤ cap E C0 k t := by
    intro t _
    exact div_nonneg (mul_nonneg hC0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hm := StoppedExponential.maximal_total (deletionLaw E)
    (fun t σ => increment C C0 k M σ t) _ (Fintype.card E-M)
    (stopped_differences C C0 k M hC) (cap E C0 k) hb
    (fun t _ σ => increment_abs_le hC hC0 σ t) a ha
  have hv : variance C0 k M (Fintype.card E) =
      ∑ t ∈ range (Fintype.card E-M), (cap E C0 k t)^2 :=
    variance_eq_sum_steps C0 k M (Fintype.card E) hMK
  rw [← hv] at hm
  exact ((deletionLaw E).event_mono
    (failure_subset_crossing C C0 k M hM hMK hC0 hsmall a)).trans hm

/-- The manuscript's Theorem 11.1, with terminal conditioning left untouched. -/
theorem conditional_stopped_counting : Statement E := by
  intro C k M C0 _hne hC hM hMK hC0 hsmall L hL a ha
  exact conditional_event_bound (deletionLaw E) (terminalEvent M L)
    (Failure C C0 k M a) hL
    (unconditional_stopped_counting C k M C0 hC hM hMK (by linarith) hsmall a ha)

/-- The degenerate zero-variance case has failure probability exactly zero.
This avoids interpreting the manuscript's exponential quotient at V=0. -/
theorem failure_probability_zero_of_variance_zero (C : Finset (Finset E))
    (k M : ℕ) (C0 : ℝ) (hC : UniformFamily C k) (hM : 0 < M)
    (hMK : M ≤ Fintype.card E) (hC0 : 0 ≤ C0)
    (hsmall : C0*k/M ≤ (1/2:ℝ)) (a : ℝ) (ha : 0 ≤ a)
    (hv : variance C0 k M (Fintype.card E) = 0)
    (L : Finset E → Prop) (hL : 0 < (deletionLaw E).event (terminalEvent M L)) :
    ((deletionLaw E).condition (terminalEvent M L) hL).event (Failure C C0 k M a) = 0 := by
  have hv' : ∑ t ∈ range (Fintype.card E-M), (cap E C0 k t)^2 = 0 := by
    unfold cap
    rw [← variance_eq_sum_steps C0 k M (Fintype.card E) hMK]
    exact hv
  have hz := StoppedExponential.zero_variance (deletionLaw E)
    (fun t σ => increment C C0 k M σ t) (Fintype.card E-M) (cap E C0 k)
    (fun t _ σ => increment_abs_le hC hC0 σ t) a ha hv'
  have hp : (deletionLaw E).event (Failure C C0 k M a) ≤ 0 := by
    calc
      _ ≤ _ := (deletionLaw E).event_mono
        (failure_subset_crossing C C0 k M hM hMK hC0 hsmall a)
      _ = 0 := hz
  apply le_antisymm _ (((deletionLaw E).condition (terminalEvent M L) hL).event_nonneg _)
  simpa using conditional_event_bound (deletionLaw E) (terminalEvent M L)
    (Failure C C0 k M a) hL hp

end LooseHamilton.StoppedCounting

namespace LooseHamilton
theorem theorem111 : Theorem111 := by
  intro E _ _
  exact StoppedCounting.conditional_stopped_counting
end LooseHamilton
