module

public import HittingTimeLooseHamilton.FirstFailureDeterministic
public import HittingTimeLooseHamilton.StoppedCounting

public section

/-! Finite first-failure bounds with the terminal conditioning unchanged. -/
noncomputable section
namespace LooseHamilton.StoppedCounting
variable {E : Type*} [Fintype E] [DecidableEq E]

@[expose] def CapFailure (C : Finset (Finset E)) (C0 : ℝ) (k M : ℕ) (T : ℝ)
    (σ : FiniteOrder E) : Prop :=
  ∃ t ≤ Fintype.card E - M,
    baseline C k (Fintype.card E-t) - T ≤ Real.log (familyCount C (state σ t)) ∧
    ∃ e ∈ state σ t, C0*k/(Fintype.card E-t : ℕ) < marginal C (state σ t) e

@[expose] def PathFailure (C : Finset (Finset E)) (C0 : ℝ) (k M : ℕ) (B : ℝ)
    (σ : FiniteOrder E) : Prop :=
  ∃ t ≤ Fintype.card E - M,
    familyCount C (state σ t) = 0 ∨
    Real.log (familyCount C (state σ t)) < baseline C k (Fintype.card E-t) - B ∨
    ∃ e ∈ state σ t, C0*k/(Fintype.card E-t : ℕ) < marginal C (state σ t) e

theorem pathFailure_subset {C : Finset (Finset E)} {C0 a B T : ℝ} {k M : ℕ}
    (hC : C.Nonempty) (hM : 0<M) (hMK : M≤Fintype.card E)
    (hC0 : 0≤C0) (hsmall : C0*k/M ≤ (1/2:ℝ))
    (hbudget : a+variance C0 k M (Fintype.card E) ≤ B)
    (hmargin : a+variance C0 k M (Fintype.card E) < T)
    (σ : FiniteOrder E) (hf : PathFailure C C0 k M B σ) :
    CapFailure C C0 k M T σ ∨ Failure C C0 k M a σ := by
  classical
  by_cases hcap : CapFailure C C0 k M T σ
  · exact Or.inl hcap
  right
  by_contra hn
  have hh := all_good_of_no_failure hC hM hMK hC0 hsmall hmargin
    (fun t ht hel e he => le_of_not_gt (fun hq => hcap ⟨t,ht,hel,e,he,hq⟩)) hn
  obtain ⟨t, ht, hf⟩ := hf
  obtain ⟨hg, hlo⟩ := hh t ht
  rcases hf with hz | hlo' | ⟨e, he, hq⟩
  · exact (Nat.ne_of_gt hg.1) hz
  · linarith
  · exact (not_lt_of_ge (hg.2 e he)) hq

private theorem event_or_le {Ω : Type*} [Fintype Ω] (p : FiniteEntropy.Law Ω)
    (P Q : Ω → Prop) : p.event (fun ω => P ω ∨ Q ω) ≤ p.event P+p.event Q := by
  classical
  unfold FiniteEntropy.Law.event
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq,p.nonneg ω]

theorem first_failure_probability (C : Finset (Finset E)) (k M : ℕ) (C0 a B T : ℝ)
    (hC : C.Nonempty) (hu : UniformFamily C k) (hM : 0<M) (hMK : M≤Fintype.card E)
    (hC0 : 1≤C0) (hsmall : C0*k/M ≤ (1/2:ℝ)) (ha : 0<a)
    (hbudget : a+variance C0 k M (Fintype.card E) ≤ B)
    (hmargin : a+variance C0 k M (Fintype.card E) < T)
    (L : Finset E → Prop) (hL : 0<(deletionLaw E).event (terminalEvent M L)) :
    ((deletionLaw E).condition (terminalEvent M L) hL).event (PathFailure C C0 k M B) ≤
    ((deletionLaw E).condition (terminalEvent M L) hL).event (CapFailure C C0 k M T) +
      ((deletionLaw E).event (terminalEvent M L))⁻¹ *
        Real.exp (-a^2/(2*variance C0 k M (Fintype.card E))) := by
  let p := (deletionLaw E).condition (terminalEvent M L) hL
  have hs := p.event_mono (pathFailure_subset hC hM hMK (by linarith) hsmall hbudget hmargin)
  exact (hs.trans (event_or_le p _ _)).trans
    (add_le_add_right (conditional_stopped_counting C k M C0 hC hu hM hMK hC0 hsmall L hL a ha) _)

/-- A positive deterministic upper bound on the variance gives a useful bound
even when the actual variance vanishes. -/
theorem first_failure_probability_budget (C : Finset (Finset E)) (k M : ℕ) (C0 a B T W : ℝ)
    (hC : C.Nonempty) (hu : UniformFamily C k) (hM : 0<M) (hMK : M≤Fintype.card E)
    (hC0 : 1≤C0) (hsmall : C0*k/M ≤ (1/2:ℝ)) (ha : 0<a)
    (hW : 0<W) (hVW : variance C0 k M (Fintype.card E) ≤ W)
    (hbudget : a+W ≤ B) (hmargin : a+W < T)
    (L : Finset E → Prop) (hL : 0<(deletionLaw E).event (terminalEvent M L)) :
    ((deletionLaw E).condition (terminalEvent M L) hL).event (PathFailure C C0 k M B) ≤
    ((deletionLaw E).condition (terminalEvent M L) hL).event (CapFailure C C0 k M T) +
      ((deletionLaw E).event (terminalEvent M L))⁻¹ * Real.exp (-a^2/(2*W)) := by
  let p := (deletionLaw E).condition (terminalEvent M L) hL
  have hs := p.event_mono (pathFailure_subset hC hM hMK (by linarith) hsmall
    (show a+variance C0 k M (Fintype.card E) ≤ B by linarith)
    (show a+variance C0 k M (Fintype.card E) < T by linarith))
  have hsplit := hs.trans (event_or_le p _ _)
  apply hsplit.trans
  apply add_le_add_right
  by_cases hv : variance C0 k M (Fintype.card E) = 0
  · change ((deletionLaw E).condition (terminalEvent M L) hL).event _ ≤ _
    rw [failure_probability_zero_of_variance_zero C k M C0 hu hM hMK
      (by linarith) hsmall a ha.le hv L hL]
    positivity
  · have hvpos : 0<variance C0 k M (Fintype.card E) :=
      lt_of_le_of_ne (variance_nonneg C0 k M (Fintype.card E)) (Ne.symm hv)
    have he : -a^2/(2*variance C0 k M (Fintype.card E)) ≤ -a^2/(2*W) := by
      have hd := div_le_div_of_nonneg_left (sq_nonneg a) (by positivity : 0<2*variance C0 k M (Fintype.card E))
        (show 2*variance C0 k M (Fintype.card E) ≤ 2*W by linarith)
      simpa only [neg_div] using neg_le_neg hd
    exact (conditional_stopped_counting C k M C0 hC hu hM hMK hC0 hsmall L hL a ha).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (inv_nonneg.mpr hL.le))

end LooseHamilton.StoppedCounting
