module

public import HittingTimeLooseHamilton.StoppedCountingStatement

public section

/-! The first-failure argument for an arbitrary finite family under deletion.
A reached state includes the first state whose count or marginal test could
fail. Its count is positive by the exact deletion identity, independently of
any convention for the logarithm of zero. -/
noncomputable section
namespace LooseHamilton.StoppedCounting
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A stopped lower bound strictly inside the eligibility threshold prevents
any first failure of either positivity or the marginal cap. -/
theorem all_good_of_reached_lower
    {C : Finset (Finset E)} {C0 a T : ℝ} {k M : ℕ} {σ : FiniteOrder E}
    (hC : C.Nonempty) (hM : 0 < M) (hMK : M ≤ Fintype.card E)
    (hC0 : 0 ≤ C0) (hsmall : C0 * k / M ≤ (1 / 2 : ℝ))
    (hmargin : a + variance C0 k M (Fintype.card E) < T)
    (hcap : ∀ t ≤ Fintype.card E - M,
      baseline C k (Fintype.card E - t) - T ≤ Real.log (familyCount C (state σ t)) →
      ∀ e ∈ state σ t, marginal C (state σ t) e ≤ C0 * k / (Fintype.card E - t : ℕ))
    (hlower : ∀ t, Reached C C0 k M σ t →
      baseline C k (Fintype.card E - t) - a - variance C0 k M (Fintype.card E) ≤
        Real.log (familyCount C (state σ t))) :
    ∀ t ≤ Fintype.card E - M,
      Good C C0 k σ t ∧
      baseline C k (Fintype.card E - t) - a - variance C0 k M (Fintype.card E) ≤
        Real.log (familyCount C (state σ t)) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    have hreach : Reached C C0 k M σ t :=
      ⟨ht, fun u hu => (ih u hu (by omega)).1⟩
    have hpos := reached_count_pos hC hM hMK hC0 hsmall hreach
    have hlo := hlower t hreach
    exact ⟨⟨hpos, hcap t ht (by linarith)⟩, hlo⟩

/-- Absence of the stopped-counting failure event and an eligible-state
marginal cap imply the count bound and marginal cap along the entire path. -/
theorem all_good_of_no_failure
    {C : Finset (Finset E)} {C0 a T : ℝ} {k M : ℕ} {σ : FiniteOrder E}
    (hC : C.Nonempty) (hM : 0 < M) (hMK : M ≤ Fintype.card E)
    (hC0 : 0 ≤ C0) (hsmall : C0 * k / M ≤ (1 / 2 : ℝ))
    (hmargin : a + variance C0 k M (Fintype.card E) < T)
    (hcap : ∀ t ≤ Fintype.card E - M,
      baseline C k (Fintype.card E - t) - T ≤ Real.log (familyCount C (state σ t)) →
      ∀ e ∈ state σ t, marginal C (state σ t) e ≤ C0 * k / (Fintype.card E - t : ℕ))
    (hno : ¬ Failure C C0 k M a σ) :
    ∀ t ≤ Fintype.card E - M,
      Good C C0 k σ t ∧
      baseline C k (Fintype.card E - t) - a - variance C0 k M (Fintype.card E) ≤
        Real.log (familyCount C (state σ t)) := by
  apply all_good_of_reached_lower hC hM hMK hC0 hsmall hmargin hcap
  intro t ht
  have hn : ¬ (Real.log (familyCount C (state σ t)) -
      baseline C k (Fintype.card E - t) < -a - variance C0 k M (Fintype.card E)) :=
    fun hh => hno ⟨t, ht, hh⟩
  have := le_of_not_gt hn
  linarith

/-- The same conclusion includes the weaker eligibility bound at every state. -/
theorem all_eligible_of_no_failure
    {C : Finset (Finset E)} {C0 a T : ℝ} {k M : ℕ} {σ : FiniteOrder E}
    (hC : C.Nonempty) (hM : 0 < M) (hMK : M ≤ Fintype.card E)
    (hC0 : 0 ≤ C0) (hsmall : C0 * k / M ≤ (1 / 2 : ℝ))
    (hmargin : a + variance C0 k M (Fintype.card E) < T)
    (hcap : ∀ t ≤ Fintype.card E - M,
      baseline C k (Fintype.card E - t) - T ≤ Real.log (familyCount C (state σ t)) →
      ∀ e ∈ state σ t, marginal C (state σ t) e ≤ C0 * k / (Fintype.card E - t : ℕ))
    (hno : ¬ Failure C C0 k M a σ) :
    ∀ t ≤ Fintype.card E - M,
      0 < familyCount C (state σ t) ∧
      baseline C k (Fintype.card E - t) - T < Real.log (familyCount C (state σ t)) ∧
      ∀ e ∈ state σ t, marginal C (state σ t) e ≤ C0 * k / (Fintype.card E - t : ℕ) := by
  intro t ht
  obtain ⟨hg, hlo⟩ := all_good_of_no_failure hC hM hMK hC0 hsmall hmargin hcap hno t ht
  exact ⟨hg.1, by linarith, hg.2⟩

end LooseHamilton.StoppedCounting
