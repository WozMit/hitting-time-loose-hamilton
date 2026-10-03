module

public import HittingTimeLooseHamilton.LargeSourceEntropy
public import HittingTimeLooseHamilton.BootstrapActualSourceFrames

public section

/-! Entropy budgets for actual source frames, at the generous polynomial cutoff.
The input is the logarithmic lower bound supplied by the event A_j, never an
entropy-budget hypothesis. -/
noncomputable section
namespace LooseHamilton.BootstrapActualBudgets
open Filter Topology AuxiliaryFrame BootstrapBases

/-- A single size threshold covers every actual auxiliary frame and host. -/
theorem eventually_all_frames (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ∀ M : Finset (Finset (Fin N)),
      N = (r-1)*k+M.card → IsPairMatching M → 1 ≤ M.card →
      (M.card : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) →
      ∀ H : SimpleHypergraph (Fin N), c*N*Real.log N ≤ H.card → H.card ≤ N.choose r →
      ∀ X : ℕ, 0 < X → logarithmicBaseline r k H.card M -
        (N : ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X : ℝ) →
      ∀ F : Frame r M, (X : ℝ)*(N : ℝ)^(-(100*(r : ℝ))) ≤ F.cycleCount H →
        F.entropyBudget H 2 :=
  eventually_large_source_entropy r hr c (100*(r : ℝ)) hc (by positivity)

/-- The source count dictionary transfers the cutoff to the actual frame;
its budget is then a conclusion, with the fixed constant two. -/
theorem source_budget {N r X : ℕ} {M : Finset (Finset (Fin N))}
    (hM : IsPairMatching M) (b : Base M) (F : Frame r M)
    (P : Finset (Fin N)) (u v : Fin N) (H : SimpleHypergraph (Fin N))
    (hD : F.val.deleted = deleted b ∪ P)
    (hm : F.markers = insert {u,v} (markers hM b)) (hrel : F.val.relative = none)
    (hall : ∀ E : Frame r M,
      (X : ℝ)*(N : ℝ)^(-(100*(r : ℝ))) ≤ E.cycleCount H → E.entropyBudget H 2)
    (hsource : (X : ℝ)*(N : ℝ)^(-(100*(r : ℝ))) ≤
      completionCount r (markers hM b) (H ∩ allowedEdges r (originalPorts M))
        (deleted b ∪ P) {u,v}) : F.entropyBudget H 2 := by
  apply hall F
  rw [BootstrapActualSourceFrames.source_count hM b F P u v hD hm hrel H]
  exact hsource

/-- Legal source data produce an actual source frame with its entropy budget. -/
theorem exists_budgeted_source {N r X : ℕ} {M : Finset (Finset (Fin N))}
    (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    (P : Finset (Fin N)) (u v : Fin N) (H : SimpleHypergraph (Fin N))
    (hs : LegalPrivateCompletion r (markers hM b) P {u,v})
    (hp : ({u,v} : Finset (Fin N)) ⊆ active b)
    (hall : ∀ E : Frame r M,
      (X : ℝ)*(N : ℝ)^(-(100*(r : ℝ))) ≤ E.cycleCount H → E.entropyBudget H 2)
    (hsource : (X : ℝ)*(N : ℝ)^(-(100*(r : ℝ))) ≤
      completionCount r (markers hM b) (H ∩ allowedEdges r (originalPorts M))
        (deleted b ∪ P) {u,v}) :
    ∃ F : Frame r M, F.val.deleted = deleted b ∪ P ∧
      F.markers = insert {u,v} (markers hM b) ∧ F.val.relative = none ∧
      F.entropyBudget H 2 := by
  obtain ⟨F,hd,hm,_,hq⟩ := BootstrapActualSourceFrames.exists_source hM b hr P u v hs hp
  exact ⟨F,hd,hm,hq,source_budget hM b F P u v H hd hm hq hall hsource⟩

/-- Uniform actual-source applicability from the benchmark event. In particular,
there is no abstract budget assumption in this application theorem. -/
theorem eventually_budgeted_sources (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ∀ M : Finset (Finset (Fin N)),
      N = (r-1)*k+M.card → ∀ hM : IsPairMatching M, 1 ≤ M.card →
      (M.card : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) →
      ∀ H : SimpleHypergraph (Fin N), c*N*Real.log N ≤ H.card → H.card ≤ N.choose r →
      ∀ X : ℕ, 0 < X → logarithmicBaseline r k H.card M -
        (N : ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X : ℝ) →
      ∀ b : Base M, ∀ P : Finset (Fin N), ∀ u v : Fin N,
        LegalPrivateCompletion r (markers hM b) P {u,v} →
        ({u,v} : Finset (Fin N)) ⊆ active b →
        (X : ℝ)*(N : ℝ)^(-(100*(r : ℝ))) ≤
          completionCount r (markers hM b) (H ∩ allowedEdges r (originalPorts M))
            (deleted b ∪ P) {u,v} →
        ∃ F : Frame r M, F.val.deleted = deleted b ∪ P ∧
          F.markers = insert {u,v} (markers hM b) ∧ F.val.relative = none ∧
          F.entropyBudget H 2 := by
  filter_upwards [eventually_all_frames r hr c hc] with N hN
  intro k M hsize hM hs hsbound H hlow hhigh X hX hAX b P u v hlegal hp hsource
  exact exists_budgeted_source hM b hr P u v H hlegal hp
    (hN k M hsize hM hs hsbound H hlow hhigh X hX hAX) hsource

end LooseHamilton.BootstrapActualBudgets
