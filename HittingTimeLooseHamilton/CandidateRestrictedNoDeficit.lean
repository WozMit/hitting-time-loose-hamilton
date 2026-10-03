module

public import HittingTimeLooseHamilton.RestrictedNoDeficit
public import HittingTimeLooseHamilton.CandidateBalanceSpecification

public section

/-! Item 30.5 applied to the actual frame batch from item 30.2.
All terminal constraints remain on the original vertex set. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame

/-- The printed pointwise no-deficit estimate for the exact frame experiment.
The remaining numeric hypotheses (k comparable to N and the range of nu) are
explicit and will be discharged uniformly in item 30.8. -/
theorem frame_pointwise_no_deficit {C K : ℝ} (hC : 0 < C) (hK : 0 < K) (B : ℝ) :
    ∃ N₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ (r M : ℕ) (ell : V → ℕ) (original : Finset (Finset V)),
      CoreAdmissible r M ell original B →
      ∀ ω : Outcome V r M ell, TerminalRegular C ω.1.val →
      ∀ (f : Frame r original) (D : Finset V) (j : ℕ),
      (Fintype.card V:ℝ) ≤ K*f.k →
      1 ≤ FrameScales.nu (Fintype.card V) →
      FrameScales.nu (Fintype.card V) ≤ Real.log (Fintype.card V:ℝ) →
      let H := extensionState ω.1 ω.2 j
      let J0 := unexposed f D H
      let τ := batchSize f D H
      τ ≤ J0.card ∧
        1-noDeficitError (C*K) (epsilon/8) (Fintype.card V)
          (FrameScales.nu (Fintype.card V)) ≤
        (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder J0.card)).event
          (fun σ => ∀ v, ell v ≤ vertexDegree
            (exposed f D ω.1.val ∪ (unexposed f D ω.1.val \
              batchSelection J0 J0.card rfl τ σ)) v) := by
  obtain ⟨N₀,hN₀⟩ := restricted_no_deficit_exposure hC hK B
  refine ⟨N₀,?_⟩
  intro V _ _ hN r M ell original hadm ω ht f D j hk hnu hnulog
  exact hN₀ V hN r M ell original hadm ω.1 ht
    (samplingUniverse f D) (unexposed f D (extensionState ω.1 ω.2 j))
    (exposed f D ω.1.val) (unexposed f D ω.1.val)
    inter_subset_right rfl rfl f.k (FrameScales.nu (Fintype.card V)) hk hnu hnulog

end LooseHamilton.CandidateBalance
