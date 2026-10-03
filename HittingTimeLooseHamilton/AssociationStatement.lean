module

public import HittingTimeLooseHamilton.AssociationModels
public import HittingTimeLooseHamilton.OneVertexStatement

public section

/-! Exact statement of Lemma 4.2: degree-preserving association switching. -/
noncomputable section
namespace LooseHamilton

/-- Lemma 4.2 in the original fixed feasible degree-sequence model.
The denominator is a real difference and must be strictly positive. The set
B is arbitrary once the degree sequence is fixed; it is not chosen from the
random graph. No Hamiltonicity or asymptotic hypothesis is imposed. -/
@[expose] def Lemma42 : Prop :=
  ∀ (N r : ℕ), 0 < N → 3 ≤ r → ∀ d : Fin N → ℕ,
    ∀ [Nonempty (FixedDegreeState (Fin N) r d)], ∀ (y : Fin N) (B : Finset (Fin N)),
    y ∉ B → ∀ hA : 0 < associationSlack r d B,
    PoissonDominated (fixedDegreeLaw r d) (fun F => associationStatistic F.val y B)
      ⟨associationRate r d y B,associationRate_nonneg hA⟩
end LooseHamilton
