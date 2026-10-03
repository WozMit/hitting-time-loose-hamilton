module

public import HittingTimeLooseHamilton.StoppedCountingPath
public import HittingTimeLooseHamilton.StoppedCountingVariance
public import HittingTimeLooseHamilton.StoppedCountingConditioning

public section

/-! Exact finite specification of the manuscript's Conditional stopped counting
theorem (`thm:stoppedabstract`, Theorem 11.1). A terminal event is a predicate
of the size-M host. The stopping rule itself observes only deletion history.
The state reached by the first failing active deletion is included. -/
noncomputable section
namespace LooseHamilton.StoppedCounting
variable {E : Type*} [Fintype E] [DecidableEq E]

@[expose] def baseline (C : Finset (Finset E)) (k j : ℕ) : ℝ :=
  Real.log (familyCount C Finset.univ) - k * deletionHarmonic j (Fintype.card E)

@[expose] def Failure (C : Finset (Finset E)) (C0 : ℝ) (k M : ℕ) (a : ℝ)
    (σ : FiniteOrder E) : Prop :=
  ∃ t : ℕ, Reached C C0 k M σ t ∧
    Real.log (familyCount C (state σ t)) - baseline C k (Fintype.card E - t) <
      -a - variance C0 k M (Fintype.card E)

/-- Uniform deletion is a uniformly sampled rank bijection. -/
@[expose] def deletionLaw (E : Type*) [Fintype E] [DecidableEq E] : FiniteEntropy.Law (FiniteOrder E) := by
  letI : Nonempty (FiniteOrder E) := ⟨Fintype.equivFin E⟩
  exact FiniteEntropy.uniform

@[expose] def terminalEvent (M : ℕ) (L : Finset E → Prop) (σ : FiniteOrder E) : Prop :=
  L (orderPrefix σ M)

@[expose] def Statement (E : Type*) [Fintype E] [DecidableEq E] : Prop :=
  ∀ (C : Finset (Finset E)) (k M : ℕ) (C0 : ℝ),
    C.Nonempty → UniformFamily C k → 0 < M → M ≤ Fintype.card E →
    1 ≤ C0 → C0 * k / M ≤ (1 / 2 : ℝ) →
    ∀ (L : Finset E → Prop) (hL : 0 < (deletionLaw E).event (terminalEvent M L)),
    ∀ a : ℝ, 0 < a →
      ((deletionLaw E).condition (terminalEvent M L) hL).event (Failure C C0 k M a) ≤
        ((deletionLaw E).event (terminalEvent M L))⁻¹ *
          Real.exp (-a ^ 2 / (2 * variance C0 k M (Fintype.card E)))

end LooseHamilton.StoppedCounting

namespace LooseHamilton
@[expose] def Theorem111 : Prop :=
  ∀ (E : Type) [Fintype E] [DecidableEq E], StoppedCounting.Statement E
end LooseHamilton
