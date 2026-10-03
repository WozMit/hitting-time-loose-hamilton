module

public import HittingTimeLooseHamilton.KahnHistory
public import HittingTimeLooseHamilton.KahnMixtureEntropy
public import HittingTimeLooseHamilton.KahnStatement
public import HittingTimeLooseHamilton.KahnRevealData
public import HittingTimeLooseHamilton.KahnMatchingRandomOrder

public section

/-! Applying the ordered entropy chain rule to perfect matchings. -/
open scoped BigOperators
noncomputable section
namespace Kahn.MatchingLaw
variable {n r : ℕ} {H : Hypergraph n r}

/-- Reindexing all companion observations in any vertex order remains injective. -/
lemma ordered_companions_injective (hr : 0 < r) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun M : MatchingIn H => fun i : Fin n =>
      M.val.companion (σ.symm i)) := by
  intro M N h
  apply Subtype.ext
  apply M.val.ext_companion hr
  intro v
  have hv := congr_fun h (σ v)
  simpa using hv

/-- The chain-rule identity before averaging the independently chosen vertex order. -/
theorem entropy_chain_permutation (μ : FiniteEntropy.Law (MatchingIn H))
    (hr : 0 < r) (σ : Equiv.Perm (Fin n)) :
    FiniteEntropy.entropy μ.mass =
      ∑ v : Fin n, μ.conditionalMapEntropy (fun M => M.val.companion v)
        (fun M => M.val.past σ v) := by
  let X : Fin n → MatchingIn H → Finset (Fin n) :=
    fun i M => M.val.companion (σ.symm i)
  have hc := μ.entropy_ordered_chain X (ordered_companions_injective hr σ)
  have hcond (i : Fin n) :
      μ.conditionalMapEntropy (X i) (FiniteEntropy.Law.history X i.val) =
      μ.conditionalMapEntropy (fun M => M.val.companion (σ.symm i))
        (fun M => M.val.past σ (σ.symm i)) := by
    apply μ.conditionalMapEntropy_eq_of_factors (X i)
      (FiniteEntropy.Law.history X i.val) (fun M => M.val.past σ (σ.symm i))
      (fun h w => h (σ w)) (fun h j => h (σ.symm j))
    · funext M w
      simp [FiniteEntropy.Law.history, PerfectMatching.past, X]
    · funext M j
      simp [FiniteEntropy.Law.history, PerfectMatching.past, X]
  rw [hc]
  simp_rw [hcond]
  exact Equiv.sum_comp σ.symm (fun v =>
    μ.conditionalMapEntropy (fun M => M.val.companion v) (fun M => M.val.past σ v))

/-- Conditioning on the reveal evidence is a coarsening of conditioning on the past. -/
lemma conditionalEntropy_le_evidence (μ : FiniteEntropy.Law (MatchingIn H))
    (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    μ.conditionalMapEntropy (fun M => M.val.companion v) (fun M => M.val.past σ v) ≤
    μ.conditionalMapEntropy (fun M => M.val.companion v) (fun M => M.val.evidence σ v) := by
  have h := μ.conditionalMapEntropy_comp_le (fun M => M.val.companion v)
    (fun M => M.val.past σ v) (PerfectMatching.evidenceFromPast r σ v)
  simpa only [Function.comp_def, PerfectMatching.evidenceFromPast_eq] using h

/-- The entropy inequality for a fixed order, before forgetting that order. -/
lemma entropy_le_evidence (μ : FiniteEntropy.Law (MatchingIn H))
    (hr : 0 < r) (σ : Equiv.Perm (Fin n)) :
    FiniteEntropy.entropy μ.mass ≤
      ∑ v : Fin n, μ.conditionalMapEntropy (fun M => M.val.companion v)
        (fun M => M.val.evidence σ v) := by
  rw [entropy_chain_permutation μ hr σ]
  exact Finset.sum_le_sum (fun v _ => conditionalEntropy_le_evidence μ σ v)

/-- Averaging an independent vertex order and then forgetting it gives (30).
The order law may be arbitrary; the counting argument later takes it uniform. -/
theorem entropy_le_mixed_evidence (μ : FiniteEntropy.Law (MatchingIn H))
    (hr : 0 < r) (ν : FiniteEntropy.Law (Equiv.Perm (Fin n))) :
    FiniteEntropy.entropy μ.mass ≤
      ∑ v : Fin n, (ν.prod μ).conditionalMapEntropy
        (fun sM => sM.2.val.companion v) (fun sM => sM.2.val.evidence sM.1 v) := by
  calc
    FiniteEntropy.entropy μ.mass = ∑ σ, ν.mass σ * FiniteEntropy.entropy μ.mass := by
      rw [← Finset.sum_mul, ν.total, one_mul]
    _ ≤ ∑ σ, ν.mass σ * ∑ v : Fin n,
        μ.conditionalMapEntropy (fun M => M.val.companion v)
          (fun M => M.val.evidence σ v) :=
      Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left
        (entropy_le_evidence μ hr σ) (ν.nonneg σ))
    _ = ∑ v : Fin n, ∑ σ, ν.mass σ *
        μ.conditionalMapEntropy (fun M => M.val.companion v)
          (fun M => M.val.evidence σ v) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := Finset.sum_le_sum (fun v _ => ν.average_conditionalMapEntropy_le μ
      (fun _ M => M.val.companion v) (fun σ M => M.val.evidence σ v))

/-- Equation (30), with a uniform independent order and the tagged reveal law. -/
theorem entropy_le_jointReveal (μ : FiniteEntropy.Law (MatchingIn H)) (hr : 0 < r) :
    FiniteEntropy.entropy μ.mass ≤
      ∑ v : Fin n, (jointRevealLaw μ v).conditionalEntropy Prod.snd := by
  have h := entropy_le_mixed_evidence μ hr
    (FiniteEntropy.uniform (A := Equiv.Perm (Fin n)))
  apply le_trans h
  apply Finset.sum_le_sum
  intro v _
  exact (orderLaw μ).conditionalMapEntropy_comp_le
    (fun sM => sM.2.val.companion v) (fun sM => sM.2.val.evidence sM.1 v)
    tagEvidence

end Kahn.MatchingLaw
