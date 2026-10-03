module

public import HittingTimeLooseHamilton.PrivateMigrationCandidates
public import HittingTimeLooseHamilton.MigrationWeightedTargets

public section

/-! # Averaging private candidates over the target coordinate

A bad candidate has `r-2` private vertices, so its target incidence is counted
at most `r-2` times. The explicit exceptional-target constant is consequently
`sqrt ((r-2)*η)`. Root-link sampling is a separate deterministic hypothesis on
unordered legal labels; this module does not infer it from global density.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exceptional target vertices are defined from actual bad directed candidates. -/
@[expose] def privateExceptionalTargets (bad : Finset (Finset V × V × V))
    (ε N : ℝ) (r : ℕ) : Finset V :=
  univ.filter fun t => ε * N^(r-1) < (privateBadCandidateFiber bad t).card

/-- Finite candidate-to-target averaging, with the private-block multiplicity
made explicit. Here `N` is the ambient scale used in the candidate estimate. -/
theorem private_candidate_target_averaging {r : ℕ} (hr : 3 ≤ r)
    (bad : Finset (Finset V × V × V)) (η N : ℝ) (hη : 0 < η) (hN : 0 < N)
    (hsize : ∀ c ∈ bad, c.1.card ≤ r-2)
    (hbad : (bad.card : ℝ) ≤ η * N^r) :
    ((privateExceptionalTargets bad (Real.sqrt ((r-2 : ℕ) * η)) N r).card : ℝ) ≤
      Real.sqrt ((r-2 : ℕ) * η) * N := by
  have hd : (0 : ℝ) < (r-2 : ℕ) := by exact_mod_cast (show 0 < r-2 by omega)
  have hs := Migration.coordinate_incidence_sum_le bad (fun c => c.1) (r-2) hsize
  have hs' : (∑ t : V, (privateBadCandidateFiber bad t).card : ℝ) ≤
      (r-2 : ℕ) * (bad.card : ℝ) := by
    exact_mod_cast hs
  have he : r-1+1 = r := by omega
  apply Migration.coordinate_exceptional_targets univ
    (fun t => (privateBadCandidateFiber bad t).card)
    (Real.sqrt ((r-2 : ℕ) * η)) N (r-1)
    (fun _ _ => Nat.cast_nonneg _) (Real.sqrt_pos.2 (mul_pos hd hη)) hN
  rw [Real.sq_sqrt (mul_pos hd hη).le, he]
  calc
    _ ≤ (r-2 : ℕ) * (bad.card : ℝ) := hs'
    _ ≤ (r-2 : ℕ) * (η * N^r) := mul_le_mul_of_nonneg_left hbad hd.le
    _ = _ := by ring

/-- Outside the exceptional set the bad unordered root-link labels have the
same density upper bound; taking the image never increases cardinality. -/
theorem private_bad_labels_le_of_not_exceptional
    (bad : Finset (Finset V × V × V)) (ε N : ℝ) (r : ℕ) (t : V)
    (ht : t ∉ privateExceptionalTargets bad ε N r) :
    ((privateBadLabels bad t).card : ℝ) ≤ ε * N^(r-1) := by
  have hf : ((privateBadCandidateFiber bad t).card : ℝ) ≤ ε * N^(r-1) := by
    simpa [privateExceptionalTargets, not_lt] using ht
  exact (Nat.cast_le.mpr (privateBadLabels_card_le bad t)).trans hf

/-- Full private-coordinate deterministic implication: global directed candidate
balance, averaging with its `r-2` multiplicity, and an explicit root-link sampling
hypothesis yield constant-factor migration outside the exceptional target set.
The positive constants `κ` and `lam` expose the constant-factor quantifiers. -/
theorem private_coordinate_mobility_most_targets
    {r : ℕ} {markers host : Finset (Finset V)}
    (S q : Finset V) (x : V) (targets : Finset V) (hr : 3 ≤ r)
    (_hS : S.card = r-3)
    (_hsource : LegalPrivateCompletion r markers (insert x S) q)
    (hD : ∀ t ∈ targets, LegalPrivateCompletion r markers (insert t S) q)
    (bad : Finset (Finset V × V × V)) (η N κ lam μ : ℝ)
    (hη : 0 < η) (hN : 0 < N) (_hκ : 0 < κ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hsize : ∀ c ∈ bad, c.1.card ≤ r-2)
    (hbad : (bad.card : ℝ) ≤ η * N^r)
    (hlink : ∀ t ∈ targets,
      ((privateBadLabels bad t).card : ℝ) ≤
        Real.sqrt ((r-2 : ℕ) * η) * N^(r-1) →
      κ * migrationRootDegree host x ≤
        ((privateMigrationLabels r markers host (insert t S) q x \
          privateBadLabels bad t).card : ℝ))
    (hbalance : ∀ t ∈ targets, ∀ R u v,
      PrivateMigrationLegal r markers host (insert t S) q x R {u,v} →
      (insert t R,u,v) ∉ bad →
      lam * (completionCount r markers host (insert x S) q : ℝ) / μ ≤
        privateCandidateCompletionCount r markers host S q x (insert t R,u,v)) :
    ∃ exceptional : Finset V,
      (exceptional.card : ℝ) ≤ Real.sqrt ((r-2 : ℕ) * η) * N ∧
      ∀ t ∈ targets, t ∉ exceptional →
        κ * lam * (migrationRootDegree host x : ℝ) / μ *
            (completionCount r markers host (insert x S) q : ℝ) ≤
          completionCount r markers host (insert t S) q := by
  refine ⟨privateExceptionalTargets bad (Real.sqrt ((r-2 : ℕ) * η)) N r,
    private_candidate_target_averaging hr bad η N hη hN hsize hbad, ?_⟩
  intro t ht hnot
  exact private_coordinate_mobility_of_candidate_balance S q x t hr (hD t ht)
    bad κ lam μ hlam.le hμ
    (hlink t ht (private_bad_labels_le_of_not_exceptional bad _ N r t hnot))
    (hbalance t ht)

end LooseHamilton
