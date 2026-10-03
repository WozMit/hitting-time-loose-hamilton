module

public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! Atoms and cumulative probabilities of a natural-number statistic on a finite law. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω]

@[expose] def natLawAtom (p : FiniteEntropy.Law Ω) (X : Ω → ℕ) (q : ℕ) : ℝ :=
  p.event (fun ω => X ω = q)

lemma natLawAtom_nonneg (p : FiniteEntropy.Law Ω) (X : Ω → ℕ) (q : ℕ) :
    0 ≤ natLawAtom p X q := p.event_nonneg _

lemma sum_natLawAtom_range (p : FiniteEntropy.Law Ω) (X : Ω → ℕ) (k : ℕ) :
    ∑ q ∈ range k, natLawAtom p X q = p.event (fun ω => X ω < k) := by
  classical
  unfold natLawAtom FiniteEntropy.Law.event
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp [eq_comm]

lemma sum_natLawAtom_total (p : FiniteEntropy.Law Ω) (X : Ω → ℕ) (K : ℕ)
    (hX : ∀ ω, X ω ≤ K) : ∑ q ∈ range (K+1), natLawAtom p X q = 1 := by
  rw [sum_natLawAtom_range]
  have heq : (fun ω => X ω < K+1) = (fun _ => True) := by
    funext ω
    exact propext ⟨fun _ => trivial,fun _ => by have := hX ω; omega⟩
  rw [heq,p.event_true]

lemma natLawAtom_eq_zero (p : FiniteEntropy.Law Ω) (X : Ω → ℕ) (K : ℕ)
    (hX : ∀ ω, X ω ≤ K) {q : ℕ} (hq : K < q) : natLawAtom p X q = 0 := by
  apply p.event_eq_zero_of_false
  intro ω he
  have := hX ω
  omega

lemma event_ge_eq_one_sub_atoms (p : FiniteEntropy.Law Ω) (X : Ω → ℕ) (k : ℕ) :
    p.event (fun ω => k ≤ X ω) = 1-∑ q ∈ range k, natLawAtom p X q := by
  rw [sum_natLawAtom_range,← p.event_compl]
  congr 1
  funext ω
  exact propext (not_lt.symm)
end LooseHamilton
