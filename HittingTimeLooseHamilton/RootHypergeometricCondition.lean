module

public import HittingTimeLooseHamilton.RootHypergeometricCount
public import HittingTimeLooseHamilton.RootHypergeometricTailShift

public section

/-! The exact one-step tail interlacing for a uniform subset conditioned to hit a fixed set. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma root_uniform_hit_tail_upper (U S : Finset A) (hS : S⊆U) (b : ℕ)
    [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T => 1≤(T.val∩S).card)) (k : ℕ) :
    ((FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).condition
      (fun T => 1≤(T.val∩S).card) hE).event (fun T => k+1≤(T.val∩S).card) ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
        (fun T => k≤(T.val∩S).card) := by
  classical
  let p : FiniteEntropy.Law ↥(U.powersetCard b) := FiniteEntropy.uniform
  let X : ↥(U.powersetCard b) → ℕ := fun T => (T.val∩S).card
  by_cases hbc : b≤(U\S).card
  · have hc : ∀i j : ℕ, i≤j → natLawAtom p X (j+1)*natLawAtom p X i ≤
        natLawAtom p X (i+1)*natLawAtom p X j := by
      intro i j hij
      dsimp [p,X]
      simp_rw [root_intersection_natLawAtom U S hS b]
      have h := rootHypergeometricWeight_cross S.card (U\S).card b hbc hij
      rw [div_mul_div_comm,div_mul_div_comm]
      exact div_le_div_of_nonneg_right h (by positivity)
    apply natLaw_hit_condition_tail_upper p X b _ hc hE k
    intro T
    exact (card_le_card inter_subset_left).trans_eq (mem_powersetCard.mp T.property).2
  · have hall (T : ↥(U.powersetCard b)) : 1≤(T.val∩S).card := by
      have hsub : T.val\S⊆U\S := sdiff_subset_sdiff (mem_powersetCard.mp T.property).1 (Subset.refl _)
      have hc := card_le_card hsub
      have hs := card_sdiff_add_card_inter T.val S
      rw [(mem_powersetCard.mp T.property).2] at hs
      omega
    rw [condition_event_eq_joint]
    have he : (fun T : ↥(U.powersetCard b) => 1≤(T.val∩S).card)=(fun _ => True) := by
      funext T
      exact propext ⟨fun _ => trivial,fun _ => hall T⟩
    rw [he,FiniteEntropy.Law.event_true,div_one]
    exact p.event_mono (fun T h => by omega)

lemma root_uniform_hit_tail_lower (U S : Finset A) (b : ℕ)
    [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T => 1≤(T.val∩S).card)) (k : ℕ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T => k≤(T.val∩S).card) ≤
    ((FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).condition
      (fun T => 1≤(T.val∩S).card) hE).event (fun T => k≤(T.val∩S).card) :=
  natLaw_hit_condition_tail_lower _ _ hE k

/-- The two stochastic inequalities printed in the proof of Lemma 5.6, valid
for every finite universe, including degenerate support positions. -/
theorem root_uniform_hit_tail_interlacing (U S : Finset A) (hS : S⊆U) (b : ℕ)
    [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T => 1≤(T.val∩S).card)) :
    ∀k : ℕ,
      (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
        (fun T => k≤(T.val∩S).card) ≤
      ((FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).condition
        (fun T => 1≤(T.val∩S).card) hE).event (fun T => k≤(T.val∩S).card) ∧
      ((FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).condition
        (fun T => 1≤(T.val∩S).card) hE).event (fun T => k+1≤(T.val∩S).card) ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
        (fun T => k≤(T.val∩S).card) := by
  intro k
  exact ⟨root_uniform_hit_tail_lower U S b hE k,root_uniform_hit_tail_upper U S hS b hE k⟩
end LooseHamilton
