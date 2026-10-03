module

public import HittingTimeLooseHamilton.RootCountCoupling
public import HittingTimeLooseHamilton.RootHypergeometricCondition

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

@[expose] def rootIntersectionIndex (U S : Finset A) (b : ℕ) (T : ↥(U.powersetCard b)) : Fin (b+1) :=
  ⟨(T.val∩S).card,by
    have hh := (card_le_card (inter_subset_left (s₁:=T.val) (s₂:=S))).trans_eq
      (mem_powersetCard.mp T.property).2
    omega⟩

@[expose] def rootOriginalCountLaw (U S : Finset A) (b : ℕ) [Nonempty ↥(U.powersetCard b)] :
    FiniteEntropy.Law (Fin (b+1)) :=
  (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).map (rootIntersectionIndex U S b)

@[expose] def rootHitCountLaw (U S : Finset A) (b : ℕ) [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T=>1≤(T.val∩S).card)) : FiniteEntropy.Law (Fin (b+1)) :=
  ((FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).condition
    (fun T=>1≤(T.val∩S).card) hE).map (rootIntersectionIndex U S b)

lemma rootUniformCount_tail_interlacing (U S : Finset A) (hS : S⊆U) (b : ℕ)
    [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T=>1≤(T.val∩S).card)) :
    (∀ k,rootCountTail (rootOriginalCountLaw U S b) k≤rootCountTail (rootHitCountLaw U S b hE) k) ∧
    (∀ k,rootCountTail (rootHitCountLaw U S b hE) (k+1)≤rootCountTail (rootOriginalCountLaw U S b) k) := by
  have hi := root_uniform_hit_tail_interlacing U S hS b hE
  constructor <;> intro k
  · simpa only [rootCountTail,rootOriginalCountLaw,rootHitCountLaw,
      FiniteEntropy.Law.event_map,rootIntersectionIndex] using (hi k).1
  · simpa only [rootCountTail,rootOriginalCountLaw,rootHitCountLaw,
      FiniteEntropy.Law.event_map,rootIntersectionIndex] using (hi k).2

/-- Concrete coupling of the intersection count of a uniform b-set and that
count conditioned on hitting S, with a jump of at most one. -/
@[expose] def rootUniformCountCoupling (U S : Finset A) (hS : S⊆U) (b : ℕ)
    [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T=>1≤(T.val∩S).card)) : FiniteEntropy.Law (Fin (b+1)×Fin (b+1)) :=
  rootCountCoupling (rootOriginalCountLaw U S b) (rootHitCountLaw U S b hE)
    (rootUniformCount_tail_interlacing U S hS b hE).1
    (rootUniformCount_tail_interlacing U S hS b hE).2

lemma rootUniformCountCoupling_first (U S : Finset A) (hS : S⊆U) (b : ℕ)
    [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T=>1≤(T.val∩S).card)) :
    (rootUniformCountCoupling U S hS b hE).map Prod.fst=rootOriginalCountLaw U S b :=
  rootCountCoupling_first _ _ _ _

lemma rootUniformCountCoupling_second (U S : Finset A) (hS : S⊆U) (b : ℕ)
    [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T=>1≤(T.val∩S).card)) :
    (rootUniformCountCoupling U S hS b hE).map Prod.snd=rootHitCountLaw U S b hE :=
  rootCountCoupling_second _ _ _ _

lemma rootUniformCountCoupling_support (U S : Finset A) (hS : S⊆U) (b : ℕ)
    [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T=>1≤(T.val∩S).card)) (x : Fin (b+1)×Fin (b+1))
    (hx : (rootUniformCountCoupling U S hS b hE).mass x≠0) :
    x.1.val≤x.2.val ∧ x.2.val≤x.1.val+1 :=
  rootCountCoupling_support _ _ _ _ x hx

end LooseHamilton
