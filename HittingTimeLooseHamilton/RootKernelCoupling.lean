module

public import HittingTimeLooseHamilton.RootOuterTransport

public section
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators

/-- Finite averaging of conditional laws. -/
@[expose] def rootLawMix {I A : Type*} [Fintype I] [Fintype A]
    (p : FiniteEntropy.Law I) (K : I → FiniteEntropy.Law A) : FiniteEntropy.Law A where
  mass a := ∑ i, p.mass i*(K i).mass a
  nonneg a := sum_nonneg (fun i _ => mul_nonneg (p.nonneg i) ((K i).nonneg a))
  total := by rw [sum_comm]; simp_rw [←mul_sum,FiniteEntropy.Law.total,mul_one]; exact p.total

lemma rootLawMix_map {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    (p : FiniteEntropy.Law I) (K : I → FiniteEntropy.Law A) (f : A → B) :
    (rootLawMix p K).map f = rootLawMix p (fun i => (K i).map f) := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro b
  simp only [FiniteEntropy.Law.map,FiniteEntropy.Law.event,rootLawMix]
  have hsum (a : A) : (if f a=b then ∑ i, p.mass i*(K i).mass a else 0) =
      ∑ i, if f a=b then p.mass i*(K i).mass a else 0 := by
    by_cases ha : f a=b <;> simp [ha]
  simp_rw [hsum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  by_cases ha : f a=b <;> simp [ha]

lemma rootLawMix_map_index {I J A : Type*} [Fintype I] [Fintype J] [Fintype A]
    (p : FiniteEntropy.Law I) (f : I → J) (K : J → FiniteEntropy.Law A) :
    rootLawMix p (fun i => K (f i)) = rootLawMix (p.map f) K := by
  apply FiniteEntropy.Law.ext_mass
  intro a
  exact (p.sum_map_mul f (fun j => (K j).mass a)).symm

/-- Any coupling of the indices lifts through a family of coupled kernels.
Only positive-mass fibers need the desired pointwise relation. -/
theorem root_couple_kernels {I J A B : Type*}
    [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    (p : FiniteEntropy.Law I) (q : FiniteEntropy.Law J)
    (π : FiniteEntropy.Law (I×J)) (hp : π.map Prod.fst=p) (hq : π.map Prod.snd=q)
    (K : I → FiniteEntropy.Law A) (L : J → FiniteEntropy.Law B)
    (C : I×J → FiniteEntropy.Law (A×B))
    (hC₁ : ∀ ij, (C ij).map Prod.fst=K ij.1)
    (hC₂ : ∀ ij, (C ij).map Prod.snd=L ij.2)
    (Rel : A → B → Prop)
    (hrel : ∀ ij ab, 0<π.mass ij → 0<(C ij).mass ab → Rel ab.1 ab.2) :
    ∃ γ : FiniteEntropy.Law (A×B), γ.map Prod.fst=rootLawMix p K ∧
      γ.map Prod.snd=rootLawMix q L ∧ ∀ab,0<γ.mass ab→Rel ab.1 ab.2 := by
  classical
  refine ⟨rootLawMix π C,?_,?_,?_⟩
  · rw [rootLawMix_map]
    simp_rw [hC₁]
    rw [rootLawMix_map_index,hp]
  · rw [rootLawMix_map]
    simp_rw [hC₂]
    rw [rootLawMix_map_index,hq]
  · intro ab hab
    have hex : ∃ ij, 0<π.mass ij*(C ij).mass ab := by
      by_contra hn
      push_neg at hn
      exact not_le_of_gt hab (sum_nonpos (fun ij _ => hn ij))
    obtain ⟨ij,hij⟩ := hex
    have hπ := (mul_pos_iff.mp hij).elim And.left
      (fun h => False.elim (not_lt_of_ge (π.nonneg ij) h.1))
    have hc := (mul_pos_iff.mp hij).elim And.right
      (fun h => False.elim (not_lt_of_ge ((C ij).nonneg ab) h.2))
    exact hrel ij ab hπ hc
end LooseHamilton
