module

public import HittingTimeLooseHamilton.RootOuterSupportCoupling
public import HittingTimeLooseHamilton.RootInnerSubsetCoupling
public import HittingTimeLooseHamilton.RootNestedKernelCondition

public section
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
lemma rootLawMix_eq_kernel_snd {I A : Type*} [Fintype I] [Fintype A]
    (p : FiniteEntropy.Law I) (K : I→FiniteEntropy.Law A) :
    rootLawMix p K=(p.kernel K).map Prod.snd := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro a
  simp [rootLawMix,FiniteEntropy.Law.map,FiniteEntropy.Law.event,
    FiniteEntropy.Law.kernel,Fintype.sum_prod_type]
variable {A : Type*} [Fintype A] [DecidableEq A]
lemma root_swap_preserves_finset (U : Finset A) (x y : A) (hx : x∈U) (hy : y∈U) :
    U.map (Equiv.swap x y).toEmbedding=U := by
  apply Finset.eq_of_subset_of_card_le ?_ (by simp)
  intro z hz
  obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hz
  change Equiv.swap x y w∈U
  by_cases hwx : w=x
  · subst w; simpa using hy
  by_cases hwy : w=y
  · subst w; simpa using hx
  simpa [Equiv.swap_apply_of_ne_of_ne hwx hwy] using hw

/-- Exact outer marginals for conditioning the inner set to hit a fixed set.
Every test subset gains at most one point under the coupling. -/
theorem root_outer_hit_coupling (U S : Finset A) (hS : S⊆U) (b q : ℕ)
    (hbq : b≤q) (hq : q≤U.card)
    [Nonempty (FiniteNestedSubsets U b q)] [Nonempty ↥(U.powersetCard b)]
    [Nonempty ↥(U.powersetCard q)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T=>1≤(T.val∩S).card)) :
    ∃ γ : FiniteEntropy.Law (Finset A × Finset A),
      γ.map Prod.fst=(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).map Subtype.val ∧
      γ.map Prod.snd=((FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).conditionOr
        (fun p=>1≤(p.val.1∩S).card)).map (fun p=>p.val.2) ∧
      ∀z,0<γ.mass z→∀Γ : Finset A,(z.2∩Γ).card≤(z.1∩Γ).card+1 := by
  classical
  obtain ⟨π,hp₀,hp₁,hnear⟩ := root_inner_subset_one_swap_coupling U S hS b hE
  have hw (ij : ↥(U.powersetCard b) × ↥(U.powersetCard b)) (hij : 0<π.mass ij) :
      ∃g : Equiv.Perm A,U.map g.toEmbedding=U ∧
        ij.1.val.map g.toEmbedding=ij.2.val ∧
        (g=Equiv.refl A ∨ ∃a b : A,g=Equiv.swap a b) := by
    rcases (hnear ij.1 ij.2 hij).2.2 with he | ⟨x,hx,y,hy,hxy⟩
    · exact ⟨Equiv.refl A,by simp,by simpa using he,Or.inl rfl⟩
    · exact ⟨Equiv.swap x y,root_swap_preserves_finset U x y hx hy,
        by rw [Finset.map_eq_image]; exact hxy,Or.inr ⟨x,y,rfl⟩⟩
  obtain ⟨γ,hγ₀,hγ₁,hγ⟩ := root_outer_support_coupling U b q hbq hq _ _ π hp₀ hp₁ hw
  refine ⟨γ,?_,?_,hγ⟩
  · rw [hγ₀,rootLawMix_eq_kernel_snd]
    exact uniform_inner_outer_marginal U b q hbq hq
  · rw [hγ₁,rootLawMix_eq_kernel_snd]
    have hh := congrArg (fun p : FiniteEntropy.Law (↥(U.powersetCard b) × Finset A)=>p.map Prod.snd)
      (uniform_nested_conditioned_inner_kernel U b q hbq hq (fun T=>1≤(T.val∩S).card))
    rw [FiniteEntropy.Law.map_map] at hh
    simp only [FiniteEntropy.Law.conditionOr,dif_pos hE] at hh
    exact hh.symm

end LooseHamilton
