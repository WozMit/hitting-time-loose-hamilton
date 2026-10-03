module

public import HittingTimeLooseHamilton.RootOuterKernel
public import HittingTimeLooseHamilton.RootKernelCoupling
public import HittingTimeLooseHamilton.UniformConditionalEquivalence

public section
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- An inner-subset coupling lifts to fresh uniform outer extensions.
The relabeling may be arbitrary on zero-mass pairs; on the support it is one
transposition or the identity. Both outer marginals are exact mixtures. -/
theorem root_outer_coupling (U : Finset A) (b t : ℕ) (hbt : b≤t) (ht : t≤U.card)
    (p₀ p₁ : FiniteEntropy.Law ↥(U.powersetCard b))
    (π : FiniteEntropy.Law (↥(U.powersetCard b) × ↥(U.powersetCard b)))
    (hp₀ : π.map Prod.fst=p₀) (hp₁ : π.map Prod.snd=p₁)
    (g : ↥(U.powersetCard b) × ↥(U.powersetCard b) → Equiv.Perm A)
    (hU : ∀ ij, U.map (g ij).toEmbedding=U)
    (hI : ∀ ij : ↥(U.powersetCard b) × ↥(U.powersetCard b), ij.1.val.map (g ij).toEmbedding=ij.2.val)
    (hsmall : ∀ ij, 0<π.mass ij →
      g ij=Equiv.refl A ∨ ∃ a b : A, g ij=Equiv.swap a b) :
    ∃ γ : FiniteEntropy.Law (Finset A × Finset A),
      γ.map Prod.fst=rootLawMix p₀ (rootOuterKernel U b t hbt ht) ∧
      γ.map Prod.snd=rootLawMix p₁ (rootOuterKernel U b t hbt ht) ∧
      ∀ z, 0<γ.mass z → ∀ Γ : Finset A, (z.2∩Γ).card ≤ (z.1∩Γ).card+1 := by
  classical
  let K := rootOuterKernel U b t hbt ht
  let C (ij : ↥(U.powersetCard b) × ↥(U.powersetCard b)) :
      FiniteEntropy.Law (Finset A × Finset A) :=
    (K ij.1).map (fun T => (T,(g ij).finsetCongr T))
  have hC₀ (ij) : (C ij).map Prod.fst=K ij.1 := by
    dsimp only [C]
    rw [FiniteEntropy.Law.map_map]
    exact (K ij.1).map_id
  have hC₁ (ij) : (C ij).map Prod.snd=K ij.2 := by
    dsimp only [C]
    rw [FiniteEntropy.Law.map_map]
    exact rootOuterKernel_map U b t hbt ht ij.1 ij.2 (g ij) (hU ij) (hI ij)
  apply root_couple_kernels p₀ p₁ π hp₀ hp₁ K K C hC₀ hC₁
    (fun T₀ T₁ => ∀ Γ : Finset A,(T₁∩Γ).card≤(T₀∩Γ).card+1)
  intro ij z hij hz Γ
  have hz' : 0<(K ij.1).event (fun T => (T,(g ij).finsetCongr T)=z) := hz
  obtain ⟨T,hT⟩ := exists_of_event_pos (K ij.1) _ hz'
  have h₀ : T=z.1 := congrArg Prod.fst hT
  have h₁ : (g ij).finsetCongr T=z.2 := congrArg Prod.snd hT
  rw [←h₀,←h₁]
  rcases hsmall ij hij with he | ⟨a,b,he⟩
  · rw [he]
    simp
  · rw [he]
    exact swap_inter_card_le T Γ a b
end LooseHamilton
