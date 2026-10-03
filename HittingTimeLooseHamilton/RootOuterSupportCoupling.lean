module

public import HittingTimeLooseHamilton.RootOuterCoupling

public section
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
lemma root_prod_fst {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteEntropy.Law A) (q : FiniteEntropy.Law B) :
    (p.prod q).map Prod.fst=p := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro a
  simp only [FiniteEntropy.Law.map,FiniteEntropy.Law.event,FiniteEntropy.Law.prod,
    Fintype.sum_prod_type]
  simp [←mul_sum,q.total]
lemma root_prod_snd {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteEntropy.Law A) (q : FiniteEntropy.Law B) :
    (p.prod q).map Prod.snd=q := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro b
  simp only [FiniteEntropy.Law.map,FiniteEntropy.Law.event,FiniteEntropy.Law.prod,
    Fintype.sum_prod_type]
  simp [←sum_mul,p.total]
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- Only positive-probability inner pairs need relabeling witnesses. -/
theorem root_outer_support_coupling (U : Finset A) (b t : ℕ) (hbt : b≤t) (ht : t≤U.card)
    (p₀ p₁ : FiniteEntropy.Law ↥(U.powersetCard b))
    (π : FiniteEntropy.Law (↥(U.powersetCard b) × ↥(U.powersetCard b)))
    (hp₀ : π.map Prod.fst=p₀) (hp₁ : π.map Prod.snd=p₁)
    (hw : ∀ ij : ↥(U.powersetCard b) × ↥(U.powersetCard b), 0<π.mass ij →
      ∃ g : Equiv.Perm A, U.map g.toEmbedding=U ∧
        ij.1.val.map g.toEmbedding=ij.2.val ∧
        (g=Equiv.refl A ∨ ∃ a b : A,g=Equiv.swap a b)) :
    ∃ γ : FiniteEntropy.Law (Finset A × Finset A),
      γ.map Prod.fst=rootLawMix p₀ (rootOuterKernel U b t hbt ht) ∧
      γ.map Prod.snd=rootLawMix p₁ (rootOuterKernel U b t hbt ht) ∧
      ∀ z, 0<γ.mass z → ∀ Γ : Finset A, (z.2∩Γ).card ≤ (z.1∩Γ).card+1 := by
  classical
  let K := rootOuterKernel U b t hbt ht
  let C (ij : ↥(U.powersetCard b) × ↥(U.powersetCard b)) :
      FiniteEntropy.Law (Finset A × Finset A) :=
    if h : 0<π.mass ij then
      (K ij.1).map (fun T => (T,(hw ij h).choose.finsetCongr T))
    else (K ij.1).prod (K ij.2)
  have hC₀ (ij) : (C ij).map Prod.fst=K ij.1 := by
    dsimp only [C]
    split_ifs with h
    · rw [FiniteEntropy.Law.map_map]; exact (K ij.1).map_id
    · exact root_prod_fst _ _
  have hC₁ (ij) : (C ij).map Prod.snd=K ij.2 := by
    dsimp only [C]
    split_ifs with h
    · rw [FiniteEntropy.Law.map_map]
      exact rootOuterKernel_map U b t hbt ht ij.1 ij.2 _
        (hw ij h).choose_spec.1 (hw ij h).choose_spec.2.1
    · exact root_prod_snd _ _
  apply root_couple_kernels p₀ p₁ π hp₀ hp₁ K K C hC₀ hC₁
    (fun T₀ T₁ => ∀ Γ : Finset A,(T₁∩Γ).card≤(T₀∩Γ).card+1)
  intro ij z hij hz Γ
  have hz' : 0<(K ij.1).event (fun T =>
      (T,(hw ij hij).choose.finsetCongr T)=z) := by
    simp only [C,dif_pos hij] at hz
    exact hz
  obtain ⟨T,hT⟩ := exists_of_event_pos (K ij.1) _ hz'
  have h₀ : T=z.1 := congrArg Prod.fst hT
  have h₁ : (hw ij hij).choose.finsetCongr T=z.2 := congrArg Prod.snd hT
  rw [←h₀,←h₁]
  rcases (hw ij hij).choose_spec.2.2 with he | ⟨a,b,he⟩
  · rw [he]; simp
  · rw [he]; exact swap_inter_card_le T Γ a b
end LooseHamilton
