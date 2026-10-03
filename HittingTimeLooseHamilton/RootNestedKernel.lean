module

public import HittingTimeLooseHamilton.RootNestedFibres
public import HittingTimeLooseHamilton.RootOuterCard
public import HittingTimeLooseHamilton.RootFiniteKernels

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A nested pair is an inner set together with one of its outer completions. -/
@[expose] def nestedInnerSigmaEquiv (U : Finset A) (b q : ℕ) :
    FiniteNestedSubsets U b q ≃ Σ I : ↥(U.powersetCard b), OuterExtension U I.val q where
  toFun p := ⟨nestedInner U b q p,⟨p.val.2,p.property.1,p.property.2.2⟩⟩
  invFun x := ⟨(x.1.val,x.2.val),x.2.property.1,(mem_powersetCard.mp x.1.property).2,x.2.property.2⟩
  left_inv p := rfl
  right_inv x := by rcases x with ⟨I,T⟩; rfl

lemma nested_card_inner (U : Finset A) (b q : ℕ) (hbq : b≤q) :
    Fintype.card (FiniteNestedSubsets U b q)=
      (U.card.choose b)*((U.card-b).choose (q-b)) := by
  rw [Fintype.card_congr (nestedInnerSigmaEquiv U b q),Fintype.card_sigma]
  have hc (I : ↥(U.powersetCard b)) : Fintype.card (OuterExtension U I.val q)=
      (U.card-b).choose (q-b) := by
    have hI := mem_powersetCard.mp I.property
    rw [outerExtension_card U I.val q hI.1 (by omega),hI.2]
  simp_rw [hc]
  simp

@[expose] def nestedInnerOuter (U : Finset A) (b q : ℕ) (p : FiniteNestedSubsets U b q) :
    ↥(U.powersetCard b) × Finset A := (nestedInner U b q p,p.val.2)

lemma nestedInnerOuter_injective (U : Finset A) (b q : ℕ) :
    Function.Injective (nestedInnerOuter U b q) := by
  intro p t he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun x : ↥(U.powersetCard b) × Finset A => x.1.val) he
  · exact congrArg (fun x : ↥(U.powersetCard b) × Finset A=>x.2) he

lemma rootOuterKernel_mass (U : Finset A) (b q : ℕ) (hbq : b≤q) (hq : q≤U.card)
    (I : ↥(U.powersetCard b)) (T : Finset A) :
    (rootOuterKernel U b q hbq hq I).mass T =
      if I.val⊆T ∧ T∈U.powersetCard q then 1/((U.card-b).choose (q-b):ℝ) else 0 := by
  classical
  letI := outerExtension_nonempty U I.val q (mem_powersetCard.mp I.property).1
    (by rw [(mem_powersetCard.mp I.property).2]; exact hbq) hq
  change ((FiniteEntropy.uniform : FiniteEntropy.Law (OuterExtension U I.val q)).map Subtype.val).mass T=_
  by_cases hT : I.val⊆T ∧ T∈U.powersetCard q
  · rw [if_pos hT]
    have hh := (FiniteEntropy.uniform : FiniteEntropy.Law (OuterExtension U I.val q)).map_mass_of_injective
      Subtype.val Subtype.val_injective (⟨T,hT⟩ : OuterExtension U I.val q)
    rw [hh]
    simp only [FiniteEntropy.uniform,←one_div]
    rw [outerExtension_card U I.val q (mem_powersetCard.mp I.property).1
      (by rw [(mem_powersetCard.mp I.property).2]; exact hbq), (mem_powersetCard.mp I.property).2]
  · rw [if_neg hT]
    apply FiniteEntropy.Law.event_eq_zero_of_false
    intro t he
    exact hT (he ▸ t.property)

/-- Exact nested uniform sampling: first choose the inner b-set uniformly,
then choose a fresh uniform outer q-extension. -/
theorem uniform_nested_inner_kernel (U : Finset A) (b q : ℕ) (hbq : b≤q) (hq : q≤U.card)
    [Nonempty (FiniteNestedSubsets U b q)] [Nonempty ↥(U.powersetCard b)] :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).map (nestedInnerOuter U b q) =
      (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).kernel
        (rootOuterKernel U b q hbq hq) := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro ⟨I,T⟩
  change _ = (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).mass I *
    (rootOuterKernel U b q hbq hq I).mass T
  rw [rootOuterKernel_mass]
  by_cases hT : I.val⊆T ∧ T∈U.powersetCard q
  · rw [if_pos hT]
    let p : FiniteNestedSubsets U b q :=
      ⟨(I.val,T),hT.1,(mem_powersetCard.mp I.property).2,hT.2⟩
    have he : nestedInnerOuter U b q p=(I,T) := rfl
    rw [←he,FiniteEntropy.Law.map_mass_of_injective _ _ (nestedInnerOuter_injective U b q)]
    simp only [FiniteEntropy.uniform,←one_div,Fintype.card_coe,card_powersetCard,
      nested_card_inner U b q hbq,Nat.cast_mul]
    simp [div_eq_mul_inv,mul_inv_rev,mul_comm]
  · rw [if_neg hT,mul_zero]
    apply FiniteEntropy.Law.event_eq_zero_of_false
    intro p he
    have h1 : p.val.1=I.val := congrArg (fun x : ↥(U.powersetCard b)×Finset A=>x.1.val) he
    have h2 : p.val.2=T := congrArg Prod.snd he
    exact hT ⟨by rw [←h1,←h2]; exact p.property.1,by rw [←h2]; exact p.property.2.2⟩

end LooseHamilton
