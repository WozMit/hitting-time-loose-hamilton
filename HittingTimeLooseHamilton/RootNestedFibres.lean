module

public import HittingTimeLooseHamilton.RootOuterTransport

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]
attribute [local instance] Classical.propDecidable

@[expose] def nestedInner (U : Finset A) (b q : ℕ) (p : FiniteNestedSubsets U b q) : ↥(U.powersetCard b) :=
  ⟨p.val.1,mem_powersetCard.mpr ⟨p.property.1.trans (mem_powersetCard.mp p.property.2.2).1,p.property.2.1⟩⟩

@[expose] def nestedInnerFibreEquiv (U : Finset A) (b q : ℕ) (I : ↥(U.powersetCard b)) :
    {p : FiniteNestedSubsets U b q // nestedInner U b q p=I} ≃ OuterExtension U I.val q where
  toFun p := ⟨p.val.val.2,by
    have he : p.val.val.1=I.val := congrArg Subtype.val p.property
    exact ⟨he ▸ p.val.property.1,p.val.property.2.2⟩⟩
  invFun T := ⟨⟨(I.val,T.val),T.property.1,(mem_powersetCard.mp I.property).2,T.property.2⟩,rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg Subtype.val p.property).symm
    · rfl
  right_inv T := rfl

end LooseHamilton
