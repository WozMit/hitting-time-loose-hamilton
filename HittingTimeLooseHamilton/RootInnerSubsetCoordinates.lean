module

public import HittingTimeLooseHamilton.RootLinkInnerCoupling
public import HittingTimeLooseHamilton.RootOuterTransport

public section

/-! Subtype coordinates for the one-swap coupling on an arbitrary finite universe. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

@[expose] def rootInnerSubsetEquiv (U : Finset A) (b : ℕ) :
    RootInnerState ↥U b ≃ ↥(U.powersetCard b) where
  toFun T := ⟨T.val.image Subtype.val,mem_powersetCard.mpr ⟨by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact y.property,by
    rw [card_image_of_injective _ Subtype.val_injective]
    exact (mem_powersetCard.mp T.property).2⟩⟩
  invFun T := ⟨T.val.subtype (fun x=>x∈U),mem_powersetCard.mpr ⟨subset_univ _,by
    rw [card_subtype]
    have he : T.val.filter (fun x=>x∈U)=T.val := filter_true_of_mem (mem_powersetCard.mp T.property).1
    rw [he]
    exact (mem_powersetCard.mp T.property).2⟩⟩
  left_inv T := by
    apply Subtype.ext
    ext x
    simp only [mem_subtype,mem_image]
    constructor
    · rintro ⟨y,hy,he⟩
      exact (Subtype.ext he) ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  right_inv T := by
    apply Subtype.ext
    ext x
    simp only [mem_image,mem_subtype]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,(mem_powersetCard.mp T.property).1 hx⟩,hx,rfl⟩

lemma rootInnerSubsetEquiv_inter (U S : Finset A) (b : ℕ) (T : RootInnerState ↥U b) :
    (((rootInnerSubsetEquiv U b) T).val∩S).card=
      (T.val∩S.subtype (fun x=>x∈U)).card := by
  have he : (((rootInnerSubsetEquiv U b) T).val∩S)=
      (T.val∩S.subtype (fun x=>x∈U)).image Subtype.val := by
    ext x
    simp only [rootInnerSubsetEquiv,Equiv.coe_fn_mk,mem_inter,mem_image,mem_subtype]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hs⟩
      exact ⟨y,⟨hy,hs⟩,rfl⟩
    · rintro ⟨y,⟨hy,hs⟩,rfl⟩
      exact ⟨⟨y,hy,rfl⟩,hs⟩
  rw [he,card_image_of_injective _ Subtype.val_injective]

lemma rootInnerSubsetEquiv_sdiff (U : Finset A) (b : ℕ) (T W : RootInnerState ↥U b) :
    (((rootInnerSubsetEquiv U b) T).val\((rootInnerSubsetEquiv U b) W).val).card=
      (T.val\W.val).card := by
  change (T.val.image Subtype.val\W.val.image Subtype.val).card=_
  rw [←image_sdiff _ _ Subtype.val_injective,card_image_of_injective _ Subtype.val_injective]

lemma rootSubtype_swap (U : Finset A) (x y z : ↥U) :
    (Equiv.swap x y z).val=Equiv.swap x.val y.val z.val := by
  by_cases hzx : z=x
  · subst z
    simp
  by_cases hzy : z=y
  · subst z
    simp
  rw [Equiv.swap_apply_of_ne_of_ne hzx hzy,Equiv.swap_apply_of_ne_of_ne]
  · exact fun h=>hzx (Subtype.ext h)
  · exact fun h=>hzy (Subtype.ext h)

lemma rootInnerSubsetEquiv_swap (U : Finset A) (b : ℕ) (T W : RootInnerState ↥U b)
    (x y : ↥U) (h : T.val.image (Equiv.swap x y)=W.val) :
    (((rootInnerSubsetEquiv U b) T).val).image (Equiv.swap x.val y.val)=
      ((rootInnerSubsetEquiv U b) W).val := by
  have hh := congrArg (fun Z : Finset ↥U=>Z.image Subtype.val) h
  change (T.val.image Subtype.val).image (Equiv.swap x.val y.val)=W.val.image Subtype.val
  rw [image_image] at hh ⊢
  convert hh using 1
  congr 1
  funext z
  exact (rootSubtype_swap U x y z).symm
end LooseHamilton
