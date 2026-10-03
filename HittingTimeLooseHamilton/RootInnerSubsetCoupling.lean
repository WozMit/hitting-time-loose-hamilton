module

public import HittingTimeLooseHamilton.RootInnerSubsetCoordinates

public section

/-! The exact inner one-swap coupling on an arbitrary finite ambient subuniverse. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem root_inner_subset_one_swap_coupling (U S : Finset A) (_hS : S⊆U) (b : ℕ)
    [Nonempty ↥(U.powersetCard b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T=>1≤(T.val∩S).card)) :
    ∃ d : FiniteEntropy.Law (↥(U.powersetCard b) × ↥(U.powersetCard b)),
      d.map Prod.fst=(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)) ∧
      d.map Prod.snd=(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).condition
        (fun T=>1≤(T.val∩S).card) hE ∧
      ∀ T W, 0<d.mass (T,W) →
        (T.val\W.val).card≤1 ∧ (W.val\T.val).card≤1 ∧
        (T.val=W.val ∨ ∃x∈U,∃y∈U,T.val.image (Equiv.swap x y)=W.val) := by
  classical
  let e := rootInnerSubsetEquiv U b
  letI : Nonempty (RootInnerState ↥U b) := ⟨e.symm (Classical.choice inferInstance)⟩
  let S' := S.subtype (fun x=>x∈U)
  let E : ↥(U.powersetCard b) → Prop := fun T=>1≤(T.val∩S).card
  let E' : RootInnerState ↥U b → Prop := fun T=>1≤(T.val∩S').card
  have hcomp : (fun T=>E (e T))=E' := by
    funext T
    dsimp [E,E',S',e]
    rw [rootInnerSubsetEquiv_inter]
  have hE' : 0<(FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState ↥U b)).event E' := by
    rw [←hcomp,FiniteEntropy.Law.uniform_event_equiv e E]
    exact hE
  obtain ⟨c,hc₁,hc₂,hclose⟩ := root_inner_one_swap_coupling S' b hE'
  let d := c.map (fun z => (e z.1,e z.2))
  have hmap : (FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState ↥U b)).map e=
      (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)) := uniform_equiv_map e
  have hEE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event E := hE
  have hcond : ((FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState ↥U b)).condition E' hE').map e=
      (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).condition E hE := by
    have h := (FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState ↥U b)).conditionOr_map e E
    rw [hmap,hcomp] at h
    simpa only [FiniteEntropy.Law.conditionOr,dif_pos hEE,dif_pos hE'] using h.symm
  refine ⟨d,?_,?_,?_⟩
  · change (c.map _).map Prod.fst=_
    rw [FiniteEntropy.Law.map_map]
    have he := congrArg (fun p : FiniteEntropy.Law (RootInnerState ↥U b)=>p.map e) hc₁
    rw [FiniteEntropy.Law.map_map,hmap] at he
    exact he
  · change (c.map _).map Prod.snd=_
    rw [FiniteEntropy.Law.map_map]
    have he := congrArg (fun p : FiniteEntropy.Law (RootInnerState ↥U b)=>p.map e) hc₂
    rw [FiniteEntropy.Law.map_map,hcond] at he
    exact he
  · intro T W hTW
    obtain ⟨T,rfl⟩ := e.surjective T
    obtain ⟨W,rfl⟩ := e.surjective W
    have hinj : Function.Injective (fun z : RootInnerState ↥U b × RootInnerState ↥U b => (e z.1,e z.2)) := by
      intro x y h
      apply Prod.ext
      · exact e.injective (congrArg Prod.fst h)
      · exact e.injective (congrArg Prod.snd h)
    have hcpos : 0<c.mass (T,W) := by
      change 0<(c.map _).mass (e T,e W) at hTW
      rwa [c.map_mass_of_injective _ hinj (T,W)] at hTW
    obtain ⟨hnear₁,hnear₂,hswap⟩ := hclose T W hcpos
    refine ⟨?_,?_,?_⟩
    · simpa only [e,rootInnerSubsetEquiv_sdiff] using hnear₁
    · simpa only [e,rootInnerSubsetEquiv_sdiff] using hnear₂
    · rcases hswap with heq|⟨x,y,hxy⟩
      · left
        change T.val.image Subtype.val=W.val.image Subtype.val
        rw [heq]
      · right
        exact ⟨x.val,x.property,y.val,y.property,rootInnerSubsetEquiv_swap U b T W x y hxy⟩
end LooseHamilton
