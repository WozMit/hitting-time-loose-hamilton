module

public import HittingTimeLooseHamilton.NestedPairLaw
public import HittingTimeLooseHamilton.KahnOrdering

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A smaller k-set nested inside a t-set from the prescribed universe. -/
@[expose] def FiniteNestedSubsets (Ω : Finset A) (k t : ℕ) :=
  {p : Finset A × Finset A // p.1 ⊆ p.2 ∧ p.1.card=k ∧ p.2 ∈ Ω.powersetCard t}

@[expose] instance (Ω : Finset A) (k t : ℕ) : Fintype (FiniteNestedSubsets Ω k t) := by
  classical
  unfold FiniteNestedSubsets
  infer_instance

@[expose] instance (Ω : Finset A) (k t : ℕ) : DecidableEq (FiniteNestedSubsets Ω k t) :=
  Classical.decEq _

@[expose] def nestedOuter (Ω : Finset A) (k t : ℕ) (p : FiniteNestedSubsets Ω k t) :
    ↥(Ω.powersetCard t) := ⟨p.val.2,p.property.2.2⟩

lemma nestedOuter_fiber_card (Ω : Finset A) (k t : ℕ) (T : ↥(Ω.powersetCard t)) :
    (univ.filter (fun p : FiniteNestedSubsets Ω k t => nestedOuter Ω k t p = T)).card =
      t.choose k := by
  classical
  have ht : T.val.card=t := (mem_powersetCard.mp T.property).2
  calc
    _ = (T.val.powersetCard k).card := ?_
    _ = _ := by rw [card_powersetCard,ht]
  apply card_bij (fun p _ => p.val.1)
  · intro p hp
    have he : p.val.2=T.val := congrArg Subtype.val (mem_filter.mp hp).2
    exact mem_powersetCard.mpr ⟨he ▸ p.property.1,p.property.2.1⟩
  · intro p hp q hq hpq
    apply Subtype.ext
    apply Prod.ext hpq
    exact (congrArg Subtype.val (mem_filter.mp hp).2).trans
      (congrArg Subtype.val (mem_filter.mp hq).2).symm
  · intro S hS
    obtain ⟨hST,hSk⟩ := mem_powersetCard.mp hS
    refine ⟨⟨(S,T.val),hST,hSk,T.property⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_univ _,rfl⟩

/-- The outer component is exactly uniform: every t-set admits choose(t,k)
smaller components. This includes k=0 and k=t. -/
theorem uniform_nested_outer (Ω : Finset A) (k t : ℕ)
    [Nonempty (FiniteNestedSubsets Ω k t)] [Nonempty ↥(Ω.powersetCard t)] :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets Ω k t)).map
      (nestedOuter Ω k t) = (FiniteEntropy.uniform : FiniteEntropy.Law ↥(Ω.powersetCard t)) := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro T
  change (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets Ω k t)).event
    (fun p => nestedOuter Ω k t p=T) = _
  rw [FiniteEntropy.Law.uniform_event]
  have hequal := fun S : ↥(Ω.powersetCard t) =>
    (nestedOuter_fiber_card Ω k t S).trans (nestedOuter_fiber_card Ω k t T).symm
  have hh := Kahn.Ordering.uniform_fibre_probability (nestedOuter Ω k t) T hequal
  simpa only [FiniteEntropy.uniform,one_div] using hh

end LooseHamilton
