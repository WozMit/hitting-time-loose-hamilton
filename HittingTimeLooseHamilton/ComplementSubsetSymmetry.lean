module

public import HittingTimeLooseHamilton.UniformPrefixProbability

public section

/-! Relabelling a fixed-size subset while fixing every forbidden label. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

private def outsideSet (K S : Finset A) : Finset {x // x ∉ K} :=
  univ.filter (fun x => x.val ∈ S)

private theorem outsideSet_card (K S : Finset A) (hS : Disjoint S K) :
    (outsideSet K S).card = S.card := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    exact (mem_filter.mp hx).2
  · intro x hx y hy h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x,fun hk => disjoint_left.mp hS hx hk⟩,mem_filter.mpr ⟨mem_univ _,hx⟩,rfl⟩

/-- Every two equally sized subsets outside `K` are related by a permutation
that fixes each member of `K` individually. -/
theorem exists_perm_fix_set_maps_subsets (K S T : Finset A)
    (hS : Disjoint S K) (hT : Disjoint T K) (hc : S.card = T.card) :
    ∃ g : Equiv.Perm A, (∀ x ∈ K, g x = x) ∧ (∀ x, x ∈ S ↔ g x ∈ T) := by
  classical
  let e : ↥(outsideSet K S) ≃ ↥(outsideSet K T) :=
    Finset.equivOfCardEq ((outsideSet_card K S hS).trans (hc.trans (outsideSet_card K T hT).symm))
  let f : Equiv.Perm {x // x ∉ K} := e.extendSubtype
  have hf : ∀ x : {x // x ∉ K}, x.val ∈ S ↔ (f x).val ∈ T := by
    intro x
    have hh : x ∈ outsideSet K S ↔ f x ∈ outsideSet K T := by
      constructor
      · exact e.extendSubtype_mem x
      · intro hx
        by_contra hn
        exact e.extendSubtype_not_mem x hn hx
    simpa only [outsideSet,mem_filter,mem_univ,true_and] using hh
  let g : Equiv.Perm A := (Equiv.refl {x // x ∈ K}).subtypeCongr f
  refine ⟨g,?_,?_⟩
  · intro x hx
    exact Equiv.Perm.subtypeCongr.left_apply _ _ hx
  · intro x
    by_cases hx : x ∈ K
    · have hg : g x = x := Equiv.Perm.subtypeCongr.left_apply _ _ hx
      rw [hg]
      exact iff_of_false (fun hs => disjoint_left.mp hS hs hx) (fun ht => disjoint_left.mp hT ht hx)
    · have hg : g x = (f ⟨x,hx⟩).val := Equiv.Perm.subtypeCongr.right_apply _ _ hx
      rw [hg]
      exact hf ⟨x,hx⟩
end LooseHamilton
