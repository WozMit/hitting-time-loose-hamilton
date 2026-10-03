module

public import HittingTimeLooseHamilton.OrderComplementRefinement
public import HittingTimeLooseHamilton.HypergeometricAlgebra

public section

/-! A mixed-time inclusion/avoidance bound from exact conditional symmetries. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators

private theorem event_partition {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : FiniteEntropy.Law Ω) (f : Ω → I) (E P : Ω → Prop) :
    p.event (fun ω => E ω ∧ P ω) = ∑ i, p.event (fun ω => (E ω ∧ f ω = i) ∧ P ω) := by
  have he : (fun ω => E ω ∧ P ω) = (fun ω => ∃ i, (E ω ∧ f ω = i) ∧ P ω) := by
    funext ω
    apply propext
    exact ⟨fun h => ⟨f ω,⟨h.1,rfl⟩,h.2⟩,fun ⟨_,h⟩ => ⟨h.1.1,h.2⟩⟩
  rw [he]
  apply event_exists_eq_sum
  intro ω i j hi hj
  exact hi.1.2.symm.trans hj.1.2

section Orders
variable {A : Type*} [Fintype A] [DecidableEq A]
local instance finiteOrderNonempty : Nonempty (FiniteOrder A) := ⟨Fintype.equivFin A⟩

/-- Prescribed late labels can consume at most `|K|` early positions. The
remaining early labels stay uniform in the complement of `K`. -/
theorem uniform_mixed_prefix_bound (K D : Finset A) (a b : ℕ)
    (ha : a ≤ Fintype.card A) (hk : K.card ≤ a) (hKD : Disjoint K D) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event
      (fun σ => K ⊆ orderPrefix σ b ∧ Disjoint (orderPrefix σ a) D) ≤
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event
      (fun σ => K ⊆ orderPrefix σ b) *
      (((Fintype.card A - K.card - D.card).choose (a-K.card) : ℝ) /
        (Fintype.card A-K.card).choose (a-K.card)) := by
  classical
  let p : FiniteEntropy.Law (FiniteOrder A) := FiniteEntropy.uniform
  let n := (univ \ K).card
  let t := a-K.card
  let c : ℝ := ((n-D.card).choose t : ℝ) / n.choose t
  let E : FiniteOrder A → Prop := fun σ => K ⊆ orderPrefix σ b
  let P : FiniteOrder A → Prop := fun σ => Disjoint (earlyOutside σ K a) D
  have hd : D ⊆ univ \ K := by
    intro x hx
    exact mem_sdiff.mpr ⟨mem_univ _,fun hk => disjoint_left.mp hKD hk hx⟩
  have hupper (σ : FiniteOrder A) : (earlyOutside σ K a).card ≤ n :=
    card_le_card (sdiff_subset_sdiff (subset_univ _) (Subset.refl K))
  have hlower (σ : FiniteOrder A) : t ≤ (earlyOutside σ K a).card := by
    have h := le_card_sdiff K (orderPrefix σ a)
    rwa [orderPrefix_card σ a ha] at h
  let f : FiniteOrder A → Fin (n+1) := fun σ => ⟨(earlyOutside σ K a).card,by have := hupper σ; omega⟩
  have hP (σ : FiniteOrder A) : Disjoint (orderPrefix σ a) D ↔ P σ := by
    constructor
    · intro h
      exact h.mono_left sdiff_subset
    · intro h
      apply disjoint_left.mpr
      intro x hx hxD
      apply disjoint_left.mp h (mem_sdiff.mpr ⟨hx,?_⟩) hxD
      exact fun hxK => disjoint_left.mp hKD hxK hxD
  have hsum : p.event (fun σ => E σ ∧ P σ) ≤ p.event E * c := by
    rw [event_partition p f E P]
    have htotal : p.event E = ∑ i, p.event (fun σ => E σ ∧ f σ = i) := by
      simpa only [and_true] using event_partition p f E (fun _ => True)
    rw [htotal,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi : i.val ≤ n := by omega
    by_cases hti : t ≤ i.val
    · have heq := uniform_earlyOutside_avoidance K D a b i.val hi hd
      have hf (σ : FiniteOrder A) : f σ = i ↔ (earlyOutside σ K a).card = i.val :=
        Fin.ext_iff
      have hevent : p.event (fun σ => (E σ ∧ f σ = i) ∧ P σ) =
          p.event (fun σ => E σ ∧ f σ = i) *
            (((n-D.card).choose i.val : ℝ) / n.choose i.val) := by
        simp only [FiniteEntropy.Law.uniform_event,p,E,P,hf]
        simpa only [n,mul_div_assoc] using heq
      rw [hevent]
      apply mul_le_mul_of_nonneg_left
      · exact Hypergeometric.avoidance_ratio_antitone hi (card_le_card hd) hti
      · exact p.event_nonneg _
    · have hfalse (σ : FiniteOrder A) : ¬ f σ = i := by
        intro he
        have hi' := congrArg Fin.val he
        exact hti (hi' ▸ hlower σ)
      simp only [FiniteEntropy.Law.event]
      simp [hfalse]
  have hn : n = Fintype.card A - K.card := by simp [n,card_sdiff_of_subset (subset_univ K)]
  have he : (fun σ => K ⊆ orderPrefix σ b ∧ Disjoint (orderPrefix σ a) D) =
      (fun σ => E σ ∧ P σ) := by
    funext σ
    exact propext (and_congr Iff.rfl (hP σ))
  rw [he]
  simpa only [p,E,c,hn,t] using hsum
end Orders
end LooseHamilton
