module

public import HittingTimeLooseHamilton.RootLinkModels
public import HittingTimeLooseHamilton.CoreTrace

public section

/-! A total non-root deficit at most one imposes no constraint or one star-hitting constraint. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The root's own lower bound is separate, because its inner link size is fixed. -/
@[expose] def rootAdjustedDeficit (y : V) (ell : V → ℕ) (A : SimpleHypergraph V) (v : V) : ℕ :=
  if v=y then 0 else ell v-vertexDegree A v

@[expose] def rootLinkStar (U : SimpleHypergraph V) (v : V) : SimpleHypergraph V :=
  U.filter (fun e => v∈e)

lemma nat_total_le_one_split (δ : V → ℕ) (hδ : ∑ v,δ v ≤ 1) :
    (∀ v,δ v=0) ∨ ∃ v,δ v=1 ∧ ∀ w,w≠v → δ w=0 := by
  classical
  by_cases hz : ∀v,δ v=0
  · exact Or.inl hz
  · right
    obtain ⟨v,hv⟩ := not_forall.mp hz
    have hvle := single_le_sum (s:=(univ:Finset V)) (f:=δ) (fun _ _ => Nat.zero_le _) (mem_univ v)
    have hvone : δ v=1 := by omega
    refine ⟨v,hvone,?_⟩
    intro w hw
    have hwle := single_le_sum (s:=univ.erase v) (f:=δ) (fun _ _ => Nat.zero_le _)
      (mem_erase.mpr ⟨hw,mem_univ w⟩)
    have hs := sum_erase_add (univ:Finset V) δ (mem_univ v)
    omega

lemma root_inner_degree (U : SimpleHypergraph V) (y : V) (hU : ∀ e∈U,y∈e)
    {I : SimpleHypergraph V} (hI : I ⊆ U) : vertexDegree I y=I.card := by
  unfold vertexDegree
  rw [filter_eq_self.mpr (fun e he=>hU e (hI he))]

lemma root_link_feasible_iff_deficits (U A : SimpleHypergraph V) (ell : V → ℕ)
    (y : V) (hU : ∀ e∈U,y∈e) (hAU : Disjoint A U) (b q : ℕ)
    (hroot : ell y ≤ vertexDegree A y+b) (p : FiniteNestedSubsets U b q) :
    (∀ v,ell v ≤ vertexDegree (A∪p.val.1) v) ↔
      ∀ v,rootAdjustedDeficit y ell A v ≤ vertexDegree p.val.1 v := by
  have hI := p.property.1.trans (mem_powersetCard.mp p.property.2.2).1
  have hdis : Disjoint A p.val.1 := hAU.mono_right hI
  have hdeg : vertexDegree p.val.1 y=b := by rw [root_inner_degree U y hU hI,p.property.2.1]
  constructor
  · intro h v
    have hv := h v
    rw [vertexDegree_union hdis] at hv
    by_cases hvy : v=y
    · simp [rootAdjustedDeficit,hvy]
    · simp only [rootAdjustedDeficit,hvy,if_false]
      omega
  · intro h v
    rw [vertexDegree_union hdis]
    by_cases hvy : v=y
    · subst v
      simpa [hdeg] using hroot
    · have hv := h v
      simp only [rootAdjustedDeficit,hvy,if_false] at hv
      omega

lemma root_link_star_hit_iff (U I : SimpleHypergraph V) (hI : I ⊆ U) (v : V) :
    ¬Disjoint I (rootLinkStar U v) ↔ 1 ≤ vertexDegree I v := by
  have heq : I∩rootLinkStar U v=I.filter (fun e=>v∈e) := by
    ext e
    simp only [rootLinkStar,mem_inter,mem_filter]
    constructor
    · tauto
    · rintro ⟨he,hv⟩
      exact ⟨he,hI he,hv⟩
  rw [disjoint_iff_inter_eq_empty,heq,←card_eq_zero]
  change ¬vertexDegree I v=0 ↔ 1 ≤ vertexDegree I v
  omega

/-- Uniform feasibility is either unrestricted or exactly one inner-star hit.
The total excludes the root; the fixed root degree is checked separately. -/
theorem root_link_constraint_zero_or_star (U A : SimpleHypergraph V) (ell : V → ℕ)
    (y : V) (hU : ∀ e∈U,y∈e) (hAU : Disjoint A U) (b q : ℕ)
    (hroot : ell y ≤ vertexDegree A y+b)
    (hδ : ∑ v,rootAdjustedDeficit y ell A v ≤ 1) :
    (∀ p : FiniteNestedSubsets U b q, ∀v,ell v ≤ vertexDegree (A∪p.val.1) v) ∨
      ∃ v : V,v≠y ∧ ∀ p : FiniteNestedSubsets U b q,
        (∀w,ell w ≤ vertexDegree (A∪p.val.1) w) ↔ ¬Disjoint p.val.1 (rootLinkStar U v) := by
  rcases nat_total_le_one_split (rootAdjustedDeficit y ell A) hδ with hz | ⟨v,hv,hother⟩
  · left
    intro p
    rw [root_link_feasible_iff_deficits U A ell y hU hAU b q hroot p]
    intro v
    rw [hz v]
    exact Nat.zero_le _
  · right
    have hvy : v≠y := by intro he; subst v; simp [rootAdjustedDeficit] at hv
    refine ⟨v,hvy,?_⟩
    intro p
    rw [root_link_feasible_iff_deficits U A ell y hU hAU b q hroot p,
      root_link_star_hit_iff U p.val.1 (p.property.1.trans (mem_powersetCard.mp p.property.2.2).1) v]
    constructor
    · intro h
      simpa [hv] using h v
    · intro h w
      by_cases hw : w=v
      · subst w
        simpa [hv] using h
      · rw [hother w hw]
        exact Nat.zero_le _
end LooseHamilton
