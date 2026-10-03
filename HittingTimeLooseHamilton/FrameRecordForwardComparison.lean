module

public import HittingTimeLooseHamilton.ForwardReverseKernel
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! Forward comparison on the support of a fixed exposure record. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {Ω Aux R : Type*} [Fintype Ω] [Fintype Aux] [Fintype R]

/-- Removing null source atoms leaves every event probability unchanged. -/
lemma event_restrict_positive_mass (p : FiniteEntropy.Law Ω) (E : Ω→Prop) :
    p.event (fun ω => 0<p.mass ω ∧ E ω)=p.event E := by
  classical
  unfold FiniteEntropy.Law.event
  apply sum_congr rfl
  intro ω _
  by_cases hp : 0<p.mass ω
  · simp only [hp,true_and]
  · have hz : p.mass ω=0 := le_antisymm (le_of_not_gt hp) (p.nonneg ω)
    simp [hz]

/-- Pointwise auxiliary success is needed only at source atoms of positive mass.
The auxiliary randomness has precisely the displayed product law. -/
theorem supported_product_forward_lower (p : FiniteEntropy.Law Ω)
    (q : FiniteEntropy.Law Aux) (Bad : Ω→Prop) (W : Ω×Aux→Prop) (err : ℝ)
    (hforward : ∀ ω, 0<p.mass ω → Bad ω → 1-err≤q.event (fun σ => W (ω,σ))) :
    (1-err)*p.event Bad≤(p.prod q).event W := by
  have hh := forward_witness_lower p (fun _ => q)
    (fun ω => 0<p.mass ω ∧ Bad ω) W err (fun ω hω => hforward ω hω.1 hω.2)
  rw [event_restrict_positive_mass] at hh
  exact hh

/-- Conditioning on a fixed record makes all atoms outside that record null. -/
lemma positive_condition_mass_implies_record (Q : FiniteEntropy.Law Ω)
    (record : Ω→Prop) (hrecord : 0<Q.event record) (ω : Ω)
    (hω : 0<(Q.condition record hrecord).mass ω) : record ω := by
  classical
  by_contra hn
  simp only [FiniteEntropy.Law.condition,hn,if_false] at hω
  exact (lt_irrefl (0:ℝ)) hω

/-- Fixed-record forward comparison. The pointwise lower bound is required only
on the record and bad-source event; it is never assumed outside the record. -/
theorem conditioned_product_forward_lower (Q : FiniteEntropy.Law Ω)
    (record : Ω→Prop) (hrecord : 0<Q.event record) (q : FiniteEntropy.Law Aux)
    (Bad : Ω→Prop) (W : Ω×Aux→Prop) (err : ℝ)
    (hforward : ∀ ω, record ω → Bad ω → 1-err≤q.event (fun σ => W (ω,σ))) :
    (1-err)*(Q.condition record hrecord).event Bad≤
      ((Q.condition record hrecord).prod q).event W := by
  apply supported_product_forward_lower
  intro ω hω hb
  exact hforward ω (positive_condition_mass_implies_record Q record hrecord ω hω) hb

/-- Reverse bounds on every attained observation fiber give the same recordwise
multiplicative comparison. No additional conditioning on badness is used. -/
theorem conditioned_product_forward_reverse_comparison (Q : FiniteEntropy.Law Ω)
    (record : Ω→Prop) (hrecord : 0<Q.event record) (q : FiniteEntropy.Law Aux)
    (Bad : Ω→Prop) (W : Ω×Aux→Prop) (observation : Ω×Aux→R) (err γ : ℝ)
    (hforward : ∀ ω, record ω → Bad ω → 1-err≤q.event (fun σ => W (ω,σ)))
    (hreverse : ∀ a (ha : 0<((Q.condition record hrecord).prod q).event
        (fun z => observation z=a)),
      (((Q.condition record hrecord).prod q).condition
        (fun z => observation z=a) ha).event W≤γ) :
    (1-err)*(Q.condition record hrecord).event Bad≤γ :=
  (conditioned_product_forward_lower Q record hrecord q Bad W err hforward).trans
    (event_le_of_observation_conditional_bounds _ W observation γ hreverse)

end LooseHamilton
