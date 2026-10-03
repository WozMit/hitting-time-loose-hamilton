module

public import HittingTimeLooseHamilton.KahnConditioning

public section

/-! Positive-probability conditioning as a law on the actual event subtype. -/
noncomputable section
open Finset FiniteEntropy
open scoped BigOperators
namespace LooseHamilton
variable {S : Type*} [Fintype S]

/-- Removing zero-mass outcomes outside a conditioning event. -/
@[expose] def positiveEventLaw (p : Law S) (E : S → Prop) [DecidablePred E]
    (hE : 0 < p.event E) : Law {s // E s} where
  mass s := p.mass s.val / p.event E
  nonneg s := div_nonneg (p.nonneg s.val) hE.le
  total := by
    rw [← sum_div]
    have hs : (∑ s : {s // E s}, p.mass s.val) = p.event E := by
      rw [← sum_subtype (univ.filter E) (by simp) p.mass]
      simp [Law.event, sum_filter]
      apply sum_congr rfl
      intro a _
      split_ifs <;> rfl
    rw [hs, div_self hE.ne']

theorem positiveEventLaw_map (p : Law S) (E : S → Prop) [DecidablePred E]
    (hE : 0 < p.event E) :
    (positiveEventLaw p E hE).map Subtype.val = p.condition E hE := by
  classical
  apply Law.ext_mass
  intro s
  change (∑ t : {t // E t}, if t.val = s then p.mass t.val / p.event E else 0) = _
  rw [← sum_subtype (univ.filter E) (by simp)
    (fun t => if t = s then p.mass t / p.event E else 0)]
  simp [sum_filter, Law.condition, and_comm, ite_and]

theorem positiveEventLaw_entropy (p : Law S) (E : S → Prop) [DecidablePred E]
    (hE : 0 < p.event E) :
    entropy (positiveEventLaw p E hE).mass = entropy (p.condition E hE).mass := by
  rw [← positiveEventLaw_map p E hE]
  exact ((positiveEventLaw p E hE).entropy_map_of_injective Subtype.val Subtype.val_injective).symm

theorem positiveEventLaw_map_observation {T : Type*} [Fintype T]
    (p : Law S) (E : S → Prop) [DecidablePred E] (hE : 0 < p.event E) (f : S → T) :
    (positiveEventLaw p E hE).map (fun s => f s.val) = (p.condition E hE).map f := by
  rw [← positiveEventLaw_map p E hE, Law.map_map]
  rfl

end LooseHamilton
