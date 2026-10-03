module

public import HittingTimeLooseHamilton.BiasedCloneConditionalLaw

public section

/-! Positive-mass support laws omit all zero-probability role fibres. -/
noncomputable section
open Finset FiniteEntropy
open scoped BigOperators
namespace LooseHamilton
variable {S : Type*} [Fintype S]

lemma positive_mass_event (p : Law S) : p.event (fun s => 0 < p.mass s) = 1 := by
  classical
  unfold Law.event
  convert p.total using 1
  apply sum_congr rfl
  intro s _
  by_cases hs : 0 < p.mass s
  · simp [hs]
  · have hz : p.mass s = 0 := le_antisymm (le_of_not_gt hs) (p.nonneg s)
    simp [hz]

/-- The original law, with its zero-mass atoms removed. -/
@[expose] def supportedLaw (p : Law S) : Law {s // 0 < p.mass s} := by
  classical
  exact positiveEventLaw p (fun s => 0 < p.mass s) (by rw [positive_mass_event]; norm_num)

theorem supportedLaw_mass (p : Law S) (s : {s // 0 < p.mass s}) :
    (supportedLaw p).mass s = p.mass s.val := by
  simp [supportedLaw, positiveEventLaw, positive_mass_event]

theorem supportedLaw_map (p : Law S) : (supportedLaw p).map Subtype.val = p := by
  classical
  unfold supportedLaw
  rw [positiveEventLaw_map]
  apply Law.ext_mass
  intro s
  change (if 0 < p.mass s then p.mass s / p.event (fun s => 0 < p.mass s) else 0) = _
  rw [positive_mass_event]
  by_cases hs : 0 < p.mass s
  · simp [hs]
  · have hz : p.mass s = 0 := le_antisymm (le_of_not_gt hs) (p.nonneg s)
    simp [hz]

theorem supportedLaw_sum {T : Type*} [Fintype T] (p : Law S) (f : S → T) :
    (supportedLaw p).map (fun s => f s.val) = p.map f := by
  change (supportedLaw p).map (f ∘ Subtype.val) = _
  rw [← Law.map_map, supportedLaw_map]

end LooseHamilton
