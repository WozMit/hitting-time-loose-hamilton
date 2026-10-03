module

public import HittingTimeLooseHamilton.RootConditionalMixture
public import HittingTimeLooseHamilton.KahnConditioning

public section

/-! Finite forward--reverse witness comparison underlying Remark 5.5. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {S B R : Type*} [Fintype S] [Fintype B] [Fintype R]

/-- The auxiliary experiment retains precisely the original source marginal. -/
lemma forward_kernel_source_marginal (p : FiniteEntropy.Law S)
    (k : S → FiniteEntropy.Law B) :
    (p.kernel k).map Prod.fst = p := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro s
  simp only [FiniteEntropy.Law.map,FiniteEntropy.Law.event,FiniteEntropy.Law.kernel,
    Fintype.sum_prod_type]
  rw [sum_eq_single s]
  · simp [←mul_sum,(k s).total]
  · intro t ht hts; simp [hts]
  · simp

/-- The joint event is the average of its pointwise auxiliary probabilities. -/
lemma forward_kernel_event (p : FiniteEntropy.Law S) (k : S → FiniteEntropy.Law B)
    (W : S × B → Prop) :
    (p.kernel k).event W = ∑ s, p.mass s*(k s).event (fun b=>W (s,b)) := by
  classical
  simp only [FiniteEntropy.Law.event,FiniteEntropy.Law.kernel,Fintype.sum_prod_type,mul_sum]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro b hb
  split_ifs <;> simp

/-- A uniform forward success bound costs a multiplicative factor on the bad
source probability, with no sign restriction on the error parameter. -/
theorem forward_witness_joint_lower (p : FiniteEntropy.Law S) (k : S → FiniteEntropy.Law B)
    (Bad : S → Prop) (W : S × B → Prop) (ε : ℝ)
    (hforward : ∀ s, Bad s → 1-ε ≤ (k s).event (fun b=>W (s,b))) :
    (1-ε)*p.event Bad ≤ (p.kernel k).event (fun z=>Bad z.1 ∧ W z) := by
  classical
  rw [forward_kernel_event]
  unfold FiniteEntropy.Law.event at *
  rw [mul_sum]
  apply sum_le_sum
  intro s hs
  by_cases hb : Bad s
  · simp only [hb,if_true,true_and]
    have hh := mul_le_mul_of_nonneg_left (hforward s hb) (p.nonneg s)
    simpa only [mul_comm] using hh
  · simp [hb]

/-- The forward bound also holds for the witness event without retaining Bad. -/
theorem forward_witness_lower (p : FiniteEntropy.Law S) (k : S → FiniteEntropy.Law B)
    (Bad : S → Prop) (W : S × B → Prop) (ε : ℝ)
    (hforward : ∀ s, Bad s → 1-ε ≤ (k s).event (fun b=>W (s,b))) :
    (1-ε)*p.event Bad ≤ (p.kernel k).event W :=
  (forward_witness_joint_lower p k Bad W ε hforward).trans
    ((p.kernel k).event_mono (fun z hz=>hz.2))

/-- Exact reverse conditioning on each positive remainder fibre bounds the
same witness probability. Averaging preserves the forward multiplicative error. -/
theorem forward_reverse_kernel_comparison (p : FiniteEntropy.Law S)
    (k : S → FiniteEntropy.Law B) (Bad : S → Prop) (W : S × B → Prop)
    (remainder : S × B → R) (ε γ : ℝ)
    (hforward : ∀ s, Bad s → 1-ε ≤ (k s).event (fun b=>W (s,b)))
    (hreverse : ∀ r (hr : 0<(p.kernel k).event (fun z=>remainder z=r)),
      ((p.kernel k).condition (fun z=>remainder z=r) hr).event W ≤ γ) :
    (1-ε)*p.event Bad ≤ γ :=
  (forward_witness_lower p k Bad W ε hforward).trans
    (event_le_of_observation_conditional_bounds (p.kernel k) W remainder γ hreverse)

/-- A more flexible reverse hypothesis only needs to bound witnesses produced
from bad sources; witnesses from other sources need not satisfy that bound. -/
theorem forward_reverse_joint_kernel_comparison (p : FiniteEntropy.Law S)
    (k : S → FiniteEntropy.Law B) (Bad : S → Prop) (W : S × B → Prop)
    (remainder : S × B → R) (ε γ : ℝ)
    (hforward : ∀ s, Bad s → 1-ε ≤ (k s).event (fun b=>W (s,b)))
    (hreverse : ∀ r (hr : 0<(p.kernel k).event (fun z=>remainder z=r)),
      ((p.kernel k).condition (fun z=>remainder z=r) hr).event
        (fun z=>Bad z.1 ∧ W z) ≤ γ) :
    (1-ε)*p.event Bad ≤ γ :=
  (forward_witness_joint_lower p k Bad W ε hforward).trans
    (event_le_of_observation_conditional_bounds (p.kernel k) (fun z=>Bad z.1 ∧ W z)
      remainder γ hreverse)

end LooseHamilton
