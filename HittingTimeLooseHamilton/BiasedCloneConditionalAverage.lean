module

public import HittingTimeLooseHamilton.BiasedCloneConditionalSupport
public import HittingTimeLooseHamilton.ForwardReverseKernel

public section

/-! Exact event decomposition over the positive-mass observation fibres. -/
noncomputable section
open FiniteEntropy
open scoped BigOperators
namespace LooseHamilton
variable {S R : Type*} [Fintype S] [Fintype R]

theorem event_eq_positive_fibre_average (p : Law S) (f : S → R) (W : S → Prop) :
    p.event W =
      ∑ z : {z // 0 < (p.map f).mass z}, (supportedLaw (p.map f)).mass z *
        (p.conditionOr (fun s => f s=z.val)).event W := by
  have h := forward_kernel_event (p.map f) (fun z => p.conditionOr (fun s => f s=z))
    (fun zs => W zs.2)
  rw [Law.conditional_kernel_eq_map, Law.event_map] at h
  have hs := Law.sum_map_mul (supportedLaw (p.map f)) Subtype.val
    (fun z => (p.conditionOr (fun s => f s=z)).event W)
  rw [supportedLaw_map] at hs
  exact h.trans hs

end LooseHamilton
