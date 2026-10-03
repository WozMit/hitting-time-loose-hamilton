module

public import HittingTimeLooseHamilton.CoreConditionalCounting

public section

/-! Conditioning on a coarser observation leaves each positive refined fibre unchanged. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A I : Type*} [Fintype A] [Fintype I]

lemma root_condition_fiber_refinement (p : FiniteEntropy.Law A) (f : A → I)
    (D : I → Prop) (hE : 0<p.event (fun a=>D (f a))) (i : I)
    (hi : 0<((p.condition (fun a=>D (f a)) hE).map f).mass i) :
    0<(p.map f).mass i ∧
      (p.condition (fun a=>D (f a)) hE).conditionOr (fun a=>f a=i) =
        p.conditionOr (fun a=>f a=i) := by
  classical
  let q := p.condition (fun a=>D (f a)) hE
  change 0<q.event (fun a=>f a=i) at hi
  have he : q.event (fun a=>f a=i) =
      (if D i then p.event (fun a=>f a=i) else 0)/p.event (fun a=>D (f a)) := by
    rw [condition_event_eq_joint]
    congr 1
    by_cases hD : D i
    · simp only [hD,if_true]
      congr 1
      funext a
      exact propext ⟨fun h=>h.2,fun h=>⟨by simpa [h] using hD,h⟩⟩
    · simp only [hD,if_false]
      apply p.event_eq_zero_of_false
      rintro a ⟨hD',h⟩
      exact hD (by simpa [h] using hD')
  have hD : D i := by
    by_contra hn
    simp [hn] at he
    linarith
  simp only [hD,if_true] at he
  have hpi : 0<p.event (fun a=>f a=i) := by
    rw [he] at hi
    exact (div_pos_iff.mp hi).elim (fun h=>h.1) (fun h=>False.elim (not_lt_of_ge hE.le h.2))
  refine ⟨hpi,?_⟩
  change q.conditionOr (fun a=>f a=i)=p.conditionOr (fun a=>f a=i)
  simp only [FiniteEntropy.Law.conditionOr,dif_pos hi,dif_pos hpi]
  apply FiniteEntropy.Law.ext_mass
  intro a
  simp only [FiniteEntropy.Law.condition]
  by_cases ha : f a=i
  · have hDa : D (f a) := ha ▸ hD
    simp only [ha,if_true]
    change q.mass a / q.event (fun a=>f a=i) = p.mass a / p.event (fun a=>f a=i)
    rw [he]
    simp only [q,FiniteEntropy.Law.condition,hDa,if_true]
    field_simp
  · simp [ha]
end LooseHamilton
