module

public import HittingTimeLooseHamilton.RootNestedKernel

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators

lemma root_kernel_event_first {I X : Type*} [Fintype I] [Fintype X]
    (p : FiniteEntropy.Law I) (K : I → FiniteEntropy.Law X) (E : I → Prop) :
    (p.kernel K).event (fun z=>E z.1)=p.event E := by
  classical
  simp only [FiniteEntropy.Law.event,FiniteEntropy.Law.kernel,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i hi
  by_cases he : E i
  · simp [he,←mul_sum,(K i).total]
  · simp [he]

/-- Conditioning an event determined only by the inner set leaves the fresh
uniform completion kernel untouched. -/
lemma root_conditionOr_kernel_first {I X : Type*} [Fintype I] [Fintype X]
    (p : FiniteEntropy.Law I) (K : I → FiniteEntropy.Law X) (E : I → Prop) :
    (p.kernel K).conditionOr (fun z=>E z.1)=(p.conditionOr E).kernel K := by
  classical
  have he := root_kernel_event_first p K E
  by_cases hp : 0<p.event E
  · have hh : 0<(p.kernel K).event (fun z=>E z.1) := by rwa [he]
    simp only [FiniteEntropy.Law.conditionOr]
    rw [dif_pos hh,dif_pos hp]
    apply FiniteEntropy.Law.ext_mass
    intro ⟨i,x⟩
    change (if E i then (p.mass i*(K i).mass x)/(p.kernel K).event (fun z=>E z.1) else 0)=
      (if E i then p.mass i/p.event E else 0)*(K i).mass x
    rw [he]
    by_cases hi : E i <;> simp [hi] <;> ring
  · have hh : ¬0<(p.kernel K).event (fun z=>E z.1) := by rwa [he]
    simp [FiniteEntropy.Law.conditionOr,hp,hh]

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The exact nested-kernel identification remains valid after imposing any
inner-set event, in particular hitting the root link. -/
theorem uniform_nested_conditioned_inner_kernel (U : Finset A) (b q : ℕ)
    (hbq : b≤q) (hq : q≤U.card)
    [Nonempty (FiniteNestedSubsets U b q)] [Nonempty ↥(U.powersetCard b)]
    (E : ↥(U.powersetCard b) → Prop) :
    ((FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).conditionOr
      (fun p=>E (nestedInner U b q p))).map (nestedInnerOuter U b q) =
    ((FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).conditionOr E).kernel
      (rootOuterKernel U b q hbq hq) := by
  have hm := uniform_nested_inner_kernel U b q hbq hq
  have hh := congrArg (fun p : FiniteEntropy.Law (↥(U.powersetCard b) × Finset A) =>
    p.conditionOr (fun z=>E z.1)) hm
  rw [FiniteEntropy.Law.conditionOr_map,root_conditionOr_kernel_first] at hh
  exact hh

/-- Forgetting the inner set in the unconditioned completion experiment
recovers the uniform q-subset law. -/
theorem uniform_inner_outer_marginal (U : Finset A) (b q : ℕ)
    (hbq : b≤q) (hq : q≤U.card)
    [Nonempty (FiniteNestedSubsets U b q)] [Nonempty ↥(U.powersetCard b)]
    [Nonempty ↥(U.powersetCard q)] :
    ((FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).kernel
      (rootOuterKernel U b q hbq hq)).map Prod.snd =
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).map Subtype.val := by
  rw [← uniform_nested_inner_kernel U b q hbq hq,FiniteEntropy.Law.map_map]
  have hm := congrArg (fun p : FiniteEntropy.Law ↥(U.powersetCard q)=>p.map Subtype.val)
    (uniform_nested_outer U b q)
  rw [FiniteEntropy.Law.map_map] at hm
  exact hm

end LooseHamilton
