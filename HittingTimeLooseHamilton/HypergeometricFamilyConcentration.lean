module

public import HittingTimeLooseHamilton.HypergeometricConcentration

public section

/-! Uniform concentration over an arbitrary finite family of edge tests and all suffix times. -/
noncomputable section
open scoped BigOperators
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- One bound applies simultaneously at every time m≥M. -/
lemma process_intersection_relative_concentration (M m : ℕ) (hM : 0<M) (hMm : M≤m)
    (hm : m ≤ (completeEdges V r).card) (D : SimpleHypergraph V)
    (hD : D ⊆ completeEdges V r) (δ : ℝ) (hδ : 0<δ) :
    (processLaw V r).event (fun σ => δ*m ≤
      |((processState σ m ∩ D).card:ℝ)-(m:ℝ)/(completeEdges V r).card*D.card|) ≤
      2*Real.exp (-δ^2*M/4) := by
  have hm0 : 0<m := hM.trans_le hMm
  have hm' : (0:ℝ)<m := by exact_mod_cast hm0
  have ht := process_intersection_concentration m hm hm0 D hD (δ*m) (mul_pos hδ hm')
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have he : -(δ*(m:ℝ))^2/(4*m) = -δ^2*m/4 := by field_simp <;> ring
  rw [he]
  have hh : (M:ℝ)≤m := by exact_mod_cast hMm
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg δ)]

/-- A finite union bound requiring no asymptotic or concentration assumption. -/
theorem process_test_family_concentration {I : Type*} [Fintype I]
    (D : I → SimpleHypergraph V) (hD : ∀ i, D i ⊆ completeEdges V r)
    (M : ℕ) (hM : 0<M) (δ : ℝ) (hδ : 0<δ) :
    (processLaw V r).event (fun σ => ∃ i, ∃ m : ℕ, M≤m ∧ m≤(completeEdges V r).card ∧
      δ*m ≤ |((processState σ m ∩ D i).card:ℝ)-(m:ℝ)/(completeEdges V r).card*(D i).card|) ≤
      (Fintype.card I:ℝ)*((completeEdges V r).card+1)*2*Real.exp (-δ^2*M/4) := by
  let J := I × Fin ((completeEdges V r).card+1)
  let E : J → EdgeOrder V r → Prop := fun j σ => M≤j.2.val ∧
      δ*j.2.val ≤ |((processState σ j.2.val ∩ D j.1).card:ℝ)-
        (j.2.val:ℝ)/(completeEdges V r).card*(D j.1).card|
  have hm_event := (processLaw V r).event_mono
    (E:=fun σ => ∃ i, ∃ m : ℕ, M≤m ∧ m≤(completeEdges V r).card ∧
      δ*m ≤ |((processState σ m ∩ D i).card:ℝ)-(m:ℝ)/(completeEdges V r).card*(D i).card|)
    (F:=fun σ => ∃ j : J, E j σ) (by
      rintro σ ⟨i,m,hMm,hm,hσ⟩
      exact ⟨⟨i,⟨m,by omega⟩⟩,hMm,hσ⟩)
  apply (hm_event.trans ((processLaw V r).finite_union_bound E)).trans
  calc
    _ ≤ ∑ j : J, 2*Real.exp (-δ^2*M/4) := by
      apply sum_le_sum
      intro j _
      by_cases hMm : M≤j.2.val
      · have hm_event' := (processLaw V r).event_mono (E:=E j)
          (F:=fun σ => δ*j.2.val ≤ |((processState σ j.2.val ∩ D j.1).card:ℝ)-
            (j.2.val:ℝ)/(completeEdges V r).card*(D j.1).card|) (fun _ h => h.2)
        exact hm_event'.trans (process_intersection_relative_concentration M j.2.val hM hMm
          (by have := j.2.isLt; omega) (D j.1) (hD j.1) δ hδ)
      · simp [E,hMm,FiniteEntropy.Law.event]
        positivity
    _ = _ := by simp [J]; ring
end LooseHamilton
