module

public import HittingTimeLooseHamilton.BiasedShearerEntropy
public import Mathlib.Tactic.NormNum

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton

/-- A monotone supermodular set function is fractionally superadditive, with
an upper degree bound on the family of coordinate sets. -/
theorem supermodular_bounded_degree_sum {V I : Type*} [DecidableEq V]
    [Fintype I] (g : Finset V → ℝ) (g0 : g ∅ = 0)
    (hg : Monotone g)
    (hinc : ∀ s t : Finset V, s ⊆ t → ∀ v, v ∉ t →
      g (insert v s) - g s ≤ g (insert v t) - g t)
    (t : Finset V) (e : I → Finset V) (D : ℝ) (hD : 0 ≤ D)
    (he : ∀ i, e i ⊆ t)
    (hdeg : ∀ v, (∑ i, if v ∈ e i then (1 : ℝ) else 0) ≤ D) :
    ∑ i, g (e i) ≤ D * g t := by
  classical
  induction t using Finset.induction_on generalizing e with
  | empty =>
      have hz : ∀ i, e i = ∅ := fun i => Finset.subset_empty.mp (he i)
      simp [hz, g0]
  | @insert v t hv ih =>
      let e' : I → Finset V := fun i => (e i).erase v
      have he' : ∀ i, e' i ⊆ t := by
        intro i w hw
        have hmem := he i (Finset.mem_of_mem_erase hw)
        rcases Finset.mem_insert.mp hmem with h | h
        · exact False.elim ((Finset.ne_of_mem_erase hw) h)
        · exact h
      have hd' : ∀ w, (∑ i, if w ∈ e' i then (1 : ℝ) else 0) ≤ D := by
        intro w
        refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hdeg w)
        by_cases hw : w ∈ e' i
        · simp [hw, Finset.mem_of_mem_erase hw]
        · simp only [hw, ite_false]
          split_ifs <;> norm_num
      have hi := ih e' he' hd'
      have hdelta : 0 ≤ g (insert v t) - g t := sub_nonneg.mpr (hg (Finset.subset_insert _ _))
      have hlocal (i : I) : g (e i) ≤ g (e' i) +
          (if v ∈ e i then (1 : ℝ) else 0) * (g (insert v t) - g t) := by
        by_cases hvi : v ∈ e i
        · have hh := hinc (e' i) t (he' i) v hv
          have hi : insert v (e' i) = e i := Finset.insert_erase hvi
          rw [hi] at hh
          simp only [hvi, ite_true, one_mul]
          linarith
        · have hi : e' i = e i := Finset.erase_eq_of_notMem hvi
          simp [hi, hvi]
      have hs := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset I)) => hlocal i
      rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hs
      have hm := mul_le_mul_of_nonneg_right (hdeg v) hdelta
      nlinarith

end LooseHamilton
