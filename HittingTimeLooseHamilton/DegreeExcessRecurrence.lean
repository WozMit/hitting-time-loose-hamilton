module

public import HittingTimeLooseHamilton.DegreeExcess
public import HittingTimeLooseHamilton.OneVertexSwitchingCount

public section

/-! Translation of the exact graph-switching count into the Poisson birth-rate
inequality for the positive degree excess, including its merged zero atom. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r m : ℕ} {ell : V → ℕ} [Nonempty (TerminalState V r m ell)]

lemma degreeProbability_eq_layerCount (v : V) (t : ℕ) :
    degreeProbability r m ell v t =
      (layerCount r m ell v t : ℝ) / Fintype.card (TerminalState V r m ell) := by
  classical
  unfold degreeProbability terminalLaw
  rw [FiniteEntropy.Law.uniform_event]
  congr 1
  simp [layerCount,degreeLayer,Fintype.card_subtype]

lemma degreeProbability_switching (v : V) (t : ℕ) (ht : ell v < t) :
    ((t : ℝ)-meanDegree (V := V) r m)*degreeProbability r m ell v t ≤
      meanDegree (V := V) r m*degreeProbability r m ell v (t-1) := by
  have hcounts := oneVertex_layer_recurrence (r := r) (m := m) ht
  have hc : (Fintype.card V : ℝ)*t*(layerCount r m ell v t : ℝ) ≤
      (r : ℝ)*m*((layerCount r m ell v t : ℝ)+layerCount r m ell v (t-1)) := by
    exact_mod_cast hcounts
  have hN : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty V from ⟨v⟩)
  have hmul : meanDegree (V := V) r m * Fintype.card V = (r : ℝ)*m := by
    unfold meanDegree
    exact div_mul_cancel₀ _ hN.ne'
  have hb : ((t : ℝ)-meanDegree (V := V) r m)*(layerCount r m ell v t : ℝ) ≤
      meanDegree (V := V) r m * layerCount r m ell v (t-1) := by
    rw [← hmul] at hc
    apply (mul_le_mul_iff_left₀ hN).mp
    calc
      (((t : ℝ)-meanDegree (V := V) r m)*(layerCount r m ell v t : ℝ))*Fintype.card V =
          (Fintype.card V : ℝ)*t*(layerCount r m ell v t : ℝ) -
          (meanDegree (V := V) r m*Fintype.card V)*layerCount r m ell v t := by ring
      _ ≤ (meanDegree (V := V) r m*Fintype.card V)*
          ((layerCount r m ell v t : ℝ)+layerCount r m ell v (t-1)) -
          (meanDegree (V := V) r m*Fintype.card V)*layerCount r m ell v t :=
        sub_le_sub_right hc _
      _ = _ := by ring
  rw [degreeProbability_eq_layerCount,degreeProbability_eq_layerCount]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb
    (Nat.cast_nonneg (Fintype.card (TerminalState V r m ell)))

/-- The complete Poisson recurrence for the actual excess distribution.
At q=0 the previous degree layer is contained in the entire zero atom. -/
theorem degreeExcess_atom_recurrence (v : V) (q : ℕ) :
    (q+1 : ℝ)*natLawAtom (terminalLaw r m ell) (fun F => degreeExcess F v) (q+1) ≤
      meanDegree (V := V) r m * natLawAtom (terminalLaw r m ell) (fun F => degreeExcess F v) q := by
  have ht : ell v < degreeThreshold r m ell v+(q+1) := by
    have := degreeThreshold_ge_lower r m ell v
    omega
  have h := degreeProbability_switching (r := r) (m := m) v (degreeThreshold r m ell v+(q+1)) ht
  have hprev : degreeThreshold r m ell v+(q+1)-1 = degreeThreshold r m ell v+q := by omega
  rw [hprev] at h
  have hcoef : (q+1 : ℝ) ≤ (degreeThreshold r m ell v+(q+1) : ℕ)-meanDegree (V := V) r m := by
    have := degreeThreshold_ge_mean r m ell v
    push_cast
    linarith
  rw [degreeExcess_atom_succ]
  exact (mul_le_mul_of_nonneg_right hcoef (degreeProbability_nonneg r m ell v _)).trans
    (h.trans (mul_le_mul_of_nonneg_left (degreeProbability_le_excess_atom r m ell v q)
      (meanDegree_nonneg r m)))
end LooseHamilton
