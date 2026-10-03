module

public import HittingTimeLooseHamilton.Setup
public import HittingTimeLooseHamilton.NatLawAtoms

public section

/-! The exact threshold and positive degree excess in Lemma 4.1. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def degreeThreshold (r m : ℕ) (ell : V → ℕ) (v : V) : ℕ :=
  max (ell v) (Nat.ceil (meanDegree (V := V) r m))

@[expose] def degreeExcess {r m : ℕ} {ell : V → ℕ} (F : TerminalState V r m ell) (v : V) : ℕ :=
  vertexDegree F.val v - degreeThreshold r m ell v

lemma degreeThreshold_ge_lower (r m : ℕ) (ell : V → ℕ) (v : V) :
    ell v ≤ degreeThreshold r m ell v := le_max_left _ _

lemma meanDegree_nonneg (r m : ℕ) : 0 ≤ meanDegree (V := V) r m := by
  unfold meanDegree
  positivity

lemma degreeThreshold_ge_mean (r m : ℕ) (ell : V → ℕ) (v : V) :
    meanDegree (V := V) r m ≤ (degreeThreshold r m ell v : ℝ) := by
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right (ell v) (Nat.ceil (meanDegree (V := V) r m)))

lemma terminal_degree_le {r m : ℕ} {ell : V → ℕ} (F : TerminalState V r m ell) (v : V) :
    vertexDegree F.val v ≤ m := by
  calc
    _ ≤ F.val.card := card_le_card (filter_subset _ _)
    _ = m := F.property.2.1

lemma degreeExcess_le {r m : ℕ} {ell : V → ℕ} (F : TerminalState V r m ell) (v : V) :
    degreeExcess F v ≤ m := (Nat.sub_le _ _).trans (terminal_degree_le F v)

variable (r m : ℕ) (ell : V → ℕ) [Nonempty (TerminalState V r m ell)]

@[expose] def degreeProbability (v : V) (t : ℕ) : ℝ :=
  (terminalLaw r m ell).event (fun F => vertexDegree F.val v = t)

lemma degreeProbability_nonneg (v : V) (t : ℕ) : 0 ≤ degreeProbability r m ell v t :=
  (terminalLaw r m ell).event_nonneg _

lemma degreeExcess_atom_succ (v : V) (q : ℕ) :
    natLawAtom (terminalLaw r m ell) (fun F => degreeExcess F v) (q+1) =
      degreeProbability r m ell v (degreeThreshold r m ell v + (q+1)) := by
  unfold natLawAtom degreeProbability
  congr 1
  funext F
  apply propext
  change vertexDegree F.val v - degreeThreshold r m ell v = q+1 ↔
    vertexDegree F.val v = degreeThreshold r m ell v + (q+1)
  omega

/-- At zero, all degrees below the threshold are included, as required in the
paper's successive-ratio argument. -/
lemma degreeProbability_le_excess_atom (v : V) (q : ℕ) :
    degreeProbability r m ell v (degreeThreshold r m ell v + q) ≤
      natLawAtom (terminalLaw r m ell) (fun F => degreeExcess F v) q := by
  apply (terminalLaw r m ell).event_mono
  intro F hF
  change vertexDegree F.val v - degreeThreshold r m ell v = q
  rw [hF]
  omega
end LooseHamilton
