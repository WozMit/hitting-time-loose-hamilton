module

public import HittingTimeLooseHamilton.CompletionEnumeration
public import HittingTimeLooseHamilton.CompletionSymmetry
public import HittingTimeLooseHamilton.NormalizationFormula

public section

/-! # Proposition 2.4: exact directed normalization

The proof uses the actual endpoint-swap involution, the complete-host count on
the contracted vertex set (including its two-edge boundary), and exact factorial
cancellation. No symmetry or enumeration formula remains as an assumed input.
-/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Directed normalization for any legal pair and chosen starting endpoint. -/
theorem directed_normalization {r k : ℕ} {markers : Finset (Finset V)}
    {P pair : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (h : LegalPrivateCompletion r markers P pair)
    (root : ↥markers) (a : ↥root.val) (y : ↥pair)
    (hks : markers.card + 2 ≤ k)
    (hN : Fintype.card V = (r-1)*k + markers.card) :
    (completionDirectedCount r markers (completeEdges V r) P pair h root a y : ℝ) /
      (unrestrictedCycleCount r markers (completeEdges V r) : ℝ) =
        directedNormalizationFactor r (Fintype.card V) k markers.card := by
  let z := otherEndpoint pair h.pair_card y
  have hyz : y ≠ z := by
    intro he
    exact otherEndpoint_ne pair h.pair_card y (congrArg Subtype.val he).symm
  rw [completionDirectedCount_eq_half_complete hr hM h root a y z
    (pair_eq_endpoints pair h.pair_card y) hyz]
  rw [completionCount_complete_formula hr hM root h hks hN]
  have hs : 1 ≤ markers.card := card_pos.mpr ⟨root.val, root.property⟩
  rw [completeHost_count hr hM root.property (by omega) (by omega) hN]
  exact completeHostFormula_residual_ratio hr hs hks hN

/-- The exact statement in the manuscript's endpoint notation. -/
theorem directed_normalization_endpoints {r k : ℕ} {markers : Finset (Finset V)}
    {P : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (y z : V) (hyz : y ≠ z) (h : LegalPrivateCompletion r markers P {y,z})
    (root : ↥markers) (a : ↥root.val) (hks : 2 ≤ k-markers.card)
    (hN : Fintype.card V = (r-1)*k + markers.card) :
    (completionDirectedCount r markers (completeEdges V r) P {y,z} h root a
      ⟨y, by simp⟩ : ℝ) /
      (unrestrictedCycleCount r markers (completeEdges V r) : ℝ) =
      ((r-2).factorial : ℝ) * (k-markers.card : ℕ) * (k-markers.card-1 : ℕ) /
        ((k-1 : ℕ) * ((Fintype.card V-2*markers.card).descFactorial r : ℝ)) :=
  directed_normalization hr hM h root a _ (by omega) hN

/-- Equation (exactY), with the finite-parameter conventions explicit. -/
@[expose] def Proposition24 : Prop :=
  ∀ r N k s : ℕ, 3 ≤ r → 1 ≤ s → 2 ≤ k-s → N = (r-1)*k+s →
    ∀ markers : Finset (Finset (Fin N)), IsPairMatching markers → markers.card = s →
    ∀ (P : Finset (Fin N)) (y z : Fin N), y ≠ z →
    ∀ (h : LegalPrivateCompletion r markers P {y,z})
      (root : ↥markers) (a : ↥root.val),
      (completionDirectedCount r markers (completeEdges (Fin N) r) P {y,z}
        h root a ⟨y, by simp⟩ : ℝ) /
        (unrestrictedCycleCount r markers (completeEdges (Fin N) r) : ℝ) =
          ((r-2).factorial : ℝ) * (k-s : ℕ) * (k-s-1 : ℕ) /
            ((k-1 : ℕ) * ((N-2*s).descFactorial r : ℝ))

/-- Proposition 2.4's exact normalization, with no additional hypotheses. -/
theorem proposition24 : Proposition24 := by
  intro r N k s hr hs hks hN markers hM hcard P y z hyz h root a
  have hn : Fintype.card (Fin N) = (r-1)*k + markers.card := by
    simpa only [Fintype.card_fin, hcard] using hN
  simpa only [Fintype.card_fin, hcard] using
    directed_normalization_endpoints hr hM y z hyz h root a (by omega) hn

/-- The complete-host mean degree agrees with r times its edge count divided by N. -/
theorem completeMeanDegree_eq_mean {r N : ℕ} (hr : 1 ≤ r) (hN : 1 ≤ N) :
    completeMeanDegree r N = (r : ℝ) * (N.choose r : ℝ) / N := by
  have h := Nat.add_one_mul_choose_eq (N-1) (r-1)
  rw [Nat.sub_add_cancel hN,
    Nat.sub_add_cancel hr] at h
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  apply (eq_div_iff hn).mpr
  unfold completeMeanDegree
  have hh : (N : ℝ) * ((N-1).choose (r-1) : ℝ) = (N.choose r : ℝ) * r := by
    exact_mod_cast h
  nlinarith

end LooseHamilton
