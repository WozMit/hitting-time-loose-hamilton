module

public import HittingTimeLooseHamilton.BiasedRoleParameters

public section

/-! Finite extraction of the precise regular-path hypotheses needed by Theorem 6.1. -/
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Finset
variable {r : ℕ}

lemma regular_partitionBound (D : BiasedRoleInstance r) (hr : 3 ≤ r)
    {C L : ℝ} (hreg : PathGraphUpperRegular r C L D.host)
    (hs : (D.s : ℝ) ≤ L * (D.N : ℝ) ^ (1 / 10 : ℝ)) :
    D.partitionBound (C * (Real.log (D.N : ℝ)) ^ (-1 / 8 : ℝ)) := by
  intro A _ hA
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (3 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hbook : (D.N : ℝ) = ((r : ℝ)-1)*(D.k : ℝ)+(D.s : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (D.vertex_bookkeeping hr)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] using h
  have hcard : (A.card : ℝ) = (D.k : ℝ)+(D.s : ℝ) := by exact_mod_cast hA
  have hdiff : (A.card : ℝ)-junctionFraction r*D.N =
      (D.s : ℝ) - (D.s : ℝ)/((r : ℝ)-1) := by
    rw [hcard, hbook]
    unfold junctionFraction
    field_simp [ne_of_gt hr1] <;> ring
  have hquot : (D.s : ℝ)/((r : ℝ)-1) ≤ D.s := by
    apply div_le_self (Nat.cast_nonneg _)
    have : (3 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hnon : 0 ≤ (D.s : ℝ)/((r : ℝ)-1) := div_nonneg (Nat.cast_nonneg _) hr1.le
  have hwindow : |(A.card : ℝ)-junctionFraction r*D.N| ≤
      L*(D.N : ℝ)^(1/10 : ℝ) := by
    rw [hdiff, abs_of_nonneg (sub_nonneg.mpr hquot)]
    linarith
  have hh := hreg.partitions A (by simpa only [Fintype.card_fin] using hwindow)
  simpa only [Fintype.card_fin, μ, mul_assoc, mul_left_comm, mul_comm] using hh

lemma regular_eta_le (D : BiasedRoleInstance r) (hr : 3 ≤ r)
    {C L : ℝ} (hreg : PathGraphUpperRegular r C L D.host) :
    D.η ≤ C * (Real.log (D.N : ℝ)) ^ (-1 / 4 : ℝ) := by
  have hpos := D.maxPairDegree_pos hr
  have hne : (univ.filter (fun p : Fin D.N × Fin D.N => p.1 ≠ p.2)).Nonempty := by
    by_contra h
    have hempty := not_nonempty_iff_eq_empty.mp h
    simp [maxPairDegree, hempty] at hpos
  obtain ⟨p,hp,heq⟩ := exists_mem_eq_sup _ hne (fun p => pairDegree D.host p.1 p.2)
  have hpne := (mem_filter.mp hp).2
  have hb := hreg.codegree p.1 p.2 hpne
  change maxPairDegree D.host = pairDegree D.host p.1 p.2 at heq
  unfold η
  apply (div_le_iff₀ (D.μ_pos hr)).mpr
  rw [heq]
  simpa only [Fintype.card_fin, μ, mul_assoc, mul_left_comm, mul_comm] using hb

end LooseHamilton.BiasedRoleInstance
