module

public import HittingTimeLooseHamilton.KahnMatchingRandomOrder
public import HittingTimeLooseHamilton.KahnFallingFactorial
public import HittingTimeLooseHamilton.KahnRevealEntropy
public import Mathlib.Algebra.BigOperators.Fin

public section

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Kahn.MatchingLaw
open FiniteEntropy
variable {n r : ℕ} {H : Hypergraph n r}

lemma marginal_support_candidates (μ : Law (MatchingIn H)) (v : Fin n)
    (Y : Finset (Fin n)) (hY : (marginal μ v).mass Y ≠ 0) :
    Y ∈ candidates (r := r) v := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  constructor
  · by_contra hc
    exact hY (marginal_zero_outside μ v Y (Or.inl hc))
  · intro hv
    exact hY (marginal_zero_outside μ v Y (Or.inr hv))

lemma sum_marginal_eq_candidates (μ : Law (MatchingIn H)) (v : Fin n)
    (f : Finset (Fin n) → ℝ) :
    (∑ Y, (marginal μ v).mass Y * f Y) =
      ∑ Y ∈ candidates (r := r) v, (marginal μ v).mass Y * f Y := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro Y _ hY
  have hm : (marginal μ v).mass Y = 0 := by
    by_contra hm
    exact hY (marginal_support_candidates μ v Y hm)
  simp [hm]

/-- Conversion of the exact counting inputs to the per-vertex logarithmic penalty.
The counting hypotheses are discharged by the independent uniform-order lemmas. -/
lemma local_entropy_bound_of_counts (μ : Law (MatchingIn H)) (v : Fin n)
    (p : Law (Finset (Fin n) × (Finset (Fin n) ⊕ Finset (Fin n))))
    (hfst : p.fst = marginal μ v)
    (size : Finset (Fin n) → Fin (n / r))
    (hknown : ∀ Y Z, Y ≠ Z → p.mass (Y, Sum.inl Z) = 0)
    (hrow : ∀ Y, (∑ Z, p.mass (Y, Sum.inr Z)) = (1 / (r : ℝ)) * p.fst.mass Y)
    (hcompatible : ∀ Y Z, ¬ Y ⊆ Z → p.mass (Y, Sum.inr Z) = 0)
    (hgroup : ∀ Y (i : Fin (n / r)),
      (∑ Z, if size Z = i then p.mass (Y, Sum.inr Z) else 0) =
        p.fst.mass Y * (1 / (n : ℝ)))
    (hbound : ∀ Y ∈ candidates (r := r) v, ∀ i : Fin (n / r),
      (∑ Z, if size Z = i ∧ Y ⊆ Z then p.snd.mass (Sum.inr Z) else 0) ≤
        (1 / (n : ℝ)) * ((((i.val : ℝ) + 1) / (n / r : ℕ)) ^ (r - 1) + gamma μ v Y)) :
    p.conditionalEntropy Prod.snd ≤
      (1 / (r : ℝ)) * entropy (marginal μ v).mass +
        (1 / (n : ℝ)) * ∑ Y ∈ candidates (r := r) v, (marginal μ v).mass Y *
          ∑ i ∈ Finset.range (n / r),
            Real.log ((((i : ℝ) + 1) / (n / r : ℕ)) ^ (r - 1) + gamma μ v Y) := by
  classical
  have h := p.reveal_entropy_le_of_group_bounds_on_support (1 / (r : ℝ))
    hknown hrow size (fun Y Z => Y ⊆ Z) hcompatible
    (fun _ => 1 / (n : ℝ)) (fun _ => by positivity) hgroup
    (fun Y i => (((i.val : ℝ) + 1) / (n / r : ℕ)) ^ (r - 1) + gamma μ v Y)
    (by
      intro Y hY i
      apply hbound Y
      apply marginal_support_candidates μ v Y
      simpa only [hfst] using hY)
  rw [hfst] at h
  apply h.trans_eq
  congr 1
  simp_rw [← Finset.mul_sum]
  rw [sum_marginal_eq_candidates]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [mul_left_comm]
  congr 1
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => Real.log ((((i : ℝ) + 1) /
    (n / r : ℕ)) ^ (r - 1) + gamma μ v Y)) (n / r)

lemma jointRevealLaw_compatible_group_eq {K : Type*} [Fintype K] [DecidableEq K]
    (μ : Law (MatchingIn H)) (v : Fin n) (size : Finset (Fin n) → K)
    (i : K) (Y : Finset (Fin n)) :
    (∑ Z, if size Z = i ∧ Y ⊆ Z then (jointRevealLaw μ v).snd.mass (Sum.inr Z) else 0) =
      ∑ M, μ.mass M * (uniform (A := Equiv.Perm (Fin n))).event (fun σ =>
        v ∉ M.val.earlierEdges σ v ∧ size (M.val.available σ v) = i ∧ Y ⊆ M.val.available σ v) := by
  classical
  let E : Finset (Fin n) ⊕ Finset (Fin n) → Prop := fun e =>
    match e with
    | Sum.inl _ => False
    | Sum.inr Z => size Z = i ∧ Y ⊆ Z
  have he : (∑ Z, if size Z = i ∧ Y ⊆ Z
      then (jointRevealLaw μ v).snd.mass (Sum.inr Z) else 0) =
      (jointRevealLaw μ v).snd.event E := by
    simp only [Law.event, Fintype.sum_sum_type, E, if_false, Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr rfl
    intro Z _
    split_ifs <;> rfl
  rw [he, Law.snd_eq_map, Law.event_map]
  simp only [jointRevealLaw, Law.event_map]
  have hp (z : Equiv.Perm (Fin n) × MatchingIn H) :
      E (taggedEvidence z.1 v z.2) ↔
        v ∉ z.2.val.earlierEdges z.1 v ∧ size (z.2.val.available z.1 v) = i ∧
          Y ⊆ z.2.val.available z.1 v := by
    by_cases hv : v ∈ z.2.val.earlierEdges z.1 v <;>
      simp [E, taggedEvidence, tagEvidence, PerfectMatching.evidence, hv]
  simp_rw [hp]
  simp only [orderLaw, Law.event, Fintype.sum_prod_type, Law.prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> ring

/-- Summing the fixed-matching survival counts produces the unconditional collision
error `gamma`; the falling-factorial kernel is bounded by the power kernel. -/
lemma compatible_group_bound_of_survival_counts
    (μ : Law (MatchingIn H)) (v : Fin n) (size : Finset (Fin n) → Fin (n / r))
    (i : Fin (n / r)) (Y : Finset (Fin n)) (hY : Y.card = r - 1)
    (hrm : r - 1 < n / r)
    (hgroup : ∀ M : MatchingIn H,
      (uniform (A := Equiv.Perm (Fin n))).event (fun σ =>
        v ∉ M.val.earlierEdges σ v ∧ size (M.val.available σ v) = i) = 1 / (n : ℝ))
    (hsurvive : ∀ M : MatchingIn H,
      (uniform (A := Equiv.Perm (Fin n))).event (fun σ =>
        v ∉ M.val.earlierEdges σ v ∧ size (M.val.available σ v) = i ∧
          Y ⊆ M.val.available σ v) =
        (1 / (n : ℝ)) * (i.val.descFactorial (M.val.tau v Y) : ℝ) /
          ((n / r - 1).descFactorial (M.val.tau v Y) : ℝ)) :
    (∑ Z, if size Z = i ∧ Y ⊆ Z then (jointRevealLaw μ v).snd.mass (Sum.inr Z) else 0) ≤
      (1 / (n : ℝ)) * ((((i.val : ℝ) + 1) / (n / r : ℕ)) ^ (r - 1) + gamma μ v Y) := by
  classical
  rw [jointRevealLaw_compatible_group_eq]
  let P : ℝ := (((i.val : ℝ) + 1) / (n / r : ℕ)) ^ (r - 1)
  have hq : 0 ≤ 1 / (n : ℝ) := by positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpoint (M : MatchingIn H) :
      (uniform (A := Equiv.Perm (Fin n))).event (fun σ =>
        v ∉ M.val.earlierEdges σ v ∧ size (M.val.available σ v) = i ∧ Y ⊆ M.val.available σ v) ≤
      (1 / (n : ℝ)) * (P + if M.val.Bad v Y then 1 else 0) := by
    by_cases hb : M.val.Bad v Y
    · simp only [if_pos hb]
      have hmono := (uniform (A := Equiv.Perm (Fin n))).event_mono
        (E := fun σ => v ∉ M.val.earlierEdges σ v ∧ size (M.val.available σ v) = i ∧
          Y ⊆ M.val.available σ v)
        (F := fun σ => v ∉ M.val.earlierEdges σ v ∧ size (M.val.available σ v) = i)
        (fun _ h => ⟨h.1, h.2.1⟩)
      rw [hgroup M] at hmono
      exact hmono.trans (by nlinarith [mul_nonneg hq hP])
    · simp only [if_neg hb, add_zero]
      have ht : M.val.tau v Y = r - 1 :=
        le_antisymm (M.val.tau_le v Y hY) (Nat.le_of_not_lt hb)
      rw [hsurvive M, ht, mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hq
      have ha := Kahn.descFactorial_ratio_le_pow
        (t := i.val + 1) (m := n / r) (d := r - 1) (by omega) (by omega) hrm
      simpa [P, Nat.cast_add, Nat.cast_one] using ha
  calc
    _ ≤ ∑ M, μ.mass M * ((1 / (n : ℝ)) * (P + if M.val.Bad v Y then 1 else 0)) :=
      Finset.sum_le_sum fun M _ => mul_le_mul_of_nonneg_left (hpoint M) (μ.nonneg M)
    _ = (1 / (n : ℝ)) * (P + gamma μ v Y) := by
      unfold gamma Law.event
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hp : (∑ M, μ.mass M * (1 / (n : ℝ) * P)) = (1 / (n : ℝ)) * P := by
        rw [← Finset.sum_mul, μ.total, one_mul]
      rw [hp]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      split_ifs <;> ring

lemma unknown_row_of_group_masses
    (p : Law (Finset (Fin n) × (Finset (Fin n) ⊕ Finset (Fin n))))
    (size : Finset (Fin n) → Fin (n / r))
    (hr : 0 < r) (hn : 0 < n) (hdiv : r ∣ n)
    (hgroup : ∀ Y (i : Fin (n / r)),
      (∑ Z, if size Z = i then p.mass (Y, Sum.inr Z) else 0) =
        p.fst.mass Y * (1 / (n : ℝ))) (Y : Finset (Fin n)) :
    (∑ Z, p.mass (Y, Sum.inr Z)) = (1 / (r : ℝ)) * p.fst.mass Y := by
  classical
  have he : (∑ Z, p.mass (Y, Sum.inr Z)) =
      ∑ i : Fin (n / r), ∑ Z, if size Z = i then p.mass (Y, Sum.inr Z) else 0 := by
    rw [Finset.sum_comm]
    simp
  rw [he]
  simp only [hgroup, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnr : (r : ℝ) * (n / r : ℕ) = n := by exact_mod_cast Nat.mul_div_cancel' hdiv
  have hr' : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * p.fst.mass Y) hnr]

lemma jointRevealLaw_group_bound (μ : Law (MatchingIn H))
    (hr : 0 < r) (hm : 0 < n / r) (hrm : r - 1 < n / r)
    (v : Fin n) (Y : Finset (Fin n)) (hY : Y ∈ candidates (r := r) v)
    (i : Fin (n / r)) :
    (∑ Z, if revealGroup hm Z = i ∧ Y ⊆ Z
      then (jointRevealLaw μ v).snd.mass (Sum.inr Z) else 0) ≤
      (1 / (n : ℝ)) * ((((i.val : ℝ) + 1) / (n / r : ℕ)) ^ (r - 1) + gamma μ v Y) := by
  classical
  have hY' : Y.card = r - 1 ∧ v ∉ Y := (Finset.mem_filter.mp hY).2
  apply compatible_group_bound_of_survival_counts μ v (revealGroup hm) i Y hY'.1 hrm
  · intro M
    exact uniform_group_probability hr hm M.val v i
  · intro M
    simpa only [and_assoc] using uniform_group_survival_probability hr hm M.val v i Y hY'.2

/-- Kahn's per-vertex reveal inequality, with all random-order counts discharged.
This is the finite entropy bound obtained from equations (31)--(39). -/
theorem local_entropy_bound (μ : Law (MatchingIn H))
    (hr : 0 < r) (hm : 0 < n / r) (hrm : r - 1 < n / r) (hdiv : r ∣ n)
    (v : Fin n) :
    (jointRevealLaw μ v).conditionalEntropy Prod.snd ≤
      (1 / (r : ℝ)) * entropy (marginal μ v).mass +
        (1 / (n : ℝ)) * ∑ Y ∈ candidates (r := r) v, (marginal μ v).mass Y *
          ∑ i ∈ Finset.range (n / r),
            Real.log ((((i : ℝ) + 1) / (n / r : ℕ)) ^ (r - 1) + gamma μ v Y) := by
  classical
  have hg (Y : Finset (Fin n)) (i : Fin (n / r)) :
      (∑ Z, if revealGroup hm Z = i then (jointRevealLaw μ v).mass (Y, Sum.inr Z) else 0) =
        (jointRevealLaw μ v).fst.mass Y * (1 / (n : ℝ)) := by
    rw [fst_jointRevealLaw]
    exact jointRevealLaw_unknown_group μ hr hm v Y i
  apply local_entropy_bound_of_counts μ v (jointRevealLaw μ v)
    (fst_jointRevealLaw μ v) (revealGroup hm)
    (jointRevealLaw_known_offdiagonal μ v)
    (unknown_row_of_group_masses (jointRevealLaw μ v) (revealGroup hm) hr
      (Nat.zero_lt_of_lt v.isLt) hdiv hg)
    (jointRevealLaw_incompatible μ v) hg
  intro Y hY i
  exact jointRevealLaw_group_bound μ hr hm hrm v Y hY i

end Kahn.MatchingLaw
