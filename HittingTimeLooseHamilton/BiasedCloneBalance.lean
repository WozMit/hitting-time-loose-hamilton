module

public import HittingTimeLooseHamilton.BiasedPinskerDegree

public section

noncomputable section
open scoped BigOperators
namespace FiniteEntropy

variable {U E : Type*} [Fintype U] [Fintype E] [DecidableEq E]

/-- The local law obtained by restricting an edge marginal to one incidence row. -/
@[expose] def local_incidence_law (I : U → Finset E) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hrow : ∀ u, ∑ e ∈ I u, p e = 1) (u : U) :
    Law ↥(I u) where
  mass e := p e.val
  nonneg e := hp e.val
  total := by simpa only [Finset.sum_coe_sort] using hrow u

omit [Fintype U] [Fintype E] [DecidableEq E] in
lemma local_incidence_nonempty (I : U → Finset E) (q : ∀ u, Law ↥(I u)) (u : U) :
    Nonempty ↥(I u) := by
  classical
  by_contra h
  haveI : IsEmpty ↥(I u) := not_nonempty_iff.mp h
  have htotal := (q u).total
  simp at htotal

/-- Double counting the incidence relation with an arbitrary real edge weight. -/
lemma incidence_sum_eq (I : U → Finset E) (r : ℕ)
    (hcol : ∀ e, (Finset.univ.filter (fun u => e ∈ I u)).card = r) (f : E → ℝ) :
    (∑ u, ∑ e ∈ I u, f e) = (r : ℝ) * ∑ e, f e := by
  classical
  calc
    _ = ∑ u, ∑ e, if e ∈ I u then f e else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.sum_filter]
      simp
    _ = ∑ e, ∑ u, if e ∈ I u then f e else 0 := Finset.sum_comm
    _ = ∑ e, (r : ℝ) * f e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, hcol]
    _ = _ := (Finset.mul_sum _ _ _).symm

omit [Fintype E] [DecidableEq E] in
/-- Summed local L1 errors are bounded by the square root of the total local
entropy deficit. Each incidence row is allowed its own finite alphabet. -/
lemma local_incidence_error_bound (I : U → Finset E) (q : ∀ u, Law ↥(I u)) :
    (∑ u, ∑ e : ↥(I u), |(q u).mass e - ((I u).card : ℝ)⁻¹|) ≤
      2 * Real.sqrt ((Fintype.card U : ℝ) *
        ∑ u, (Real.log (I u).card - entropy (q u).mass)) := by
  classical
  let d : U → ℝ := fun u => ∑ e : ↥(I u), |(q u).mass e - ((I u).card : ℝ)⁻¹|
  let D : U → ℝ := fun u => Real.log (I u).card - entropy (q u).mass
  have hpoint (u : U) : (d u)^2 ≤ 4 * D u := by
    haveI := local_incidence_nonempty I q u
    simpa only [d, D, Fintype.card_coe] using l1_sq_le_four_entropy_deficit (q u)
  have h := weighted_error_sq_le (fun _ : U => (1 : ℝ)) d D (by intro; norm_num) hpoint
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have hn : 0 ≤ (Fintype.card U : ℝ) * ∑ u, D u := by
    nlinarith [sq_nonneg (∑ u, d u)]
  change (∑ u, d u) ≤ 2 * Real.sqrt ((Fintype.card U : ℝ) * ∑ u, D u)
  nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg ((Fintype.card U : ℝ) * ∑ u, D u)]

/-- Edge marginal balance from local entropy deficit and degree irregularity.
The two square roots correspond to these two independent losses. -/
theorem clone_incidence_balance (I : U → Finset E) (r : ℕ)
    (p : E → ℝ) (q : ∀ u, Law ↥(I u))
    (hq : ∀ u (e : ↥(I u)), (q u).mass e = p e.val)
    (hcol : ∀ e, (Finset.univ.filter (fun u => e ∈ I u)).card = r)
    (lam : ℝ) (hlam : 0 < lam)
    (hmean : ∑ u, ((I u).card : ℝ) = (Fintype.card U : ℝ) * lam) :
    (r : ℝ) * (∑ e, |p e - 1 / lam|) ≤
      2 * Real.sqrt ((Fintype.card U : ℝ) *
        ∑ u, (Real.log (I u).card - entropy (q u).mass)) +
      2 * Real.sqrt ((Fintype.card U : ℝ) *
        ((Fintype.card U : ℝ) * Real.log lam - ∑ u, Real.log (I u).card)) := by
  classical
  have hd (u : U) : 0 < ((I u).card : ℝ) := by
    haveI := local_incidence_nonempty I q u
    exact_mod_cast (show 0 < (I u).card by simpa using Fintype.card_pos (α := ↥(I u)))
  have hrow (u : U) : (∑ e ∈ I u, |p e - 1 / lam|) ≤
      (∑ e : ↥(I u), |(q u).mass e - ((I u).card : ℝ)⁻¹|) +
        |((I u).card : ℝ) / lam - 1| := by
    calc
      _ = ∑ e : ↥(I u), |(q u).mass e - 1 / lam| := by
        simp_rw [hq]
        exact (Finset.sum_coe_sort (I u) (fun e => |p e - 1 / lam|)).symm
      _ ≤ ∑ e : ↥(I u), (|(q u).mass e - ((I u).card : ℝ)⁻¹| +
          |((I u).card : ℝ)⁻¹ - 1 / lam|) := by
        apply Finset.sum_le_sum
        intro e _
        exact abs_sub_le _ _ _
      _ = (∑ e : ↥(I u), |(q u).mass e - ((I u).card : ℝ)⁻¹|) +
          ((I u).card : ℝ) * |((I u).card : ℝ)⁻¹ - 1 / lam| := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ = _ := by
        congr 1
        rw [show ((I u).card : ℝ) * |((I u).card : ℝ)⁻¹ - 1 / lam| =
            |((I u).card : ℝ) * (((I u).card : ℝ)⁻¹ - 1 / lam)| by
          rw [abs_mul, abs_of_pos (hd u)]]
        have heq : ((I u).card : ℝ) * (((I u).card : ℝ)⁻¹ - 1 / lam) =
            -(((I u).card : ℝ) / lam - 1) := by
          rw [mul_sub, mul_inv_cancel₀ (hd u).ne']
          ring
        rw [heq, abs_neg]
  rw [← incidence_sum_eq I r hcol]
  calc
    _ ≤ ∑ u, ((∑ e : ↥(I u), |(q u).mass e - ((I u).card : ℝ)⁻¹|) +
        |((I u).card : ℝ) / lam - 1|) := Finset.sum_le_sum (fun u _ => hrow u)
    _ = (∑ u, ∑ e : ↥(I u), |(q u).mass e - ((I u).card : ℝ)⁻¹|) +
        ∑ u, |((I u).card : ℝ) / lam - 1| := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (local_incidence_error_bound I q)
      (degree_l1_le_two_sqrt_log_deficit (fun u => ((I u).card : ℝ)) lam hlam hd hmean)

end FiniteEntropy
