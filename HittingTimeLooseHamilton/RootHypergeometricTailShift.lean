module

public import HittingTimeLooseHamilton.NatLawAtoms
public import HittingTimeLooseHamilton.CoreConditionalCounting
public import Mathlib

public section

/-! A finite decreasing likelihood-ratio argument for one-step conditional tail shifts. -/
noncomputable section
namespace LooseHamilton
open Finset

lemma weighted_prefix_comparison (f g : ℕ → ℝ) (K k : ℕ) (hk : k≤K+1)
    (hcross : ∀ i j : ℕ, i≤j → f j*g i≤f i*g j) :
    (∑ i∈range k,g i)*(∑ i∈range (K+1),f i) ≤
      (∑ i∈range k,f i)*(∑ i∈range (K+1),g i) := by
  have hsub : range k⊆range (K+1) := range_mono hk
  have hf := sum_sdiff (f:=f) hsub
  have hg := sum_sdiff (f:=g) hsub
  have hd : (∑ i∈range k,g i)*(∑ j∈range (K+1)\range k,f j) ≤
      (∑ i∈range k,f i)*(∑ j∈range (K+1)\range k,g j) := by
    rw [sum_mul,sum_mul]
    apply sum_le_sum
    intro i hi
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro j hj
    have hi' := mem_range.mp hi
    have hj' : k≤j := Nat.le_of_not_lt (by simpa using (mem_sdiff.mp hj).2)
    simpa only [mul_comm] using hcross i j (by omega)
  rw [←hf,←hg]
  nlinarith

/-- Adjacent mass likelihood ratios decreasing imply the hit-conditioned upper tail
is bounded by the original tail with threshold lowered by one. -/
theorem natLaw_tail_shift_product {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (X : Ω → ℕ) (K : ℕ) (hX : ∀ω,X ω≤K)
    (hc : ∀ i j : ℕ, i≤j → natLawAtom p X (j+1)*natLawAtom p X i ≤
      natLawAtom p X (i+1)*natLawAtom p X j) (k : ℕ) :
    p.event (fun ω => k+1≤X ω) ≤
      p.event (fun ω => 1≤X ω)*p.event (fun ω => k≤X ω) := by
  let a := natLawAtom p X
  have hnorm : ∑ i∈range (K+1),a i=1 := sum_natLawAtom_total p X K hX
  have hz : a (K+1)=0 := natLawAtom_eq_zero p X K hX (by omega)
  by_cases hk : k≤K+1
  · have hpref := weighted_prefix_comparison (fun i => a (i+1)) a K k hk hc
    have htotal : ∑ i∈range (K+1),a (i+1)=1-a 0 := by
      have h := sum_range_succ' a (K+1)
      rw [sum_range_succ,hnorm,hz,add_zero] at h
      linarith
    have hprefix : ∑ i∈range k,a (i+1)=(∑ i∈range (k+1),a i)-a 0 := by
      have h := sum_range_succ' a k
      linarith
    rw [htotal,hprefix,hnorm,mul_one] at hpref
    simp only [event_ge_eq_one_sub_atoms]
    change 1-(∑ i∈range (k+1),a i)≤(1-(∑ i∈range 1,a i))*(1-∑ i∈range k,a i)
    simp only [sum_range_one]
    nlinarith
  · rw [p.event_eq_zero_of_false (by intro ω h; have := hX ω; omega)]
    exact mul_nonneg (p.event_nonneg _) (p.event_nonneg _)

/-- Conditioning on a positive natural statistic can only increase its upper tails. -/
theorem natLaw_hit_condition_tail_lower {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (X : Ω → ℕ) (hE : 0<p.event (fun ω => 1≤X ω)) (k : ℕ) :
    p.event (fun ω => k≤X ω) ≤
      (p.condition (fun ω => 1≤X ω) hE).event (fun ω => k≤X ω) := by
  by_cases hk : k=0
  · subst k
    simp
  · rw [condition_event_eq_joint]
    have he : (fun ω => 1≤X ω ∧ k≤X ω)=(fun ω => k≤X ω) := by
      funext ω
      apply propext
      omega
    rw [he]
    apply (le_div_iff₀ hE).mpr
    exact mul_le_of_le_one_right (p.event_nonneg _) (p.event_le_one _)

theorem natLaw_hit_condition_tail_upper {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (X : Ω → ℕ) (K : ℕ) (hX : ∀ω,X ω≤K)
    (hc : ∀ i j : ℕ, i≤j → natLawAtom p X (j+1)*natLawAtom p X i ≤
      natLawAtom p X (i+1)*natLawAtom p X j)
    (hE : 0<p.event (fun ω => 1≤X ω)) (k : ℕ) :
    (p.condition (fun ω => 1≤X ω) hE).event (fun ω => k+1≤X ω) ≤
      p.event (fun ω => k≤X ω) := by
  rw [condition_event_eq_joint]
  have he : (fun ω => 1≤X ω ∧ k+1≤X ω)=(fun ω => k+1≤X ω) := by
    funext ω
    apply propext
    omega
  rw [he]
  apply (div_le_iff₀ hE).mpr
  simpa only [mul_comm] using natLaw_tail_shift_product p X K hX hc k
end LooseHamilton
