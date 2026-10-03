module

public import Mathlib

public section

/-! Decreasing adjacent mass ratios for the finite hypergeometric weights. -/
noncomputable section
namespace LooseHamilton

@[expose] def rootHypergeometricWeight (s c b k : ℕ) : ℝ :=
  if k≤b then (s.choose k:ℝ)*(c.choose (b-k):ℝ) else 0

@[expose] def rootHypergeometricRate (s c b k : ℕ) : ℝ :=
  ((s-k:ℕ):ℝ)*((b-k:ℕ):ℝ)/((k+1:ℝ)*((c-b+k+1:ℕ):ℝ))

lemma rootHypergeometricWeight_nonneg (s c b k : ℕ) :
    0≤rootHypergeometricWeight s c b k := by unfold rootHypergeometricWeight; split_ifs <;> positivity

lemma rootHypergeometricRate_nonneg (s c b k : ℕ) :
    0≤rootHypergeometricRate s c b k := by unfold rootHypergeometricRate; positivity

lemma rootHypergeometricWeight_succ (s c b k : ℕ) (hbc : b≤c) :
    rootHypergeometricWeight s c b (k+1)=
      rootHypergeometricRate s c b k*rootHypergeometricWeight s c b k := by
  by_cases hk : k<b
  · have hk1 : k+1≤b := by omega
    have hk0 : k≤b := by omega
    have hchoose1 := Nat.choose_succ_right_eq s k
    have hchoose2 := Nat.choose_succ_right_eq c (b-(k+1))
    have hsub : b-(k+1)+1=b-k := by omega
    have hsub2 : c-(b-(k+1))=c-b+k+1 := by omega
    rw [hsub,hsub2] at hchoose2
    have hc1 : (s.choose (k+1):ℝ)*(k+1)=(s.choose k:ℝ)*(s-k:ℕ) := by exact_mod_cast hchoose1
    have hc2 : (c.choose (b-k):ℝ)*(b-k:ℕ)=
        (c.choose (b-(k+1)):ℝ)*(c-b+k+1:ℕ) := by exact_mod_cast hchoose2
    unfold rootHypergeometricWeight rootHypergeometricRate
    rw [if_pos hk1,if_pos hk0]
    have hp : (0:ℝ)<(k+1:ℝ)*((c-b+k+1:ℕ):ℝ) := by positivity
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hp.ne').mpr
    calc
      _ = ((s.choose (k+1):ℝ)*(k+1))*((c.choose (b-(k+1)):ℝ)*(c-b+k+1:ℕ)) := by ring
      _ = _ := by rw [hc1,←hc2]; ring
  · have hsub : b-k=0 := Nat.sub_eq_zero_of_le (by omega)
    unfold rootHypergeometricWeight rootHypergeometricRate
    rw [if_neg (by omega : ¬k+1≤b),hsub]
    simp

lemma rootHypergeometricRate_antitone (s c b : ℕ) : Antitone (rootHypergeometricRate s c b) := by
  intro i j hij
  unfold rootHypergeometricRate
  have hs : ((s-j:ℕ):ℝ)≤(s-i:ℕ) := Nat.cast_le.mpr (Nat.sub_le_sub_left hij _)
  have hb : ((b-j:ℕ):ℝ)≤(b-i:ℕ) := Nat.cast_le.mpr (Nat.sub_le_sub_left hij _)
  have hd1 : (i+1:ℝ)≤j+1 := by exact_mod_cast Nat.add_le_add_right hij 1
  have hd2 : ((c-b+i+1:ℕ):ℝ)≤(c-b+j+1:ℕ) := by exact_mod_cast (show c-b+i+1≤c-b+j+1 by omega)
  apply div_le_div₀ (by positivity) (mul_le_mul hs hb (by positivity) (by positivity)) (by positivity)
  exact mul_le_mul hd1 hd2 (by positivity) (by positivity)

/-- Adjacent likelihood ratios decrease, in cross-multiplied form covering zero masses. -/
theorem rootHypergeometricWeight_cross (s c b : ℕ) (hbc : b≤c)
    {i j : ℕ} (hij : i≤j) :
    rootHypergeometricWeight s c b (j+1)*rootHypergeometricWeight s c b i ≤
      rootHypergeometricWeight s c b (i+1)*rootHypergeometricWeight s c b j := by
  rw [rootHypergeometricWeight_succ _ _ _ _ hbc,rootHypergeometricWeight_succ _ _ _ _ hbc]
  have h := mul_le_mul_of_nonneg_right (rootHypergeometricRate_antitone s c b hij)
    (mul_nonneg (rootHypergeometricWeight_nonneg s c b i) (rootHypergeometricWeight_nonneg s c b j))
  convert h using 1 <;> ring
end LooseHamilton
