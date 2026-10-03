module

public import HittingTimeLooseHamilton.EnumerationCodes
public import HittingTimeLooseHamilton.NormalizationFormula

public section

set_option maxHeartbeats 2000000
noncomputable section
namespace LooseHamilton

private theorem allocation_quotient_mul (d k : ℕ) :
    ((d*k).factorial / d.factorial^k) * d.factorial^k = (d*k).factorial := by
  have h := Allocation.card_mul_factorial_pow (Fin (k*d)) k d (by simp)
  have hd : d.factorial^k ∣ (d*k).factorial := by
    rw [Nat.mul_comm d k]
    exact ⟨Fintype.card (Allocation.Balanced (Fin (k*d)) k d), h.symm.trans (Nat.mul_comm _ _)⟩
  exact Nat.div_mul_cancel hd

/-- The complete-host factorial count with the integer quotient cleared. -/
theorem completeHostFormula_mul_factorials {r N k s : ℕ}
    (hr : 3 ≤ r) (hsk : s ≤ k) (hN : N = (r-1)*k+s) :
    completeHostFormula r N k s * ((k-s).factorial * (r-2).factorial^k) =
      2^(s-1) * (k-1).factorial * (N-2*s).factorial := by
  have hr' : r-1 = (r-2)+1 := by omega
  have hn : N-2*s = (r-2)*k+(k-s) := by
    rw [hr', Nat.add_mul, one_mul] at hN
    omega
  have hle : k-s ≤ N-2*s := by omega
  have hsub : N-2*s-(k-s) = (r-2)*k := by omega
  have hc := Nat.choose_mul_factorial_mul_factorial hle
  rw [hsub] at hc
  unfold completeHostFormula
  calc
    _ = 2^(s-1) * (k-1).factorial *
        ((N-2*s).choose (k-s) * (k-s).factorial) *
        ((((r-2)*k).factorial / (r-2).factorial^k) * (r-2).factorial^k) := by ring
    _ = _ := by
      rw [allocation_quotient_mul]
      calc
        _ = 2^(s-1) * (k-1).factorial *
          ((N-2*s).choose (k-s) * (k-s).factorial * ((r-2)*k).factorial) := by ring
        _ = _ := by rw [hc]

/-- Equivalent real-valued factorial expression for the integer enumeration. -/
theorem completeHostFormula_cast {r N k s : ℕ}
    (hr : 3 ≤ r) (hsk : s ≤ k) (hN : N = (r-1)*k+s) :
    (completeHostFormula r N k s : ℝ) =
      (2:ℝ)^(s-1) * (k-1).factorial * (N-2*s).factorial /
        ((k-s).factorial * ((r-2).factorial:ℝ)^k) := by
  apply (eq_div_iff (by positivity)).mpr
  exact_mod_cast completeHostFormula_mul_factorials hr hsk hN

/-- Exact ratio of the directed residual complete-host count to its original count. -/
theorem completeHostFormula_residual_ratio {r N k s : ℕ}
    (hr : 3 ≤ r) (hs : 1 ≤ s) (hsk : s+2 ≤ k)
    (hN : N = (r-1)*k+s) :
    ((completeHostFormula r (N-(r-2)) (k-1) (s+1) : ℝ) / 2) /
        (completeHostFormula r N k s : ℝ) =
      ((r-2).factorial:ℝ) * (k-s:ℕ) * (k-s-1:ℕ) /
        ((k-1:ℕ) * ((N-2*s).descFactorial r : ℝ)) := by
  have hk : 3 ≤ k := by omega
  have hr' : r-1 = (r-2)+1 := by omega
  have hkr : (r-1)*(k-1) + (r-1) = (r-1)*k := by
    rw [← Nat.mul_succ]; congr 1; omega
  have hN' : N-(r-2) = (r-1)*(k-1)+(s+1) := by omega
  have hn : N-2*s = (r-2)*k+(k-s) := by
    rw [hr', Nat.add_mul, one_mul] at hN
    omega
  have hnr : r ≤ N-2*s := by
    have : (r-2)*3 ≤ (r-2)*k := Nat.mul_le_mul_left _ hk
    omega
  have hn' : N-(r-2)-2*(s+1) = N-2*s-r := by omega
  have hm' : k-1-(s+1) = k-s-2 := by omega
  have hf1 : (k-1).factorial = (k-1) * (k-2).factorial := by
    convert Nat.factorial_succ (k-2) using 1 <;> congr 1 <;> omega
  have hf2 : (k-s).factorial = (k-s)*(k-s-1)*(k-s-2).factorial := by
    have ha : k-s = (k-s-1)+1 := by omega
    have hb : k-s-1 = (k-s-2)+1 := by omega
    conv_lhs => rw [ha, Nat.factorial_succ, ← ha]
    rw [show (k-s-1).factorial = (k-s-1)*(k-s-2).factorial by
      conv_lhs => rw [hb, Nat.factorial_succ, ← hb]]
    ring
  have hfn := Nat.factorial_mul_descFactorial hnr
  have hp : ((r-2).factorial:ℝ)^k =
      ((r-2).factorial:ℝ)^(k-1) * (r-2).factorial := by
    rw [← pow_succ]; congr 1; omega
  have hs' : s+1-1 = s := by omega
  have hs2 : (2:ℝ)^s = 2^(s-1)*2 := by
    rw [← pow_succ]; congr 1; omega
  have hdesc : ((N-2*s).descFactorial r : ℝ) ≠ 0 := by
    have hz : (N-2*s).descFactorial r ≠ 0 := by
      intro hz
      rw [hz, Nat.mul_zero] at hfn
      exact Nat.factorial_ne_zero _ hfn.symm
    exact_mod_cast hz
  rw [completeHostFormula_cast hr (by omega) hN', completeHostFormula_cast hr (by omega) hN]
  rw [hn', hm', hs', hs2, hf1, hf2, ← hfn,
    show k-1-1 = k-2 by omega]
  simp only [Nat.cast_mul]
  rw [hp]
  have hk1 : ((k-1:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show k-1 ≠ 0 by omega)
  have hfac (n : ℕ) : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hdesc, hk1, hfac, pow_ne_zero] <;> ring

/-- The complete-host enumeration is strictly positive throughout its parameter range. -/
theorem completeHostFormula_pos {r N k s : ℕ}
    (hr : 3 ≤ r) (hsk : s ≤ k) (hN : N = (r-1)*k+s) :
    0 < completeHostFormula r N k s := by
  have h : (0:ℝ) < completeHostFormula r N k s := by
    rw [completeHostFormula_cast hr hsk hN]
    positivity
  exact_mod_cast h

theorem directedNormalizationFactor_eq_ratio {r N k s : ℕ}
    (hr : 3 ≤ r) (hs : 1 ≤ s) (hsk : s+2 ≤ k)
    (hN : N = (r-1)*k+s) :
    directedNormalizationFactor r N k s =
      ((completeHostFormula r (N-(r-2)) (k-1) (s+1) : ℝ) / 2) /
        (completeHostFormula r N k s : ℝ) :=
  (completeHostFormula_residual_ratio hr hs hsk hN).symm

end LooseHamilton
