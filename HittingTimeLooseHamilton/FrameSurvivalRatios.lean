module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

public section

noncomputable section
namespace LooseHamilton.FrameSurvival

/-- Exact survival factor for a fixed `q`-edge set in a uniform batch. -/
@[expose] def zeta (m τ q : ℕ) : ℝ := ((m-q).choose τ : ℝ)/(m.choose τ : ℝ)

/-- Survival factor for a completion conditional on deleting its candidate edge. -/
@[expose] def conditionedZeta (m τ k : ℕ) : ℝ :=
  ((m-k).choose (τ-1) : ℝ)/((m-1).choose (τ-1) : ℝ)

lemma zeta_pos {m τ q : ℕ} (h : τ ≤ m-q) : 0 < zeta m τ q := by
  apply div_pos <;> exact_mod_cast Nat.choose_pos (by omega)

lemma conditionedZeta_pos {m τ k : ℕ} (hk : 1 ≤ k) (hτ : 1 ≤ τ)
    (h : τ ≤ m-k) : 0 < conditionedZeta m τ k := by
  apply div_pos <;> exact_mod_cast Nat.choose_pos (by omega)

lemma completion_ratio {m τ k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (h : τ ≤ m-k) :
    zeta m τ (k-1) / zeta m τ k =
      ((m:ℝ)-k+1)/((m:ℝ)-k-τ+1) := by
  have hm : (m.choose τ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show τ ≤ m by omega)).ne'
  have hc : ((m-k).choose τ : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
  have hd : (m:ℝ)-k-τ+1 ≠ 0 := by
    have : (k:ℝ)+τ ≤ m := by exact_mod_cast (show k+τ ≤ m by omega)
    linarith
  have he := Nat.choose_mul_succ_eq (m-k) τ
  have heR : ((m-k).choose τ : ℝ)*((m:ℝ)-k+1) =
      ((m-(k-1)).choose τ : ℝ)*((m:ℝ)-k-τ+1) := by
    have he' : m-k+1 = m-(k-1) := by omega
    have he'' : ((m-k+1-τ:ℕ):ℝ) = (m:ℝ)-k-τ+1 := by
      rw [Nat.cast_sub (by omega : τ ≤ m-k+1), Nat.cast_add,
        Nat.cast_sub hkm, Nat.cast_one]
      ring
    have hz := congrArg (fun n : ℕ => (n:ℝ)) he
    push_cast at hz
    rw [he'', he'] at hz
    simpa [Nat.cast_sub hkm] using hz
  unfold zeta
  field_simp
  nlinarith [heR]

lemma conditioned_completion_ratio {m τ k : ℕ} (hk : 1 ≤ k)
    (hτ : 1 ≤ τ) (h : τ ≤ m-k) :
    conditionedZeta m τ k / zeta m τ k =
      (m:ℝ)/((m:ℝ)-k-τ+1) := by
  have hkm : k ≤ m := by omega
  have ht : τ ≤ m := by omega
  have hm : (m.choose τ : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ht).ne'
  have hc : ((m-k).choose τ : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
  have hb : ((m-1).choose (τ-1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show τ-1 ≤ m-1 by omega)).ne'
  have hd : (m:ℝ)-k-τ+1 ≠ 0 := by
    have : (k:ℝ)+τ ≤ m := by exact_mod_cast (show k+τ ≤ m by omega)
    linarith
  have hτR : (τ:ℝ) ≠ 0 := by exact_mod_cast (show τ ≠ 0 by omega)
  have hfirst := Nat.choose_succ_right_eq (m-k) (τ-1)
  have hsecond := Nat.add_one_mul_choose_eq (m-1) (τ-1)
  have hf : ((m-k).choose τ : ℝ)*(τ:ℝ) =
      ((m-k).choose (τ-1) : ℝ)*((m:ℝ)-k-τ+1) := by
    have hz := congrArg (fun n : ℕ => (n:ℝ)) hfirst
    rw [show τ-1+1=τ by omega] at hz
    push_cast at hz
    rw [Nat.cast_sub (by omega : τ-1 ≤ m-k), Nat.cast_sub hkm,
      Nat.cast_sub hτ, Nat.cast_one] at hz
    nlinarith [hz]
  have hs : (m:ℝ)*((m-1).choose (τ-1):ℝ) = (m.choose τ:ℝ)*(τ:ℝ) := by
    have hz := congrArg (fun n : ℕ => (n:ℝ)) hsecond
    rw [show (m-1+1)=m by omega, show (τ-1+1)=τ by omega] at hz
    simpa only [Nat.cast_mul] using hz
  unfold conditionedZeta zeta
  field_simp
  have hprod := congrArg (fun x : ℝ => x * (m.choose τ:ℝ)) hf
  have hprod2 := congrArg (fun x : ℝ => x * ((m-k).choose τ:ℝ)) hs
  nlinarith [hprod, hprod2]

end LooseHamilton.FrameSurvival
