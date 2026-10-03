module

public import HittingTimeLooseHamilton.ExtensionDegreeUpper

public section

/-! Uniformly summable pointwise codegree tails along the extension. -/
noncomputable section
namespace LooseHamilton
open Finset Filter
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ}

theorem extension_pair_upper_eventually (r : ℕ) (hr : 3≤r) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V=n → ∀ (M : ℕ) (ell : V → ℕ) (F : TerminalState V r M ell) (j : ℕ),
    (M:ℝ)≤(n.choose r:ℝ)/2 → M≤j → j≤(completeEdges V r).card →
    (99/100:ℝ)*Real.log n≤(r:ℝ)*j/n →
    ∀ u v : V, u≠v → pairDegree F.val u v≤2 →
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => 4*((r:ℝ)*j/n)*(Real.log n)^(-1/4:ℝ) <
        (pairDegree (extensionState F σ j) u v:ℝ)) ≤ (n:ℝ)^(-((r:ℝ)+5)) := by
  classical
  filter_upwards [eventually_ge_atTop r,
    eventually_path_pair_exponent (4*((r:ℝ)-1)) (by norm_num : (0:ℝ)<2) (r+4),
    eventually_pair_threshold_margin (by norm_num : (0:ℝ)<2) 2] with n hn hex hmarg
  obtain ⟨hn0,hl,hex⟩ := hex
  intro V _ _ hcard M ell F j hhalf hj hjK hμ u v huv hd
  let μ : ℝ := (r:ℝ)*j/n
  let a : ℝ := μ*(Real.log n)^(-1/4:ℝ)
  let k := Nat.floor (2*a)+1
  let t : ℝ := (n:ℝ)^(1/2:ℝ)
  have hnreal : (0:ℝ)<n := by exact_mod_cast hn0
  have ht : 0<t := Real.rpow_pos_of_pos hnreal _
  have ht2 : t^2=(n:ℝ) := by
    dsimp [t]
    rw [←Real.rpow_mul_natCast hnreal.le]
    norm_num
  have hlogt : Real.log t=Real.log n/2 := by
    dsimp [t]
    rw [Real.log_rpow hnreal]
    ring
  have hK : (0:ℝ)<n.choose r := by exact_mod_cast Nat.choose_pos hn
  have hMK : M<(completeEdges V r).card := by
    rw [completeEdges_card,hcard]
    exact_mod_cast (show (M:ℝ)<n.choose r by linarith)
  have hMle : M≤n.choose r := by simpa [completeEdges_card,hcard] using hMK.le
  have ha : 0≤a := by dsimp [a,μ]; positivity
  have hbase : (pairDegree F.val u v:ℝ)≤2*a := by
    have h2 := hmarg μ hμ
    have hd' : (pairDegree F.val u v:ℝ)≤2 := by exact_mod_cast hd
    dsimp [a]
    nlinarith
  have hmono : (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => 4*a < (pairDegree (extensionState F σ j) u v:ℝ)) ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => pairDegree F.val u v+k≤pairDegree (extensionState F σ j) u v) := by
    apply FiniteEntropy.Law.event_mono
    intro σ hσ
    have hk : (Nat.floor (2*a):ℝ)≤2*a := Nat.floor_le (by positivity)
    have hh : pairDegree F.val u v+Nat.floor (2*a)<pairDegree (extensionState F σ j) u v := by
      exact_mod_cast (show (pairDegree F.val u v:ℝ)+(Nat.floor (2*a):ℝ)<
        (pairDegree (extensionState F σ j) u v:ℝ) by linarith)
    dsimp [k]
    omega
  have hmean : (((n-2).choose (r-2)-pairDegree F.val u v:ℕ):ℝ)*(j-M:ℕ)/(n.choose r-M:ℕ) ≤
      4*((r:ℝ)-1)*μ/n := by
    have hh := path_pair_mean_upper (show 2≤r by omega) hn hhalf hj
    have hsub : (((n-2).choose (r-2)-pairDegree F.val u v:ℕ):ℝ)≤(n-2).choose (r-2) :=
      Nat.cast_le.mpr (Nat.sub_le _ _)
    calc
      _ ≤ ((n-2).choose (r-2):ℝ)*(j-M:ℕ)/(n.choose r-M:ℕ) := by gcongr
      _ ≤ _ := by simpa only [Nat.cast_sub hj,Nat.cast_sub hMle] using hh
  have hpow : t^k=Real.exp ((k:ℝ)*Real.log t) := by
    rw [Real.exp_nat_mul,Real.exp_log ht]
  have htmean : t*((((n-2).choose (r-2)-pairDegree F.val u v:ℕ):ℝ)*(j-M:ℕ)/(n.choose r-M:ℕ)) ≤
      4*((r:ℝ)-1)*μ/t := by
    calc
      _ ≤ t*(4*((r:ℝ)-1)*μ/n) := mul_le_mul_of_nonneg_left hmean ht.le
      _ = _ := by rw [←ht2]; field_simp <;> ring
  have htail := extension_pair_upper_tail F (by omega) j k hjK hMK huv t ht
  have htail' := hmono.trans htail
  simp only [hcard,completeEdges_card] at htail'
  have hbound : Real.exp (t*(((n-2).choose (r-2)-pairDegree F.val u v:ℕ):ℝ)*(j-M:ℕ)/
      (n.choose r-M:ℕ))/t^k ≤ Real.exp (4*((r:ℝ)-1)*μ/t-(k:ℝ)*Real.log n/2) := by
    rw [hpow,←Real.exp_sub,hlogt]
    apply Real.exp_le_exp.mpr
    nlinarith only [show t*(((n-2).choose (r-2)-pairDegree F.val u v:ℕ):ℝ)*(j-M:ℕ)/(n.choose r-M:ℕ)≤4*((r:ℝ)-1)*μ/t by convert htmean using 1 <;> ring]
  have hk : 2*μ*(Real.log n)^(-1/4:ℝ)≤(k:ℝ) := by
    have h := (Nat.lt_floor_add_one (2*a)).le
    simpa only [k,a,Nat.cast_add,Nat.cast_one,mul_assoc] using h
  have he := hex μ k hμ hk
  have hb := htail'.trans (hbound.trans he)
  have heq : -(((r+4:ℕ):ℝ)+1) = -((r:ℝ)+5) := by push_cast; ring
  rw [heq] at hb
  simpa only [a,μ,mul_assoc] using hb
end LooseHamilton
