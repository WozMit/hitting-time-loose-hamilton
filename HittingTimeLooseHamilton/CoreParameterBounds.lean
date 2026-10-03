module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics
public import Mathlib.Tactic.GCongr

public section

/-! Uniform deterministic scalar bounds for deleting the exceptional blocks. -/
noncomputable section
namespace LooseHamilton
open Filter

lemma density_change_under_deletion {n d m t r : ℝ}
    (hn : 0 < n) (hd0 : 0 ≤ d) (hd : d ≤ n / 2)
    (hm : 0 ≤ m) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    |r * (m - t) / (n - d) - r * m / n| ≤
      (2 * (r * m / n) * d + 2 * r * t) / n := by
  have hN : 0 < n - d := by linarith
  have hA : 0 ≤ r * m / n * d := by positivity
  have hB : 0 ≤ r * t := mul_nonneg hr ht
  have hid : r * (m - t) / (n - d) - r * m / n =
      (r * m / n * d - r * t) / (n - d) := by
    field_simp <;> ring
  have hinv : 1 / (n - d) ≤ 2 / n := by
    apply (div_le_div_iff₀ hN hn).mpr
    linarith
  rw [hid, abs_div, abs_of_pos hN]
  calc
    _ ≤ (r * m / n * d + r * t) / (n - d) := by
      apply div_le_div_of_nonneg_right _ hN.le
      calc
        |r * m / n * d - r * t| ≤ |r * m / n * d| + |r * t| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg hA,abs_of_nonneg hB]
    _ ≤ (r * m / n * d + r * t) * (2 / n) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hinv (add_nonneg hA hB)
    _ = _ := by ring

lemma log_change_under_deletion {n d : ℝ} (hn : 0 < n) (hd0 : 0 ≤ d) (hd : d ≤ n / 2) :
    0 ≤ Real.log n - Real.log (n - d) ∧
      Real.log n - Real.log (n - d) ≤ 2 * d / n := by
  have hN : 0 < n - d := by linarith
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hN (by linarith))
  · have h := Real.log_le_sub_one_of_pos (div_pos hn hN)
    rw [Real.log_div hn.ne' hN.ne'] at h
    have heq : n / (n-d) - 1 = d / (n-d) := by field_simp <;> ring
    rw [heq] at h
    apply h.trans
    apply (div_le_div_iff₀ hN hn).mpr
    nlinarith

/-- The final density window follows from absolute errors of at most one. -/
lemma density_window_transfer {n N x y : ℝ}
    (hN : 1 ≤ Real.log N) (hlog0 : 0 ≤ Real.log n - Real.log N)
    (hlog : Real.log n - Real.log N ≤ 1)
    (hlarge : 5 ≤ Real.log (Real.log N))
    (hinput : |x - Real.log n| ≤ 2 * Real.log (Real.log n) + 1)
    (hchange : |y - x| ≤ 1) :
    |y - Real.log N| ≤ 3 * Real.log (Real.log N) := by
  have hln : 0 < Real.log n := by linarith
  have hlN : 0 < Real.log N := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos hln hlN)
  rw [Real.log_div hln.ne' hlN.ne'] at hh
  have hratio : Real.log n / Real.log N - 1 ≤ 1 := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hlN).mpr
    linarith
  have hloglog : Real.log (Real.log n) - Real.log (Real.log N) ≤ 1 := hh.trans hratio
  have htri := abs_add_le (y - x) (x - Real.log n)
  have htri2 := abs_add_le (y - Real.log n) (Real.log n - Real.log N)
  rw [abs_of_nonneg hlog0] at htri2
  have he1 : y - x + (x - Real.log n) = y - Real.log n := by ring
  have he2 : y - Real.log n + (Real.log n - Real.log N) = y - Real.log N := by ring
  rw [he1] at htri
  rw [he2] at htri2
  linarith

/-- A one-unit logarithmic perturbation changes the small degree floor by at most one. -/
lemma core_degree_floor_bounds {n N : ℝ} (hN : 1 ≤ N) (hnN : N ≤ n)
    (hlog : Real.log n - Real.log N ≤ 1) :
    Nat.floor (epsilon * Real.log N) ≤ Nat.floor (epsilon * Real.log n) ∧
      Nat.floor (epsilon * Real.log n) ≤ Nat.floor (epsilon * Real.log N) + 1 := by
  have hNp : 0 < N := by linarith
  have hmono : Real.log N ≤ Real.log n := Real.log_le_log hNp hnN
  have he0 : 0 ≤ epsilon := by norm_num [epsilon]
  have he1 : epsilon ≤ 1 := by norm_num [epsilon]
  have hbase : 0 ≤ epsilon * Real.log N := mul_nonneg he0 (Real.log_nonneg hN)
  constructor
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_left hmono he0)
  · rw [← Nat.floor_add_one hbase]
    apply Nat.floor_mono
    have hh := mul_le_mul_of_nonneg_left hlog he0
    nlinarith

/-- The residual lower-degree offsets are bounded independently of n. -/
lemma core_degree_offset_bound {a b j R : ℕ} (hba : b ≤ a) (hab : a ≤ b + 1) (hj : j ≤ R) :
    |(((a + 1 - j : ℕ) : ℝ) - b)| ≤ (R : ℝ) + 2 := by
  have hupper : a + 1 - j ≤ b + 2 := by omega
  have hlower : b ≤ (a + 1 - j) + R := by omega
  have hu : ((a + 1 - j : ℕ) : ℝ) ≤ (b : ℝ) + 2 := by exact_mod_cast hupper
  have hl : (b : ℝ) ≤ ((a + 1 - j : ℕ) : ℝ) + R := by exact_mod_cast hlower
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) R]

/-- Explicit n-only controls suffice uniformly for every admissible deletion. -/
theorem core_parameter_bounds_of_controls (r n : ℕ) (hn : 2 ≤ n)
    (hsmall : ((r - 2 : ℕ) : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) ≤ (n : ℝ) / 2)
    (herror : (4 + 40 * (r : ℝ)) * (r - 2 : ℕ) *
      (n : ℝ) ^ (1 / 12 : ℝ) * Real.log n / n ≤ 1)
    (hwindow : 2 * Real.log (Real.log n) + 1 ≤ Real.log n)
    (hloghalf : 1 ≤ Real.log ((n : ℝ) / 2))
    (hlarge : 5 ≤ Real.log (Real.log ((n : ℝ) / 2)))
    (hmarker : (n : ℝ) ^ (1 / 12 : ℝ) ≤ ((n : ℝ) / 2) ^ (1 / 10 : ℝ))
    (s m T : ℕ) (hs : (s : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ)) (hTm : T ≤ m)
    (hT : (T : ℝ) ≤ 20 * (r - 2 : ℕ) * s * Real.log n)
    (hdensity : |(r : ℝ) * m / n - Real.log n| ≤ 2 * Real.log (Real.log n) + 1) :
    let N := n - (r - 2) * s
    let M := m - T
    0 < N ∧ |(r : ℝ) * M / N - Real.log N| ≤ 3 * Real.log (Real.log N) ∧
      (s : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
      ∀ j ≤ 2 * (r - 2),
        |(((Nat.floor (epsilon * Real.log n) + 1 - j : ℕ) : ℝ) -
          Nat.floor (epsilon * Real.log N))| ≤ (2 * (r - 2) : ℕ) + 2 := by
  dsimp only
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hdBound : (((r - 2) * s : ℕ) : ℝ) ≤ (r - 2 : ℕ) * (n : ℝ) ^ (1 / 12 : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
  have hdhalf : (((r - 2) * s : ℕ) : ℝ) ≤ (n : ℝ) / 2 := hdBound.trans hsmall
  have hdle : (r - 2) * s ≤ n := by exact_mod_cast (show (((r - 2) * s : ℕ) : ℝ) ≤ n by linarith)
  have hNcast : ((n - (r - 2) * s : ℕ) : ℝ) = (n : ℝ) - ((r - 2) * s : ℕ) := Nat.cast_sub hdle
  have hMcast : ((m - T : ℕ) : ℝ) = (m : ℝ) - T := Nat.cast_sub hTm
  have hNhalf : (n : ℝ) / 2 ≤ ((n - (r - 2) * s : ℕ) : ℝ) := by rw [hNcast]; linarith
  have hNpos : 0 < n - (r - 2) * s := by
    exact_mod_cast (lt_of_lt_of_le (half_pos hnp) hNhalf)
  have hlogN : Real.log ((n : ℝ) / 2) ≤ Real.log ((n - (r - 2) * s : ℕ) : ℝ) :=
    Real.log_le_log (half_pos hnp) hNhalf
  have hlogN1 : 1 ≤ Real.log ((n - (r - 2) * s : ℕ) : ℝ) := hloghalf.trans hlogN
  have hloglarge : 5 ≤ Real.log (Real.log ((n - (r - 2) * s : ℕ) : ℝ)) :=
    hlarge.trans (Real.log_le_log (by linarith) hlogN)
  have hlogchange := log_change_under_deletion hnp (Nat.cast_nonneg ((r - 2) * s)) hdhalf
  rw [← hNcast] at hlogchange
  have hlogchange1 : Real.log (n : ℝ) - Real.log ((n - (r - 2) * s : ℕ) : ℝ) ≤ 1 := by
    apply hlogchange.2.trans
    apply (div_le_one hnp).mpr
    linarith
  have hmeanupper : (r : ℝ) * m / n ≤ 2 * Real.log n := by
    have h := (abs_le.mp hdensity).2
    linarith
  have hTbound : (T : ℝ) ≤ 20 * (r - 2 : ℕ) * (n : ℝ) ^ (1 / 12 : ℝ) * Real.log n := by
    apply hT.trans
    gcongr
  have hchange := density_change_under_deletion hnp (Nat.cast_nonneg ((r - 2) * s)) hdhalf
    (Nat.cast_nonneg m) (Nat.cast_nonneg T) (Nat.cast_nonneg r)
  have herr : (2 * ((r : ℝ) * m / n) * ((r - 2) * s : ℕ) + 2 * r * T) / n ≤ 1 := by
    calc
      _ ≤ (2 * (2 * Real.log n) * ((r - 2 : ℕ) * (n : ℝ) ^ (1 / 12 : ℝ)) +
        2 * r * (20 * (r - 2 : ℕ) * (n : ℝ) ^ (1 / 12 : ℝ) * Real.log n)) / n := by
          gcongr
      _ = (4 + 40 * (r : ℝ)) * (r - 2 : ℕ) * (n : ℝ) ^ (1 / 12 : ℝ) * Real.log n / n := by ring
      _ ≤ 1 := herror
  have hchange1 := hchange.trans herr
  rw [← hNcast, ← hMcast] at hchange1
  refine ⟨hNpos,density_window_transfer hlogN1 hlogchange.1 hlogchange1 hloglarge hdensity hchange1,?_,?_⟩
  · exact hs.trans (hmarker.trans (Real.rpow_le_rpow (half_pos hnp).le hNhalf (by norm_num)))
  · intro j hj
    have hN1 : (1 : ℝ) ≤ ((n - (r - 2) * s : ℕ) : ℝ) := by exact_mod_cast hNpos
    have hNn : ((n - (r - 2) * s : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n ((r - 2) * s)
    obtain ⟨hfloor1,hfloor2⟩ := core_degree_floor_bounds hN1 hNn hlogchange1
    exact core_degree_offset_bound hfloor1 hfloor2 hj

/-- The error budget is uniform over all s≤n^(1/12), not just a chosen sequence. -/
theorem core_scalar_controls_eventually (r : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧
      ((r - 2 : ℕ) : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) ≤ (n : ℝ) / 2 ∧
      (4 + 40 * (r : ℝ)) * (r - 2 : ℕ) * (n : ℝ) ^ (1 / 12 : ℝ) * Real.log n / n ≤ 1 ∧
      2 * Real.log (Real.log n) + 1 ≤ Real.log n ∧
      1 ≤ Real.log ((n : ℝ) / 2) ∧
      5 ≤ Real.log (Real.log ((n : ℝ) / 2)) ∧
      (n : ℝ) ^ (1 / 12 : ℝ) ≤ ((n : ℝ) / 2) ^ (1 / 10 : ℝ) := by
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 12 : ℝ) / n) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_nat_rpow_ratio (by norm_num : (1 / 12 : ℝ) < 1)
  have hsmalllim := hratio.const_mul ((r - 2 : ℕ) : ℝ)
  simp only [mul_zero] at hsmalllim
  have hsmall := hsmalllim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have herrlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 12 : ℝ) * Real.log n / n) atTop (nhds 0) := by
    have h := tendsto_nat_rpow_mul_log_pow (by norm_num : (1 / 12 : ℝ) - 1 < 0) 1
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [Real.rpow_sub hnp,Real.rpow_one,pow_one]
    ring
  have herrlim' := herrlim.const_mul ((4 + 40 * (r : ℝ)) * (r - 2 : ℕ))
  simp only [mul_zero] at herrlim'
  have herr := herrlim'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hloglim : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogdiv : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hll := (hlogdiv.comp hloglim).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hlog2 := hloglim.eventually (eventually_ge_atTop (2 : ℝ))
  have hhalflim : Tendsto (fun n : ℕ => (n : ℝ) / 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hloghalf := (Real.tendsto_log_atTop.comp hhalflim).eventually (eventually_ge_atTop (1 : ℝ))
  have hlarge := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hhalflim)).eventually
    (eventually_ge_atTop (5 : ℝ))
  have hmarker := (tendsto_nat_rpow_ratio (by norm_num : (1 / 12 : ℝ) < 1 / 10)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (2 : ℝ) ^ (1 / 10 : ℝ) by positivity))
  filter_upwards [hsmall,herr,hll,hlog2,hloghalf,hlarge,hmarker,eventually_ge_atTop (2 : ℕ)]
    with n hs he hll hl2 hlh hlarge hm hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨hn,?_,?_,?_,hlh,hlarge,?_⟩
  · have hs' : ((r - 2 : ℕ) : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) / n < 1 / 2 := by
      simpa only [mul_div_assoc] using hs
    have hh := (div_lt_iff₀ hnp).mp hs'
    linarith
  · have : (4 + 40 * (r : ℝ)) * (r - 2 : ℕ) * (n : ℝ) ^ (1 / 12 : ℝ) * Real.log n / n < 1 := by
      convert he using 1; ring
    exact this.le
  · have hll' : Real.log (Real.log n) < (1 / 4 : ℝ) * Real.log n :=
      (div_lt_iff₀ (by linarith : 0 < Real.log n)).mp hll
    linarith
  · rw [Real.div_rpow (Nat.cast_nonneg n) (by norm_num)]
    have hp : (0 : ℝ) < (n : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hnp _
    calc
      (n : ℝ) ^ (1 / 12 : ℝ) = ((n : ℝ) ^ (1 / 12 : ℝ) / (n : ℝ) ^ (1 / 10 : ℝ)) *
          (n : ℝ) ^ (1 / 10 : ℝ) := (div_mul_cancel₀ _ hp.ne').symm
      _ ≤ (1 / (2 : ℝ) ^ (1 / 10 : ℝ)) * (n : ℝ) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right hm.le hp.le
      _ = _ := by ring

/-- Uniformly, at least half of the original vertices survive the deletion. -/
theorem core_surviving_size_eventually (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, (s : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) →
      (n : ℝ) / 2 ≤ ((n - (r - 2) * s : ℕ) : ℝ) := by
  filter_upwards [core_scalar_controls_eventually r] with n hn
  intro s hs
  have hd : (((r - 2) * s : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    apply le_trans _ hn.2.1
    push_cast
    exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hd' : (r - 2) * s ≤ n := by exact_mod_cast (show (((r - 2) * s : ℕ) : ℝ) ≤ n by linarith)
  rw [Nat.cast_sub hd']
  linarith

/-- Uniform eventual core parameters from the manuscript's finite deletion bounds. -/
theorem core_parameter_bounds_eventually (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ s m T : ℕ,
      (s : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) → T ≤ m →
      (T : ℝ) ≤ 20 * (r - 2 : ℕ) * s * Real.log n →
      |(r : ℝ) * m / n - Real.log n| ≤ 2 * Real.log (Real.log n) + 1 →
      let N := n - (r - 2) * s
      let M := m - T
      0 < N ∧ |(r : ℝ) * M / N - Real.log N| ≤ 3 * Real.log (Real.log N) ∧
        (s : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
        ∀ j ≤ 2 * (r - 2),
          |(((Nat.floor (epsilon * Real.log n) + 1 - j : ℕ) : ℝ) -
            Nat.floor (epsilon * Real.log N))| ≤ (2 * (r - 2) : ℕ) + 2 := by
  filter_upwards [core_scalar_controls_eventually r] with n hn
  intro s m T hs hTm hT hdensity
  exact core_parameter_bounds_of_controls r n hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1
    hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2 s m T hs hTm hT hdensity

end LooseHamilton
