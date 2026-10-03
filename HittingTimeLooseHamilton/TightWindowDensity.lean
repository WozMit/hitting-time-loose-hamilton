module

public import HittingTimeLooseHamilton.TightWindowScales

public section
noncomputable section
namespace LooseHamilton
open Filter

lemma coreWindow_density_bound {r n m : ℕ} (hr : 1 ≤ r) (hn : r ≤ n)
    (hscale : 0 ≤ coreWindowScale r 2 n)
    (hlo : coreWindowLo r n ≤ m) (hhi : m ≤ coreWindowHi r n) :
    |(r : ℝ) * m / n - Real.log n| ≤ 2 * Real.log (Real.log n) + 1 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk : (0 : ℝ) ≤ (r : ℝ) / n := div_nonneg hr0.le hn0.le
  have hk1 : (r : ℝ) / n ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast hn)
  have hcancel (a : ℝ) : (r : ℝ) / n * coreWindowScale r a n =
      Real.log n + a * Real.log (Real.log n) := by
    unfold coreWindowScale
    field_simp
    <;> ring
  have hfloor : coreWindowScale r (-2) n - 1 ≤ (coreWindowLo r n : ℝ) := by
    have h := Nat.lt_floor_add_one (coreWindowScale r (-2) n)
    change coreWindowScale r (-2) n - 1 ≤ (Nat.floor (coreWindowScale r (-2) n) : ℝ)
    linarith
  have hceil : (coreWindowHi r n : ℝ) ≤ coreWindowScale r 2 n + 1 :=
    (Nat.ceil_lt_add_one hscale).le
  have hmlo : (coreWindowLo r n : ℝ) ≤ m := by exact_mod_cast hlo
  have hmhi : (m : ℝ) ≤ coreWindowHi r n := by exact_mod_cast hhi
  have hl := mul_le_mul_of_nonneg_left (hfloor.trans hmlo) hk
  have hh := mul_le_mul_of_nonneg_left (hmhi.trans hceil) hk
  rw [mul_sub,hcancel,mul_one] at hl
  rw [mul_add,hcancel,mul_one] at hh
  have he : (r : ℝ) * m / n = ((r : ℝ)/n) * m := by ring
  rw [he]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma coreWindow_density_bound_eventually {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, coreWindowLo r n ≤ m → m ≤ coreWindowHi r n →
      |(r : ℝ) * m / n - Real.log n| ≤ 2 * Real.log (Real.log n) + 1 := by
  filter_upwards [coreWindowScale_eventually_nonneg hr 2,eventually_ge_atTop r] with n hs hn
  exact fun m hlo hhi => coreWindow_density_bound hr hn hs hlo hhi
end LooseHamilton
