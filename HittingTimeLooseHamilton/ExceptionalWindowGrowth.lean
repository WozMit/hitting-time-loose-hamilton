module

public import HittingTimeLooseHamilton.ExceptionalWindowScales

public section

namespace LooseHamilton
open Filter

theorem exceptionalWindowLo_grows {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (exceptionalWindowLo r) atTop atTop := by
  have hc : (0 : ℝ) < (99 / 100 : ℝ) / r := by
    apply div_pos (by norm_num)
    exact_mod_cast (show 0 < r by omega)
  exact tendsto_nat_floor_atTop.comp (tendsto_nat_mul_log_atTop.const_mul_atTop hc)

theorem exceptionalWindow_path_times {r : ℕ} (hr : 3 ≤ r) (t : ℕ) :
    ∀ᶠ n : ℕ in atTop, t ≤ exceptionalWindowLo r n ∧ t < n.choose r ∧
      exceptionalWindowHi r n ≤ n.choose r := by
  filter_upwards [(exceptionalWindowLo_grows (by omega : 1 ≤ r)).eventually
    (eventually_gt_atTop t), exceptionalWindow_times_le_complete_eventually hr] with n ht hw
  exact ⟨Nat.le_of_lt ht, ht.trans_le hw.1, hw.2⟩
end LooseHamilton
