module

public import HittingTimeLooseHamilton.CandidateLogSurvival
public import HittingTimeLooseHamilton.FrameEntropyBudget

public section

noncomputable section
namespace LooseHamilton.CandidateLogSurvival

lemma log_one_sub_lower {h : ℝ} (h0 : 0≤h) (hh : h≤1/2) :
    -2*h ≤ Real.log (1-h) := by
  have hd : 0<1-h := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hd
  have he : -2*h ≤ 1-(1-h)⁻¹ := by
    apply (mul_le_mul_iff_left₀ hd).mp
    have hid : (1-(1-h)⁻¹)*(1-h)= -h := by field_simp <;> ring
    rw [hid]
    nlinarith [mul_nonneg h0 (show 0≤1-2*h by linarith)]
  exact he.trans hl

/-- Survival with its actual hypergeometric probability preserves the imposed
entropy budget, with precisely one additional unit of its error coefficient. -/
theorem budget_after_survival {Ω : Type*} {r N k m τ : ℕ} {mu B h : ℝ}
    {F G : Finset Ω} (hr : 3≤r) (hmu : 0<mu) (hm : 0<m)
    (hsmall : 2*(k+τ)≤m) (h0 : 0≤h) (hh : h≤1/2)
    (hbudget : FrameEntropy.budget r N k mu B F)
    (hsurvive : (1-h)*zeta m k τ*(F.card:ℝ) ≤ G.card)
    (herror : 2*h + 2*(k:ℝ)*τ*(k+τ)/(m:ℝ)^2 ≤
      (N:ℝ)/Real.sqrt (FrameScales.L1 N)) :
    FrameEntropy.budget r N k (mu*(((m:ℝ)-τ)/m)) (B+1) G := by
  have hz := zeta_pos (show k+τ<m by omega)
  have hf : (0:ℝ)<F.card := Nat.cast_pos.mpr hbudget.1.card_pos
  have hhpos : 0<1-h := by linarith
  have hg : (0:ℝ)<G.card := (mul_pos (mul_pos hhpos hz) hf).trans_le hsurvive
  have hlog := Real.log_le_log (mul_pos (mul_pos hhpos hz) hf) hsurvive
  rw [Real.log_mul (mul_pos hhpos hz).ne' hf.ne', Real.log_mul hhpos.ne' hz.ne'] at hlog
  have hlh := log_one_sub_lower h0 hh
  have hlz := (abs_le.mp (log_zeta_error hm hsmall)).1
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have htR : (τ:ℝ)<m := by exact_mod_cast (show τ<m by omega)
  have hq : 0<((m:ℝ)-τ)/m := div_pos (by linarith) hmR
  have hmean := Real.log_le_sub_one_of_pos hq
  have heq : ((m:ℝ)-τ)/m-1=-(τ:ℝ)/m := by field_simp <;> ring
  rw [heq] at hmean
  have hmean' := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg k : (0:ℝ)≤k)
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hrpos : 0<(r:ℝ)-1 := by linarith
  have hbench : FrameEntropy.benchmark r k (mu*(((m:ℝ)-τ)/m)) =
      FrameEntropy.benchmark r k mu+(k:ℝ)*Real.log (((m:ℝ)-τ)/m) := by
    unfold FrameEntropy.benchmark
    rw [← mul_assoc, Real.log_mul (mul_pos hrpos hmu).ne' hq.ne']
    ring
  refine ⟨Finset.card_pos.mp (Nat.cast_pos.mp hg), ?_⟩
  rw [hbench]
  have hb := hbudget.2
  have hsplit : (B+1)*(N:ℝ)/Real.sqrt (FrameScales.L1 N) =
      B*(N:ℝ)/Real.sqrt (FrameScales.L1 N)+(N:ℝ)/Real.sqrt (FrameScales.L1 N) := by ring
  rw [hsplit]
  ring_nf at hmean' hlz herror hb ⊢
  linarith
end LooseHamilton.CandidateLogSurvival
