module

public import HittingTimeLooseHamilton.FrameEntropyBiasedInstance
public import HittingTimeLooseHamilton.FrameScalarEnvelopes

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Filter Topology AuxiliaryFrame

lemma logarithm_double_transport {N n : ℝ} (hn : 2 ≤ n) (hle : N ≤ 2*n)
    (hpos : 0<N) (hlog : 4 ≤ Real.log N) :
    Real.log N ≤ 2*Real.log n ∧
    Real.sqrt (Real.log (Real.log N)) ≤ 2*Real.sqrt (Real.log (Real.log n)) := by
  have hnpos : 0<n := by linarith
  have hNN : N≤n*n := by nlinarith
  have hl : Real.log N ≤ 2*Real.log n := by
    have hh := Real.log_le_log hpos hNN
    rw [Real.log_mul hnpos.ne' hnpos.ne'] at hh
    linarith
  have hln : 2 ≤ Real.log n := by linarith
  have hll : Real.log 2 ≤ Real.log (Real.log n) :=
    Real.log_le_log (by norm_num) hln
  have hlnpos : 0<Real.log n := by linarith
  have hllpos : 0≤Real.log (Real.log n) := Real.log_nonneg (by linarith)
  have hllN : Real.log (Real.log N) ≤ 2*Real.log (Real.log n) := by
    have hh := Real.log_le_log (by linarith : 0<Real.log N) hl
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hlnpos.ne'] at hh
    linarith
  refine ⟨hl,?_⟩
  have hh := Real.sqrt_le_sqrt (show Real.log (Real.log N) ≤ 4*Real.log (Real.log n) by linarith)
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)] at hh
  norm_num at hh
  exact hh

/-- Both active-size entropy normalization losses are bounded at one threshold
chosen before the frame and its prescribed marker directions. -/
theorem eventually_frame_entropy_transport (r : ℕ) (B : ℝ) (hB : 0≤B) :
    ∀ᶠ N : ℕ in atTop, ∀ original : Finset (Finset (Fin N)),
      ∀ F : Frame r original,
      0 ≤ F.entropyXi B ∧
      F.entropyXi B ≤ (2*B)/Real.sqrt (Real.log F.n) ∧
      Real.sqrt (Real.log (Real.log N)) ≤
        2*Real.sqrt (Real.log (Real.log F.n)) := by
  filter_upwards [eventually_ge_atTop (8*r+4),
    FrameScales.L1_tendsto.eventually (eventually_ge_atTop 4)] with N hN hlog original F
  have hd := F.val.deleted_card_le
  have hc := F.n_add_deleted
  simp only [Fintype.card_fin] at hc
  have hn : 2≤F.n := by omega
  have hnR : (2:ℝ)≤F.n := by exact_mod_cast hn
  have hnpos : (0:ℝ)<F.n := by positivity
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlow : (N:ℝ)≤2*F.n := by exact_mod_cast (show N≤2*F.n by omega)
  have hup : (F.n:ℝ)≤N := by exact_mod_cast (show F.n≤N by omega)
  have ht := logarithm_double_transport hnR hlow hNpos hlog
  have hlpos : 0<Real.log (F.n:ℝ) := Real.log_pos (by linarith)
  have hspos := Real.sqrt_pos.mpr hlpos
  have hsNpos : 0<Real.sqrt (Real.log (N:ℝ)) := Real.sqrt_pos.mpr (by change 4≤Real.log (N:ℝ) at hlog; linarith)
  have hsle := Real.sqrt_le_sqrt (Real.log_le_log hnpos hup)
  refine ⟨by unfold AuxiliaryFrame.Frame.entropyXi; positivity, ?_, ht.2⟩
  unfold AuxiliaryFrame.Frame.entropyXi
  simp only [Fintype.card_fin, FrameScales.L1]
  apply (div_le_iff₀ hnpos).mpr
  apply (div_le_iff₀ hsNpos).mpr
  have hmul := mul_le_mul_of_nonneg_left hlow hB
  have hratio := (le_div_iff₀ hspos).mpr (show 2*B*Real.sqrt (Real.log F.n) ≤ 2*B*Real.sqrt (Real.log N) by gcongr)
  have hh := mul_le_mul_of_nonneg_right hratio hnpos.le
  calc
    B*(N:ℝ) ≤ 2*B*(F.n:ℝ) := by nlinarith
    _ ≤ _ := by convert hh using 1 <;> ring
/-- Bounded marker modifications preserve the active-size polynomial budget,
uniformly over the original matching and the frame. -/
theorem eventually_frame_marker_transport (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ original : Finset (Finset (Fin N)),
      (original.card:ℝ) ≤ (N:ℝ)^(1/10:ℝ) →
      ∀ F : Frame r original, (F.s:ℝ) ≤ 6*(F.n:ℝ)^(1/10:ℝ) := by
  filter_upwards [eventually_ge_atTop (8*r+4)] with N hN original ho F
  have hd := F.val.deleted_card_le
  have hc := F.n_add_deleted
  simp only [Fintype.card_fin] at hc
  have hn : 2≤F.n := by omega
  have hnR : (1:ℝ)≤F.n := by exact_mod_cast (show 1≤F.n by omega)
  have hlow : (N:ℝ)≤2*F.n := by exact_mod_cast (show N≤2*F.n by omega)
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg N) hlow (by norm_num : (0:ℝ)≤1/10)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg F.n)] at hp
  have htwo : (2:ℝ)^(1/10:ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hone : (1:ℝ) ≤ (F.n:ℝ)^(1/10:ℝ) := Real.one_le_rpow hnR (by norm_num)
  have hmark : F.s ≤ original.card+2 := by
    have hh := F.marker_budget.introduced_le
    have hc := Finset.card_le_card_sdiff_add_card (s := F.markers) (t := original)
    change F.markers.card ≤ _
    omega
  have hm : (F.s:ℝ) ≤ original.card+2 := by exact_mod_cast hmark
  nlinarith [mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (Nat.cast_nonneg F.n) (1/10:ℝ))]
end LooseHamilton.CandidateBalance
