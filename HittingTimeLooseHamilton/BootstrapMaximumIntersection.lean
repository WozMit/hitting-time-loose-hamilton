module

public import HittingTimeLooseHamilton.FrameCandidateCountsUniform
public import HittingTimeLooseHamilton.ExceptionalWindowScales

public section

/-! Uniform intersection with balanced original-frame labels. -/
noncomputable section
namespace LooseHamilton.BootstrapMaximumIntersection
open Finset Filter AuxiliaryFrame

theorem eventually_intersection (r : ℕ) (hr : 2 ≤ r)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ {original : Finset (Finset (Fin N))},
      IsPairMatching original → (original.card:ℝ) ≤ (N:ℝ)^(1/10:ℝ) →
      ∀ (F : Frame r original), F.val.deleted = ∅ →
      (r:ℝ)*ε N*(N:ℝ)^r + 2*FrameScales.alpha N*(F.candidates.card:ℝ) <
        F.candidates.card := by
  obtain ⟨N₀,hN₀⟩ := Frame.uniform_candidate_counts r hr
  have hf : (0:ℝ) < r.factorial := Nat.cast_pos.mpr (Nat.factorial_pos r)
  have hcut : (0:ℝ) < 1/(8*(r.factorial:ℝ)) := by positivity
  have he := (hε.const_mul (r:ℝ)).eventually (gt_mem_nhds (show (r:ℝ)*0 < 1/(8*(r.factorial:ℝ)) by simpa only [mul_zero] using hcut))
  have hchoose := (normalized_nat_choose_tendsto r).eventually
    (lt_mem_nhds (show (1:ℝ)/(2*r.factorial) < 1/r.factorial by
      apply (div_lt_div_iff₀ (by positivity) hf).mpr
      linarith))
  filter_upwards [he,hchoose,eventually_ge_atTop (max 1 N₀),
    FrameScales.alpha_tendsto_zero.eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/8))] with N he hchoose hN ha
  intro original hM hs F hd
  have hn : F.n = N := by simp [Frame.n,Frame.active,Code.active,hd]
  have hcounts := (hN₀ (Fin N) original (by simpa using (show N₀≤N by omega))
    hM (by simpa using hs) F).1
  rw [hn] at hcounts
  have hprod : (1:ℝ) ≤ (r*(r-1):ℕ) := by exact_mod_cast (show 1≤r*(r-1) by have := Nat.mul_pos (show 0<r by omega) (show 0<r-1 by omega); omega)
  have hC : (N.choose r:ℝ)/2 ≤ F.candidates.card := by
    nlinarith [mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg (N.choose r) : (0:ℝ)≤_)]
  have hnpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hp : (0:ℝ)<(N:ℝ)^r := by positivity
  have hc : (N:ℝ)^r/(2*r.factorial) < (N.choose r:ℝ) := by
    have hh := (lt_div_iff₀ hp).mp hchoose
    convert hh using 1 <;> ring
  have hc' : (N:ℝ)^r/(4*r.factorial) < (F.candidates.card:ℝ) := by
    have heq : (N:ℝ)^r/(2*r.factorial) = 2*((N:ℝ)^r/(4*r.factorial)) := by ring
    rw [heq] at hc
    linarith
  have hdelta : (r:ℝ)*ε N*(N:ℝ)^r < (N:ℝ)^r/(8*r.factorial) := by
    convert mul_lt_mul_of_pos_right he hp using 1 <;> ring
  have hcp : (0:ℝ)<F.candidates.card := (by positivity : (0:ℝ)<(N:ℝ)^r/(4*r.factorial)).trans hc'
  have ha' := mul_lt_mul_of_pos_right ha hcp
  have heq : (N:ℝ)^r/(4*r.factorial) = 2*((N:ℝ)^r/(8*r.factorial)) := by ring
  rw [heq] at hc'
  nlinarith

/-- A common ambient exception fraction, independent of source and base. -/
@[expose] def error (r N : ℕ) : ℝ :=
  (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (FrameScales.alpha N) +
    Real.sqrt 2*(FrameScales.alpha N)^(1/4:ℝ) +
      ((r-2:ℕ)+2*(N:ℝ)^(1/10:ℝ)+2)/(N:ℝ)

theorem error_nonneg (r N : ℕ) (hα : 0 ≤ FrameScales.alpha N) : 0 ≤ error r N := by
  unfold error
  positivity

theorem error_tendsto_zero (r : ℕ) : Tendsto (error r) atTop (nhds 0) := by
  have hs := FrameScales.alpha_tendsto_zero.sqrt
  have hp := FrameScales.alpha_tendsto_zero.rpow_const (p := (1/4:ℝ))
    (Or.inr (by norm_num))
  have hl := CandidateBalance.frame_loss_ratio_tendsto_zero 2 ((r-2:ℕ)+2)
  have hh := ((hs.const_mul (Real.sqrt (r-2:ℕ)+1)).add
    (hp.const_mul (Real.sqrt 2))).add hl
  convert hh using 1
  · ext N
    unfold error
    congr 1
    ring
  · simp

theorem error_dominates {r N s : ℕ}
    (hs : (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ)) :
    (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (FrameScales.alpha N) +
      Real.sqrt 2*(FrameScales.alpha N)^(1/4:ℝ) +
      ((r-2:ℕ)+2*(s:ℝ)+2)/(N:ℝ) ≤ error r N := by
  unfold error
  gcongr

theorem step_bound_le {r N s p : ℕ} (hN : 0 < N)
    (hs : (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ)) (hp : p ≤ 2*s) :
    (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (FrameScales.alpha N)*(N:ℝ) +
      Real.sqrt 2*(FrameScales.alpha N)^(1/4:ℝ)*(N:ℝ) + (r-2:ℕ)+p+1 ≤
        error r N*(N:ℝ) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hp' : (p:ℝ) ≤ 2*(s:ℝ) := by exact_mod_cast hp
  unfold error
  simp only [add_mul,div_mul_cancel₀ _ hn]
  nlinarith

theorem eventually_error_intersection (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ N : ℕ in atTop, ∀ {original : Finset (Finset (Fin N))},
      IsPairMatching original → (original.card:ℝ) ≤ (N:ℝ)^(1/10:ℝ) →
      ∀ (F : Frame r original), F.val.deleted = ∅ →
      (r:ℝ)*error r N*(N:ℝ)^r + 2*FrameScales.alpha N*(F.candidates.card:ℝ) <
        F.candidates.card :=
  eventually_intersection r hr (error r) (error_tendsto_zero r)

end LooseHamilton.BootstrapMaximumIntersection
