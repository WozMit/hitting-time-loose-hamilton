module

public import HittingTimeLooseHamilton.FrameSurvivalAsymptotic
public import HittingTimeLooseHamilton.FrameScales

public section

/-! Uniform batch feasibility and a positive exponent-scale lower bound.
The threshold precedes every host and frame parameter choice. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Filter FrameSurvival

/-- A floored batch retains at least half the lower estimate for its real size. -/
lemma batch_lower_of_density (N m k : ℕ) (ν R L : ℝ)
    (hN : 0 < (N:ℝ)) (hk : 0 < (k:ℝ)) (hR : 0 < R)
    (hkN : (k:ℝ) ≤ N) (hν : 0 ≤ ν) (hL : 0 ≤ L)
    (hdensity : (N:ℝ)*L/(8*R) ≤ m) (hlarge : 2 ≤ ν*L/(8*R)) :
    ν*L/(16*R) ≤ (batchSize m k ν:ℝ) := by
  have hden : 0 < 8*R := by positivity
  have hm : (N:ℝ)*L ≤ (m:ℝ)*(8*R) := (div_le_iff₀ hden).mp hdensity
  have hn : (k:ℝ)*L ≤ (N:ℝ)*L := mul_le_mul_of_nonneg_right hkN hL
  have hx : ν*L/(8*R) ≤ ν*(m:ℝ)/k := by
    apply (div_le_div_iff₀ hden hk).2
    nlinarith [mul_le_mul_of_nonneg_left (hn.trans hm) hν]
  have hf := Nat.lt_floor_add_one (ν*(m:ℝ)/k)
  change ν*(m:ℝ)/k < (batchSize m k ν:ℝ)+1 at hf
  have he : ν*L/(16*R) = (ν*L/(8*R))/2 := by ring
  rw [he]
  linarith

/-- Purely scalar part of item 30.8. Once m0 >= N*log(N)/(8*r) and
N <= 8(r-1)k <= 8(r-1)N are proved, both quarter bounds and the required
lower exponent scale follow for the ACTUAL floored batch. -/
theorem eventually_frame_batch_parameters (r : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ N : ℕ in atTop, ∀ m k : ℕ,
      (N:ℝ) ≤ (8*((r:ℝ)-1))*k → (k:ℝ) ≤ N →
      (N:ℝ)*FrameScales.L1 N/(8*(r:ℝ)) ≤ m →
      0 < m ∧ 1 ≤ k ∧
      1 ≤ batchSize m k (FrameScales.nu N) ∧
      4*k ≤ m ∧ 4*batchSize m k (FrameScales.nu N) ≤ m ∧
      FrameScales.nu N*FrameScales.L1 N/(16*(r:ℝ)) ≤
        (batchSize m k (FrameScales.nu N):ℝ) := by
  have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr
  have ha : 0 < 8*((r:ℝ)-1) := by linarith
  have hsmall := FrameScales.nu_div_vertices_tendsto_zero.eventually
    (gt_mem_nhds (show (0:ℝ) < 1/(4*(8*((r:ℝ)-1))) by positivity))
  filter_upwards [eventually_gt_atTop (0:ℕ),
    FrameScales.nu_tendsto.eventually (eventually_ge_atTop (1:ℝ)),
    FrameScales.L1_tendsto.eventually (eventually_ge_atTop (32*(r:ℝ))), hsmall]
    with N hN hnu hlog hs
  intro m k hNk hkN hdensity
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hrpos : (0:ℝ) < r := by linarith
  have hden : 0 < 8*(r:ℝ) := by positivity
  have hL : 0 ≤ FrameScales.L1 N := by linarith
  have hm4 : 4*(N:ℝ) ≤ m := by
    have hd := (div_le_iff₀ hden).mp hdensity
    have ht := mul_le_mul_of_nonneg_left hlog hNR.le
    nlinarith
  have hdense : (4:ℝ) ≤ (m:ℝ)/N := (le_div_iff₀ hNR).2 (by linarith)
  have hf := batch_feasible_finite N m k (FrameScales.nu N) (8*((r:ℝ)-1)) 1 1
    hNR ha (by norm_num) (by norm_num) hNk (by simpa using hkN) hnu hs.le
    (by simpa using hdense)
  refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,?_⟩
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply batch_lower_of_density N m k (FrameScales.nu N) r (FrameScales.L1 N)
    hNR hkpos hrpos hkN (by linarith) hL hdensity
  apply (le_div_iff₀ hden).2
  nlinarith [mul_le_mul_of_nonneg_right hnu hL]

end LooseHamilton.CandidateBalance
