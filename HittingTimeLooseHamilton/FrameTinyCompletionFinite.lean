module

public import HittingTimeLooseHamilton.CandidateNormalizationTransfer
public import HittingTimeLooseHamilton.AuxiliaryFrameParameters
public import HittingTimeLooseHamilton.CandidateLogSurvival

public section

/-! Polynomial host bounds and deterministic tiny-completion transfer. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- The actual raw-host density is bounded by the full simple hypergraph count. -/
theorem mu_polynomial_upper (F : Frame r original) (H : Finset (Finset V)) :
    F.mu H ≤ (r:ℝ)*(Fintype.card V:ℝ)^r := by
  have hsub : F.rawHost H ⊆ completeEdges V r := by
    intro e he
    exact (mem_completeEdges r e).mpr ((mem_allowedEdges r (originalPorts original) e).mp
      (F.rawHost_original_prohibition H he)).1
  have hc : F.m H ≤ (Fintype.card V)^r :=
    (card_le_card hsub).trans (by simpa only [completeEdges_card] using Nat.choose_le_pow (Fintype.card V) r)
  unfold mu
  by_cases hn : F.n = 0
  · simp [hn]; positivity
  · have hnR : (1:ℝ) ≤ F.n := by exact_mod_cast (show 1≤F.n by omega)
    calc
      _ ≤ (r:ℝ)*F.m H := div_le_self (by positivity) hnR
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (Nat.cast_nonneg _)

/-- Deleting host edges cannot create directed completions. -/
theorem completionCount_delete_le (F : Frame r original) (H T : Finset (Finset V))
    (c : Finset V × V × V) : F.completionCount (H\T) c ≤ F.completionCount H c := by
  apply card_le_card
  intro E hE
  obtain ⟨hsub,C,hdir,hstart⟩ := (F.mem_completionFamily (H\T) c E).mp hE
  apply (F.mem_completionFamily H c E).mpr
  refine ⟨?_,C,hdir,hstart⟩
  intro e he
  have hh := mem_filter.mp (hsub he)
  exact mem_filter.mpr ⟨mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp hh.1).1).1,
    (mem_inter.mp hh.1).2⟩,hh.2⟩

end LooseHamilton.AuxiliaryFrame.Frame
namespace LooseHamilton

/-- Tiny completions remain below one quarter of the destination benchmark.
Only monotonicity and the surviving main count are needed. -/
theorem tiny_completion_normalized_le (X Y X' Y' μ b z q : ℝ)
    (hX : 0<X) (hz : 0<z) (hY : Y≤X*q) (hmono : Y'≤Y)
    (hμ : 0≤μ) (hb : 0≤b) (hq : 8*b*μ*q≤z) (hmain : z*X/2≤X') :
    candidateNormalizedCount X' Y' μ b ≤ 1/4 := by
  have hXp : 0<X' := lt_of_lt_of_le (by positivity) hmain
  have hY' : Y'*(b*μ) ≤ X*q*(b*μ) :=
    mul_le_mul_of_nonneg_right (hmono.trans hY) (mul_nonneg hb hμ)
  have hprod := mul_le_mul_of_nonneg_left hq hX.le
  unfold candidateNormalizedCount
  rw [div_div_eq_mul_div]
  apply (div_le_iff₀ hXp).mpr
  nlinarith

/-- Normalized counts near one cannot lie below a sufficiently small cutoff. -/
theorem normal_completion_above_cutoff (X Y μ b q ε : ℝ)
    (hX : 0<X) (hμ : 0<μ) (hb : 0<b) (hε : ε≤1/2)
    (hnormal : |candidateNormalizedCount X Y μ b-1|≤ε)
    (hq : 2*b*μ*q≤1) : X*q≤Y := by
  have hl : 1/2≤candidateNormalizedCount X Y μ b := by
    have := (abs_le.mp hnormal).1
    linarith
  unfold candidateNormalizedCount at hl
  rw [div_div_eq_mul_div] at hl
  have hmul := (le_div_iff₀ hX).mp hl
  have hcut := mul_le_mul_of_nonneg_left hq hX.le
  have hpos := mul_pos hb hμ
  nlinarith

end LooseHamilton
