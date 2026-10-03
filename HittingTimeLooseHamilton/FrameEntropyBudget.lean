module

public import HittingTimeLooseHamilton.FrameScales
public import HittingTimeLooseHamilton.EntropySubfamily

public section

/-! The frame budget is imposed on the actual cycle count. It is not inferred
from the bounded number of relative-direction constraints. The error uses the
original N, whereas k and mu are the frame parameters. -/
noncomputable section
namespace LooseHamilton.FrameEntropy
open FiniteEntropy

/-- The manuscript's benchmark at the frame mean degree. -/
@[expose] def benchmark (r k : ℕ) (mu : ℝ) : ℝ :=
  (k:ℝ)*Real.log (((r:ℝ)-1)*mu)-((r:ℝ)-1)*k

/-- Positivity makes the paper's logarithm and uniform cycle sampling meaningful. -/
@[expose] def budget {Ω : Type*} (r N k : ℕ) (mu B : ℝ) (F : Finset Ω) : Prop :=
  F.Nonempty ∧ benchmark r k mu-B*(N:ℝ)/Real.sqrt (FrameScales.L1 N)≤Real.log F.card

lemma budget_mono {Ω : Type*} {r N k : ℕ} {mu B B' : ℝ} {F : Finset Ω}
    (h : budget r N k mu B F) (hBB : B≤B') : budget r N k mu B' F := by
  refine ⟨h.1,?_⟩
  have hm := mul_le_mul_of_nonneg_right hBB (Nat.cast_nonneg N : (0:ℝ)≤N)
  have hd := div_le_div_of_nonneg_right hm (Real.sqrt_nonneg (FrameScales.L1 N))
  exact (sub_le_sub_left hd _).trans h.2

lemma budget_uniform_entropy {Ω : Type*} [Fintype Ω]
    {r N k : ℕ} {mu B : ℝ} {F : Finset Ω} (h : budget r N k mu B F) :
    benchmark r k mu-B*(N:ℝ)/Real.sqrt (FrameScales.L1 N)≤
      entropy (uniformSubfamily F h.1).mass := by
  rw [entropy_uniformSubfamily]
  exact h.2

lemma budget_iff_uniform_entropy {Ω : Type*} [Fintype Ω]
    (r N k : ℕ) (mu B : ℝ) (F : Finset Ω) (hF : F.Nonempty) :
    budget r N k mu B F ↔
      benchmark r k mu-B*(N:ℝ)/Real.sqrt (FrameScales.L1 N)≤
        entropy (uniformSubfamily F hF).mass := by
  rw [entropy_uniformSubfamily]
  exact ⟨fun h => h.2,fun h => ⟨hF,h⟩⟩

/-- The imposed frame budget implies the coarser log-count hypothesis of
Lemma 7.1, without assuming any equidistribution of marker directions. -/
lemma budget_coarse {Ω : Type*} {r N k : ℕ} {mu B : ℝ} {F : Finset Ω}
    (hr : 3≤r) (hmu : 0<mu) (hB : 0≤B) (hk : k≤N)
    (hscale : 1≤Real.sqrt (FrameScales.L1 N)) (h : budget r N k mu B F) :
    (k:ℝ)*Real.log mu-(((r:ℝ)-1)+B)*N≤Real.log F.card := by
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : 0<(r:ℝ)-1 := by linarith
  have hl : 0≤Real.log ((r:ℝ)-1) := Real.log_nonneg (by linarith)
  have he : benchmark r k mu =
      (k:ℝ)*Real.log mu+(k:ℝ)*Real.log ((r:ℝ)-1)-((r:ℝ)-1)*k := by
    unfold benchmark
    rw [Real.log_mul hr1.ne' hmu.ne']
    ring
  have herror : B*(N:ℝ)/Real.sqrt (FrameScales.L1 N)≤B*N :=
    div_le_self (by positivity) hscale
  have hkR : (k:ℝ)≤N := by exact_mod_cast hk
  have hc := mul_le_mul_of_nonneg_left hkR hr1.le
  have hh := h.2
  rw [he] at hh
  nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k) hl]
end LooseHamilton.FrameEntropy
