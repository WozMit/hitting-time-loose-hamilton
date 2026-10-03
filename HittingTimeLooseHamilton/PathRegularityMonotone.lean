module

public import HittingTimeLooseHamilton.PathRegularityModels

public section

noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma PathPartitionRegular.mono {r : ℕ} {C D L L' : ℝ} {F : SimpleHypergraph V}
    (h : PathPartitionRegular r C L F) (hCD : C ≤ D) (hL : L' ≤ L) :
    PathPartitionRegular r D L' F := by
  intro A hA
  have hpow : 0 ≤ (Fintype.card V:ℝ)^(1/10:ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  apply (h A (hA.trans (mul_le_mul_of_nonneg_right hL hpow))).trans
  have hμ : 0 ≤ meanDegree (V:=V) r F.card := by unfold meanDegree; positivity
  have hl : 0 ≤ (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ) :=
    Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  gcongr

lemma PathGraphUpperRegular.mono {r : ℕ} {C D L L' : ℝ} {F : SimpleHypergraph V}
    (h : PathGraphUpperRegular r C L F) (hCD : C ≤ D) (hL : L' ≤ L) :
    PathGraphUpperRegular r D L' F := by
  have hμ : 0 ≤ meanDegree (V:=V) r F.card := by unfold meanDegree; positivity
  have hl : 0 ≤ (Real.log (Fintype.card V:ℝ))^(-1/4:ℝ) :=
    Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  refine ⟨fun v => (h.upper_degree v).trans (mul_le_mul_of_nonneg_right hCD hμ),?_,
    h.partitions.mono hCD hL⟩
  intro u v huv
  exact (h.codegree u v huv).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hμ) hl)

lemma PathGraphRegular.mono {r : ℕ} {c c' C D L L' : ℝ} {F : SimpleHypergraph V}
    (h : PathGraphRegular r c C L F) (hc : c' ≤ c) (hCD : C ≤ D) (hL : L' ≤ L) :
    PathGraphRegular r c' D L' F := by
  have hμ : 0 ≤ meanDegree (V:=V) r F.card := by unfold meanDegree; positivity
  exact ⟨h.toPathGraphUpperRegular.mono hCD hL,
    fun v => (mul_le_mul_of_nonneg_right hc hμ).trans (h.lower_degree v)⟩
end LooseHamilton
