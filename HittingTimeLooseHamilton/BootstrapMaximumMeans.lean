module

public import HittingTimeLooseHamilton.FrameRestrictedParametersUniform
public import HittingTimeLooseHamilton.BootstrapOriginalFrame

public section

noncomputable section
namespace LooseHamilton.BootstrapMaximumMeans
open Finset Filter AuxiliaryFrame

theorem eventually_original_mean_lower (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ {original : Finset (Finset (Fin N))},
      IsPairMatching original → (original.card:ℝ) ≤ (N:ℝ)^(1/10:ℝ) →
      ∀ (F : Frame r original), F.val.deleted = ∅ →
      ∀ H : SimpleHypergraph (Fin N), H ⊆ completeEdges (Fin N) r →
      (∀ v, (vertexDegree H v:ℝ) ≤ C*meanDegree (V:=Fin N) r H.card) →
      meanDegree (V:=Fin N) r H.card / 2 ≤ F.mu H := by
  filter_upwards [CandidateBalance.eventually_frame_loss_coefficient r 0 C] with N hsmall
  intro original hmatch hs F hd H hH hdeg
  have hn : F.n = N := by simp [Frame.n,Frame.active,Code.active,hd]
  have hmu : 0 ≤ meanDegree (V:=Fin N) r H.card := by unfold meanDegree; positivity
  have hloss := CandidateBalance.raw_edge_loss F H hH _ hdeg
  simp only [hd,empty_union,hmatch.ports_card,Nat.cast_mul,Nat.cast_ofNat] at hloss
  have hcoeff := mul_le_mul_of_nonneg_right hsmall.2 (Nat.cast_nonneg H.card : (0:ℝ)≤H.card)
  have hm : (H.card:ℝ) ≤ 2*F.m H := by
    have hp := mul_le_mul_of_nonneg_right hs (mul_nonneg hC hmu)
    have hL : (H.card:ℝ)-(F.m H:ℝ) ≤
        (4*(r:ℝ)+2*(N:ℝ)^(1/10:ℝ))*C*meanDegree (V:=Fin N) r H.card := by
      nlinarith [mul_nonneg (show 0≤4*(r:ℝ) by positivity) (mul_nonneg hC hmu)]
    simp only [meanDegree,Fintype.card_fin] at hL
    have he : (4*(r:ℝ)+2*(N:ℝ)^(1/10:ℝ))*C*((r:ℝ)*H.card/N) =
      (((4*(r:ℝ)+2*(N:ℝ)^(1/10:ℝ)+0)*C*r)/N)*H.card := by ring
    rw [he] at hL
    linarith
  unfold Frame.mu meanDegree
  rw [hn]
  simp only [Fintype.card_fin]
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg r : (0:ℝ)≤r)) hsmall.1.le
  have he : (r:ℝ)*(2*(F.m H:ℝ))/N = 2*((r:ℝ)*F.m H/N) := by ring
  rw [he] at hh
  linarith

/-- The negligible-source cutoff is below the final scale for every uniform host. -/
theorem tiny_source_le {N r : ℕ} (hr : 1 ≤ r) (hN : 1 ≤ N)
    (H : SimpleHypergraph (Fin N)) (hH : H ⊆ completeEdges (Fin N) r)
    (hmu : 0 < meanDegree (V:=Fin N) r H.card)
    (X : ℝ) (hX : 0 ≤ X) :
    X/(N:ℝ)^(2*r) ≤ (r:ℝ)*X/meanDegree (V:=Fin N) r H.card := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0:ℝ) < N := by linarith
  have hcard : (H.card:ℝ) ≤ (N:ℝ)^r := by
    have hh := (card_le_card hH).trans (by
      simpa only [completeEdges_card,Fintype.card_fin] using Nat.choose_le_pow N r)
    exact_mod_cast hh
  have hp : (N:ℝ)^r ≤ (N:ℝ)^(2*r) := pow_le_pow_right₀ hn (by omega)
  have hupper : meanDegree (V:=Fin N) r H.card ≤ (r:ℝ)*(N:ℝ)^(2*r) := by
    unfold meanDegree
    simp only [Fintype.card_fin]
    apply (div_le_iff₀ hnpos).mpr
    have hh := mul_le_mul_of_nonneg_left (hcard.trans hp) (Nat.cast_nonneg r : (0:ℝ)≤r)
    exact hh.trans (le_mul_of_one_le_right (by positivity) hn)
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(N:ℝ)^(2*r)) hmu).mpr
  have hh := mul_le_mul_of_nonneg_left hupper hX
  nlinarith

end LooseHamilton.BootstrapMaximumMeans
