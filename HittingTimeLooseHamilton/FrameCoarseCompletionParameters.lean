module

public import HittingTimeLooseHamilton.FrameCoarseCompletionBudget
public import HittingTimeLooseHamilton.FrameCompletionInstance
public import HittingTimeLooseHamilton.FrameRestrictedParameters
public import HittingTimeLooseHamilton.CompletionMatching

public section

/-! Actual contracted vertex and host parameters for frame completions. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

@[expose] def completionMu (F : Frame r original) (H : Finset (Finset V))
    (c : Finset V × V × V) : ℝ :=
  (r:ℝ)*(F.completionRawHost H c).card/(F.completionActive c).card

lemma completionActive_card (F : Frame r original) {c : Finset V × V × V}
    (hc : F.LegalCandidate c) : (F.completionActive c).card = F.n-(r-2) := by
  rw [completionActive, card_sdiff_of_subset (subset_union_left.trans hc.2.1), hc.1.private_card]
  rfl

lemma completionActive_le (F : Frame r original) (c : Finset V × V × V) :
    (F.completionActive c).card≤F.n := card_le_card sdiff_subset

lemma completionRawHost_surviving (F : Frame r original) (H : Finset (Finset V))
    (c : Finset V × V × V) :
    F.completionRawHost H c = survivingHost (F.rawHost H) c.1 := by
  ext e
  simp only [completionRawHost, survivingHost, mem_filter]
  constructor
  · rintro ⟨he,hs⟩
    exact ⟨he, disjoint_left.mpr (fun x hx hp => (mem_sdiff.mp (hs hx)).2 hp)⟩
  · rintro ⟨he,hd⟩
    refine ⟨he, fun x hx => mem_sdiff.mpr ⟨(mem_filter.mp he).2 hx, ?_⟩⟩
    exact fun hp => disjoint_left.mp hd hx hp

lemma completion_degree_le (F : Frame r original) (H : Finset (Finset V))
    (c : Finset V × V × V) (v : V) :
    vertexDegree (F.completionRawHost H c) v≤vertexDegree (F.rawHost H) v :=
  vertexDegree_mono (filter_subset _ _) v

lemma completion_edge_loss (F : Frame r original) (H : Finset (Finset V))
    {c : Finset V × V × V} (hc : F.LegalCandidate c) (d : ℝ)
    (hd : ∀v, (vertexDegree (F.rawHost H) v:ℝ)≤d) :
    (F.m H:ℝ)-(F.completionRawHost H c).card≤(r-2:ℕ)*d := by
  have h := deleteVertices_edge_loss_real (F.rawHost H) c.1 d hd
  rw [deleteVertices_card, ←F.completionRawHost_surviving, hc.1.private_card] at h
  exact h

/-- Bounded private deletion retains at least half the raw edges once the
active vertex count exceeds twice the degree-loss constant. -/
lemma completion_retains_half (F : Frame r original) (H : Finset (Finset V))
    {c : Finset V × V × V} (hc : F.LegalCandidate c) (C : ℝ)
    (hn : 0<F.n) (hC : 0≤C)
    (hlarge : 2*(r-2:ℕ)*C*r≤(F.n:ℝ))
    (hd : ∀v, (vertexDegree (F.rawHost H) v:ℝ)≤C*F.mu H) :
    (F.m H:ℝ)≤2*(F.completionRawHost H c).card := by
  have hl := F.completion_edge_loss H hc (C*F.mu H) hd
  have hnR : (0:ℝ)<F.n := Nat.cast_pos.mpr hn
  have hm := mul_le_mul_of_nonneg_right hlarge (Nat.cast_nonneg (F.m H) : (0:ℝ)≤F.m H)
  unfold mu at hl
  have hl' : ((F.m H:ℝ)-(F.completionRawHost H c).card)*F.n≤
      (r-2:ℕ)*C*r*F.m H := by
    apply (le_div_iff₀ hnR).mp
    convert hl using 1 <;> ring
  nlinarith

/-- Contracted and raw means are uniformly comparable; no completion-density
assumption is added. -/
lemma completion_mu_comparison (F : Frame r original) (H : Finset (Finset V))
    {c : Finset V × V × V} (hc : F.LegalCandidate c)
    (hn : 0<F.n) (hlarge : 2*(r-2)≤F.n)
    (hretain : (F.m H:ℝ)≤2*(F.completionRawHost H c).card) :
    F.mu H/2≤F.completionMu H c ∧ F.completionMu H c≤2*F.mu H := by
  have hnc : 0<(F.completionActive c).card := by
    rw [F.completionActive_card hc]; omega
  have hcard := F.completionActive_le c
  have hcard2 : F.n≤2*(F.completionActive c).card := by
    rw [F.completionActive_card hc]; omega
  have hm : (F.completionRawHost H c).card≤F.m H := card_le_card (filter_subset _ _)
  have hnR : (0:ℝ)<F.n := Nat.cast_pos.mpr hn
  have hncR : (0:ℝ)<(F.completionActive c).card := Nat.cast_pos.mpr hnc
  have hcardR : ((F.completionActive c).card:ℝ)≤F.n := Nat.cast_le.mpr hcard
  have hcard2R : (F.n:ℝ)≤2*(F.completionActive c).card := by exact_mod_cast hcard2
  have hmR : ((F.completionRawHost H c).card:ℝ)≤F.m H := Nat.cast_le.mpr hm
  unfold mu completionMu
  constructor
  · apply (le_div_iff₀ hncR).mpr
    rw [div_div, div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos hnR (by norm_num : (0:ℝ)<2))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hretain (Nat.cast_nonneg r : (0:ℝ)≤r),
      mul_le_mul_of_nonneg_left hcardR (show (0:ℝ)≤(r:ℝ)*F.m H by positivity)]
  · apply (div_le_iff₀ hncR).mpr
    simp only [←mul_div_assoc]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmR (Nat.cast_nonneg r : (0:ℝ)≤r),
      mul_le_mul_of_nonneg_left hcard2R (show (0:ℝ)≤(r:ℝ)*F.m H by positivity)]
end LooseHamilton.AuxiliaryFrame.Frame
