module

public import HittingTimeLooseHamilton.AuxiliaryFrameParameters
public import HittingTimeLooseHamilton.FrameEntropyBudget

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open FiniteEntropy
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- Equation (framebudget), for the actual possibly direction-restricted family.
The error denominator uses the original vertex count, not the reduced frame size. -/
@[expose] def entropyBudget (F : Frame r original) (host : Finset (Finset V)) (B : ℝ) : Prop :=
  FrameEntropy.budget r (Fintype.card V) F.k (F.mu host) B (F.cycleFamily host)

lemma entropyBudget_iff (F : Frame r original) (host : Finset (Finset V)) (B : ℝ) :
    F.entropyBudget host B ↔ 0<F.cycleCount host ∧
      (F.k:ℝ)*Real.log (((r:ℝ)-1)*F.mu host)-((r:ℝ)-1)*F.k-
        B*(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V)) ≤
        Real.log (F.cycleCount host) := by
  simp only [entropyBudget,FrameEntropy.budget,FrameEntropy.benchmark,cycleCount,Finset.card_pos]

lemma entropyBudget_uniform_entropy (F : Frame r original)
    (host : Finset (Finset V)) (B : ℝ) (h : F.entropyBudget host B) :
    (F.k:ℝ)*Real.log (((r:ℝ)-1)*F.mu host)-((r:ℝ)-1)*F.k-
      B*(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V)) ≤
      entropy (uniformSubfamily (F.cycleFamily host) h.1).mass :=
  FrameEntropy.budget_uniform_entropy h

lemma entropyBudget_mono (F : Frame r original) (host : Finset (Finset V))
    {B B' : ℝ} (h : F.entropyBudget host B) (hBB : B≤B') :
    F.entropyBudget host B' := FrameEntropy.budget_mono h hBB

/-- Equation (candidatebad), at precisely the Section 7 alpha scale. -/
@[expose] def candidateBadAtScale (F : Frame r original) (host : Finset (Finset V)) : Prop :=
  F.candidateBad host (FrameScales.alpha (Fintype.card V))

/-- A bad frame has an actual legal candidate witnessing the relative discrepancy. -/
lemma candidateBad_witness (F : Frame r original) (host : Finset (Finset V))
    {alpha : ℝ} (ha : 0≤alpha) (h : F.candidateBad host alpha) :
    ∃c∈F.candidates,
      |(F.completionCount host c:ℝ)/
        ((F.cycleCount host:ℝ)/(((r:ℝ)-1)^2*F.mu host))-1| > alpha := by
  classical
  have hp : 0<((F.candidates.filter (fun c =>
      |(F.completionCount host c:ℝ)/
        ((F.cycleCount host:ℝ)/(((r:ℝ)-1)^2*F.mu host))-1| > alpha)).card:ℝ) :=
    lt_of_le_of_lt (mul_nonneg ha (Nat.cast_nonneg _)) h
  obtain ⟨c,hc⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hp)
  exact ⟨c,(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩
lemma entropyBudget_mu_pos (F : Frame r original) (hr : 3≤r)
    (host : Finset (Finset V)) {B : ℝ} (h : F.entropyBudget host B) :
    0<F.mu host := by
  have hk := F.k_pos hr h.1
  have hn : 0<F.n := lt_of_lt_of_le hk F.k_le_n
  obtain ⟨E,hE⟩ := h.1
  have hm : 0<F.m host := by
    have he : E.card=F.k := F.edge_card hr hE
    exact lt_of_lt_of_le (he ▸ hk) (Finset.card_le_card (F.mem_cycleFamily host E |>.mp hE).1)
  unfold mu
  exact div_pos (mul_pos (by exact_mod_cast (show 0<r by omega))
    (Nat.cast_pos.mpr hm)) (Nat.cast_pos.mpr hn)

lemma candidate_normalizer_pos (F : Frame r original) (hr : 3≤r)
    (host : Finset (Finset V)) {B : ℝ} (h : F.entropyBudget host B) :
    0<(F.cycleCount host:ℝ)/(((r:ℝ)-1)^2*F.mu host) := by
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hX : 0<(F.cycleCount host:ℝ) := by
    exact_mod_cast ((F.entropyBudget_iff host B).mp h).1
  exact div_pos hX (mul_pos (sq_pos_of_pos (by linarith)) (F.entropyBudget_mu_pos hr host h))

lemma entropyBudget_coarse (F : Frame r original) (hr : 3≤r)
    (host : Finset (Finset V)) {B : ℝ} (hB : 0≤B)
    (hscale : 1≤Real.sqrt (FrameScales.L1 (Fintype.card V)))
    (h : F.entropyBudget host B) :
    (F.k:ℝ)*Real.log (F.mu host)-(((r:ℝ)-1)+B)*(Fintype.card V:ℝ)≤
      Real.log (F.cycleCount host) := by
  apply FrameEntropy.budget_coarse hr (F.entropyBudget_mu_pos hr host h) hB _ hscale h
  exact F.k_le_n.trans (by have := F.n_add_deleted; omega)
end LooseHamilton.AuxiliaryFrame.Frame
