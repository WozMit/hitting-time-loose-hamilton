module

public import HittingTimeLooseHamilton.FrameCoarseCompletionParameters
public import HittingTimeLooseHamilton.FrameEntropyInheritedRegularity
public import HittingTimeLooseHamilton.CoreRestrictionDegrees

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Filter Finset
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ} {original : Finset (Finset V)}

lemma rawHost_inherited_degree (F : Frame r original)
    (j h : ℕ) (c C L : ℝ) (ω : CandidateBalance.Outcome V r M ell)
    (hh : 4*r≤h) (hC : 0≤C)
    (hreg : CandidateBalance.InheritedRegularity original j h c C L ω) :
    ∀v, (vertexDegree (F.rawHost (extensionState ω.1 ω.2 j)) v:ℝ)≤
      C*F.mu (extensionState ω.1 ω.2 j) := by
  have hs := hreg.2.2.2 F.val.deleted (F.val.deleted_card_le.trans hh)
  change PathGraphUpperRegular r C L
    (fixedPortHost (inducedHost F.active (extensionState ω.1 ω.2 j))
      (restrictedPorts F.active (originalPorts original))) at hs
  rw [←F.restrict_rawHost_eq_fixedPortHost _ (extensionState_subset _ _ _)] at hs
  intro v
  by_cases hv : v∈F.active
  · have hd := hs.upper_degree (⟨v,hv⟩:↥F.active)
    rw [vertexDegree_restrictEdges F.active (F.rawHost (extensionState ω.1 ω.2 j))
      (fun e he => (mem_filter.mp he).2) ⟨v,hv⟩] at hd
    have hm : meanDegree (V:=↥F.active) r
        (restrictEdges F.active (F.rawHost (extensionState ω.1 ω.2 j))).card =
        F.mu (extensionState ω.1 ω.2 j) := by
      rw [restrictEdges_card_of_supported F.active (F.rawHost (extensionState ω.1 ω.2 j))
        (fun e he => (mem_filter.mp he).2)]
      simp [meanDegree, mu, m, n]
    rwa [hm] at hd
  · have hd : vertexDegree (F.rawHost (extensionState ω.1 ω.2 j)) v=0 := by
      unfold vertexDegree
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      exact hv ((mem_filter.mp (mem_filter.mp he).1).2 (mem_filter.mp he).2)
    rw [hd, Nat.cast_zero]
    apply mul_nonneg hC
    unfold mu
    positivity

/-- All bounded-contraction estimates share one threshold before the frame,
host and candidate are selected. -/
theorem completion_parameters_eventually (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0≤C) (hB : 0≤B) :
    ∀ᶠ N : ℕ in atTop, ∀ original : Finset (Finset (Fin N)),
      ∀ F : Frame r original, ∀ H : SimpleHypergraph (Fin N),
      ∀ c : Finset (Fin N) × Fin N × Fin N,
      F.LegalCandidate c → F.entropyBudget H B →
      Real.log N/2≤F.mu H →
      (∀v, (vertexDegree (F.rawHost H) v:ℝ)≤C*F.mu H) →
      (F.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ)))≤F.completionCount H c →
      F.mu H/2≤F.completionMu H c ∧ F.completionMu H c≤2*F.mu H ∧
      (N:ℝ)≤2*(F.completionActive c).card ∧
      ((F.k-1:ℕ):ℝ)*Real.log (F.completionMu H c)-
        (2*((r:ℝ)+B+100*r))*(F.completionActive c).card ≤
          Real.log (F.completionCount H c) := by
  have hsize : ∀ᶠ N : ℕ in atTop,
      4*(r-2:ℕ)*C*r + 8*r ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (16*r+4),hsize,
    FrameScales.L1_tendsto.eventually (eventually_ge_atTop 8)]
    with N hN hlarge hlog original F H c hc hb hmu hd hY
  have hn := F.n_add_deleted
  have hdel := F.val.deleted_card_le
  simp only [Fintype.card_fin] at hn
  have hnN : N≤2*F.n := by omega
  have hnNR : (N:ℝ)≤2*F.n := by exact_mod_cast hnN
  have hlarge' : 2*(r-2:ℕ)*C*r≤(F.n:ℝ) := by nlinarith
  have hretain := F.completion_retains_half H hc C F.n_pos hC hlarge' hd
  have hm := F.completion_mu_comparison H hc F.n_pos (by omega) hretain
  have hmu1 : 1≤F.mu H := by change 8≤Real.log N at hlog; linarith
  have hmc : 0<F.completionMu H c := by linarith [hm.1]
  have hNnc : (N:ℝ)≤2*(F.completionActive c).card := by
    rw [F.completionActive_card hc]
    exact_mod_cast (show N≤2*(F.n-(r-2)) by omega)
  have hscale : 1≤Real.sqrt (FrameScales.L1 N) := by
    have hh : 1≤FrameScales.L1 N := le_trans (by norm_num) hlog
    simpa using Real.sqrt_le_sqrt hh
  have hcoarse := F.completion_coarse_log_contracted hr H c hB
    (by simpa using (show 0<N by omega)) (by simpa using hscale) hb hmu1 hmc hm.2
    (by simpa using hY)
  have hcoeff : 0≤(r:ℝ)+B+100*r := by positivity
  have hmul := mul_le_mul_of_nonneg_left hNnc hcoeff
  simp only [Fintype.card_fin] at hcoarse
  exact ⟨hm.1,hm.2,hNnc,by nlinarith⟩
end LooseHamilton.AuxiliaryFrame.Frame
