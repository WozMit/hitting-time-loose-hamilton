module

public import HittingTimeLooseHamilton.FrameCoarseCompletionUniformParameters
public import HittingTimeLooseHamilton.FrameCompletionInstanceDegree
public import HittingTimeLooseHamilton.FrameCompletionInstanceOverlap
public import HittingTimeLooseHamilton.FrameRestrictedParametersUniform

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Filter FiniteEntropy

/-- Data are actual frame and completion families, with only inherited degree,
density and the imposed budget/cutoff as inputs. -/
structure CoarseCompletionInput (r : ℕ) (C B : ℝ) (N : ℕ) where
  original : Finset (Finset (Fin N))
  frame : Frame r original
  host : SimpleHypergraph (Fin N)
  candidate : Finset (Fin N) × Fin N × Fin N
  legal : frame.LegalCandidate candidate
  budget : frame.entropyBudget host B
  density : Real.log N/2≤frame.mu host
  degree : ∀v, (vertexDegree (frame.rawHost host) v:ℝ)≤C*frame.mu host
  cutoff : (frame.cycleCount host:ℝ)*(N:ℝ)^(-(100*(r:ℝ)))≤frame.completionCount host candidate

lemma CoarseCompletionInput.nonempty {r N : ℕ} {C B : ℝ}
    (d : CoarseCompletionInput r C B N) :
    (d.frame.completionFamily d.host d.candidate).Nonempty := by
  have hn := d.frame.n_add_deleted
  have hp := d.frame.n_pos
  apply d.frame.completion_nonempty_of_cutoff d.host d.candidate
    (by simp only [Fintype.card_fin] at hn ⊢; omega) d.budget.1
  simpa only [Fintype.card_fin] using d.cutoff

/-- The same coarse-overlap constant and threshold work for every legal
completion above the polynomial cutoff, preserving all prescribed directions. -/
theorem completion_uniformOverlap_eventually (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ d : CoarseCompletionInput r C B N,
        IndexedSurvival.uniformOverlap (d.frame.completionFamily d.host d.candidate) id ≤
          K*(N:ℝ)/Real.log (d.frame.mu d.host) := by
  classical
  obtain ⟨K,hK,hseq⟩ := BiasedRoleInstance.eventual_ordinary_overlap_bound r hr (2*C)
    (2*((r:ℝ)+B+100*r)) (by positivity) (by positivity)
  refine ⟨2*K,by positivity,?_⟩
  by_contra hbad
  have hbad' : ∀ i : ℕ, ∃ N : ℕ, i≤N ∧ ∃ d : CoarseCompletionInput r C B N,
      ¬ IndexedSurvival.uniformOverlap (d.frame.completionFamily d.host d.candidate) id ≤
        (2*K)*(N:ℝ)/Real.log (d.frame.mu d.host) := by
    simpa only [eventually_atTop,not_exists,not_forall,not_le,Classical.not_imp,
      exists_prop] using hbad
  choose N hN d hfail using hbad'
  have hNt : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
  let D := fun i => (d i).frame.completionEntropyInstance (d i).host (d i).candidate
    (d i).legal (d i).nonempty
  have hmu : Tendsto (fun i => (d i).frame.mu (d i).host) atTop atTop := by
    apply tendsto_atTop_mono (fun i => (d i).density)
    exact (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hNt)).atTop_div_const
      (by norm_num : (0:ℝ)<2)
  have hparams : ∀ᶠ i in atTop,
      (d i).frame.mu (d i).host/2≤(D i).μ ∧
      (D i).μ≤2*(d i).frame.mu (d i).host ∧
      (N i:ℝ)≤2*(D i).N ∧
      ((D i).k:ℝ)*Real.log (D i).μ-
        (2*((r:ℝ)+B+100*r))*(D i).N≤entropy (D i).cycleLaw.mass := by
    filter_upwards [hNt.eventually (completion_parameters_eventually r hr C B hC.le hB)]
      with i hi
    have hh := hi (d i).original (d i).frame (d i).host (d i).candidate
      (d i).legal (d i).budget (d i).density (d i).degree (d i).cutoff
    have hent := (d i).frame.completionEntropyInstance_entropy (d i).host
      (d i).candidate (d i).legal (d i).nonempty
    change entropy (D i).cycleLaw.mass = _ at hent
    rw [hent]
    simpa only [D,completionEntropyInstance_N,completionEntropyInstance_mu,
      completionEntropyInstance_k _ hr _ (d i).budget.1,
      completionEntropyInstance_entropy,completionMu] using hh
  have hμ : Tendsto (fun i => (D i).μ) atTop atTop := by
    apply tendsto_atTop_mono' _ (hparams.mono (fun i hi => hi.1))
    exact hmu.atTop_div_const (by norm_num : (0:ℝ)<2)
  have hdeg : ∀ᶠ i in atTop, ∀v, (vertexDegree (D i).host v:ℝ)≤(2*C)*(D i).μ := by
    filter_upwards [hparams] with i hi
    apply (d i).frame.completionEntropyInstance_degree_le
    intro v
    have hv : (vertexDegree ((d i).frame.completionRawHost (d i).host (d i).candidate) v:ℝ) ≤
        vertexDegree ((d i).frame.rawHost (d i).host) v := by
      exact_mod_cast ((d i).frame.completion_degree_le (d i).host (d i).candidate v)
    have hh := mul_le_mul_of_nonneg_left hi.1 hC.le
    have hd := (d i).degree v
    dsimp [D] at hi ⊢
    nlinarith
  have hbound := hseq D hμ hdeg (hparams.mono (fun i hi => hi.2.2.2))
  have hlog := Real.tendsto_log_atTop.comp hmu
  obtain ⟨i,hi,hp,hl,hm⟩ := (hbound.and (hparams.and
    ((hlog.eventually (eventually_ge_atTop 2)).and
      (hmu.eventually (eventually_gt_atTop 1))))).exists
  dsimp only [Function.comp_def] at hl
  apply hfail i
  rw [(d i).frame.uniformOverlap_eq_completionEntropyInstance
    (d i).host (d i).candidate (d i).legal (d i).nonempty]
  apply hi.trans
  have hlog2 : Real.log (2:ℝ)≤1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hmc : 0<(d i).frame.mu (d i).host/2 := by positivity
  have hlc := Real.log_le_log hmc hp.1
  rw [Real.log_div (by linarith : (d i).frame.mu (d i).host≠0) (by norm_num : (2:ℝ)≠0)] at hlc
  have hhalf : Real.log ((d i).frame.mu (d i).host)/2≤Real.log (D i).μ := by linarith
  have hlogpos : 0<Real.log (D i).μ := by linarith
  have hn := (d i).frame.n_add_deleted
  simp only [Fintype.card_fin] at hn
  have hnc : ((D i).N:ℝ)≤N i := by
    dsimp [D]
    exact_mod_cast ((d i).frame.completionActive_le (d i).candidate).trans
      (show (d i).frame.n≤N i by omega)
  apply (div_le_div_iff₀ hlogpos (Real.log_pos hm)).mpr
  have hnum := mul_le_mul_of_nonneg_left hnc hK.le
  nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0≤2*K*(N i:ℝ) by positivity),
    mul_le_mul_of_nonneg_right hnum (Real.log_pos hm).le]
end LooseHamilton.AuxiliaryFrame.Frame

namespace LooseHamilton.CandidateBalance
open Filter AuxiliaryFrame

/-- Actual inherited regularity and the imposed count conditions discharge
all coarse completion overlap hypotheses simultaneously. -/
theorem inherited_completion_overlap_eventually (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r≤h → M≤j → j≤(completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      ∀ a : Finset (Fin N) × Fin N × Fin N, f.LegalCandidate a →
        (f.cycleCount (extensionState ω.1 ω.2 j):ℝ)*(N:ℝ)^(-(100*(r:ℝ)))≤
          f.completionCount (extensionState ω.1 ω.2 j) a →
        IndexedSurvival.uniformOverlap (f.completionFamily (extensionState ω.1 ω.2 j) a) id ≤
          K*(N:ℝ)/Real.log (f.mu (extensionState ω.1 ω.2 j)) := by
  obtain ⟨K,hK,hbound⟩ := Frame.completion_uniformOverlap_eventually r hr C B hC hB
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,inherited_frame_density_eventually r 0 C hC.le] with N hb hd
  intro M ell original offset hadm f j h c L ω hh hMj hj hreg hbudget a ha hcut
  let H := extensionState ω.1 ω.2 j
  have hden := hd M ell original offset hadm f ∅ (by simp) j h c L ω hMj hj hreg
  let d : Frame.CoarseCompletionInput r C B N :=
    { original := original
      frame := f
      host := H
      candidate := a
      legal := ha
      budget := hbudget
      density := hden.2.2
      degree := f.rawHost_inherited_degree j h c C L ω hh hC.le hreg
      cutoff := hcut }
  exact hb d
end LooseHamilton.CandidateBalance
