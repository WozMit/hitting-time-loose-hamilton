module

public import HittingTimeLooseHamilton.CoreExposureData
public import HittingTimeLooseHamilton.CoreConditionalCounting
public import HittingTimeLooseHamilton.StoppingBias

public section

/-! Exact conditional law of the surviving core in the original process. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def coreExposureEvent (r m : ℕ) (B D : Finset V) (T : SimpleHypergraph V)
    (σ : EdgeOrder V r) : Prop :=
  tauOne σ = (m : WithTop ℕ) ∧ lowDegreeVertices (processState σ m) = B ∧
    traceOn D (processState σ m) = T

theorem coreExposureEvent_mem_fiber {r m : ℕ} {B D : Finset V}
    {T : SimpleHypergraph V} {σ : EdgeOrder V r}
    (h : coreExposureEvent r m B D T σ) :
    processState σ m ∈ coreExposureFiber r m B D T := by
  obtain ⟨ht,hB,hT⟩ := h
  obtain ⟨hb,hNI⟩ := firstTime_spec (completeEdges V r).card (processState σ) NoIsolated (t := m) ht
  exact (mem_coreExposureFiber _ _ _ _ _ _).mpr
    ⟨processState_subset σ m, by rw [processState_card,min_eq_left hb],hNI,hB,hT⟩

/-- A feasible stopped exposure automatically satisfies every exposed-data
consistency condition used to describe its completions. -/
theorem CoreExposure.of_fiber {r m : ℕ} {B D : Finset V} {T F : SimpleHypergraph V}
    (hBD : B ⊆ D) (hF : F ∈ coreExposureFiber r m B D T) : CoreExposure r m B D T := by
  obtain ⟨hu,hc,hNI,hB,hT⟩ := (mem_coreExposureFiber _ _ _ _ _ _).mp hF
  refine ⟨?_,?_,hBD,?_,?_⟩
  · rw [← hT]; exact (filter_subset _ _).trans hu
  · intro e he; rw [← hT] at he; exact ((mem_traceOn _ _ _).mp he).2
  · intro v hv
    have hd : vertexDegree T v = vertexDegree F v := by rw [← hT,trace_degree_deleted F hv]
    rw [hd]
    exact ⟨hNI v, by rw [← hB,mem_lowDegreeVertices]⟩
  · rw [← hT,← hc]; exact card_le_card (filter_subset _ _)

theorem coreExposureEvent_core_iff {r m : ℕ} {B D : Finset V}
    {T G : SimpleHypergraph V} (h : CoreExposure r m B D T)
    (hG : G ∈ coreCompletionFamily r m D T) (σ : EdgeOrder V r) :
    (coreExposureEvent r m B D T σ ∧ coreOutside D (processState σ m) = G) ↔
      stoppingStateEvent σ (T ∪ G) := by
  have hf := (mem_coreExposureFiber _ _ _ _ _ _).mp (union_mem_coreExposureFiber h hG)
  rw [stoppingStateEvent_iff_time_card, hf.2.1]
  constructor
  · rintro ⟨⟨ht,hB,hT⟩,hcore⟩
    exact ⟨ht, by rw [← hT,← hcore,trace_core_union]⟩
  · rintro ⟨ht,hstate⟩
    refine ⟨⟨ht,?_,?_⟩,?_⟩
    · rw [hstate]; exact hf.2.2.2.1
    · rw [hstate]; exact hf.2.2.2.2
    · rw [hstate]; exact coreOutside_union_core h hG

/-- Equal masses follow from Lemma 3.1: all critical edges are in the fixed
trace, so the stopping bias is constant over every feasible core. -/
theorem coreExposure_fibre_probability [Nonempty V] {r m : ℕ} {B D : Finset V}
    {T G : SimpleHypergraph V} (hbase : 1 ≤ lowerDegreeBase V)
    (h : CoreExposure r m B D T) (hG : G ∈ coreCompletionFamily r m D T) :
    (processLaw V r).event (fun σ => coreExposureEvent r m B D T σ ∧
      coreOutside D (processState σ m) = G) =
    ((exposedCriticalEdges B T).card : ℝ) /
      ((m : ℝ) * ((Fintype.card V).choose r).choose m) := by
  have hf := (mem_coreExposureFiber _ _ _ _ _ _).mp (union_mem_coreExposureFiber h hG)
  have hevent : (fun σ => coreExposureEvent r m B D T σ ∧
      coreOutside D (processState σ m) = G) =
      (fun σ => stoppingStateEvent σ (T ∪ G)) := by
    funext σ; exact propext (coreExposureEvent_core_iff h hG σ)
  rw [hevent,stopping_bias (T ∪ G) hf.1 hf.2.2.1]
  unfold stoppingBias
  rw [criticalEdges_eq_exposed hbase hf.2.2.2.1 h.low_subset,hf.2.2.2.2,hf.2.1]

/-- Proposition 3.3, the exact conditional uniformity assertion. This is a law
of the original stopped process conditioned only on m,B,D and its full trace.
Every member of Omega has probability the reciprocal of its cardinality. -/
theorem core_conditional_uniform [Nonempty V] {r m : ℕ} {B D : Finset V}
    {T : SimpleHypergraph V} (hbase : 1 ≤ lowerDegreeBase V)
    (h : CoreExposure r m B D T)
    (hE : 0 < (processLaw V r).event (coreExposureEvent r m B D T))
    (G : SimpleHypergraph V) (hG : G ∈ coreCompletionFamily r m D T) :
    ((processLaw V r).condition (coreExposureEvent r m B D T) hE).event
      (fun σ => coreOutside D (processState σ m) = G) =
        1 / ((coreCompletionFamily r m D T).card : ℝ) := by
  apply conditional_uniform_of_equal_fibres (processLaw V r) _ _ _ hE
    (fun σ hσ => coreOutside_mem_completion h.low_subset (coreExposureEvent_mem_fiber hσ))
    (((exposedCriticalEdges B T).card : ℝ) /
      ((m : ℝ) * ((Fintype.card V).choose r).choose m))
    (fun G hG => coreExposure_fibre_probability hbase h hG) G hG

/-- The earlier trace can be recovered from the full trace, so a deterministic
choice based on it places no additional restriction on an exposed fibre. -/
theorem exposure_deterministic_deletion {r m : ℕ} {B D : Finset V}
    {T : SimpleHypergraph V} (hBD : B ⊆ D)
    (chooseD : Finset V → SimpleHypergraph V → Finset V)
    (hchoice : chooseD B (traceOn B T) = D) (σ : EdgeOrder V r)
    (hσ : coreExposureEvent r m B D T σ) :
    chooseD B (traceOn B (processState σ m)) = D := by
  have ht := hσ.2.2
  rw [← traceOn_trace hBD (processState σ m),ht,hchoice]
end LooseHamilton
