module

public import HittingTimeLooseHamilton.CoreExposureProbability
public import HittingTimeLooseHamilton.CoreCompletionEquiv

public section

/-! Conditional uniformity stated directly on Omega(M,ell) over W=[n]\D. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The core on W is uniformly distributed over the exact existing terminal
model. The event is an equality of induced hypergraphs on the surviving subtype. -/
theorem core_terminal_uniform {r m : ℕ} {B D : Finset V} {T : SimpleHypergraph V}
    (hbase : 1 ≤ lowerDegreeBase V) (h : CoreExposure r m B D T)
    (hE : 0 < (processLaw V r).event (coreExposureEvent r m B D T))
    (G : TerminalState ↥(univ \ D) r (m-T.card) (fun w => coreLowerBound D T w.val)) :
    ((processLaw V r).condition (coreExposureEvent r m B D T) hE).event
      (fun σ => restrictEdges (univ \ D) (coreOutside D (processState σ m)) = G.val) =
      1 / (Fintype.card (TerminalState ↥(univ \ D) r (m-T.card)
        (fun w => coreLowerBound D T w.val)) : ℝ) := by
  let A := (coreCompletionEquiv r m D T).symm G
  have heq (σ : EdgeOrder V r) :
      (restrictEdges (univ \ D) (coreOutside D (processState σ m)) = G.val) ↔
      coreOutside D (processState σ m) = A.val := by
    have hs : ∀ e ∈ coreOutside D (processState σ m), e ⊆ univ \ D := by
      intro e he v hv
      exact mem_sdiff.mpr ⟨mem_univ _,fun hd =>
        disjoint_left.mp ((mem_coreOutside _ _ _).mp he).2 hv hd⟩
    constructor
    · intro hh
      have hh' := congrArg (fun E => E.image (liftEdge (univ \ D))) hh
      change coreOutside D (processState σ m) = G.val.image (liftEdge (univ \ D))
      simpa only [liftEdges_restrictEdges _ _ hs] using hh'
    · intro hh
      rw [hh]
      exact restrictEdges_liftEdges _ _
  have hevents : (fun σ : EdgeOrder V r => restrictEdges (univ \ D) (coreOutside D (processState σ m)) = G.val) =
      (fun σ => coreOutside D (processState σ m) = A.val) := by
    funext σ; exact propext (heq σ)
  rw [hevents,core_conditional_uniform hbase h hE A.val A.property]
  have hc := Fintype.card_congr (coreCompletionEquiv r m D T)
  rw [Fintype.card_coe] at hc
  rw [hc]
omit [Nonempty V] in
/-- The restricted surviving edge family is exactly the existing induced host. -/
theorem restricted_core_eq_inducedHost (D : Finset V) (F : SimpleHypergraph V) :
    restrictEdges (univ \ D) (coreOutside D F) = inducedHost (univ \ D) F := by
  have hs : ∀ e ∈ coreOutside D F, e ⊆ univ \ D := by
    intro e he v hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun hd =>
      disjoint_left.mp ((mem_coreOutside _ _ _).mp he).2 hv hd⟩
  ext e
  rw [mem_inducedHost,ambientEdge_eq_liftEdge]
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    rw [lift_restrictEdge _ _ (hs f hf)]
    exact ((mem_coreOutside _ _ _).mp hf).1
  · intro he
    apply mem_image.mpr
    refine ⟨liftEdge (univ \ D) e,(mem_coreOutside _ _ _).mpr ⟨he,?_⟩,restrict_liftEdge _ _⟩
    apply disjoint_left.mpr
    intro v hv hd
    exact (mem_sdiff.mp (liftEdge_subset _ _ hv)).2 hd

/-- Feasibility means positive probability of the stated exposure; exposed-data
consistency is a consequence, not an additional hypothesis on completions. -/
theorem core_exposure_of_positive {r m : ℕ} {B D : Finset V} {T : SimpleHypergraph V}
    (hBD : B ⊆ D)
    (hE : 0 < (processLaw V r).event (coreExposureEvent r m B D T)) :
    CoreExposure r m B D T := by
  classical
  have hex : ∃ σ, coreExposureEvent r m B D T σ := by
    by_contra hn
    push_neg at hn
    have hz := (processLaw V r).event_eq_zero_of_false hn
    linarith
  obtain ⟨σ,hσ⟩ := hex
  exact CoreExposure.of_fiber hBD (coreExposureEvent_mem_fiber hσ)

/-- The paper's conditional law for any feasible exposure containing the low set. -/
theorem core_terminal_uniform_of_feasible {r m : ℕ} {B D : Finset V}
    {T : SimpleHypergraph V} (hbase : 1 ≤ lowerDegreeBase V) (hBD : B ⊆ D)
    (hE : 0 < (processLaw V r).event (coreExposureEvent r m B D T))
    (G : TerminalState ↥(univ \ D) r (m-T.card) (fun w => coreLowerBound D T w.val)) :
    ((processLaw V r).condition (coreExposureEvent r m B D T) hE).event
      (fun σ => restrictEdges (univ \ D) (coreOutside D (processState σ m)) = G.val) =
      1 / (Fintype.card (TerminalState ↥(univ \ D) r (m-T.card)
        (fun w => coreLowerBound D T w.val)) : ℝ) :=
  core_terminal_uniform hbase (core_exposure_of_positive hBD hE) hE G
/-- The conditional law phrased literally as the induced graph on W. -/
theorem core_induced_uniform_of_feasible {r m : ℕ} {B D : Finset V}
    {T : SimpleHypergraph V} (hbase : 1 ≤ lowerDegreeBase V) (hBD : B ⊆ D)
    (hE : 0 < (processLaw V r).event (coreExposureEvent r m B D T))
    (G : TerminalState ↥(univ \ D) r (m-T.card) (fun w => coreLowerBound D T w.val)) :
    ((processLaw V r).condition (coreExposureEvent r m B D T) hE).event
      (fun σ => inducedHost (univ \ D) (processState σ m) = G.val) =
      1 / (Fintype.card (TerminalState ↥(univ \ D) r (m-T.card)
        (fun w => coreLowerBound D T w.val)) : ℝ) := by
  simpa only [restricted_core_eq_inducedHost] using
    core_terminal_uniform_of_feasible hbase hBD hE G
end LooseHamilton
