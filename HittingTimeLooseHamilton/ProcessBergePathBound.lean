module

public import HittingTimeLooseHamilton.BergePathCounting
public import HittingTimeLooseHamilton.ProcessEndpointTail

public section

/-! A union bound over every possible short path in the actual upper process
state, whose two endpoints have low degree in the actual lower state. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fixed-length bad path event, before taking the union over lengths 1--4. -/
@[expose] def lowEndpointBergeEvent {r : ℕ} (a b t h : ℕ) (σ : EdgeOrder V r) : Prop :=
  ∃ u v : V, vertexDegree (processState σ a) u ≤ h ∧
    vertexDegree (processState σ a) v ≤ h ∧ Nonempty (BergePath (processState σ b) t u v)

theorem process_low_endpoint_berge_bound {r t : ℕ} (hr : 2 ≤ r) (ht : 1 ≤ t)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ (completeEdges V r).card)
    (hta : t ≤ a) (htN : t < (completeEdges V r).card)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (h : ℕ) :
    (processLaw V r).event (lowEndpointBergeEvent a b t h) ≤
      ((Fintype.card V : ℝ)^(t+1) * (((Fintype.card V-2).choose (r-2) : ℕ) : ℝ)^t) *
      (((b : ℝ) / (completeEdges V r).card)^t *
        Real.exp (-(((a-t : ℕ) : ℝ) / ((completeEdges V r).card-t : ℕ)) *
          ((2 * (Fintype.card V-2).choose (r-1) - t : ℕ) : ℝ) * (1-q)
          - ((2*h : ℕ) : ℝ) * Real.log q)) := by
  classical
  let E : BergeTemplate V r t → EdgeOrder V r → Prop := fun p σ =>
    p.edgeSet ⊆ processState σ b ∧ vertexDegree (processState σ a) p.initial ≤ h ∧
      vertexDegree (processState σ a) p.terminal ≤ h
  have hev : (processLaw V r).event (lowEndpointBergeEvent a b t h) ≤
      (processLaw V r).event (fun σ => ∃ p, E p σ) := by
    apply FiniteEntropy.Law.event_mono
    rintro σ ⟨u,v,hu,hv,⟨p⟩⟩
    refine ⟨p.toTemplate (processState_subset σ b), ?_⟩
    exact ⟨p.toTemplate_edgeSet _, by simpa using hu, by simpa using hv⟩
  apply hev.trans
  apply bergeTemplate_event_union_bound (processLaw V r) hr E (by positivity)
  intro p
  have hh := process_endpoint_low_degree_bound (V:=V) (by omega : 1 ≤ r)
    p.edgeSet p.edgeSet_subset_complete (p.endpoints_ne ht) a b hab hb
    (by simpa using hta) (by simpa using htN) q hq0 hq1 h
  simpa only [E, BergeTemplate.edgeSet_card] using hh

/-- Factoring the path-count bound separates the leading `n` from the fixed
power of its logarithmic path branching factor. -/
theorem process_low_endpoint_berge_bound_factored {r t : ℕ} (hr : 2 ≤ r) (ht : 1 ≤ t)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ (completeEdges V r).card)
    (hta : t ≤ a) (htN : t < (completeEdges V r).card)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (h : ℕ) :
    (processLaw V r).event (lowEndpointBergeEvent a b t h) ≤
      (Fintype.card V : ℝ) *
      (((Fintype.card V : ℝ) * (((Fintype.card V-2).choose (r-2) : ℕ) : ℝ) *
        ((b : ℝ) / (completeEdges V r).card))^t) *
        Real.exp (-(((a-t : ℕ) : ℝ) / ((completeEdges V r).card-t : ℕ)) *
          ((2 * (Fintype.card V-2).choose (r-1) - t : ℕ) : ℝ) * (1-q)
          - ((2*h : ℕ) : ℝ) * Real.log q) := by
  apply (process_low_endpoint_berge_bound hr ht a b hab hb hta htN q hq0 hq1 h).trans_eq
  rw [pow_succ, mul_pow, mul_pow]
  ring

/-- Every separatedness failure is a path of one of the four counted lengths. -/
theorem shortBerge_failure_iff {r : ℕ} (σ : EdgeOrder V r) (a b : ℕ) :
    (∃ u ∈ lowDegreeVertices (processState σ a),
      ∃ v ∈ lowDegreeVertices (processState σ a),
        u ≠ v ∧ shortBergeConnected (processState σ b) u v) ↔
      ∃ t : Fin 4, lowEndpointBergeEvent a b (t.val+1) (lowerDegreeBase V) σ := by
  constructor
  · rintro ⟨u,hu,v,hv,hne,t,ht,ht4,hp⟩
    refine ⟨⟨t-1, by omega⟩,u,v,(mem_lowDegreeVertices _ _).mp hu,
      (mem_lowDegreeVertices _ _).mp hv, ?_⟩
    simpa only [show t-1+1=t by omega] using hp
  · rintro ⟨t,u,v,hu,hv,⟨p⟩⟩
    refine ⟨u,(mem_lowDegreeVertices _ _).mpr hu,v,(mem_lowDegreeVertices _ _).mpr hv,
      ?_,t.val+1,by omega,by have := t.isLt; omega,⟨p⟩⟩
    have hh := (p.toTemplate (processState_subset σ b)).endpoints_ne (by omega)
    simpa using hh

/-- The entire short-path failure is bounded by the four fixed-length events. -/
theorem shortBerge_failure_probability_le_sum {r : ℕ} (a b : ℕ) :
    (processLaw V r).event (fun σ =>
      ∃ u ∈ lowDegreeVertices (processState σ a),
        ∃ v ∈ lowDegreeVertices (processState σ a),
          u ≠ v ∧ shortBergeConnected (processState σ b) u v) ≤
      ∑ t : Fin 4, (processLaw V r).event
        (lowEndpointBergeEvent a b (t.val+1) (lowerDegreeBase V)) := by
  have he : (fun σ : EdgeOrder V r =>
      ∃ u ∈ lowDegreeVertices (processState σ a),
        ∃ v ∈ lowDegreeVertices (processState σ a),
          u ≠ v ∧ shortBergeConnected (processState σ b) u v) =
      (fun σ => ∃ t : Fin 4, lowEndpointBergeEvent a b (t.val+1) (lowerDegreeBase V) σ) := by
    funext σ
    exact propext (shortBerge_failure_iff σ a b)
  rw [he]
  exact (processLaw V r).finite_union_bound _
end LooseHamilton
