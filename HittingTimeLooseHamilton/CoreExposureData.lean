module

public import HittingTimeLooseHamilton.CoreTrace

public section

/-! Data exposed at the stopping time, and every compatible unexposed core.
The conditions below describe only exposed degrees and edges. They do not
assume a distribution on the unexposed core. -/
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Intrinsic consistency conditions of a feasible trace exposure. -/
structure CoreExposure (r m : ℕ) (B D : Finset V) (T : SimpleHypergraph V) : Prop where
  trace_uniform : T ⊆ completeEdges V r
  trace_meets : ∀ e ∈ T, ¬ Disjoint e D
  low_subset : B ⊆ D
  deleted_degree : ∀ v ∈ D, 1 ≤ vertexDegree T v ∧
    (vertexDegree T v ≤ lowerDegreeBase V ↔ v ∈ B)
  trace_card : T.card ≤ m

/-- Every host compatible with the exposed m,B,D,T. -/
@[expose] def coreExposureFiber (r m : ℕ) (B D : Finset V) (T : SimpleHypergraph V) :
    Finset (SimpleHypergraph V) := univ.filter (fun F =>
  F ⊆ completeEdges V r ∧ F.card = m ∧ NoIsolated F ∧
    lowDegreeVertices F = B ∧ traceOn D F = T)

/-- Ambient-vertex description of Omega(m-|T|,ell) on the surviving vertices. -/
@[expose] def coreCompletionFamily (r m : ℕ) (D : Finset V) (T : SimpleHypergraph V) :
    Finset (SimpleHypergraph V) := univ.filter (fun G =>
  G ⊆ completeEdges V r ∧ (∀ e ∈ G, Disjoint e D) ∧ G.card = m-T.card ∧
    ∀ v, v ∉ D → coreLowerBound D T v ≤ vertexDegree G v)

@[simp] theorem mem_coreExposureFiber (r m : ℕ) (B D : Finset V)
    (T F : SimpleHypergraph V) :
    F ∈ coreExposureFiber r m B D T ↔ F ⊆ completeEdges V r ∧ F.card = m ∧
      NoIsolated F ∧ lowDegreeVertices F = B ∧ traceOn D F = T := by simp [coreExposureFiber]

@[simp] theorem mem_coreCompletionFamily (r m : ℕ) (D : Finset V)
    (T G : SimpleHypergraph V) :
    G ∈ coreCompletionFamily r m D T ↔ G ⊆ completeEdges V r ∧
      (∀ e ∈ G, Disjoint e D) ∧ G.card = m-T.card ∧
        ∀ v, v ∉ D → coreLowerBound D T v ≤ vertexDegree G v := by simp [coreCompletionFamily]

theorem traceOn_union_core {r m : ℕ} {B D : Finset V} {T G : SimpleHypergraph V}
    (h : CoreExposure r m B D T) (hG : G ∈ coreCompletionFamily r m D T) :
    traceOn D (T ∪ G) = T := by
  have hg := (mem_coreCompletionFamily _ _ _ _ _).mp hG
  ext e
  simp only [mem_traceOn, mem_union]
  constructor
  · rintro ⟨he,hd⟩
    rcases he with he | he
    · exact he
    · exact False.elim (hd (hg.2.1 e he))
  · intro he; exact ⟨Or.inl he,h.trace_meets e he⟩

theorem coreOutside_union_core {r m : ℕ} {B D : Finset V} {T G : SimpleHypergraph V}
    (h : CoreExposure r m B D T) (hG : G ∈ coreCompletionFamily r m D T) :
    coreOutside D (T ∪ G) = G := by
  have hg := (mem_coreCompletionFamily _ _ _ _ _).mp hG
  ext e
  simp only [mem_coreOutside, mem_union]
  constructor
  · rintro ⟨he,hd⟩
    rcases he with he | he
    · exact False.elim (h.trace_meets e he hd)
    · exact he
  · intro he; exact ⟨Or.inr he,hg.2.1 e he⟩

/-- Adding any degree-feasible surviving core gives exactly the same exposure. -/
theorem union_mem_coreExposureFiber {r m : ℕ} {B D : Finset V} {T G : SimpleHypergraph V}
    (h : CoreExposure r m B D T) (hG : G ∈ coreCompletionFamily r m D T) :
    T ∪ G ∈ coreExposureFiber r m B D T := by
  obtain ⟨hGu,hGo,hGc,hGd⟩ := (mem_coreCompletionFamily _ _ _ _ _).mp hG
  have hdis : Disjoint T G := disjoint_left.mpr (fun e he hg => h.trace_meets e he (hGo e hg))
  have hdegree (v : V) : vertexDegree (T ∪ G) v = vertexDegree T v + vertexDegree G v :=
    vertexDegree_union hdis v
  have hzero (v : V) (hv : v ∈ D) : vertexDegree G v = 0 := by
    have hc := coreOutside_union_core h hG
    rw [← hc]
    exact coreOutside_degree_deleted _ hv
  have hhigh (v : V) (hv : v ∉ D) : lowerDegreeBase V + 1 ≤ vertexDegree (T ∪ G) v := by
    have hg := hGd v hv
    unfold coreLowerBound at hg
    rw [hdegree]
    omega
  apply (mem_coreExposureFiber _ _ _ _ _ _).mpr
  refine ⟨union_subset h.trace_uniform hGu, ?_, ?_, ?_, traceOn_union_core h hG⟩
  · rw [card_union_of_disjoint hdis,hGc]
    have := h.trace_card
    omega
  · intro v
    by_cases hv : v ∈ D
    · rw [hdegree,hzero v hv,add_zero]; exact (h.deleted_degree v hv).1
    · have := hhigh v hv; omega
  · ext v
    rw [mem_lowDegreeVertices]
    by_cases hv : v ∈ D
    · rw [hdegree,hzero v hv,add_zero]; exact (h.deleted_degree v hv).2
    · have hb : v ∉ B := fun hb => hv (h.low_subset hb)
      have := hhigh v hv
      simp only [hb, iff_false]
      omega

/-- Conversely the surviving part of every exposed host is a feasible core. -/
theorem coreOutside_mem_completion {r m : ℕ} {B D : Finset V} {T F : SimpleHypergraph V}
    (hBD : B ⊆ D) (hF : F ∈ coreExposureFiber r m B D T) :
    coreOutside D F ∈ coreCompletionFamily r m D T := by
  obtain ⟨hFu,hFc,hNI,hB,hT⟩ := (mem_coreExposureFiber _ _ _ _ _ _).mp hF
  apply (mem_coreCompletionFamily _ _ _ _ _).mpr
  refine ⟨(filter_subset _ _).trans hFu,?_,?_,?_⟩
  · intro e he; exact ((mem_coreOutside _ _ _).mp he).2
  · rw [coreOutside_card,hT,hFc]
  · intro v hv
    have hvB : v ∉ B := fun hb => hv (hBD hb)
    have hd : lowerDegreeBase V < vertexDegree F v := by
      by_contra hn
      exact hvB (hB ▸ (mem_lowDegreeVertices _ _).mpr (by omega))
    have hs := trace_degree_add_core D F v
    rw [hT] at hs
    unfold coreLowerBound
    omega
end LooseHamilton
