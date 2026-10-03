module

public import HittingTimeLooseHamilton.StoppingBiasDeterministic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! The exceptional low-degree set and short Berge paths from Lemma 3.2.
All predicates concern the actual process state and the original vertex set. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The manuscript's exceptional set: degrees at most floor(epsilon log n). -/
@[expose] def lowDegreeVertices (F : SimpleHypergraph V) : Finset V :=
  univ.filter (fun v => vertexDegree F v ≤ lowerDegreeBase V)

@[simp] theorem mem_lowDegreeVertices (F : SimpleHypergraph V) (v : V) :
    v ∈ lowDegreeVertices F ↔ vertexDegree F v ≤ lowerDegreeBase V := by
  simp [lowDegreeVertices]

/-- A Berge path uses distinct vertices and distinct host edges; each edge
contains the two consecutive path vertices. Its length counts edges. -/
structure BergePath (F : SimpleHypergraph V) (t : ℕ) (u v : V) where
  vertices : Fin (t + 1) → V
  vertices_injective : Function.Injective vertices
  edges : Fin t → Finset V
  edges_injective : Function.Injective edges
  edge_mem : ∀ i, edges i ∈ F
  left_mem : ∀ i, vertices i.castSucc ∈ edges i
  right_mem : ∀ i, vertices i.succ ∈ edges i
  initial : vertices 0 = u
  terminal : vertices (Fin.last t) = v

/-- Berge distance at most four, requiring a positive-length path. -/
@[expose] def shortBergeConnected (F : SimpleHypergraph V) (u v : V) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ t ≤ 4 ∧ Nonempty (BergePath F t u v)

/-- Exactly the four structural conclusions of Lemma 3.2, including a nonempty
exceptional set. The uniformity parameter is explicit for the later theorem. -/
structure exceptionalSetGood (r : ℕ) (C : ℝ) (F : SimpleHypergraph V) : Prop where
  low_nonempty : 1 ≤ (lowDegreeVertices F).card
  low_card_bound : ((lowDegreeVertices F).card : ℝ) ≤
    Real.rpow (Fintype.card V : ℝ) (1 / 12 : ℝ)
  max_degree : ∀ v : V, (vertexDegree F v : ℝ) ≤ C * Real.log (Fintype.card V : ℝ)
  pair_degree : ∀ u v : V, u ≠ v → pairDegree F u v ≤ 2
  separated : ∀ u ∈ lowDegreeVertices F, ∀ v ∈ lowDegreeVertices F,
    u ≠ v → ¬ shortBergeConnected F u v

/-- The event is evaluated at the finite original minimum-degree-one stopping
state, without conditioning or resampling the host. -/
@[expose] def stoppedExceptionalEvent {r : ℕ} (C : ℝ) (σ : EdgeOrder V r) : Prop :=
  ∃ t : ℕ, tauOne σ = (t : WithTop ℕ) ∧ exceptionalSetGood r C (processState σ t)

theorem vertexDegree_mono {F G : SimpleHypergraph V} (hFG : F ⊆ G) (v : V) :
    vertexDegree F v ≤ vertexDegree G v :=
  card_le_card (filter_subset_filter _ hFG)

theorem pairDegree_mono {F G : SimpleHypergraph V} (hFG : F ⊆ G) (u v : V) :
    pairDegree F u v ≤ pairDegree G u v :=
  card_le_card (filter_subset_filter _ hFG)

/-- Adding edges can only remove vertices from the low-degree set. -/
theorem lowDegreeVertices_antitone {F G : SimpleHypergraph V} (hFG : F ⊆ G) :
    lowDegreeVertices G ⊆ lowDegreeVertices F := by
  intro v hv
  exact (mem_lowDegreeVertices F v).mpr
    ((vertexDegree_mono hFG v).trans ((mem_lowDegreeVertices G v).mp hv))

/-- A Berge path survives the addition of host edges. -/
@[expose] def BergePath.mono {F G : SimpleHypergraph V} {t : ℕ} {u v : V}
    (p : BergePath F t u v) (hFG : F ⊆ G) : BergePath G t u v where
  vertices := p.vertices
  vertices_injective := p.vertices_injective
  edges := p.edges
  edges_injective := p.edges_injective
  edge_mem i := hFG (p.edge_mem i)
  left_mem := p.left_mem
  right_mem := p.right_mem
  initial := p.initial
  terminal := p.terminal

theorem shortBergeConnected_mono {F G : SimpleHypergraph V} (hFG : F ⊆ G)
    {u v : V} (h : shortBergeConnected F u v) : shortBergeConnected G u v := by
  obtain ⟨t,ht,ht',⟨p⟩⟩ := h
  exact ⟨t,ht,ht',⟨p.mono hFG⟩⟩

/-- A stopped graph always has a degree-one vertex: it lies on the final critical edge. -/
theorem degree_one_at_stop [Nonempty V] {r : ℕ} (σ : EdgeOrder V r) {t : ℕ}
    (ht : tauOne σ = (t : WithTop ℕ)) : ∃ v : V, vertexDegree (processState σ t) v = 1 := by
  have hNI := (firstTime_spec (completeEdges V r).card (processState σ) NoIsolated (t := t) ht).2
  have hevent : stoppingStateEvent σ (processState σ t) := ⟨t,ht,rfl⟩
  obtain ⟨_,e,he,_⟩ := (stoppingStateEvent_iff_last_critical σ (processState σ t)
    (processState_subset σ t) hNI).mp hevent
  obtain ⟨_,v,_,hv⟩ := (mem_criticalEdges _ _).mp he
  exact ⟨v,hv⟩

/-- A threshold of at least one ensures that the stopped exceptional set is nonempty. -/
theorem low_nonempty_at_stop [Nonempty V] {r : ℕ} (σ : EdgeOrder V r) {t : ℕ}
    (ht : tauOne σ = (t : WithTop ℕ)) (hbase : 1 ≤ lowerDegreeBase V) :
    1 ≤ (lowDegreeVertices (processState σ t)).card := by
  obtain ⟨v,hv⟩ := degree_one_at_stop σ ht
  apply card_pos.mpr
  exact ⟨v,(mem_lowDegreeVertices _ _).mpr (hv ▸ hbase)⟩

/-- Transfer the early/late process estimates to every intervening host.
Low vertices are controlled in the lower host, paths and degrees in the upper host. -/
theorem exceptionalSetGood_of_bracket {r : ℕ} {C : ℝ} {L F U : SimpleHypergraph V}
    (hLF : L ⊆ F) (hFU : F ⊆ U)
    (hne : 1 ≤ (lowDegreeVertices F).card)
    (hsmall : ((lowDegreeVertices L).card : ℝ) ≤
      Real.rpow (Fintype.card V : ℝ) (1 / 12 : ℝ))
    (hmax : ∀ v : V, (vertexDegree U v : ℝ) ≤ C * Real.log (Fintype.card V : ℝ))
    (hpair : ∀ u v : V, u ≠ v → pairDegree U u v ≤ 2)
    (hsep : ∀ u ∈ lowDegreeVertices L, ∀ v ∈ lowDegreeVertices L,
      u ≠ v → ¬ shortBergeConnected U u v) : exceptionalSetGood r C F := by
  refine ⟨hne,?_,?_,?_,?_⟩
  · exact (Nat.cast_le.mpr (card_le_card (lowDegreeVertices_antitone hLF))).trans hsmall
  · intro v
    exact (Nat.cast_le.mpr (vertexDegree_mono hFU v)).trans (hmax v)
  · intro u v huv
    exact (pairDegree_mono hFU u v).trans (hpair u v huv)
  · intro u hu v hv huv hpath
    exact hsep u (lowDegreeVertices_antitone hLF hu) v (lowDegreeVertices_antitone hLF hv)
      huv (shortBergeConnected_mono hFU hpath)

/-- The deterministic process-bracketing implication used by Lemma 3.2. -/
theorem stoppedExceptionalEvent_of_bracket [Nonempty V] {r : ℕ} {C : ℝ}
    (σ : EdgeOrder V r) {t lo hi : ℕ}
    (ht : tauOne σ = (t : WithTop ℕ)) (hlo : lo ≤ t) (hhi : t ≤ hi)
    (hbase : 1 ≤ lowerDegreeBase V)
    (hsmall : ((lowDegreeVertices (processState σ lo)).card : ℝ) ≤
      Real.rpow (Fintype.card V : ℝ) (1 / 12 : ℝ))
    (hmax : ∀ v : V, (vertexDegree (processState σ hi) v : ℝ) ≤
      C * Real.log (Fintype.card V : ℝ))
    (hpair : ∀ u v : V, u ≠ v → pairDegree (processState σ hi) u v ≤ 2)
    (hsep : ∀ u ∈ lowDegreeVertices (processState σ lo),
      ∀ v ∈ lowDegreeVertices (processState σ lo),
      u ≠ v → ¬ shortBergeConnected (processState σ hi) u v) :
    stoppedExceptionalEvent C σ := by
  exact ⟨t,ht,exceptionalSetGood_of_bracket (processState_mono σ hlo)
    (processState_mono σ hhi) (low_nonempty_at_stop σ ht hbase) hsmall hmax hpair hsep⟩
end LooseHamilton
