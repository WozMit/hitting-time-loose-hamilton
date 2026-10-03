module

public import HittingTimeLooseHamilton.UniformPrefixProbability
public import HittingTimeLooseHamilton.HypergraphIncidenceCounts
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

/-! Finite upper tails obtained by counting prescribed subsets of incident edges. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- At least `k` selected edges in a support force some prescribed k-subset to appear. -/
theorem process_support_upper_tail (m k : ℕ) (hm : m ≤ (completeEdges V r).card)
    (hk : k ≤ m) (S : SimpleHypergraph V) (hS : S ⊆ completeEdges V r) :
    (processLaw V r).event (fun σ => k ≤ (S ∩ processState σ m).card) ≤
      (S.card.choose k : ℝ) *
        (((Fintype.card V).choose r - k).choose (m-k) : ℝ) /
          (((Fintype.card V).choose r).choose m : ℝ) := by
  classical
  let E : ↥(S.powersetCard k) → EdgeOrder V r → Prop :=
    fun K σ => K.val ⊆ processState σ m
  have hmono : (processLaw V r).event (fun σ => k ≤ (S ∩ processState σ m).card) ≤
      (processLaw V r).event (fun σ => ∃ K, E K σ) := by
    apply FiniteEntropy.Law.event_mono
    intro σ h
    obtain ⟨K, hK, hc⟩ := exists_subset_card_eq h
    exact ⟨⟨K, mem_powersetCard.mpr ⟨Subset.trans hK inter_subset_left, hc⟩⟩,
      Subset.trans hK inter_subset_right⟩
  apply hmono.trans
  apply ((processLaw V r).finite_union_bound E).trans_eq
  have he (K : ↥(S.powersetCard k)) : (processLaw V r).event (E K) =
      (((Fintype.card V).choose r - k).choose (m-k) : ℝ) /
        (((Fintype.card V).choose r).choose m : ℝ) := by
    obtain ⟨hsub, hc⟩ := mem_powersetCard.mp K.property
    simpa only [E, hc] using process_contains_probability m hm K.val
      (Subset.trans hsub hS) (by omega)
  simp_rw [he]
  simp only [sum_const, card_univ, Fintype.card_coe, card_powersetCard, nsmul_eq_mul]
  ring

/-- The raw edge support and complete-edge subtype have the same incidence count. -/
lemma incidentSupport_card {r : ℕ} (hr : 1 ≤ r) (v : V) :
    ((completeEdges V r).filter (fun e => v ∈ e)).card =
      (Fintype.card V - 1).choose (r - 1) := by
  rw [← edgeIncidences_card hr v]
  apply card_bij (fun e he => (⟨e, (mem_filter.mp he).1⟩ : Edge V r))
  · intro e he
    exact (mem_edgeIncidences).mpr (mem_filter.mp he).2
  · intro e he f hf h; exact congrArg Subtype.val h
  · intro e he
    exact ⟨e.val, mem_filter.mpr ⟨e.property, (mem_edgeIncidences).mp he⟩, rfl⟩

lemma pairSupport_card {r : ℕ} (hr : 2 ≤ r) {u v : V} (huv : u ≠ v) :
    ((completeEdges V r).filter (fun e => u ∈ e ∧ v ∈ e)).card =
      (Fintype.card V - 2).choose (r - 2) := by
  rw [← pairIncidences_card hr huv]
  apply card_bij (fun e he => (⟨e, (mem_filter.mp he).1⟩ : Edge V r))
  · intro e he
    exact (mem_pairIncidences).mpr (mem_filter.mp he).2
  · intro e he f hf h; exact congrArg Subtype.val h
  · intro e he
    exact ⟨e.val, mem_filter.mpr ⟨e.property, (mem_pairIncidences).mp he⟩, rfl⟩

lemma incidentSupport_inter (σ : EdgeOrder V r) (m : ℕ) (v : V) :
    ((completeEdges V r).filter (fun e => v ∈ e)) ∩ processState σ m =
      (processState σ m).filter (fun e => v ∈ e) := by
  ext e
  simp only [mem_inter, mem_filter]
  constructor
  · rintro ⟨⟨_,hv⟩,he⟩; exact ⟨he,hv⟩
  · rintro ⟨he,hv⟩; exact ⟨⟨processState_subset σ m he,hv⟩,he⟩

lemma pairSupport_inter (σ : EdgeOrder V r) (m : ℕ) (u v : V) :
    ((completeEdges V r).filter (fun e => u ∈ e ∧ v ∈ e)) ∩ processState σ m =
      (processState σ m).filter (fun e => u ∈ e ∧ v ∈ e) := by
  ext e
  simp only [mem_inter, mem_filter]
  constructor
  · rintro ⟨⟨_,hv⟩,he⟩; exact ⟨he,hv⟩
  · rintro ⟨he,hv⟩; exact ⟨⟨processState_subset σ m he,hv⟩,he⟩

theorem process_vertex_degree_tail {r : ℕ} (hr : 1 ≤ r) (m k : ℕ)
    (hm : m ≤ (completeEdges V r).card) (hk : k ≤ m) (v : V) :
    (processLaw V r).event (fun σ => k ≤ vertexDegree (processState σ m) v) ≤
      (((Fintype.card V - 1).choose (r - 1)).choose k : ℝ) *
        (((Fintype.card V).choose r - k).choose (m-k) : ℝ) /
          (((Fintype.card V).choose r).choose m : ℝ) := by
  have h := process_support_upper_tail m k hm hk
    ((completeEdges V r).filter (fun e => v ∈ e)) (filter_subset _ _)
  simpa only [incidentSupport_inter, vertexDegree, incidentSupport_card hr] using h

theorem process_maximum_degree_tail {r : ℕ} (hr : 1 ≤ r) (m k : ℕ)
    (hm : m ≤ (completeEdges V r).card) (hk : k ≤ m) :
    (processLaw V r).event (fun σ => ∃ v, k ≤ vertexDegree (processState σ m) v) ≤
      (Fintype.card V : ℝ) * (((Fintype.card V - 1).choose (r - 1)).choose k : ℝ) *
        (((Fintype.card V).choose r - k).choose (m-k) : ℝ) /
          (((Fintype.card V).choose r).choose m : ℝ) := by
  apply ((processLaw V r).finite_union_bound _).trans
  calc
    _ ≤ ∑ _v : V, (((Fintype.card V - 1).choose (r - 1)).choose k : ℝ) *
        (((Fintype.card V).choose r - k).choose (m-k) : ℝ) /
          (((Fintype.card V).choose r).choose m : ℝ) :=
      sum_le_sum fun v _ => process_vertex_degree_tail hr m k hm hk v
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

theorem process_pair_degree_tail {r : ℕ} (hr : 2 ≤ r) (m k : ℕ)
    (hm : m ≤ (completeEdges V r).card) (hk : k ≤ m) {u v : V} (huv : u ≠ v) :
    (processLaw V r).event (fun σ => k ≤ pairDegree (processState σ m) u v) ≤
      (((Fintype.card V - 2).choose (r - 2)).choose k : ℝ) *
        (((Fintype.card V).choose r - k).choose (m-k) : ℝ) /
          (((Fintype.card V).choose r).choose m : ℝ) := by
  have h := process_support_upper_tail m k hm hk
    ((completeEdges V r).filter (fun e => u ∈ e ∧ v ∈ e)) (filter_subset _ _)
  simpa only [pairSupport_inter, pairDegree, pairSupport_card hr huv] using h

/-- Ordered pairs of different vertices, without including diagonal pairs. -/
abbrev DistinctVertexPair (V : Type*) := Σ u : V, {v : V // v ≠ u}

lemma distinctVertexPair_card : Fintype.card (DistinctVertexPair V) =
    Fintype.card V * (Fintype.card V - 1) := by
  classical
  rw [Fintype.card_sigma]
  have hc (u : V) : Fintype.card {v : V // v ≠ u} = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp_rw [hc]
  simp

/-- A union bound for a large codegree at any ordered pair of distinct vertices. -/
theorem process_maximum_pair_degree_tail {r : ℕ} (hr : 2 ≤ r) (m k : ℕ)
    (hm : m ≤ (completeEdges V r).card) (hk : k ≤ m) :
    (processLaw V r).event (fun σ => ∃ u v, u ≠ v ∧ k ≤ pairDegree (processState σ m) u v) ≤
      (Fintype.card V * (Fintype.card V - 1) : ℕ) *
        (((Fintype.card V - 2).choose (r - 2)).choose k : ℝ) *
        (((Fintype.card V).choose r - k).choose (m-k) : ℝ) /
          (((Fintype.card V).choose r).choose m : ℝ) := by
  classical
  let E : DistinctVertexPair V → EdgeOrder V r → Prop :=
    fun p σ => k ≤ pairDegree (processState σ m) p.1 p.2.val
  have hmono : (processLaw V r).event
      (fun σ => ∃ u v, u ≠ v ∧ k ≤ pairDegree (processState σ m) u v) ≤
        (processLaw V r).event (fun σ => ∃ p, E p σ) := by
    apply FiniteEntropy.Law.event_mono
    rintro σ ⟨u,v,hne,h⟩
    exact ⟨⟨u,⟨v,hne.symm⟩⟩,h⟩
  apply hmono.trans
  apply ((processLaw V r).finite_union_bound E).trans
  calc
    _ ≤ ∑ _p : DistinctVertexPair V,
        (((Fintype.card V - 2).choose (r - 2)).choose k : ℝ) *
        (((Fintype.card V).choose r - k).choose (m-k) : ℝ) /
          (((Fintype.card V).choose r).choose m : ℝ) :=
      sum_le_sum fun p _ => process_pair_degree_tail hr m k hm hk p.2.property.symm
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, distinctVertexPair_card]
      ring

/-- In particular, no pair has codegree at least three except on this event bound. -/
theorem process_pair_degree_three_bound {r : ℕ} (hr : 2 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) (h3 : 3 ≤ m) :
    (processLaw V r).event (fun σ => ∃ u v, u ≠ v ∧ 3 ≤ pairDegree (processState σ m) u v) ≤
      (Fintype.card V * (Fintype.card V - 1) : ℕ) *
        (((Fintype.card V - 2).choose (r - 2)).choose 3 : ℝ) *
        (((Fintype.card V).choose r - 3).choose (m-3) : ℝ) /
          (((Fintype.card V).choose r).choose m : ℝ) :=
  process_maximum_pair_degree_tail hr m 3 hm h3

end LooseHamilton
