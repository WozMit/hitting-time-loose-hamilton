module

public import HittingTimeLooseHamilton.FiniteMomentBounds
public import HittingTimeLooseHamilton.HypergraphIncidenceCounts
public import HittingTimeLooseHamilton.UniformPrefixProbability
public import HittingTimeLooseHamilton.StoppingBiasDeterministic

public section

/-! Exact first and second moments of isolated vertices in the fixed-size
uniform hypergraph process, and their finite stopping-time consequences. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- The exact one-vertex isolation probability. -/
@[expose] def isolationProbability (V : Type*) [Fintype V] (r m : ℕ) : ℝ :=
  (((Fintype.card V).choose r - (Fintype.card V - 1).choose (r-1)).choose m : ℝ) /
    (((Fintype.card V).choose r).choose m : ℝ)

/-- The exact simultaneous isolation probability for two distinct vertices. -/
@[expose] def pairIsolationProbability (V : Type*) [Fintype V] (r m : ℕ) : ℝ :=
  (((Fintype.card V).choose r -
    (2 * (Fintype.card V - 1).choose (r-1) - (Fintype.card V - 2).choose (r-2))).choose m : ℝ) /
    (((Fintype.card V).choose r).choose m : ℝ)

private theorem typed_edge_avoids (σ : EdgeOrder V r) (m : ℕ) (D : Finset (Edge V r)) :
    (∀ e ∈ D, m ≤ edgeRank σ e) ↔ Disjoint (processState σ m) (D.image Subtype.val) := by
  constructor
  · intro h
    apply disjoint_left.mpr
    intro f hf hd
    obtain ⟨e,he,rfl⟩ := mem_image.mp hd
    obtain ⟨e',he',heq⟩ := mem_image.mp hf
    have hh : e' = e := Subtype.ext heq
    subst e'
    have hl : edgeRank σ e < m := by simpa using he'
    exact (Nat.not_lt_of_ge (h e he)) hl
  · intro h e he
    by_contra hn
    have hm : edgeRank σ e < m := Nat.lt_of_not_ge hn
    exact disjoint_left.mp h (mem_image.mpr ⟨e,by simpa using hm,rfl⟩)
      (mem_image.mpr ⟨e,he,rfl⟩)

private theorem typed_image_card (D : Finset (Edge V r)) :
    (D.image Subtype.val).card = D.card :=
  card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)

private theorem typed_image_subset (D : Finset (Edge V r)) :
    D.image Subtype.val ⊆ completeEdges V r := by
  intro e he
  obtain ⟨f,_,rfl⟩ := mem_image.mp he
  exact f.property

theorem process_isolated_probability (hr : 1 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) (v : V) :
    (processLaw V r).event (fun σ => vertexDegree (processState σ m) v = 0) =
      isolationProbability V r m := by
  have hev : (fun σ : EdgeOrder V r => vertexDegree (processState σ m) v = 0) =
      (fun σ => Disjoint (processState σ m) ((edgeIncidences r v).image Subtype.val)) := by
    funext σ
    exact propext ((processState_degree_zero_iff σ m v).trans (typed_edge_avoids σ m _))
  rw [hev,process_avoids_probability m hm _ (typed_image_subset _),typed_image_card,edgeIncidences_card hr]
  rfl

theorem process_pair_isolated_probability (hr : 2 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) {u v : V} (huv : u ≠ v) :
    (processLaw V r).event (fun σ => vertexDegree (processState σ m) u = 0 ∧
      vertexDegree (processState σ m) v = 0) = pairIsolationProbability V r m := by
  have hev : (fun σ : EdgeOrder V r => vertexDegree (processState σ m) u = 0 ∧
      vertexDegree (processState σ m) v = 0) =
      (fun σ => Disjoint (processState σ m) ((edgeIncidences r u ∪ edgeIncidences r v).image Subtype.val)) := by
    funext σ
    exact propext ((processState_two_degrees_zero_iff σ m u v).trans (typed_edge_avoids σ m _))
  rw [hev,process_avoids_probability m hm _ (typed_image_subset _),typed_image_card,edgeIncidences_union_card hr huv]
  rfl

/-- Real-valued count of isolated vertices at a deterministic process time. -/
@[expose] def isolatedCount (m : ℕ) (σ : EdgeOrder V r) : ℝ :=
  FiniteEntropy.Law.finiteIndicatorCount (fun v σ => vertexDegree (processState σ m) v = 0) σ

theorem isolatedCount_eq_card (m : ℕ) (σ : EdgeOrder V r) :
    isolatedCount m σ = ((univ.filter (fun v => vertexDegree (processState σ m) v = 0)).card : ℝ) := by
  classical
  unfold isolatedCount FiniteEntropy.Law.finiteIndicatorCount
  dsimp only
  calc
    _ = ∑ v : V, if vertexDegree (processState σ m) v = 0 then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro v _
      by_cases h : vertexDegree (processState σ m) v = 0 <;> simp [h]
    _ = _ := sum_boole (R := ℝ) (fun v => vertexDegree (processState σ m) v = 0) univ

theorem isolatedCount_nonneg (m : ℕ) (σ : EdgeOrder V r) : 0 ≤ isolatedCount m σ :=
  FiniteEntropy.Law.finiteIndicatorCount_nonneg _ _

theorem isolatedCount_zero_iff (m : ℕ) (σ : EdgeOrder V r) :
    isolatedCount m σ = 0 ↔ NoIsolated (processState σ m) := by
  classical
  rw [isolatedCount_eq_card]
  simp [NoIsolated,card_eq_zero,filter_eq_empty_iff,Nat.one_le_iff_ne_zero]

theorem isolatedCount_one_le_iff (m : ℕ) (σ : EdgeOrder V r) :
    1 ≤ isolatedCount m σ ↔ ¬ NoIsolated (processState σ m) := by
  rw [← isolatedCount_zero_iff,isolatedCount_eq_card]
  norm_cast
  omega

/-- E Z = n a, with the exact without-replacement isolation probability a. -/
theorem isolatedCount_mean (hr : 1 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) :
    (processLaw V r).finiteMean (isolatedCount m) =
      (Fintype.card V : ℝ) * isolationProbability V r m := by
  change (processLaw V r).finiteMean
    (FiniteEntropy.Law.finiteIndicatorCount (fun v σ => vertexDegree (processState σ m) v = 0)) = _
  rw [FiniteEntropy.Law.finiteMean_indicatorCount]
  simp_rw [process_isolated_probability hr m hm]
  simp

/-- E Z² = n a + n(n-1)b, with b the exact two-vertex isolation probability.
The natural predecessor also makes the formula valid for empty vertex types. -/
theorem isolatedCount_second_moment (hr : 2 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) :
    (processLaw V r).finiteMean (fun σ => (isolatedCount m σ)^2) =
      (Fintype.card V : ℝ) * isolationProbability V r m +
      (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) * pairIsolationProbability V r m := by
  classical
  simp only [isolatedCount]
  rw [FiniteEntropy.Law.finiteMean_indicatorCount_sq]
  have inner (u : V) :
      (∑ v : V, (processLaw V r).event (fun σ => vertexDegree (processState σ m) u = 0 ∧
          vertexDegree (processState σ m) v = 0)) =
        isolationProbability V r m + (Fintype.card V - 1 : ℕ) * pairIsolationProbability V r m := by
    rw [← sum_erase_add _ _ (mem_univ u)]
    have hdiag : (processLaw V r).event (fun σ => vertexDegree (processState σ m) u = 0 ∧
        vertexDegree (processState σ m) u = 0) = isolationProbability V r m := by
      simpa using process_isolated_probability (by omega : 1 ≤ r) m hm u
    rw [hdiag]
    have hoff : (∑ v ∈ (univ : Finset V).erase u,
        (processLaw V r).event (fun σ => vertexDegree (processState σ m) u = 0 ∧
          vertexDegree (processState σ m) v = 0)) =
        (Fintype.card V - 1 : ℕ) * pairIsolationProbability V r m := by
      calc
        _ = ∑ _v ∈ (univ : Finset V).erase u, pairIsolationProbability V r m := by
          apply sum_congr rfl
          intro v hv
          exact process_pair_isolated_probability hr m hm (Ne.symm (mem_erase.mp hv).1)
        _ = _ := by simp
    rw [hoff]
    ring
  simp_rw [inner]
  simp only [sum_const,card_univ,nsmul_eq_mul]
  ring

/-- The first-moment late-time bound. -/
theorem process_has_isolated_probability_le (hr : 1 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) :
    (processLaw V r).event (fun σ => ¬ NoIsolated (processState σ m)) ≤
      (Fintype.card V : ℝ) * isolationProbability V r m := by
  have h := (processLaw V r).finite_markov (isolatedCount_nonneg m) (by norm_num : (0 : ℝ) < 1)
  have hev : (fun σ : EdgeOrder V r => 1 ≤ isolatedCount m σ) =
      (fun σ => ¬ NoIsolated (processState σ m)) := by
    funext σ; exact propext (isolatedCount_one_le_iff m σ)
  rw [hev,div_one,isolatedCount_mean hr m hm] at h
  exact h

/-- The second-moment early-time bound. -/
theorem process_noIsolated_probability_le (hr : 2 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card)
    (hpos : 0 < (Fintype.card V : ℝ) * isolationProbability V r m) :
    (processLaw V r).event (fun σ => NoIsolated (processState σ m)) ≤
      ((Fintype.card V : ℝ) * isolationProbability V r m +
        (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) * pairIsolationProbability V r m -
        ((Fintype.card V : ℝ) * isolationProbability V r m)^2) /
      ((Fintype.card V : ℝ) * isolationProbability V r m)^2 := by
  have hmean := isolatedCount_mean (by omega : 1 ≤ r) m hm
  have h := (processLaw V r).finite_second_moment_zero (isolatedCount m) (hmean ▸ hpos)
  have hev : (fun σ : EdgeOrder V r => isolatedCount m σ = 0) =
      (fun σ => NoIsolated (processState σ m)) := by
    funext σ; exact propext (isolatedCount_zero_iff m σ)
  rw [hev,hmean,isolatedCount_second_moment hr m hm] at h
  exact h
/-- Monotonicity identifies the stopping event with the deterministic state event. -/
theorem tauOne_le_iff_noIsolated (σ : EdgeOrder V r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) :
    tauOne σ ≤ (m : WithTop ℕ) ↔ NoIsolated (processState σ m) := by
  constructor
  · intro h
    have hne : tauOne σ ≠ ⊤ := by
      intro he
      rw [he] at h
      exact (WithTop.coe_ne_top : (m : WithTop ℕ) ≠ ⊤) (top_le_iff.mp h)
    obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp hne
    have hs := (tauOne_eq_iff_first σ k).mp hk.symm
    have hkm : k ≤ m := WithTop.coe_le_coe.mp (hk ▸ h)
    exact noIsolated_mono (processState_mono σ hkm) hs.2.1
  · intro h
    exact firstTime_le _ _ _ hm h

theorem tauOne_late_probability_le (hr : 1 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) :
    (processLaw V r).event (fun σ => (m : WithTop ℕ) < tauOne σ) ≤
      (Fintype.card V : ℝ) * isolationProbability V r m := by
  have hev : (fun σ : EdgeOrder V r => (m : WithTop ℕ) < tauOne σ) =
      (fun σ => ¬ NoIsolated (processState σ m)) := by
    funext σ
    apply propext
    rw [← not_le, tauOne_le_iff_noIsolated σ m hm]
  rw [hev]
  exact process_has_isolated_probability_le hr m hm

theorem tauOne_early_probability_le (hr : 2 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card)
    (hpos : 0 < (Fintype.card V : ℝ) * isolationProbability V r m) :
    (processLaw V r).event (fun σ => tauOne σ ≤ (m : WithTop ℕ)) ≤
      ((Fintype.card V : ℝ) * isolationProbability V r m +
        (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) * pairIsolationProbability V r m -
        ((Fintype.card V : ℝ) * isolationProbability V r m)^2) /
      ((Fintype.card V : ℝ) * isolationProbability V r m)^2 := by
  have hev : (fun σ : EdgeOrder V r => tauOne σ ≤ (m : WithTop ℕ)) =
      (fun σ => NoIsolated (processState σ m)) := by
    funext σ; exact propext (tauOne_le_iff_noIsolated σ m hm)
  rw [hev]
  exact process_noIsolated_probability_le hr m hm hpos
end LooseHamilton
