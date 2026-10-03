module

public import HittingTimeLooseHamilton.HypergeometricProcessTail
public import HittingTimeLooseHamilton.HypergraphIncidenceCounts
public import HittingTimeLooseHamilton.ExceptionalWindowScales
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- Chernoff lower tail for the actual vertex degree in a fixed-size prefix. -/
theorem process_vertex_degree_lower_tail (hr : 1 ≤ r) (m : ℕ)
    (hm : m ≤ (completeEdges V r).card) (hN : 0 < (completeEdges V r).card)
    (v : V) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (k : ℕ) :
    (processLaw V r).event (fun σ => vertexDegree (processState σ m) v ≤ k) ≤
      Real.exp (-(m : ℝ) / (completeEdges V r).card *
        ((Fintype.card V - 1).choose (r - 1) : ℝ) * (1 - q) - (k : ℝ) * Real.log q) := by
  let D := (edgeIncidences r v).image Subtype.val
  have hD : D ⊆ completeEdges V r := by
    intro e he
    obtain ⟨e,_,rfl⟩ := mem_image.mp he
    exact e.property
  have hcard : D.card = (Fintype.card V - 1).choose (r - 1) := by
    rw [show D.card = (edgeIncidences r v).card from card_image_iff.mpr
      (fun _ _ _ _ h => Subtype.ext h), edgeIncidences_card hr]
  have hdegree (σ : EdgeOrder V r) : (processState σ m ∩ D).card =
      vertexDegree (processState σ m) v := by
    unfold vertexDegree
    congr 1
    ext e
    constructor
    · intro he
      obtain ⟨heH,heD⟩ := mem_inter.mp he
      obtain ⟨f,hf,hef⟩ := mem_image.mp heD
      exact mem_filter.mpr ⟨heH,hef ▸ (mem_edgeIncidences.mp hf)⟩
    · intro he
      obtain ⟨heH,hv⟩ := mem_filter.mp he
      exact mem_inter.mpr ⟨heH,mem_image.mpr
        ⟨⟨e,processState_subset σ m heH⟩,mem_edgeIncidences.mpr hv,rfl⟩⟩
  simpa only [hdegree,hcard] using process_intersection_lower_tail_exp m hm hN D hD q hq0 hq1 k

/-- A finite first-moment bound for the exceptional-set cardinality. -/
theorem low_degree_set_card_probability_le (m : ℕ) (c z : ℝ) (hz : 0 < z)
    (hv : ∀ v : V, (processLaw V r).event
      (fun σ => vertexDegree (processState σ m) v ≤ lowerDegreeBase V) ≤ c) :
    (processLaw V r).event (fun σ => ¬ ((lowDegreeVertices (processState σ m)).card : ℝ) ≤ z) ≤
      (Fintype.card V : ℝ) * c / z := by
  classical
  let E : V → EdgeOrder V r → Prop := fun v σ => vertexDegree (processState σ m) v ≤ lowerDegreeBase V
  let X := FiniteEntropy.Law.finiteIndicatorCount E
  have hX (σ : EdgeOrder V r) : X σ = ((lowDegreeVertices (processState σ m)).card : ℝ) := by
    dsimp [X,FiniteEntropy.Law.finiteIndicatorCount,lowDegreeVertices,E]
    calc
      _ = ∑ v : V, if vertexDegree (processState σ m) v ≤ lowerDegreeBase V then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro v _
        by_cases h : vertexDegree (processState σ m) v ≤ lowerDegreeBase V <;> simp [h]
      _ = _ := sum_boole (R := ℝ) (fun v => vertexDegree (processState σ m) v ≤ lowerDegreeBase V) univ
  have hmean : (processLaw V r).finiteMean X ≤ (Fintype.card V : ℝ) * c := by
    rw [FiniteEntropy.Law.finiteMean_indicatorCount]
    calc
      _ ≤ ∑ _v : V, c := sum_le_sum (fun v _ => hv v)
      _ = _ := by simp
  have hmono : (processLaw V r).event (fun σ => ¬ ((lowDegreeVertices (processState σ m)).card : ℝ) ≤ z) ≤
      (processLaw V r).event (fun σ => z ≤ X σ) := by
    apply FiniteEntropy.Law.event_mono
    intro σ hσ
    rw [hX]
    exact (lt_of_not_ge hσ).le
  exact hmono.trans (((processLaw V r).finite_markov
    (FiniteEntropy.Law.finiteIndicatorCount_nonneg E) hz).trans
      (div_le_div_of_nonneg_right hmean hz.le))

/-- The explicit early-window rate from a mean at least 0.98 log n. -/
theorem process_low_degree_probability_le {n : ℕ} (hn : 0 < n) (hr : 1 ≤ r)
    (m : ℕ) (hm : m ≤ n.choose r) (hN : 0 < n.choose r)
    (hmean : (98 / 100 : ℝ) * Real.log n ≤
      (m : ℝ) / (n.choose r : ℝ) * ((n - 1).choose (r - 1) : ℝ)) (v : Fin n) :
    (processLaw (Fin n) r).event
      (fun σ => vertexDegree (processState σ m) v ≤ lowerDegreeBase (Fin n)) ≤
      (n : ℝ) ^ (-exceptionalWindowRate) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : 0 < epsilon := by norm_num [epsilon]
  have hq1 : epsilon ≤ 1 := by norm_num [epsilon]
  have hlog : Real.log epsilon ≤ 0 := Real.log_nonpos hq0.le hq1
  have hk : (lowerDegreeBase (Fin n) : ℝ) ≤ epsilon * Real.log n := by
    simpa [lowerDegreeBase,Fintype.card_fin] using
      Nat.floor_le (mul_nonneg hq0.le (Real.log_nonneg hn1))
  have hm' : m ≤ (completeEdges (Fin n) r).card := by simpa [completeEdges_card] using hm
  have hN' : 0 < (completeEdges (Fin n) r).card := by simpa [completeEdges_card] using hN
  have h := process_vertex_degree_lower_tail hr m hm' hN' v epsilon hq0 hq1 (lowerDegreeBase (Fin n))
  simp only [completeEdges_card,Fintype.card_fin] at h
  have hexponent : -(m : ℝ) / (n.choose r : ℝ) *
      ((n - 1).choose (r - 1) : ℝ) * (1 - epsilon) -
      (lowerDegreeBase (Fin n) : ℝ) * Real.log epsilon ≤ -exceptionalWindowRate * Real.log n := by
    have h1 := mul_le_mul_of_nonneg_right hmean (sub_nonneg.mpr hq1)
    have h2 := mul_le_mul_of_nonpos_right hk hlog
    unfold exceptionalWindowRate
    simp only [neg_div]
    nlinarith
  apply h.trans ((Real.exp_le_exp.mpr hexponent).trans_eq _)
  rw [Real.rpow_def_of_pos hnpos]
  congr 1
  ring

end LooseHamilton
