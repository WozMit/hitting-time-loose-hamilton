module

public import HittingTimeLooseHamilton.BernoulliSubsetTails
public import HittingTimeLooseHamilton.BernoulliFixedSizeTransfer
public import HittingTimeLooseHamilton.HypergraphIncidenceCounts
public import HittingTimeLooseHamilton.WindowMeanAsymptotics

public section

/-! The terminal-feasibility probability is the unconditioned uniform-M-edge probability. -/
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace LooseHamilton
set_option maxHeartbeats 800000
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The beta of equation (eq:beta), before conditioning on degree lower bounds. -/
@[expose] def terminalFeasibilityProbability (r M : ℕ) (ell : V → ℕ) : ℝ :=
  (processLaw V r).event (fun σ => ∀ v, ell v ≤ vertexDegree (processState σ M) v)

/-- Exact uniform fixed-size counting interpretation of beta. -/
theorem terminalFeasibilityProbability_eq_ratio (r M : ℕ) (ell : V → ℕ)
    (hM : M ≤ (completeEdges V r).card) :
    terminalFeasibilityProbability r M ell =
      ((((completeEdges V r).powersetCard M).filter
        (fun F => ∀ v, ell v ≤ vertexDegree F v)).card : ℝ) /
        (((Fintype.card V).choose r).choose M : ℝ) := by
  classical
  exact process_state_probability M hM (fun F => ∀ v, ell v ≤ vertexDegree F v)

/-- The same lower bounds in complete-edge coordinates. -/
@[expose] def incidenceFeasible (r : ℕ) (ell : V → ℕ) (S : Finset (Edge V r)) : Prop :=
  ∀ v, ell v ≤ (S ∩ edgeIncidences r v).card

lemma incidenceFeasible_mono (r : ℕ) (ell : V → ℕ) : Monotone (incidenceFeasible r ell) := by
  intro S T hST h v
  exact (h v).trans (card_le_card (inter_subset_inter hST (Subset.refl _)))

lemma prefix_incidence_degree (r M : ℕ) (σ : EdgeOrder V r) (v : V) :
    (orderPrefix (orderRankEquiv (Edge V r) σ) M ∩ edgeIncidences r v).card =
      vertexDegree (processState σ M) v := by
  have hs : (orderPrefix (orderRankEquiv (Edge V r) σ) M ∩ edgeIncidences r v).image
      Subtype.val = (processState σ M).filter (fun e => v ∈ e) := by
    ext e
    simp only [mem_image,mem_inter,mem_orderPrefix,mem_edgeIncidences,mem_filter]
    constructor
    · rintro ⟨a,⟨ha,hv⟩,rfl⟩
      exact ⟨mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_attach _ _, by simpa [edgeRank,orderRankEquiv] using ha⟩,rfl⟩,hv⟩
    · rintro ⟨he,hv⟩
      obtain ⟨a,ha,rfl⟩ := mem_image.mp he
      exact ⟨a,⟨by simpa [edgeRank,orderRankEquiv] using (mem_filter.mp ha).2,hv⟩,rfl⟩
  rw [← card_image_of_injective _ Subtype.val_injective,hs]
  rfl

lemma terminalFeasibilityProbability_eq_prefix (r M : ℕ) (ell : V → ℕ) :
    terminalFeasibilityProbability r M ell =
      BernoulliSubset.prefixProbability M (incidenceFeasible r ell) := by
  have h := FiniteEntropy.Law.uniform_event_equiv (orderRankEquiv (Edge V r))
    (fun σ => incidenceFeasible r ell (orderPrefix σ M))
  simpa only [terminalFeasibilityProbability,processLaw,BernoulliSubset.prefixProbability,
    incidenceFeasible,prefix_incidence_degree] using h

/-- Finite bound with explicit scalar hypotheses, proved by FKG and transfer. -/
theorem terminal_feasibility_finite (r M : ℕ) (ell : V → ℕ)
    (hr : 1 ≤ r) (hn : r ≤ Fintype.card V)
    (hM : M ≤ (completeEdges V r).card)
    (hmean : (99/100:ℝ)*Real.log (Fintype.card V:ℝ) ≤ meanDegree (V:=V) r M)
    (hell : ∀ v, (ell v:ℝ) ≤ (11/1000:ℝ)*Real.log (Fintype.card V:ℝ))
    (hu : (Fintype.card V:ℝ)^(-91/100:ℝ) ≤ 1/2) :
    Real.exp (-2*(Fintype.card V:ℝ)^(-91/100:ℝ)*Fintype.card V) -
      Real.exp (-(M:ℝ)/1010000) ≤ terminalFeasibilityProbability r M ell := by
  let K := Fintype.card (Edge V r)
  let p : ℝ := (99/100:ℝ)*M/K
  have hK : K = (Fintype.card V).choose r := by simp [K,completeEdges_card]
  have hK0 : (0:ℝ)<K := by rw [hK]; exact_mod_cast Nat.choose_pos hn
  have hmK : (M:ℝ) ≤ K := by
    exact_mod_cast (show M ≤ K by simpa [K] using hM)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    apply (div_le_iff₀ hK0).mpr
    nlinarith [(show (0:ℝ) ≤ M from Nat.cast_nonneg M)]
  let ρ := BernoulliSubset.law (A:=Edge V r) p hp0 hp1
  have hsize : p * K = (99/100:ℝ)*M := by dsimp [p]; field_simp <;> ring
  have hdeg (v : V) : p * (edgeIncidences r v).card =
      (99/100:ℝ)*meanDegree (V:=V) r M := by
    rw [edgeIncidences_card hr]
    dsimp [p]
    rw [hK]
    calc
      _ = (99/100:ℝ)*M * (((Fintype.card V-1).choose (r-1):ℝ)/
        ((Fintype.card V).choose r:ℝ)) := by ring
      _ = _ := by rw [vertex_incidence_ratio hr hn]; unfold meanDegree; ring
  have hn1 : 1 ≤ Fintype.card V := hr.trans hn
  have hl : 0 ≤ Real.log (Fintype.card V:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hfail (v : V) : ρ.event (fun S => ¬ell v ≤ (S ∩ edgeIncidences r v).card) ≤
      (Fintype.card V:ℝ)^(-91/100:ℝ) := by
    simp only [not_le]
    apply BernoulliSubset.degree_failure_bound p hp0 hp1 _ _ _ hn1 _ (hell v)
    rw [hdeg]
    nlinarith
  have hall := BernoulliSubset.all_events_lower_bound p hp0 hp1
    (fun v (S : Finset (Edge V r)) => ell v ≤ (S ∩ edgeIncidences r v).card)
    (fun v S T hST h => h.trans (card_le_card (inter_subset_inter hST (Subset.refl _))))
    ((Fintype.card V:ℝ)^(-91/100:ℝ)) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hu hfail
  have hover := BernoulliSubset.size_overflow_bound p hp0 hp1 M hsize
  have htrans := BernoulliSubset.fixed_size_transfer p hp0 hp1 M
    (incidenceFeasible r ell) (incidenceFeasible_mono r ell)
  rw [terminalFeasibilityProbability_eq_prefix]
  change _ ≤ ρ.event (incidenceFeasible r ell) at hall
  change ρ.event (fun S => M<S.card) ≤ _ at hover
  change ρ.event (incidenceFeasible r ell)-ρ.event (fun S => M<S.card) ≤ _ at htrans
  linarith
end LooseHamilton
