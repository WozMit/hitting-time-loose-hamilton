module

public import HittingTimeLooseHamilton.BiasedMatchingCollisionModels
public import HittingTimeLooseHamilton.KahnLocalBound
public import Mathlib.Data.Fintype.EquivFin

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- Pad each actual incidence set by an injection into the common degree bound. -/
@[expose] def kahnPaddingEmbedding {n r D : ℕ} (H : Kahn.Hypergraph n r)
    (hD : ∀ v, Fintype.card (KahnIncident H v) ≤ D) (v : Fin n) :
    KahnIncident H v ↪ Fin D :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hD v))

/-- The actual Kahn error sum, expressed over the host incidence types. -/
lemma kahn_errorSum_incident {n r : ℕ} {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) :
    Kahn.MatchingLaw.errorSum μ =
      ∑ v, ∑ e : KahnIncident H v, (kahnIncidentLaw μ v).mass e *
        (Kahn.MatchingLaw.gamma μ v (e.val.erase v))^(1/((r:ℝ)-1)) := by
  unfold Kahn.MatchingLaw.errorSum
  apply Finset.sum_congr rfl
  intro v _
  rw [← Kahn.MatchingLaw.sum_marginal_eq_candidates]
  rw [← kahnIncidentLaw_map_erase μ v, Law.sum_map_mul]
  rfl

/-- Entropy collision control for actual random perfect matchings. The sole
remaining combinatorial input is the unweighted incidence collision sum. -/
lemma kahn_collision_bound_of_incidence_sum {n r D : ℕ}
    (H : Kahn.Hypergraph n r) (μ : Law (Kahn.MatchingIn H))
    (hn : 0 < n) (hDpos : 0 < D) (hr : 2 ≤ r)
    (hD : ∀ v, Fintype.card (KahnIncident H v) ≤ D)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (hcollision : (∑ v, ∑ e : KahnIncident H v,
      Kahn.MatchingLaw.gamma μ v (e.val.erase v)) ≤ (n:ℝ)*D*ζ) :
    Kahn.MatchingLaw.errorSum μ ≤
      (n:ℝ)*ζ^(1/(2*((r:ℝ)-1))) +
      2*((n:ℝ)*Real.log D - Kahn.MatchingLaw.marginalEntropySum μ +
        (n:ℝ)*Real.log 2) / Real.log (1/ζ) := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hDpos
  let emb := kahnPaddingEmbedding H hD
  let p : Fin n → Law (Fin D) := fun v => (kahnIncidentLaw μ v).map (emb v)
  let γ : Fin n × Fin D → ℝ := fun z =>
    collisionPadValue (emb z.1)
      (fun e => Kahn.MatchingLaw.gamma μ z.1 (e.val.erase z.1)) z.2
  have hγ (z : Fin n × Fin D) : γ z ∈ Set.Icc (0:ℝ) 1 := by
    apply collisionPadValue_mem_Icc
    intro e
    exact ⟨Kahn.MatchingLaw.gamma_nonneg μ _ _, Kahn.MatchingLaw.gamma_le_one μ _ _⟩
  have hmean : (∑ z, γ z) ≤ (Fintype.card (Fin n):ℝ) * Fintype.card (Fin D) * ζ := by
    simp only [Fintype.card_fin, Fintype.sum_prod_type]
    change (∑ v, ∑ a, collisionPadValue (emb v)
      (fun e => Kahn.MatchingLaw.gamma μ v (e.val.erase v)) a) ≤ _
    simp_rw [collisionPadValue_sum]
    exact hcollision
  have ha : 0 ≤ 1/((r:ℝ)-1) := by
    have : (2:ℝ) ≤ r := by exact_mod_cast hr
    exact div_nonneg zero_le_one (by linarith)
  have h := padded_collision_bound p γ (fun z => (hγ z).1) (fun z => (hγ z).2)
    hζ hζ1 ha hmean
  have hentropy (v : Fin n) : entropy (p v).mass =
      entropy (Kahn.MatchingLaw.marginal μ v).mass := by
    dsimp [p]
    rw [Law.entropy_map_of_injective _ _ (emb v).injective, kahnIncidentLaw_entropy]
  have hmoment (v : Fin n) :
      (∑ a, (p v).mass a * (γ (v,a))^(1/((r:ℝ)-1))) =
      ∑ e : KahnIncident H v, (kahnIncidentLaw μ v).mass e *
        (Kahn.MatchingLaw.gamma μ v (e.val.erase v))^(1/((r:ℝ)-1)) := by
    dsimp [p]
    rw [Law.sum_map_mul]
    simp only [γ, collisionPadValue_apply]
  simp_rw [hmoment, hentropy] at h
  rw [← kahn_errorSum_incident] at h
  simp only [Fintype.card_fin] at h
  have halpha : (1/((r:ℝ)-1))/2 = 1/(2*((r:ℝ)-1)) := by rw [div_div, mul_comm ((r:ℝ)-1) 2]
  rw [halpha] at h
  exact h

end LooseHamilton
