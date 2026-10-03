module

public import HittingTimeLooseHamilton.BiasedCloneBalance
public import HittingTimeLooseHamilton.BiasedCollisionCounting

public section

/-! Local and degree entropy deficits for actual Kahn matching distributions. -/
noncomputable section
open scoped BigOperators
namespace LooseHamilton
open FiniteEntropy Finset
variable {n r : ℕ}

@[expose] def kahnHostIncidences (H : Kahn.Hypergraph n r) (v : Fin n) : Finset ↥H.edges := by
  classical
  exact univ.filter fun e => v ∈ e.val

@[expose] def kahnIncidentEquiv (H : Kahn.Hypergraph n r) (v : Fin n) :
    KahnIncident H v ≃ ↥(kahnHostIncidences H v) where
  toFun e := ⟨⟨e.val,e.property.1⟩, by simp [kahnHostIncidences, e.property.2]⟩
  invFun e := ⟨e.val.val,e.val.property, (Finset.mem_filter.mp e.property).2⟩
  left_inv e := rfl
  right_inv e := rfl

@[expose] def kahnHostLocalLaw {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (v : Fin n) : Law ↥(kahnHostIncidences H v) :=
  (kahnIncidentLaw μ v).map (kahnIncidentEquiv H v)

@[expose] def kahnEdgeProbability {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (e : ↥H.edges) : ℝ :=
  μ.event fun M => e.val ∈ M.val.val

theorem kahnIncidentLaw_mass {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (v : Fin n) (e : KahnIncident H v) :
    (kahnIncidentLaw μ v).mass e = μ.event (fun M => e.val ∈ M.val.val) := by
  classical
  change μ.event (fun M => kahnIncidentEdge v M = e) = _
  congr 1
  funext M
  apply propext
  constructor
  · intro h
    have he := congrArg Subtype.val h
    exact he ▸ M.val.edge_mem v
  · intro he
    apply Subtype.ext
    exact (M.val.eq_edge_of_mem he e.property.2).symm

theorem kahnHostLocalLaw_mass {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (v : Fin n) (e : ↥(kahnHostIncidences H v)) :
    (kahnHostLocalLaw μ v).mass e = kahnEdgeProbability μ e.val := by
  unfold kahnHostLocalLaw
  obtain ⟨e, rfl⟩ := (kahnIncidentEquiv H v).surjective e
  rw [Law.map_mass_of_injective _ _ (kahnIncidentEquiv H v).injective,
    kahnIncidentLaw_mass]
  rfl

theorem kahnHostLocalLaw_entropy {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (v : Fin n) :
    entropy (kahnHostLocalLaw μ v).mass = entropy (Kahn.MatchingLaw.marginal μ v).mass := by
  rw [kahnHostLocalLaw, Law.entropy_map_of_injective _ _ (kahnIncidentEquiv H v).injective,
    kahnIncidentLaw_entropy]

theorem kahnHostIncidences_card (H : Kahn.Hypergraph n r) (v : Fin n) :
    (kahnHostIncidences H v).card = Fintype.card (KahnIncident H v) := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (kahnIncidentEquiv H v)).symm

theorem kahnHostIncidences_column (H : Kahn.Hypergraph n r) (e : ↥H.edges) :
    (univ.filter (fun v => e ∈ kahnHostIncidences H v)).card = r := by
  classical
  have he : univ.filter (fun v => e ∈ kahnHostIncidences H v) = e.val := by
    ext v; simp [kahnHostIncidences]
  rw [he, H.uniform e.val e.property]

@[expose] def kahnLocalDeficit {H : Kahn.Hypergraph n r} (μ : Law (Kahn.MatchingIn H)) : ℝ :=
  ∑ v : Fin n, (Real.log (Fintype.card (KahnIncident H v)) -
    entropy (Kahn.MatchingLaw.marginal μ v).mass)

@[expose] def kahnDegreeDeficit (H : Kahn.Hypergraph n r) (lam : ℝ) : ℝ :=
  (n : ℝ)*Real.log lam - ∑ v : Fin n, Real.log (Fintype.card (KahnIncident H v))

/-- The two concrete deficits sum to the precise total local entropy loss. -/
theorem kahn_deficits_add {H : Kahn.Hypergraph n r} (μ : Law (Kahn.MatchingIn H)) (lam : ℝ) :
    kahnLocalDeficit μ + kahnDegreeDeficit H lam =
      (n : ℝ)*Real.log lam - Kahn.MatchingLaw.marginalEntropySum μ := by
  unfold kahnLocalDeficit kahnDegreeDeficit Kahn.MatchingLaw.marginalEntropySum
  rw [sum_sub_distrib]
  ring

theorem kahn_local_deficit_nonneg {H : Kahn.Hypergraph n r} (μ : Law (Kahn.MatchingIn H)) :
    0 ≤ kahnLocalDeficit μ := by
  apply sum_nonneg
  intro v _
  haveI := local_incidence_nonempty (kahnHostIncidences H) (kahnHostLocalLaw μ) v
  have h := entropy_le_log_card (kahnHostLocalLaw μ v)
  rw [kahnHostLocalLaw_entropy, Fintype.card_coe, kahnHostIncidences_card] at h
  linarith

theorem kahn_incident_card_sum (H : Kahn.Hypergraph n r) :
    (∑ v : Fin n, (Fintype.card (KahnIncident H v) : ℝ)) =
      (r : ℝ)*H.edges.card := by
  have h := kahn_incidence_sum H (fun _ => (1 : ℝ))
  simpa using h

@[expose] def kahnMeanDegree (H : Kahn.Hypergraph n r) : ℝ := (r : ℝ)*H.edges.card/n

theorem kahn_incident_mean (H : Kahn.Hypergraph n r) (hn : 0 < n) :
    (∑ v : Fin n, (Fintype.card (KahnIncident H v) : ℝ)) =
      (n : ℝ)*kahnMeanDegree H := by
  rw [kahn_incident_card_sum, kahnMeanDegree]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

theorem kahn_incident_card_pos {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (v : Fin n) :
    0 < (Fintype.card (KahnIncident H v) : ℝ) := by
  haveI := local_incidence_nonempty (kahnHostIncidences H) (kahnHostLocalLaw μ) v
  have h := Fintype.card_pos (α := ↥(kahnHostIncidences H v))
  rw [Fintype.card_coe, kahnHostIncidences_card] at h
  exact_mod_cast h

theorem kahn_mean_degree_pos {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (hn : 0 < n) : 0 < kahnMeanDegree H := by
  have hp := kahn_incident_card_pos μ (⟨0,hn⟩ : Fin n)
  have hs := single_le_sum (s := (univ : Finset (Fin n)))
    (f := fun v => (Fintype.card (KahnIncident H v) : ℝ))
    (fun v _ => Nat.cast_nonneg _) (mem_univ (⟨0,hn⟩ : Fin n))
  rw [kahn_incident_mean H hn] at hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

/-- The degree deficit is Jensen's logarithmic mean gap. -/
theorem kahn_degree_deficit_nonneg {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (lam : ℝ) (hlam : 0 < lam)
    (hmean : (∑ v : Fin n, (Fintype.card (KahnIncident H v) : ℝ)) = (n : ℝ)*lam) :
    0 ≤ kahnDegreeDeficit H lam := by
  classical
  have hp := kahn_incident_card_pos μ
  have hs := sum_le_sum (s := (univ : Finset (Fin n)))
    (fun v _ => Real.log_le_sub_one_of_pos (div_pos (hp v) hlam))
  simp_rw [Real.log_div (hp _).ne' hlam.ne'] at hs
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_div, hmean] at hs
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  have he : (n : ℝ)*lam/lam = n := by field_simp
  rw [he] at hs
  unfold kahnDegreeDeficit
  linarith

/-- Actual perfect-matching edge marginals are balanced by their two concrete deficits. -/
theorem kahn_matching_balance {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (lam : ℝ) (hlam : 0 < lam)
    (hmean : (∑ v : Fin n, (Fintype.card (KahnIncident H v) : ℝ)) = (n : ℝ)*lam) :
    (r : ℝ)*(∑ e : ↥H.edges, |kahnEdgeProbability μ e-1/lam|) ≤
      2*Real.sqrt ((n : ℝ)*kahnLocalDeficit μ) +
      2*Real.sqrt ((n : ℝ)*kahnDegreeDeficit H lam) := by
  classical
  have h := clone_incidence_balance (kahnHostIncidences H) r (kahnEdgeProbability μ)
    (kahnHostLocalLaw μ) (kahnHostLocalLaw_mass μ) (kahnHostIncidences_column H)
    lam hlam (by simpa only [kahnHostIncidences_card, Fintype.card_fin] using hmean)
  simpa only [kahnHostIncidences_card, kahnHostLocalLaw_entropy, Fintype.card_fin,
    kahnLocalDeficit, kahnDegreeDeficit] using h

/-- The same estimate at the actual average host degree `r|H|/n`. -/
theorem kahn_matching_balance_mean {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (hn : 0 < n) :
    (r : ℝ)*(∑ e : ↥H.edges, |kahnEdgeProbability μ e-1/kahnMeanDegree H|) ≤
      2*Real.sqrt ((n : ℝ)*kahnLocalDeficit μ) +
      2*Real.sqrt ((n : ℝ)*kahnDegreeDeficit H (kahnMeanDegree H)) :=
  kahn_matching_balance μ _ (kahn_mean_degree_pos μ hn) (kahn_incident_mean H hn)

end LooseHamilton
