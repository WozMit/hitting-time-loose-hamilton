module

public import HittingTimeLooseHamilton.BiasedMatchingCollisionAverage

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- Every atom is controlled by the entropy deficit from a common finite alphabet.
This is the binary coarsening estimate in the proof of Lemma 7.1. -/
lemma coarse_atom_bound {A : Type*} [Fintype A] (p : Law A)
    {D : ℕ} (hD : 2 ≤ D) (emb : A ↪ Fin D) (a : A) :
    p.mass a ≤ (Real.log D - entropy p.mass + Real.log 2) / Real.log D := by
  classical
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (by omega)
  let q : Law (Fin D) := p.map emb
  have hpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hgt : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have h := rare_event_entropy_bound q (uniform : Law (Fin D))
    (fun _ => by simp only [uniform]; positivity) (fun b => b = emb a)
    (t := (D : ℝ)⁻¹) (inv_pos.mpr hpos) (by simpa using inv_lt_one_of_one_lt₀ hgt)
    (by simp [Law.event, uniform])
  rw [finiteRelativeEntropy_uniform] at h
  have he : q.event (fun b => b = emb a) = p.mass a := by
    simp [q, Law.event, Law.map, emb.injective.eq_iff]
  rw [he] at h
  simpa only [q, Law.entropy_map_of_injective p emb emb.injective,
    Fintype.card_fin, one_div, inv_inv] using h

/-- Collision probability is at most the largest-atom estimate, with no need to
choose an atom attaining the maximum. -/
lemma coarse_collision_bound {A : Type*} [Fintype A] (p : Law A)
    {D : ℕ} (hD : 2 ≤ D) (emb : A ↪ Fin D) :
    (∑ a, (p.mass a)^2) ≤
      (Real.log D - entropy p.mass + Real.log 2) / Real.log D := by
  have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) =>
    mul_le_mul_of_nonneg_left (coarse_atom_bound p hD emb a) (p.nonneg a))
  simpa only [← pow_two, ← Finset.sum_mul, p.total, one_mul] using h

/-- Incidence collision, summed over all vertices of an actual perfect-matching
law, is bounded by the padded entropy deficit. -/
lemma coarse_incidence_collision_bound {n r D : ℕ}
    (H : Kahn.Hypergraph n r) (p : Law (Kahn.MatchingIn H))
    (hD : 2 ≤ D) (hdeg : ∀ v, Fintype.card (KahnIncident H v) ≤ D) :
    (∑ v, ∑ e : KahnIncident H v, ((kahnIncidentLaw p v).mass e)^2) ≤
      ((n : ℝ)*Real.log D - Kahn.MatchingLaw.marginalEntropySum p +
        (n : ℝ)*Real.log 2) / Real.log D := by
  have h := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin n))) =>
    coarse_collision_bound (kahnIncidentLaw p v) hD (kahnPaddingEmbedding H hdeg v))
  simp_rw [kahnIncidentLaw_entropy] at h
  simpa only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Kahn.MatchingLaw.marginalEntropySum] using h

/-- The same estimate averaged over a role ensemble. -/
lemma coarse_ensemble_incidence_collision_bound {R : Type*} [Fintype R]
    {n r D : ℕ} (ν : Law R) (H : R → Kahn.Hypergraph n r)
    (p : (i : R) → Law (Kahn.MatchingIn (H i))) (hD : 2 ≤ D)
    (hdeg : ∀ i v, Fintype.card (KahnIncident (H i) v) ≤ D) :
    (∑ i, ν.mass i * ∑ v, ∑ e : KahnIncident (H i) v,
      ((kahnIncidentLaw (p i) v).mass e)^2) ≤
      (averageKahnPaddedDeficit ν H p D + (n : ℝ)*Real.log 2) / Real.log D := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset R)) =>
    mul_le_mul_of_nonneg_left
      (coarse_incidence_collision_bound (H i) (p i) hD (hdeg i)) (ν.nonneg i))
  have he : (∑ i, ν.mass i *
      (((n : ℝ)*Real.log D - Kahn.MatchingLaw.marginalEntropySum (p i) +
        (n : ℝ)*Real.log 2) / Real.log D)) =
      (averageKahnPaddedDeficit ν H p D + (n : ℝ)*Real.log 2) / Real.log D := by
    simp only [← mul_div_assoc, ← Finset.sum_div, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, ν.total, one_mul, averageKahnPaddedDeficit]
  rwa [he] at h

end LooseHamilton
