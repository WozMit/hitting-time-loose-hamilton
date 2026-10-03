module

public import HittingTimeLooseHamilton.BiasedCollisionPadded
public import HittingTimeLooseHamilton.KahnStatement

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

/-- Host edges incident with a given vertex, before padding to a common degree. -/
@[expose] def KahnIncident {n r : ℕ} (H : Kahn.Hypergraph n r) (v : Fin n) :=
  {e : Finset (Fin n) // e ∈ H.edges ∧ v ∈ e}

@[expose] instance {n r : ℕ} (H : Kahn.Hypergraph n r) (v : Fin n) :
    Fintype (KahnIncident H v) := by classical unfold KahnIncident; infer_instance

/-- The edge at a vertex, valued in the actual host incidence type. -/
@[expose] def kahnIncidentEdge {n r : ℕ} {H : Kahn.Hypergraph n r}
    (v : Fin n) (M : Kahn.MatchingIn H) : KahnIncident H v :=
  ⟨M.val.edge v, M.property (M.val.edge_mem v), M.val.mem_edge v⟩

@[expose] def kahnIncidentLaw {n r : ℕ} {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (v : Fin n) : Law (KahnIncident H v) :=
  μ.map (kahnIncidentEdge v)

lemma kahnIncident_erase_injective {n r : ℕ} {H : Kahn.Hypergraph n r}
    (v : Fin n) : Function.Injective (fun e : KahnIncident H v => e.val.erase v) := by
  classical
  intro e f h
  apply Subtype.ext
  have hh := congrArg (insert v) h
  simpa only [Finset.insert_erase e.property.2, Finset.insert_erase f.property.2] using hh

lemma kahnIncidentLaw_map_erase {n r : ℕ} {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (v : Fin n) :
    (kahnIncidentLaw μ v).map (fun e => e.val.erase v) = Kahn.MatchingLaw.marginal μ v := by
  rw [kahnIncidentLaw, Law.map_map]
  rfl

lemma kahnIncidentLaw_entropy {n r : ℕ} {H : Kahn.Hypergraph n r}
    (μ : Law (Kahn.MatchingIn H)) (v : Fin n) :
    entropy (kahnIncidentLaw μ v).mass = entropy (Kahn.MatchingLaw.marginal μ v).mass := by
  rw [← kahnIncidentLaw_map_erase μ v,
    Law.entropy_map_of_injective _ _ (kahnIncident_erase_injective v)]

/-- Extend a function on occupied slots by zero on all padding positions. -/
@[expose] def collisionPadValue {A B : Type*} [Fintype A] (f : A ↪ B) (g : A → ℝ) (b : B) : ℝ := by
  classical
  exact ∑ a, if f a = b then g a else 0

lemma collisionPadValue_apply {A B : Type*} [Fintype A]
    (f : A ↪ B) (g : A → ℝ) (a : A) : collisionPadValue f g (f a) = g a := by
  classical
  simp [collisionPadValue, f.injective.eq_iff]

lemma collisionPadValue_sum {A B : Type*} [Fintype A] [Fintype B]
    (f : A ↪ B) (g : A → ℝ) : (∑ b, collisionPadValue f g b) = ∑ a, g a := by
  classical
  unfold collisionPadValue
  rw [Finset.sum_comm]
  simp

lemma collisionPadValue_zero {A B : Type*} [Fintype A]
    (f : A ↪ B) (g : A → ℝ) (b : B) (hb : ∀ a, f a ≠ b) :
    collisionPadValue f g b = 0 := by
  classical
  simp [collisionPadValue, hb]

lemma collisionPadValue_mem_Icc {A B : Type*} [Fintype A]
    (f : A ↪ B) (g : A → ℝ) (hg : ∀ a, g a ∈ Set.Icc (0:ℝ) 1) (b : B) :
    collisionPadValue f g b ∈ Set.Icc (0:ℝ) 1 := by
  classical
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    rw [collisionPadValue_apply]
    exact hg a
  · rw [collisionPadValue_zero f g b (by simpa using h)]
    exact ⟨le_refl _, zero_le_one⟩

end LooseHamilton
