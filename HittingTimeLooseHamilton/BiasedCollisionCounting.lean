module

public import HittingTimeLooseHamilton.BiasedMatchingCollisionModels
public import HittingTimeLooseHamilton.KahnMatchingCoordinates
public import Mathlib.Tactic

public section

/-! Pair-degree counting controls the unweighted Kahn collision probabilities. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
open scoped BigOperators
namespace LooseHamilton

/-- All host edges containing a pair from one matching block. -/
@[expose] def matchingCollisionEdges {n r : ℕ} (H : Kahn.Hypergraph n r)
    (M : Kahn.PerfectMatching n r) : Finset (Finset (Fin n)) :=
  M.val.biUnion fun B => B.powersetCard 2 |>.biUnion fun q => H.edges.filter (q ⊆ ·)

/-- Kahn's bad event is witnessed by a same-block vertex pair in the candidate edge. -/
theorem kahn_bad_mem_collision {n r : ℕ} (H : Kahn.Hypergraph n r)
    (M : Kahn.PerfectMatching n r) {f : Finset (Fin n)} (hf : f ∈ H.edges)
    {v : Fin n} (hv : v ∈ f) (hbad : M.Bad v (f.erase v)) :
    f ∈ matchingCollisionEdges H M := by
  classical
  have hex : ∃ x ∈ f, ∃ y ∈ f, x ≠ y ∧ M.edge x = M.edge y := by
    by_contra hn
    push_neg at hn
    have hi : Set.InjOn M.edge (f.erase v : Set (Fin n)) := by
      intro x hx y hy he
      by_contra hxy
      exact hn x (mem_of_mem_erase hx) y (mem_of_mem_erase hy) hxy he
    have hd : ∀ x ∈ f.erase v, M.edge x ≠ M.edge v := by
      intro x hx
      exact hn x (mem_of_mem_erase hx) v hv (ne_of_mem_erase hx)
    have ht := (M.tau_eq_card_iff v (f.erase v)).mpr ⟨hi, hd⟩
    rw [card_erase_of_mem hv, H.uniform f hf] at ht
    exact (Nat.ne_of_lt hbad) ht
  obtain ⟨x, hx, y, hy, hxy, hsame⟩ := hex
  apply mem_biUnion.mpr
  refine ⟨M.edge x, M.edge_mem x, mem_biUnion.mpr ?_⟩
  refine ⟨{x,y}, mem_powersetCard.mpr ⟨?_, card_pair hxy⟩, ?_⟩
  · intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact M.mem_edge _
    · rw [hsame]; exact M.mem_edge _
  · apply mem_filter.mpr
    exact ⟨hf, by simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hx hy⟩

/-- There are at most one pair-degree bound per pair in every matching block. -/
theorem matchingCollisionEdges_card_le {n r : ℕ} (H : Kahn.Hypergraph n r)
    (M : Kahn.PerfectMatching n r) (κ : ℕ)
    (hκ : ∀ q : Finset (Fin n), q.card = 2 →
      (H.edges.filter (q ⊆ ·)).card ≤ κ) :
    (matchingCollisionEdges H M).card ≤ M.val.card * (r.choose 2) * κ := by
  classical
  unfold matchingCollisionEdges
  calc
    _ ≤ ∑ B ∈ M.val, (B.powersetCard 2 |>.biUnion
        fun q => H.edges.filter (q ⊆ ·)).card := card_biUnion_le
    _ ≤ ∑ B ∈ M.val, ∑ q ∈ B.powersetCard 2, (H.edges.filter (q ⊆ ·)).card := by
      exact sum_le_sum fun B _ => card_biUnion_le
    _ ≤ ∑ B ∈ M.val, ∑ _q ∈ B.powersetCard 2, κ := by
      apply sum_le_sum
      intro B hB
      exact sum_le_sum fun q hq => hκ q (mem_powersetCard.mp hq).2
    _ = _ := by
      simp only [sum_const, smul_eq_mul, card_powersetCard]
      rw [sum_congr rfl (fun B hB => by rw [M.property.1 B hB])]
      simp [Nat.mul_assoc]

/-- Each host edge has exactly `r` incident vertices. -/
theorem kahn_incidence_sum {n r : ℕ} (H : Kahn.Hypergraph n r)
    (g : Finset (Fin n) → ℝ) :
    (∑ v : Fin n, ∑ e : KahnIncident H v, g e.val) =
      (r : ℝ) * ∑ f ∈ H.edges, g f := by
  classical
  have hs : ∀ v : Fin n, (∑ e : KahnIncident H v, g e.val) =
      ∑ f ∈ H.edges, if v ∈ f then g f else 0 := by
    intro v
    rw [← sum_filter]
    symm
    exact sum_subtype _ (fun f => by simp [KahnIncident]) g
  simp_rw [hs]
  rw [sum_comm]
  simp_rw [← sum_filter]
  have hv : ∀ f : Finset (Fin n), univ.filter (· ∈ f) = f := by intro f; ext; simp
  simp_rw [hv, sum_const, nsmul_eq_mul]
  rw [mul_sum]
  exact sum_congr rfl fun f hf => by rw [H.uniform f hf]

/-- A single matching makes at most `n choose(r,2) κ` incidences nongeneric. -/
theorem kahn_bad_incidence_count {n r : ℕ} (H : Kahn.Hypergraph n r)
    (M : Kahn.PerfectMatching n r) (κ : ℕ)
    (hκ : ∀ q : Finset (Fin n), q.card = 2 →
      (H.edges.filter (q ⊆ ·)).card ≤ κ) :
    (∑ v : Fin n, ∑ e : KahnIncident H v,
      if M.Bad v (e.val.erase v) then (1 : ℝ) else 0) ≤
        (n : ℝ) * (r.choose 2) * κ := by
  classical
  calc
    _ ≤ ∑ v : Fin n, ∑ e : KahnIncident H v,
        if e.val ∈ matchingCollisionEdges H M then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro v _
      apply sum_le_sum
      intro e _
      by_cases hb : M.Bad v (e.val.erase v)
      · simp [hb, kahn_bad_mem_collision H M e.property.1 e.property.2 hb]
      · simp only [hb, ↓reduceIte]
        positivity
    _ = (r : ℝ) * (matchingCollisionEdges H M).card := by
      rw [kahn_incidence_sum H (fun f => if f ∈ matchingCollisionEdges H M then 1 else 0), sum_boole]
      congr 2
      congr 1
      ext f
      simp only [mem_filter, and_iff_right_iff_imp]
      intro hf
      obtain ⟨B, hB, hf⟩ := mem_biUnion.mp hf
      obtain ⟨q, hq, hf⟩ := mem_biUnion.mp hf
      exact (mem_filter.mp hf).1
    _ ≤ (r : ℝ) * (M.val.card * (r.choose 2) * κ : ℕ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast matchingCollisionEdges_card_le H M κ hκ)
        (Nat.cast_nonneg r)
    _ = _ := by
      have hn : (n : ℝ) = M.val.card * r := by exact_mod_cast M.card_blocks_mul
      push_cast
      rw [hn]
      ring

/-- The exact unweighted collision sum used in the manuscript, for any law on
perfect matchings and a uniform pair-degree bound. -/
theorem kahn_gamma_incidence_sum_le {n r : ℕ} (H : Kahn.Hypergraph n r)
    (μ : FiniteEntropy.Law (Kahn.MatchingIn H)) (κ : ℕ)
    (hκ : ∀ q : Finset (Fin n), q.card = 2 →
      (H.edges.filter (q ⊆ ·)).card ≤ κ) :
    (∑ v : Fin n, ∑ e : KahnIncident H v,
      Kahn.MatchingLaw.gamma μ v (e.val.erase v)) ≤
        (n : ℝ) * (r.choose 2) * κ := by
  classical
  unfold Kahn.MatchingLaw.gamma FiniteEntropy.Law.event
  have hs : (∑ v : Fin n, ∑ e : KahnIncident H v,
      ∑ M : Kahn.MatchingIn H, if M.val.Bad v (e.val.erase v) then μ.mass M else 0) =
      ∑ M : Kahn.MatchingIn H, μ.mass M *
        (∑ v : Fin n, ∑ e : KahnIncident H v,
          if M.val.Bad v (e.val.erase v) then (1 : ℝ) else 0) := by
    simp_rw [mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    rw [sum_comm]
  rw [hs]
  calc
    _ ≤ ∑ M : Kahn.MatchingIn H, μ.mass M *
        ((n : ℝ) * (r.choose 2) * κ) := by
      exact sum_le_sum fun M _ => mul_le_mul_of_nonneg_left
        (kahn_bad_incidence_count H M.val κ hκ) (μ.nonneg M)
    _ = _ := by rw [← sum_mul, μ.total, one_mul]

end LooseHamilton
