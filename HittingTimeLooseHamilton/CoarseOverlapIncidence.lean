module

public import HittingTimeLooseHamilton.CoarseOverlapAtoms

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy

lemma coarse_incident_mass {n r : ℕ} {H : Kahn.Hypergraph n r}
    (p : Law (Kahn.MatchingIn H)) (v : Fin n) (e : KahnIncident H v) :
    (kahnIncidentLaw p v).mass e = p.event (fun M => e.val ∈ M.val.val) := by
  classical
  change p.event (fun M => kahnIncidentEdge v M = e) = _
  congr 1
  funext M
  apply propext
  constructor
  · intro h
    have he := congrArg Subtype.val h
    change M.val.edge v = e.val at he
    rw [← he]
    exact M.val.edge_mem v
  · intro h
    apply Subtype.ext
    exact (M.val.eq_edge_of_mem h e.property.2).symm

/-- Every nonempty matching edge is seen at at least one of its vertices. -/
lemma coarse_edge_collision_le_incidence {n r : ℕ}
    (H : Kahn.Hypergraph n r) (p : Law (Kahn.MatchingIn H)) (hr : 0 < r) :
    (∑ e ∈ H.edges, (p.event (fun M => e ∈ M.val.val))^2) ≤
      ∑ v, ∑ e : KahnIncident H v, ((kahnIncidentLaw p v).mass e)^2 := by
  classical
  simp_rw [coarse_incident_mass]
  have he (v : Fin n) :
      (∑ e : KahnIncident H v, (p.event (fun M => e.val ∈ M.val.val))^2) =
      ∑ e ∈ H.edges, if v ∈ e then (p.event (fun M => e ∈ M.val.val))^2 else 0 := by
    rw [show (∑ e : KahnIncident H v, (p.event (fun M => e.val ∈ M.val.val))^2) =
      ∑ e ∈ (H.edges.filter (v ∈ ·)), (p.event (fun M => e ∈ M.val.val))^2 from
      (Finset.sum_subtype (H.edges.filter (v ∈ ·)) (p := fun e => e ∈ H.edges ∧ v ∈ e) (by simp) (fun e => (p.event (fun M => e ∈ M.val.val))^2)).symm]
    exact Finset.sum_filter _ _
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e he
  have hc : 0 < e.card := by rw [H.uniform e he]; exact hr
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hc
  calc
    _ = (if v ∈ e then (p.event (fun M => e ∈ M.val.val))^2 else 0) := by simp [hv]
    _ ≤ ∑ v : Fin n, if v ∈ e then (p.event (fun M => e ∈ M.val.val))^2 else 0 := by
      exact Finset.single_le_sum (f := fun w => if w ∈ e then (p.event (fun M => e ∈ M.val.val))^2 else 0) (fun w _ => by split_ifs <;> positivity) (Finset.mem_univ v)

end LooseHamilton
