module

public import HittingTimeLooseHamilton.Setup

public section

/-! # The partner of an original port
A fixed matching canonically determines the partner needed to index the
single-original-port deletion bases. This construction uses only the original
matching, and not an observed hypergraph.
-/
noncomputable section
namespace LooseHamilton.OriginalPortPartner
open Finset
variable {V : Type*} [DecidableEq V]
variable {M : Finset (Finset V)}

/-- Every original port lies in a marked pair with a distinct second endpoint. -/
theorem exists_partner (hM : IsPairMatching M) (a : ↥(originalPorts M)) :
    ∃ b : V, b ≠ a.val ∧ {a.val,b} ∈ M := by
  obtain ⟨e,he,ha⟩ := mem_biUnion.mp a.property
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp (hM.1 e he)
  rcases mem_insert.mp ha with h | h
  · subst x
    exact ⟨y,hxy.symm,he⟩
  · have hya : a.val = y := mem_singleton.mp h
    exact ⟨x,by simpa [hya] using hxy,by simpa [hya, pair_comm] using he⟩

/-- Partner chosen solely from the fixed original matching. -/
@[expose] def partner (hM : IsPairMatching M) (a : ↥(originalPorts M)) : V :=
  Classical.choose (exists_partner hM a)

theorem partner_ne (hM : IsPairMatching M) (a : ↥(originalPorts M)) :
    partner hM a ≠ a.val := (Classical.choose_spec (exists_partner hM a)).1

theorem pair_mem (hM : IsPairMatching M) (a : ↥(originalPorts M)) :
    {a.val,partner hM a} ∈ M := (Classical.choose_spec (exists_partner hM a)).2

/-- Uniqueness of the original marker containing the given port. -/
theorem pair_eq_of_mem (hM : IsPairMatching M) (a : ↥(originalPorts M))
    {e : Finset V} (he : e ∈ M) (ha : a.val ∈ e) :
    e = {a.val,partner hM a} := by
  by_contra hne
  exact disjoint_left.mp (hM.2 he (pair_mem hM a) hne) ha (by simp)

/-- Any distinct endpoint paired with the given port is its selected partner. -/
theorem partner_unique (hM : IsPairMatching M) (a : ↥(originalPorts M))
    {b : V} (hb : b ≠ a.val) (hp : {a.val,b} ∈ M) : b = partner hM a := by
  have he := pair_eq_of_mem hM a hp (by simp)
  have hm : b ∈ ({a.val,partner hM a} : Finset V) := by rw [← he]; simp
  simpa [hb] using hm

theorem partner_mem_ports (hM : IsPairMatching M) (a : ↥(originalPorts M)) :
    partner hM a ∈ originalPorts M :=
  mem_biUnion.mpr ⟨_,pair_mem hM a,by simp⟩

/-- Removing the pair removes both of its endpoints from the remaining markers. -/
theorem pair_disjoint_remainder (hM : IsPairMatching M) (a : ↥(originalPorts M)) :
    Disjoint ({a.val,partner hM a} : Finset V)
      (originalPorts (M.erase {a.val,partner hM a})) := by
  apply disjoint_left.mpr
  intro v hv hp
  obtain ⟨e,he,hve⟩ := mem_biUnion.mp hp
  exact disjoint_left.mp (hM.2 (pair_mem hM a) (mem_erase.mp he).2
    (mem_erase.mp he).1.symm) hv hve

theorem self_not_mem_remainder_ports (hM : IsPairMatching M)
    (a : ↥(originalPorts M)) :
    a.val ∉ originalPorts (M.erase {a.val,partner hM a}) := by
  exact fun h => disjoint_left.mp (pair_disjoint_remainder hM a) (by simp) h

theorem partner_not_mem_remainder_ports (hM : IsPairMatching M)
    (a : ↥(originalPorts M)) :
    partner hM a ∉ originalPorts (M.erase {a.val,partner hM a}) := by
  exact fun h => disjoint_left.mp (pair_disjoint_remainder hM a) (by simp) h

theorem remainder_matching (hM : IsPairMatching M) (a : ↥(originalPorts M)) :
    IsPairMatching (M.erase {a.val,partner hM a}) := by
  refine ⟨fun e he => hM.1 e (mem_erase.mp he).2, ?_⟩
  intro e he f hf hne
  exact hM.2 (mem_erase.mp he).2 (mem_erase.mp hf).2 hne

theorem remainder_edge_avoids_self (hM : IsPairMatching M)
    (a : ↥(originalPorts M)) {e : Finset V}
    (he : e ∈ M.erase {a.val,partner hM a}) : a.val ∉ e := by
  intro ha
  exact self_not_mem_remainder_ports hM a (mem_biUnion.mpr ⟨e,he,ha⟩)

end LooseHamilton.OriginalPortPartner
