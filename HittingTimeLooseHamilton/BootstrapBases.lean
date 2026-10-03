module

public import HittingTimeLooseHamilton.OriginalPortPartner
public import HittingTimeLooseHamilton.Operations

public section

/-! # Fixed bases for the marginal bootstrap
The index set depends only on the original matching. The forbidden port set is
always the restriction of the original ports, even after a marker is removed.
-/
noncomputable section
namespace LooseHamilton.BootstrapBases
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Base (M : Finset (Finset V)) := Option ↥(originalPorts M)

@[expose] def deleted {M : Finset (Finset V)} : Base M → Finset V
  | none => ∅
  | some a => {a.val}

@[expose] def active {M : Finset (Finset V)} (t : Base M) : Finset V := univ \ deleted t

@[expose] def markers {M : Finset (Finset V)} (hM : IsPairMatching M) : Base M → Finset (Finset V)
  | none => M
  | some a => M.erase {a.val, OriginalPortPartner.partner hM a}

@[expose] def fixedPorts {M : Finset (Finset V)} (t : Base M) : Finset ↥(active t) :=
  restrictedPorts (active t) (originalPorts M)

@[expose] def host {M : Finset (Finset V)} (r : ℕ) (H : SimpleHypergraph V) (t : Base M) :
    SimpleHypergraph ↥(active t) :=
  inducedHost (active t) (H ∩ allowedEdges r (originalPorts M))

omit [Fintype V] in
@[simp] theorem deleted_none (M : Finset (Finset V)) : deleted (none : Base M) = ∅ := rfl
omit [Fintype V] in
@[simp] theorem deleted_some {M : Finset (Finset V)} (a : ↥(originalPorts M)) :
    deleted (some a) = {a.val} := rfl
@[simp] theorem active_none (M : Finset (Finset V)) : active (none : Base M) = univ := by
  simp [active]
omit [Fintype V] in
@[simp] theorem markers_none {M : Finset (Finset V)} (hM : IsPairMatching M) :
    markers hM none = M := rfl
omit [Fintype V] in
@[simp] theorem markers_some {M : Finset (Finset V)} (hM : IsPairMatching M)
    (a : ↥(originalPorts M)) :
    markers hM (some a) = M.erase {a.val, OriginalPortPartner.partner hM a} := rfl

theorem card_bases {M : Finset (Finset V)} (hM : IsPairMatching M) :
    Fintype.card (Base M) = 1 + 2 * M.card := by
  simp [Base, hM.ports_card, Nat.add_comm]

theorem card_bases_le {M : Finset (Finset V)} (hM : IsPairMatching M) :
    Fintype.card (Base M) ≤ Fintype.card V + 1 := by
  rw [card_bases hM]
  have := hM.twice_card_le
  omega

omit [Fintype V] in
theorem deleted_card_le {M : Finset (Finset V)} (t : Base M) : (deleted t).card ≤ 1 := by
  cases t <;> simp [deleted]

omit [Fintype V] in
theorem markers_matching {M : Finset (Finset V)} (hM : IsPairMatching M) (t : Base M) :
    IsPairMatching (markers hM t) := by
  cases t with
  | none => exact hM
  | some a => exact OriginalPortPartner.remainder_matching hM a

theorem markers_retained {M : Finset (Finset V)} (hM : IsPairMatching M) (t : Base M)
    {e : Finset V} (he : e ∈ markers hM t) : e ⊆ active t := by
  cases t with
  | none => simp
  | some a =>
    intro v hv
    have ha := OriginalPortPartner.remainder_edge_avoids_self hM a he
    simp only [active, deleted, mem_sdiff, mem_univ, mem_singleton, true_and]
    exact fun h => ha (h ▸ hv)

/-- The original filter commutes with restriction, for every ambient host. -/
theorem host_eq {M : Finset (Finset V)} (r : ℕ) (H : SimpleHypergraph V) (t : Base M) :
    host r H t = inducedHost (active t) H ∩ allowedEdges r (fixedPorts t) := by
  rw [fixedPorts, ← inducedHost_allowed]
  ext e
  simp [host, mem_inducedHost]

@[simp] theorem mem_fixedPorts {M : Finset (Finset V)} (t : Base M) (v : ↥(active t)) :
    v ∈ fixedPorts t ↔ v.val ∈ originalPorts M := by
  simp [fixedPorts]

/-- In ambient coordinates the forbidden set is exactly U₀ ∩ (V \ D). -/
theorem ambient_fixedPorts {M : Finset (Finset V)} (t : Base M) :
    ambientEdge (active t) (fixedPorts t) = originalPorts M ∩ active t := by
  ext v
  simp [ambientEdge, fixedPorts, restrictedPorts, Finset.mem_map, and_comm]

/-- The partner survives deletion of the chosen original port. -/
theorem partner_survives {M : Finset (Finset V)} (hM : IsPairMatching M)
    (a : ↥(originalPorts M)) : OriginalPortPartner.partner hM a ∈ active (some a) := by
  simp [active, OriginalPortPartner.partner_ne hM a]

/-- The surviving partner remains forbidden although no remaining marker contains it. -/
theorem surviving_partner_filter {M : Finset (Finset V)} (hM : IsPairMatching M)
    (a : ↥(originalPorts M)) :
    (⟨OriginalPortPartner.partner hM a, partner_survives hM a⟩ : ↥(active (some a)))
      ∈ fixedPorts (some a) ∧
    OriginalPortPartner.partner hM a ∉ originalPorts (markers hM (some a)) := by
  exact ⟨(mem_fixedPorts _ _).mpr (OriginalPortPartner.partner_mem_ports hM a),
    OriginalPortPartner.partner_not_mem_remainder_ports hM a⟩

end LooseHamilton.BootstrapBases
