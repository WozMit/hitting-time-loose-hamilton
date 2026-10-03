module

public import HittingTimeLooseHamilton.PrivateContraction
public import HittingTimeLooseHamilton.CompletionModels

public section

/-! # The actual private-block completion bijection

For a fixed unordered pair in an existing unmarked host edge, erasing that edge
and inserting it back are inverse maps of the two actual edge-set families.
-/
noncomputable section
open Finset
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Contracting a role gives a completion in the same host. -/
theorem erase_mem_completionFamily {r : ℕ} {markers host : Finset (Finset V)}
    {e q : Finset V} (hr : 3 ≤ r) (hd : Disjoint e (originalPorts markers))
    {E : Finset (Finset V)} (hE : E ∈ edgeRoleFamily r markers host e q) :
    E.erase e ∈ completionFamily r markers host (e \ q) q := by
  obtain ⟨hC, hH, he, hq⟩ := (mem_edgeRoleFamily _ _ _ _ _ _ hr).mp hE
  exact (mem_completionFamily _ _ _ _ _ _).mpr
    ⟨contract_edge_role hr hC he hd hq, (erase_subset _ _).trans hH⟩

/-- Every completion expands to a cycle in the specified role class. -/
theorem insert_mem_edgeRoleFamily {r : ℕ} {markers host : Finset (Finset V)}
    {e q : Finset V} (hr : 3 ≤ r) (he : e.card = r) (heH : e ∈ host)
    (hq : q ∈ e.powersetCard 2) (hd : Disjoint e (originalPorts markers))
    {F : Finset (Finset V)} (hF : F ∈ completionFamily r markers host (e \ q) q) :
    insert e F ∈ edgeRoleFamily r markers host e q := by
  obtain ⟨hC, hH⟩ := (mem_completionFamily _ _ _ _ _ _).mp hF
  obtain ⟨hC', hq'⟩ := expand_edge_role hr he hq hd hC
  exact (mem_edgeRoleFamily _ _ _ _ _ _ hr).mpr
    ⟨hC', insert_subset heH hH, mem_insert_self _ _, hq'⟩

/-- A genuine edge-set equivalence, not a count identity assumed as a premise. -/
@[expose] def edgeRoleCompletionEquiv {r : ℕ} {markers host : Finset (Finset V)}
    {e q : Finset V} (hr : 3 ≤ r) (he : e.card = r) (heH : e ∈ host)
    (hq : q ∈ e.powersetCard 2) (hd : Disjoint e (originalPorts markers)) :
    ↥(edgeRoleFamily r markers host e q) ≃
      ↥(completionFamily r markers host (e \ q) q) where
  toFun E := ⟨E.val.erase e, erase_mem_completionFamily hr hd E.property⟩
  invFun F := ⟨insert e F.val, insert_mem_edgeRoleFamily hr he heH hq hd F.property⟩
  left_inv E := by
    apply Subtype.ext
    exact insert_erase ((mem_edgeRoleFamily _ _ _ _ _ _ hr).mp E.property).2.2.1
  right_inv F := by
    apply Subtype.ext
    exact erase_insert (expanded_edge_absent hr he hq
      ((mem_completionFamily _ _ _ _ _ _).mp F.property).1)

/-- One endpoint-pair class is counted by exactly the corresponding completion count. -/
theorem edgeRole_card_eq_completionCount {r : ℕ} {markers host : Finset (Finset V)}
    {e q : Finset V} (hr : 3 ≤ r) (he : e.card = r) (heH : e ∈ host)
    (hq : q ∈ e.powersetCard 2) (hd : Disjoint e (originalPorts markers)) :
    (edgeRoleFamily r markers host e q).card =
      completionCount r markers host (e \ q) q := by
  have h := Fintype.card_congr (edgeRoleCompletionEquiv hr he heH hq hd)
  rw [Fintype.card_coe, Fintype.card_coe] at h
  exact h

/-- The manuscript's edge-count identity for an existing unmarked host edge. -/
theorem edge_count_identity {r : ℕ} {markers host : Finset (Finset V)}
    {e : Finset V} (hr : 3 ≤ r) (he : e.card = r) (heH : e ∈ host)
    (hd : Disjoint e (originalPorts markers)) :
    FiniteFamily.incidenceCount (unrestrictedCycleFamily r markers host) e =
      ∑ q ∈ e.powersetCard 2, completionCount r markers host (e \ q) q := by
  rw [edge_incidence_partition r markers host e hr]
  apply sum_congr rfl
  intro q hq
  exact edgeRole_card_eq_completionCount hr he heH hq hd

/-- For a uniform host, the size assumption follows from membership. -/
theorem edge_count_identity_of_uniform {r : ℕ} {markers host : Finset (Finset V)}
    {e : Finset V} (hr : 3 ≤ r) (hH : host ⊆ completeEdges V r) (heH : e ∈ host)
    (hd : Disjoint e (originalPorts markers)) :
    FiniteFamily.incidenceCount (unrestrictedCycleFamily r markers host) e =
      ∑ q ∈ e.powersetCard 2, completionCount r markers host (e \ q) q :=
  edge_count_identity hr ((mem_completeEdges _ _).mp (hH heH)) heH hd

/-- Without host membership, the incidence count vanishes; the indicator is essential. -/
theorem edge_count_identity_with_indicator {r : ℕ} {markers host : Finset (Finset V)}
    {e : Finset V} (hr : 3 ≤ r) (he : e.card = r)
    (hd : Disjoint e (originalPorts markers)) :
    FiniteFamily.incidenceCount (unrestrictedCycleFamily r markers host) e =
      if e ∈ host then ∑ q ∈ e.powersetCard 2, completionCount r markers host (e \ q) q
      else 0 := by
  split_ifs with heH
  · exact edge_count_identity hr he heH hd
  · unfold FiniteFamily.incidenceCount
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro E hE
    obtain ⟨hE, heE⟩ := mem_filter.mp hE
    exact heH (((mem_unrestrictedCycleFamily _ _ _ _ hr).mp hE).2 heE)

end LooseHamilton
