module

public import HittingTimeLooseHamilton.CycleSurgery
public import HittingTimeLooseHamilton.EdgeRoles

public section

/-! # Edge-set contraction and expansion

These statements use the actual mixed-cycle predicate. Ambient active sets
allow the deletion of private vertices without identifying distinct edge sets.
-/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty pair disjoint from the old marked ports is a new marker. -/
theorem new_pair_not_mem {markers : Finset (Finset V)} {q : Finset V}
    (hq : q.Nonempty) (hd : Disjoint q (originalPorts markers)) : q ∉ markers := by
  intro hqM
  obtain ⟨v, hv⟩ := hq
  exact disjoint_left.mp hd hv (mem_biUnion.mpr ⟨q, hqM, hv⟩)

/-- Delete the private block of an unmarked ordinary edge and retain its pair. -/
theorem contract_edge_role {r : ℕ} {markers edges : Finset (Finset V)}
    {e q : Finset V} (hr : 3 ≤ r) (hC : IsMixedCycle r markers edges)
    (he : e ∈ edges) (hd : Disjoint e (originalPorts markers))
    (hq : edgeEndpointPair markers edges e = q) :
    IsMixedCycleOn r (univ \ (e \ q)) (insert q markers) (edges.erase e) := by
  obtain ⟨C⟩ := hC
  let a : ↥edges := ⟨e, he⟩
  have hp : C.onUniv.endpointPair a = q := (C.edgeEndpointPair_eq hr a).symm.trans hq
  have hP : C.onUniv.privateBlock a = e \ q := by
    exact (C.private_eq_sdiff_endpointPair hr a).trans (congrArg (fun p => e \ p) hq)
  have D := C.onUniv.contractUnmarked a hd
  rw [hp, hP] at D
  exact ⟨D⟩

/-- There is at least one deleted private vertex for every r ≥ 3 edge role. -/
theorem private_complement_nonempty {r : ℕ} {e q : Finset V}
    (hr : 3 ≤ r) (he : e.card = r) (hq : q ∈ e.powersetCard 2) :
    (e \ q).Nonempty := by
  rw [← card_pos, card_sdiff_of_subset (mem_powersetCard.mp hq).1, he,
    (mem_powersetCard.mp hq).2]
  omega

/-- An edge containing a deleted private vertex cannot occur in a completion. -/
theorem expanded_edge_absent {r : ℕ} {markers F : Finset (Finset V)}
    {e q : Finset V} (hr : 3 ≤ r) (he : e.card = r) (hq : q ∈ e.powersetCard 2)
    (hC : IsMixedCycleOn r (univ \ (e \ q)) (insert q markers) F) : e ∉ F := by
  intro heF
  obtain ⟨D⟩ := hC
  obtain ⟨v, hv⟩ := private_complement_nonempty hr he hq
  have hvs := D.edge_subset_active heF (mem_sdiff.mp hv).1
  exact (mem_sdiff.mp hvs).2 hv

/-- Expansion restores the original edge and recovers exactly the prescribed role. -/
theorem expand_edge_role {r : ℕ} {markers F : Finset (Finset V)}
    {e q : Finset V} (hr : 3 ≤ r) (he : e.card = r) (hq : q ∈ e.powersetCard 2)
    (hd : Disjoint e (originalPorts markers))
    (hC : IsMixedCycleOn r (univ \ (e \ q)) (insert q markers) F) :
    IsMixedCycle r markers (insert e F) ∧
      edgeEndpointPair markers (insert e F) e = q := by
  have hqe := (mem_powersetCard.mp hq).1
  have hqc := (mem_powersetCard.mp hq).2
  have hqne : q.Nonempty := by rw [← card_pos, hqc]; omega
  have hqM : q ∉ markers := new_pair_not_mem hqne (hd.mono_left hqe)
  have hP : (e \ q).card = r - 2 := by rw [card_sdiff_of_subset hqe, he, hqc]
  have hPS : Disjoint (e \ q) (univ \ (e \ q)) := by
    apply disjoint_left.mpr
    intro v hv hvs
    exact (mem_sdiff.mp hvs).2 hv
  have hE : e ∉ F := expanded_edge_absent hr he hq hC
  have hUnion : q ∪ (e \ q) = e := union_sdiff_of_subset hqe
  obtain ⟨D⟩ := hC
  have hExpand : q ∪ (e \ q) ∉ F := by rwa [hUnion]
  have hX : ∃ A : MixedCycleOnWitness r ((univ \ (e \ q)) ∪ (e \ q))
      ((insert q markers).erase q) (insert (q ∪ (e \ q)) F),
      A.endpointPair ⟨q ∪ (e \ q), mem_insert_self _ _⟩ = q := by
    exact ⟨D.expand ⟨q, mem_insert_self _ _⟩ (e \ q) hP hPS hExpand,
      D.expand_endpointPair ⟨q, mem_insert_self _ _⟩ (e \ q) hP hPS hExpand⟩
  have hSu : (univ \ (e \ q)) ∪ (e \ q) = (univ : Finset V) := by
    ext v
    simp
  rw [hSu, erase_insert hqM, hUnion] at hX
  obtain ⟨A, hA⟩ := hX
  exact ⟨⟨A.toSpanning⟩, (A.toSpanning.edgeEndpointPair_eq hr ⟨e, mem_insert_self _ _⟩).trans hA⟩

end LooseHamilton
