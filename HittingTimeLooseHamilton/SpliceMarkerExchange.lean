module

public import HittingTimeLooseHamilton.EndpointExpansionSlots
public import HittingTimeLooseHamilton.EndpointCutModels

public section
noncomputable section
namespace LooseHamilton
open Finset
variable {α : Type*} [DecidableEq α]

/-- Exchange two named markers while fixing each marker in the base family. -/
@[expose] def exchangeTwoInsertedEquiv (M : Finset α) (p q p' q' : α)
    (hp : p ∉ insert q M) (hq : q ∉ M)
    (hp' : p' ∉ insert q' M) (hq' : q' ∉ M) :
    ↥(insert p (insert q M)) ≃ ↥(insert p' (insert q' M)) :=
  (subtypeInsertEquivOption hp).trans
    ((Equiv.optionCongr (replaceInsertedEquiv M q q' hq hq')).trans
      (subtypeInsertEquivOption hp').symm)

@[simp] theorem exchangeTwoInsertedEquiv_first (M : Finset α) (p q p' q' : α)
    (hp : p ∉ insert q M) (hq : q ∉ M)
    (hp' : p' ∉ insert q' M) (hq' : q' ∉ M) :
    exchangeTwoInsertedEquiv M p q p' q' hp hq hp' hq' ⟨p, mem_insert_self _ _⟩ =
      ⟨p', mem_insert_self _ _⟩ := by
  simp [exchangeTwoInsertedEquiv, subtypeInsertEquivOption]

@[simp] theorem exchangeTwoInsertedEquiv_second (M : Finset α) (p q p' q' : α)
    (hp : p ∉ insert q M) (hq : q ∉ M)
    (hp' : p' ∉ insert q' M) (hq' : q' ∉ M) :
    exchangeTwoInsertedEquiv M p q p' q' hp hq hp' hq'
      ⟨q, mem_insert_of_mem (mem_insert_self _ _)⟩ =
      ⟨q', mem_insert_of_mem (mem_insert_self _ _)⟩ := by
  have hqp : q ≠ p := fun h => hp (h ▸ mem_insert_self q M)
  have hqp' : q' ≠ p' := fun h => hp' (h ▸ mem_insert_self q' M)
  simp [exchangeTwoInsertedEquiv, subtypeInsertEquivOption, hqp, hqp',
    replaceInsertedEquiv]

@[simp] theorem exchangeTwoInsertedEquiv_old (M : Finset α) (p q p' q' : α)
    (hp : p ∉ insert q M) (hq : q ∉ M)
    (hp' : p' ∉ insert q' M) (hq' : q' ∉ M) (a : ↥M) :
    exchangeTwoInsertedEquiv M p q p' q' hp hq hp' hq'
      ⟨a, mem_insert_of_mem (mem_insert_of_mem a.property)⟩ =
      ⟨a, mem_insert_of_mem (mem_insert_of_mem a.property)⟩ := by
  have hap : a.val ≠ p := fun h => hp (mem_insert_of_mem (h ▸ a.property))
  have haq : a.val ≠ q := fun h => hq (h ▸ a.property)
  have hap' : a.val ≠ p' := fun h => hp' (mem_insert_of_mem (h ▸ a.property))
  have haq' : a.val ≠ q' := fun h => hq' (h ▸ a.property)
  simp [exchangeTwoInsertedEquiv, subtypeInsertEquivOption, replaceInsertedEquiv,
    hap, haq, hap', haq']

section Matching
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjoin a marker disjoint from all existing ports. -/
theorem insert_marker_matching {M : Finset (Finset V)} {p : Finset V}
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hp : Disjoint p (originalPorts M)) :
    ((insert p M : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  have hd : ∀ m ∈ M, Disjoint p m := by
    intro m hm
    exact disjoint_left.mpr fun v hv hvm =>
      disjoint_left.mp hp hv (mem_biUnion.mpr ⟨m, hm, hvm⟩)
  intro m hm n hn hmn
  change m ∈ insert p M at hm
  change n ∈ insert p M at hn
  rcases mem_insert.mp hm with he | hm
  · subst m
    rcases mem_insert.mp hn with he | hn
    · exact False.elim (hmn he.symm)
    · exact hd n hn
  · rcases mem_insert.mp hn with he | hn
    · subst n
      exact (hd m hm).symm
    · exact hM hm hn hmn

/-- Adjoin two disjoint markers, both avoiding all old ports. -/
theorem insert_two_markers_matching {M : Finset (Finset V)} {p q : Finset V}
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hp : Disjoint p (originalPorts M)) (hq : Disjoint q (originalPorts M))
    (hpq : Disjoint p q) :
    ((insert p (insert q M) : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  apply insert_marker_matching (insert_marker_matching hM hq)
  apply disjoint_left.mpr
  intro v hv hvm
  change v ∈ (insert q M).biUnion id at hvm
  obtain ⟨m, hm, hvm⟩ := mem_biUnion.mp hvm
  rcases mem_insert.mp hm with he | hm
  · subst m
    exact disjoint_left.mp hpq hv hvm
  · exact disjoint_left.mp hp hv (mem_biUnion.mpr ⟨m, hm, hvm⟩)
end Matching
end LooseHamilton
