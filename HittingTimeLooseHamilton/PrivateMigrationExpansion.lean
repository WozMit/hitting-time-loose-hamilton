module

public import HittingTimeLooseHamilton.PrivateMigrationData
public import HittingTimeLooseHamilton.ActiveCycleRoles

public section

/-! # Expanding a migration label into an output completion -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers host : Finset (Finset V)} {D q : Finset V}
  {x : V} {R uv : Finset V} {F : Finset (Finset V)}

theorem privateMigration_input_x_absent
    (hF : F ∈ privateMigrationInputFamily r markers host D q x R uv)
    {e : Finset V} (he : e ∈ F) : x ∉ e := by
  obtain ⟨⟨C⟩, _⟩ := (mem_privateMigrationInputFamily _ _ _ _ _ _ _ _ _).mp hF
  intro hx
  have := C.edge_subset_active he hx
  simpa using this

theorem privateMigration_new_edge_absent
    (hF : F ∈ privateMigrationInputFamily r markers host D q x R uv) :
    uv ∪ insert x R ∉ F := by
  intro he
  exact privateMigration_input_x_absent hF he (mem_union_right _ (mem_insert_self _ _))

theorem privateMigration_expand_mem (hr : 3 ≤ r)
    (h : PrivateMigrationLegal r markers host D q x R uv)
    (hF : F ∈ privateMigrationInputFamily r markers host D q x R uv) :
    insert (uv ∪ insert x R) F ∈ completionFamily r markers host D q := by
  obtain ⟨⟨C⟩, hFH⟩ := (mem_privateMigrationInputFamily _ _ _ _ _ _ _ _ _).mp hF
  have hPS : Disjoint (insert x R) (univ \ (D ∪ insert x R)) := by
    apply disjoint_left.mpr
    intro y hy hz
    exact (mem_sdiff.mp hz).2 (mem_union_right _ hy)
  have hS : (univ \ (D ∪ insert x R)) ∪ insert x R = univ \ D := by
    ext y
    have hd := h.private_deleted_disjoint
    simp only [mem_union, mem_sdiff, mem_univ, true_and]
    constructor
    · rintro (hy | hy)
      · exact fun hD => hy (Or.inl hD)
      · exact fun hD => disjoint_left.mp hd hy hD
    · intro hy
      by_cases hp : y ∈ insert x R
      · exact Or.inr hp
      · exact Or.inl (by simpa using And.intro hy hp)
  have hM : (insert uv (insert q markers)).erase uv = insert q markers :=
    erase_insert h.pair_not_mem
  have CE := C.expand ⟨uv, mem_insert_self _ _⟩ (insert x R)
    (h.private_card hr) hPS (privateMigration_new_edge_absent hF)
  apply (mem_completionFamily _ _ _ _ _ _).mpr
  refine ⟨?_, insert_subset h.edge_mem hFH⟩
  rw [hS, hM] at CE
  exact ⟨CE⟩

theorem privateMigration_expand_role (hr : 3 ≤ r)
    (h : PrivateMigrationLegal r markers host D q x R uv)
    (hF : F ∈ privateMigrationInputFamily r markers host D q x R uv) :
    edgeEndpointPair (insert q markers) (insert (uv ∪ insert x R) F)
      (uv ∪ insert x R) = uv := by
  obtain ⟨⟨C⟩, _⟩ := (mem_privateMigrationInputFamily _ _ _ _ _ _ _ _ _).mp hF
  have hPS : Disjoint (insert x R) (univ \ (D ∪ insert x R)) := by
    apply disjoint_left.mpr
    intro y hy hz
    exact (mem_sdiff.mp hz).2 (mem_union_right _ hy)
  let CE := C.expand ⟨uv, mem_insert_self _ _⟩ (insert x R)
    (h.private_card hr) hPS (privateMigration_new_edge_absent hF)
  have hp := CE.edgeEndpointPair_eq hr ⟨uv ∪ insert x R, mem_insert_self _ _⟩
  have hM : (insert uv (insert q markers)).erase uv = insert q markers :=
    erase_insert h.pair_not_mem
  have heq := hp.trans (C.expand_endpointPair _ _ _ _ _)
  simpa only [hM] using heq

@[simp] theorem privateMigration_erase_expand
    (hF : F ∈ privateMigrationInputFamily r markers host D q x R uv) :
    (insert (uv ∪ insert x R) F).erase (uv ∪ insert x R) = F :=
  erase_insert (privateMigration_new_edge_absent hF)

end LooseHamilton
