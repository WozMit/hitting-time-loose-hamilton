module

public import HittingTimeLooseHamilton.EndpointCutMatching
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

/-! Freshness and active-set identities for the inverses of endpoint cuts. -/
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z : V}

 theorem endpoint_source_matching
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) :
    ((insert {y,z} M : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  have hd : ∀ m ∈ M, Disjoint ({y,z} : Finset V) m := by
    intro m hm
    apply hs.ports_disjoint.mono subset_union_right
    intro v hv
    exact mem_biUnion.mpr ⟨m,hm,hv⟩
  intro m hm n hn hmn
  rcases mem_insert.mp hm with rfl | hm <;> rcases mem_insert.mp hn with rfl | hn
  · exact False.elim (hmn rfl)
  · exact hd n hn
  · exact (hd m hm).symm
  · exact hM hm hn hmn

theorem endpoint_source_pair_fresh (hs : LegalPrivateCompletion r M P {y,z}) :
    {y,z} ∉ M := by
  intro hm
  have hy : y ∈ P ∪ ({y,z} : Finset V) := by simp
  have hyM : y ∈ originalPorts M := mem_biUnion.mpr ⟨{y,z},hm,by simp⟩
  exact disjoint_left.mp hs.ports_disjoint hy hyM

private theorem restore_deleted (D : Finset V) (hd : Disjoint D P) :
    (univ \ (P ∪ D)) ∪ D = univ \ P := by
  ext v
  simp only [mem_union, mem_sdiff, mem_univ, true_and]
  constructor
  · rintro (h | h)
    · exact fun hp => h (Or.inl hp)
    · exact fun hp => disjoint_left.mp hd h hp
  · intro h
    by_cases hv : v ∈ D
    · exact Or.inr hv
    · exact Or.inl (fun hp => (hp.elim h hv))

namespace EndpointCutLegalI
variable {l : EndpointCutLabelI V}

theorem y_not_core (hl : EndpointCutLegalI r M G P y z l) :
    y ∉ univ \ (P ∪ l.deleted y) := by simp [EndpointCutLabelI.deleted]

theorem private_core_disjoint (hl : EndpointCutLegalI r M G P y z l) :
    Disjoint (univ \ (P ∪ l.deleted y)) l.2 := by
  apply disjoint_left.mpr
  intro v hv hR
  exact (mem_sdiff.mp hv).2 (mem_union_right _ (mem_insert_of_mem hR))

theorem y_not_private (hl : EndpointCutLegalI r M G P y z l) : y ∉ l.2 := by
  intro hy
  exact disjoint_left.mp hl.private_disjoint hy (by simp)

theorem deleted_disjoint (hl : EndpointCutLegalI r M G P y z l)
    (hs : LegalPrivateCompletion r M P {y,z}) : Disjoint (l.deleted y) P := by
  apply disjoint_left.mpr
  intro v hv hp
  rcases mem_insert.mp hv with rfl | hv
  · exact disjoint_left.mp hs.private_pair_disjoint hp (by simp)
  · exact disjoint_left.mp hl.private_disjoint hv (mem_union_left _ (mem_union_left _ hp))

theorem restore_active (hl : EndpointCutLegalI r M G P y z l)
    (hs : LegalPrivateCompletion r M P {y,z}) :
    (univ \ (P ∪ l.deleted y)) ∪ {y} ∪ l.2 = univ \ P := by
  rw [union_assoc, show ({y} : Finset V) ∪ l.2 = insert y l.2 from by ext v; simp]
  exact restore_deleted (l.deleted y) (hl.deleted_disjoint hs)

end EndpointCutLegalI

namespace EndpointCutLegalII
variable {l : EndpointCutLabelII V}

private theorem first_port (hl : EndpointCutLegalII r M G P y z l) : l.1 ∈ originalPorts M :=
  mem_biUnion.mpr ⟨l.oldMarker,hl.oldMarker_mem,by simp [EndpointCutLabelII.oldMarker]⟩
private theorem second_port (hl : EndpointCutLegalII r M G P y z l) : l.2.1 ∈ originalPorts M :=
  mem_biUnion.mpr ⟨l.oldMarker,hl.oldMarker_mem,by simp [EndpointCutLabelII.oldMarker]⟩

theorem added_injective (hl : EndpointCutLegalII r M G P y z l)
    (hs : LegalPrivateCompletion r M P {y,z}) : Function.Injective ![y,l.1,l.2.1] := by
  have hyu : y ≠ l.1 := by
    intro h
    exact disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp)) (h.symm ▸ hl.first_port)
  have hyv : y ≠ l.2.1 := by
    intro h
    exact disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp)) (h.symm ▸ hl.second_port)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [hl.ports_ne, Ne.symm hl.ports_ne, Ne.symm hyu, Ne.symm hyv]

theorem added_not_core (hl : EndpointCutLegalII r M G P y z l) (i : Fin 3) :
    ![y,l.1,l.2.1] i ∉ univ \ (P ∪ l.deleted y) := by
  fin_cases i <;> simp [EndpointCutLabelII.deleted]

theorem private_cards (hl : EndpointCutLegalII r M G P y z l) (i : Fin 2) :
    (![l.2.2.2.1,l.2.2.2.2] i).card = r-2 := by
  fin_cases i
  · exact hl.first_private_card
  · exact hl.second_private_card

theorem private_pairwise (hl : EndpointCutLegalII r M G P y z l) :
    Pairwise (fun i j : Fin 2 => Disjoint (![l.2.2.2.1,l.2.2.2.2] i) (![l.2.2.2.1,l.2.2.2.2] j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact hl.private_disjoint
  · exact hl.private_disjoint.symm
  · exact False.elim (hij rfl)

theorem private_core_disjoint (hl : EndpointCutLegalII r M G P y z l) (i : Fin 2) :
    Disjoint (univ \ (P ∪ l.deleted y)) (![l.2.2.2.1,l.2.2.2.2] i) := by
  apply disjoint_left.mpr
  intro v hv hR
  apply (mem_sdiff.mp hv).2
  apply mem_union_right
  fin_cases i
  · exact mem_union_left _ (mem_union_right _ hR)
  · exact mem_union_right _ hR

theorem added_not_private (hl : EndpointCutLegalII r M G P y z l) (i : Fin 3) (j : Fin 2) :
    ![y,l.1,l.2.1] i ∉ ![l.2.2.2.1,l.2.2.2.2] j := by
  have hi : ![y,l.1,l.2.1] i ∈ P ∪ originalPorts M ∪ {y,z,l.2.2.1} := by
    fin_cases i
    · simp
    · exact mem_union_left _ (mem_union_right _ hl.first_port)
    · exact mem_union_left _ (mem_union_right _ hl.second_port)
  intro h
  fin_cases j
  · exact disjoint_left.mp hl.first_private_disjoint h hi
  · exact disjoint_left.mp hl.second_private_disjoint h hi

theorem deleted_disjoint (hl : EndpointCutLegalII r M G P y z l)
    (hs : LegalPrivateCompletion r M P {y,z}) : Disjoint (l.deleted y) P := by
  apply disjoint_left.mpr
  intro v hv hp
  rcases mem_union.mp hv with hv | hv
  · rcases mem_union.mp hv with hv | hv
    · simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact disjoint_left.mp hs.private_pair_disjoint hp (by simp)
      · exact disjoint_left.mp hs.ports_disjoint (mem_union_left _ hp) hl.first_port
      · exact disjoint_left.mp hs.ports_disjoint (mem_union_left _ hp) hl.second_port
    · exact disjoint_left.mp hl.first_private_disjoint hv (mem_union_left _ (mem_union_left _ hp))
  · exact disjoint_left.mp hl.second_private_disjoint hv (mem_union_left _ (mem_union_left _ hp))

theorem restore_active (hl : EndpointCutLegalII r M G P y z l)
    (hs : LegalPrivateCompletion r M P {y,z}) :
    (univ \ (P ∪ l.deleted y)) ∪ {y,l.1,l.2.1} ∪ (l.2.2.2.1 ∪ l.2.2.2.2) = univ \ P := by
  simpa [EndpointCutLabelII.deleted, union_assoc] using restore_deleted (l.deleted y) (hl.deleted_disjoint hs)

end EndpointCutLegalII
end LooseHamilton
