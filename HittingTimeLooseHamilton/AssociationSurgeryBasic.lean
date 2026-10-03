module

public import HittingTimeLooseHamilton.OneVertexSwitchingBasic

public section

noncomputable section
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two disjoint edges exchange their distinguished vertices. -/
@[expose] def associationSwitch (F : SimpleHypergraph V) (e f : Finset V) (z a : V) :
    SimpleHypergraph V :=
  insert (switchedEdge e z a) (insert (switchedEdge f a z) ((F.erase e).erase f))

structure AssociationSwitchValid (F : SimpleHypergraph V) (e f : Finset V) (z a : V) : Prop where
  e_mem : e ∈ F
  f_mem : f ∈ F
  disjoint : Disjoint e f
  z_mem : z ∈ e
  a_mem : a ∈ f
  new_e_absent : switchedEdge e z a ∉ F
  new_f_absent : switchedEdge f a z ∉ F

namespace AssociationSwitchValid
variable {F : SimpleHypergraph V} {e f : Finset V} {z a : V}
variable (h : AssociationSwitchValid F e f z a)
include h

lemma a_not_mem : a ∉ e := fun ha => Finset.disjoint_left.mp h.disjoint ha h.a_mem
lemma z_not_mem : z ∉ f := fun hz => Finset.disjoint_left.mp h.disjoint h.z_mem hz
lemma vertices_ne : z ≠ a := fun hz => h.a_not_mem (hz ▸ h.z_mem)
lemma edges_ne : e ≠ f := fun hf => h.z_not_mem (hf ▸ h.z_mem)

lemma switched_disjoint : Disjoint (switchedEdge e z a) (switchedEdge f a z) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  rcases (mem_switchedEdge _ _ _ _).mp hx with rfl | ⟨hxz,hxe⟩
  · exact switchedEdge_not_mem h.a_mem h.z_not_mem hx'
  · rcases (mem_switchedEdge _ _ _ _).mp hx' with rfl | ⟨_,hxf⟩
    · contradiction
    · exact Finset.disjoint_left.mp h.disjoint hxe hxf

lemma switched_ne : switchedEdge e z a ≠ switchedEdge f a z := by
  intro hh
  have hm : a ∈ switchedEdge e z a := by simp
  exact switchedEdge_not_mem h.a_mem h.z_not_mem (hh ▸ hm)

lemma f_mem_erase : f ∈ F.erase e := Finset.mem_erase.mpr ⟨h.edges_ne.symm,h.f_mem⟩
lemma new_f_notMem_erase : switchedEdge f a z ∉ (F.erase e).erase f :=
  fun hx => h.new_f_absent (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
lemma new_e_not_mem_insert : switchedEdge e z a ∉
    insert (switchedEdge f a z) ((F.erase e).erase f) := by
  simp only [Finset.mem_insert, not_or]
  exact ⟨h.switched_ne,fun hx => h.new_e_absent (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))⟩

/-- Additive counting identity for any natural-valued edge statistic. -/
lemma sum_switch_add (g : Finset V → ℕ) :
    (∑ b ∈ associationSwitch F e f z a, g b) + g e + g f =
      (∑ b ∈ F, g b) + g (switchedEdge e z a) + g (switchedEdge f a z) := by
  have h₁ := Finset.sum_erase_add F g h.e_mem
  have h₂ := Finset.sum_erase_add (F.erase e) g h.f_mem_erase
  rw [associationSwitch, Finset.sum_insert h.new_e_not_mem_insert,
    Finset.sum_insert h.new_f_notMem_erase]
  omega

lemma card : (associationSwitch F e f z a).card = F.card := by
  have hs := h.sum_switch_add (fun _ => 1)
  simpa using hs

lemma uniform {r : ℕ} (hF : F ⊆ completeEdges V r) :
    associationSwitch F e f z a ⊆ completeEdges V r := by
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [mem_completeEdges, switchedEdge_card h.z_mem h.a_not_mem]
    exact mem_completeEdges _ _ |>.mp (hF h.e_mem)
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · rw [mem_completeEdges, switchedEdge_card h.a_mem h.z_not_mem]
      exact mem_completeEdges _ _ |>.mp (hF h.f_mem)
    · exact hF (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb))

lemma degree (x : V) : vertexDegree (associationSwitch F e f z a) x = vertexDegree F x := by
  have hs := h.sum_switch_add (fun b => if x ∈ b then 1 else 0)
  have hsum (G : SimpleHypergraph V) : (∑ b ∈ G, if x ∈ b then 1 else 0) = vertexDegree G x := by
    simp [vertexDegree, Finset.sum_boole]
  rw [hsum, hsum] at hs
  by_cases hxz : x = z
  · subst x
    simp [h.z_mem,h.z_not_mem,h.vertices_ne] at hs
    omega
  · by_cases hxa : x = a
    · subst x
      simp [h.a_mem,h.a_not_mem,h.vertices_ne.symm] at hs
      omega
    · simp [hxz,hxa] at hs
      omega

lemma reverse : associationSwitch (associationSwitch F e f z a)
    (switchedEdge e z a) (switchedEdge f a z) a z = F := by
  simp only [associationSwitch, switchedEdge_reverse h.z_mem h.a_not_mem,
    switchedEdge_reverse h.a_mem h.z_not_mem]
  ext b
  simp only [Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl | ⟨_,_,rfl | rfl | ⟨_,_,hb⟩⟩)
    · exact h.e_mem
    · exact h.f_mem
    · contradiction
    · contradiction
    · exact hb
  · intro hb
    by_cases he : b = e
    · exact Or.inl he
    · by_cases hf : b = f
      · exact Or.inr (Or.inl hf)
      · exact Or.inr (Or.inr ⟨(fun hh => h.new_f_absent (hh ▸ hb)),
          (fun hh => h.new_e_absent (hh ▸ hb)), Or.inr (Or.inr ⟨hf,he,hb⟩)⟩)

end AssociationSwitchValid
end LooseHamilton
