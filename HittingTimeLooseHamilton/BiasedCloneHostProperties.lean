module

public import HittingTimeLooseHamilton.BiasedCloneHost

public section

noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cloneHost_project {G : SimpleHypergraph V} {U : Finset (V × Fin 3)}
    {B : Finset (V × Fin 3)} (hB : B ∈ cloneHost G U) : B.image Prod.fst ∈ G := by
  obtain ⟨hB,_⟩ := mem_filter.mp hB
  obtain ⟨e,he,hBe⟩ := mem_biUnion.mp hB
  simpa [directedCloneEdges_project hBe] using he

theorem cloneHost_fst_injective {G : SimpleHypergraph V} {U : Finset (V × Fin 3)}
    {B : Finset (V × Fin 3)} (hB : B ∈ cloneHost G U) :
    Set.InjOn Prod.fst (↑B : Set (V × Fin 3)) := by
  obtain ⟨hB,_⟩ := mem_filter.mp hB
  obtain ⟨e,_,hBe⟩ := mem_biUnion.mp hB
  exact directedCloneEdges_fst_injective hBe

theorem cloneHost_uniform (G : SimpleHypergraph V) (U : Finset (V × Fin 3))
    (r : ℕ) (hG : ∀ e∈G, e.card=r) : ∀ B∈cloneHost G U, B.card=r := by
  intro B hB
  rw [← card_image_iff.mpr (cloneHost_fst_injective hB)]
  exact hG _ (cloneHost_project hB)

theorem cloneHost_subset_slots (G : SimpleHypergraph V) (U : Finset (V × Fin 3)) :
    ∀ B∈cloneHost G U, B⊆U := by
  intro B hB
  exact (mem_filter.mp hB).2

theorem directedCloneEdge_injective (e : Finset V) :
    Function.Injective (fun p : V × V => directedCloneEdge e p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have ha : (a,(0:Fin 3)) ∈ directedCloneEdge e a b := by
    rw [mem_directedCloneEdge]; exact Or.inl ⟨rfl,rfl⟩
  have hb : (b,(1:Fin 3)) ∈ directedCloneEdge e a b := by
    rw [mem_directedCloneEdge]; exact Or.inr (Or.inl ⟨rfl,rfl⟩)
  change directedCloneEdge e a b = directedCloneEdge e c d at h
  rw [h, mem_directedCloneEdge] at ha hb
  have hac : a=c := by simpa using ha
  have hbd : b=d := by simpa using hb
  exact Prod.ext hac hbd

theorem directedCloneEdges_disjoint {e f : Finset V} (hef : e ≠ f) :
    Disjoint (directedCloneEdges e) (directedCloneEdges f) := by
  apply disjoint_left.mpr
  intro B hBe hBf
  exact hef ((directedCloneEdges_project hBe).symm.trans (directedCloneEdges_project hBf))
end LooseHamilton
