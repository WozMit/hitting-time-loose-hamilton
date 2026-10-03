module

public import HittingTimeLooseHamilton.BiasedCloneMatching
public import HittingTimeLooseHamilton.PathRegularityModels

public section

/-! The actual clone host uses the one uncoloured private slot and two directed
junction slots. It is restricted to an explicitly given active slot set. -/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def directedCloneEdge (e : Finset V) (a b : V) : Finset (V × Fin 3) :=
  {(a,0), (b,1)} ∪ (e \ {a,b}).image (fun v => (v,2))

@[expose] def directedCloneEdges (e : Finset V) : Finset (Finset (V × Fin 3)) :=
  ((e ×ˢ e).filter (fun p => p.1 ≠ p.2)).image (fun p => directedCloneEdge e p.1 p.2)

@[expose] def cloneHost (G : SimpleHypergraph V) (U : Finset (V × Fin 3)) :
    SimpleHypergraph (V × Fin 3) :=
  (G.biUnion directedCloneEdges).filter (fun B => B ⊆ U)

theorem directedCloneEdges_card_le (e : Finset V) :
    (directedCloneEdges e).card ≤ e.card * e.card := by
  exact (card_image_le.trans (card_filter_le _ _)).trans_eq (card_product _ _)

theorem directedCloneEdge_project (e : Finset V) {a b : V} (ha : a ∈ e) (hb : b ∈ e) :
    (directedCloneEdge e a b).image Prod.fst = e := by
  ext v
  simp only [directedCloneEdge, image_union, image_insert, image_singleton,
    image_image, Function.comp_def]
  simp only [mem_union, mem_insert, mem_singleton, mem_image, mem_sdiff]
  constructor
  · rintro (h | ⟨w, hw, rfl⟩)
    · rcases h with rfl | rfl <;> assumption
    · exact hw.1
  · intro hv
    by_cases h₁ : v = a
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : v = b
    · exact Or.inl (Or.inr h₂)
    exact Or.inr ⟨v, ⟨hv, by simp [h₁,h₂]⟩, rfl⟩

theorem directedCloneEdges_project {e : Finset V} {B : Finset (V × Fin 3)}
    (hB : B ∈ directedCloneEdges e) : B.image Prod.fst = e := by
  obtain ⟨⟨a,b⟩, hab, rfl⟩ := mem_image.mp hB
  obtain ⟨hab, _⟩ := mem_filter.mp hab
  exact directedCloneEdge_project e (mem_product.mp hab).1 (mem_product.mp hab).2

theorem mem_directedCloneEdge {e : Finset V} {a b v : V} {t : Fin 3} :
    (v,t) ∈ directedCloneEdge e a b ↔
    (v=a ∧ t=0) ∨ (v=b ∧ t=1) ∨ (v∈e ∧ v≠a ∧ v≠b ∧ t=2) := by
  simp [directedCloneEdge, Prod.ext_iff, and_assoc, eq_comm]

theorem directedCloneEdge_fst_injective (e : Finset V) (a b : V) (hab : a ≠ b) :
    Set.InjOn Prod.fst (↑(directedCloneEdge e a b) : Set (V × Fin 3)) := by
  rintro ⟨v,t⟩ hx ⟨w,u⟩ hy hv
  change v=w at hv
  subst w
  change (v,t) ∈ directedCloneEdge e a b at hx
  change (v,u) ∈ directedCloneEdge e a b at hy
  rw [mem_directedCloneEdge] at hx hy
  rcases hx with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨hv,hva,hvb,rfl⟩ <;>
    rcases hy with ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨_,h₁,h₂,rfl⟩ <;> simp_all

theorem directedCloneEdges_fst_injective {e : Finset V} {B : Finset (V × Fin 3)}
    (hB : B ∈ directedCloneEdges e) : Set.InjOn Prod.fst (↑B : Set (V × Fin 3)) := by
  obtain ⟨⟨a,b⟩, hab, rfl⟩ := mem_image.mp hB
  exact directedCloneEdge_fst_injective e a b (mem_filter.mp hab).2

theorem cloneHost_degree_le (G : SimpleHypergraph V) (U : Finset (V × Fin 3))
    (r : ℕ) (hG : ∀ e∈G, e.card=r) (x : V × Fin 3) :
    vertexDegree (cloneHost G U) x ≤ r*r*vertexDegree G x.1 := by
  calc
    _ ≤ ((G.filter (fun e => x.1∈e)).biUnion directedCloneEdges).card := by
      apply card_le_card
      intro B hB
      obtain ⟨hB,hx⟩ := mem_filter.mp hB
      obtain ⟨hB,_⟩ := mem_filter.mp hB
      obtain ⟨e,he,hBe⟩ := mem_biUnion.mp hB
      exact mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he,
        (directedCloneEdges_project hBe) ▸ mem_image_of_mem Prod.fst hx⟩, hBe⟩
    _ ≤ (G.filter (fun e => x.1∈e)).card * (r*r) := by
      apply card_biUnion_le_card_mul
      intro e he
      simpa [hG e (mem_filter.mp he).1] using directedCloneEdges_card_le e
    _ = _ := by simp [vertexDegree, Nat.mul_comm]

theorem cloneHost_pairDegree_le (G : SimpleHypergraph V) (U : Finset (V × Fin 3))
    (r : ℕ) (hG : ∀ e∈G, e.card=r) (x y : V × Fin 3) :
    pairDegree (cloneHost G U) x y ≤ r*r*pairDegree G x.1 y.1 := by
  calc
    _ ≤ ((G.filter (fun e => x.1∈e ∧ y.1∈e)).biUnion directedCloneEdges).card := by
      apply card_le_card
      intro B hB
      obtain ⟨hB,hx,hy⟩ := mem_filter.mp hB
      obtain ⟨hB,_⟩ := mem_filter.mp hB
      obtain ⟨e,he,hBe⟩ := mem_biUnion.mp hB
      refine mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, ?_, ?_⟩, hBe⟩
      · exact (directedCloneEdges_project hBe) ▸ mem_image_of_mem Prod.fst hx
      · exact (directedCloneEdges_project hBe) ▸ mem_image_of_mem Prod.fst hy
    _ ≤ (G.filter (fun e => x.1∈e ∧ y.1∈e)).card * (r*r) := by
      apply card_biUnion_le_card_mul
      intro e he
      simpa [hG e (mem_filter.mp he).1] using directedCloneEdges_card_le e
    _ = _ := by simp [pairDegree, Nat.mul_comm]

theorem cloneHost_pairDegree_same_projection (G : SimpleHypergraph V)
    (U : Finset (V × Fin 3)) {x y : V × Fin 3} (hxy : x≠y) (hfst : x.1=y.1) :
    pairDegree (cloneHost G U) x y = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro B hB
  obtain ⟨hB,hx,hy⟩ := mem_filter.mp hB
  obtain ⟨hB,_⟩ := mem_filter.mp hB
  obtain ⟨e,_,he⟩ := mem_biUnion.mp hB
  exact hxy (directedCloneEdges_fst_injective he hx hy hfst)
end LooseHamilton
