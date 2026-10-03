module

public import HittingTimeLooseHamilton.BiasedCloneHostProperties

public section

noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Slot universe before the marker-occupied slots are removed. -/
@[expose] def fullCloneSlots (A : Finset V) : Finset (V × Fin 3) :=
  univ.filter (fun p => (p.1∈A ∧ (p.2=0 ∨ p.2=1)) ∨ (p.1∉A ∧ p.2=2))

@[simp] theorem mem_fullCloneSlots (A : Finset V) (v : V) (t : Fin 3) :
    (v,t) ∈ fullCloneSlots A ↔ (v∈A ∧ (t=0 ∨ t=1)) ∨ (v∉A ∧ t=2) := by
  simp [fullCloneSlots]

theorem directedCloneEdge_subset_full (e A : Finset V) {a b : V}
    (ha : a∈e) (hb : b∈e) :
    directedCloneEdge e a b ⊆ fullCloneSlots A ↔ e∩A={a,b} := by
  constructor
  · intro h
    have haA : a∈A := by
      have hx := h (show (a,(0:Fin 3))∈directedCloneEdge e a b by simp [mem_directedCloneEdge])
      simpa using hx
    have hbA : b∈A := by
      have hx := h (show (b,(1:Fin 3))∈directedCloneEdge e a b by simp [mem_directedCloneEdge])
      simpa using hx
    ext v
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hv,hvA⟩
      by_contra hn
      have hva : v≠a := fun he => hn (Or.inl he)
      have hvb : v≠b := fun he => hn (Or.inr he)
      have hx := h (show (v,(2:Fin 3))∈directedCloneEdge e a b by
        simp [mem_directedCloneEdge,hv,hva,hvb])
      simp [hvA] at hx
    · rintro (rfl | rfl) <;> exact ⟨by assumption, by assumption⟩
  · intro h x hx
    obtain ⟨v,t⟩ := x
    rw [mem_directedCloneEdge] at hx
    have haA : a∈A := (mem_inter.mp (h ▸ (by simp : a∈({a,b}:Finset V)))).2
    have hbA : b∈A := (mem_inter.mp (h ▸ (by simp : b∈({a,b}:Finset V)))).2
    rcases hx with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨hv,hva,hvb,rfl⟩
    · simp [haA]
    · simp [hbA]
    · have hvA : v∉A := by
        intro hvA
        have hh : v∈({a,b}:Finset V) := h ▸ mem_inter.mpr ⟨hv,hvA⟩
        simpa [hva,hvb] using hh
      simp [hvA]

theorem compatibleCloneEdges_card (e A : Finset V) :
    ((directedCloneEdges e).filter (fun B => B ⊆ fullCloneSlots A)).card =
      if (e∩A).card=2 then 2 else 0 := by
  classical
  by_cases he : (e∩A).card=2
  · obtain ⟨a,b,hab,heq⟩ := card_eq_two.mp he
    have ha : a∈e := (mem_inter.mp (heq ▸ (by simp : a∈({a,b}:Finset V)))).1
    have hb : b∈e := (mem_inter.mp (heq ▸ (by simp : b∈({a,b}:Finset V)))).1
    have hf : (directedCloneEdges e).filter (fun B => B ⊆ fullCloneSlots A) =
        {directedCloneEdge e a b, directedCloneEdge e b a} := by
      ext B
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hB,hU⟩
        obtain ⟨⟨c,d⟩,hcd,rfl⟩ := mem_image.mp hB
        obtain ⟨hcd,hne⟩ := mem_filter.mp hcd
        obtain ⟨hc,hd⟩ := mem_product.mp hcd
        have heq' := (directedCloneEdge_subset_full e A hc hd).mp hU
        have hc' : c=a ∨ c=b := by
          have hh : c∈({a,b}:Finset V) := heq ▸ (heq' ▸ (by simp : c∈({c,d}:Finset V)))
          simpa using hh
        have hd' : d=a ∨ d=b := by
          have hh : d∈({a,b}:Finset V) := heq ▸ (heq' ▸ (by simp : d∈({c,d}:Finset V)))
          simpa using hh
        rcases hc' with rfl | rfl <;> rcases hd' with rfl | rfl
        · exact (hne rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hne rfl).elim
      · rintro (rfl | rfl)
        · exact ⟨mem_image.mpr ⟨(a,b), mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab⟩,rfl⟩,
            (directedCloneEdge_subset_full e A ha hb).mpr heq⟩
        · exact ⟨mem_image.mpr ⟨(b,a), mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩,hab.symm⟩,rfl⟩,
            (directedCloneEdge_subset_full e A hb ha).mpr (heq.trans (pair_comm a b))⟩
    rw [hf, if_pos he, card_pair]
    intro h
    have hh : (a,b)=(b,a) := directedCloneEdge_injective e (a₁ := (a,b)) (a₂ := (b,a)) h
    exact hab (congrArg Prod.fst hh)
  · rw [if_neg he, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro B hB
    obtain ⟨hB,hU⟩ := mem_filter.mp hB
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hB
    obtain ⟨hab,hne⟩ := mem_filter.mp hab
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    have hh := (directedCloneEdge_subset_full e A ha hb).mp hU
    exact he (by rw [hh, card_pair hne])
end LooseHamilton
