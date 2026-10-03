module

public import HittingTimeLooseHamilton.BootstrapPrivateMobility
public import HittingTimeLooseHamilton.BootstrapEndpointMobility
public import HittingTimeLooseHamilton.SequentialMobilityLabels

public section

/-! Concrete ordered states for private-then-endpoint migration. -/
noncomputable section
namespace LooseHamilton.SequentialCompletion
open Finset Migration
variable {V : Type*} [Fintype V] [DecidableEq V]

structure State (V : Type*) (d : ℕ) where
  coords : Fin d → V
  first : V
  second : V

@[expose] def State.block {d : ℕ} (s : State V d) : Finset V := univ.image s.coords

@[expose] def State.weight {d : ℕ} (s : State V d) (r : ℕ) (M H : SimpleHypergraph V) : ℕ :=
  completionCount r M H s.block {s.first,s.second}

@[expose] def State.Valid {d r : ℕ} (s : State V d) (M : SimpleHypergraph V) : Prop :=
  Function.Injective s.coords ∧ LegalPrivateCompletion r M s.block {s.first,s.second}

@[expose] def State.replacePrivate {d : ℕ} (s : State V d) (i : Fin d) (v : V) : State V d :=
  ⟨Function.update s.coords i v,s.first,s.second⟩

@[expose] def State.replaceFirst {d : ℕ} (s : State V d) (v : V) : State V d :=
  ⟨s.coords,v,s.second⟩

@[expose] def State.replaceSecond {d : ℕ} (s : State V d) (v : V) : State V d :=
  ⟨s.coords,s.first,v⟩

@[expose] def State.remainder {d : ℕ} (s : State V d) (i : Fin d) : Finset V :=
  (univ.erase i).image s.coords

theorem block_eq_insert {d : ℕ} (s : State V d) (i : Fin d) :
    s.block = insert (s.coords i) (s.remainder i) := by
  classical
  simp only [State.block, State.remainder]
  rw [← image_insert, insert_erase (mem_univ i)]

theorem replacePrivate_block {d : ℕ} (s : State V d) (i : Fin d) (v : V) :
    (s.replacePrivate i v).block = insert v (s.remainder i) := by
  classical
  ext x
  simp only [State.block, State.replacePrivate, State.remainder, mem_image,
    mem_univ, true_and, mem_insert, mem_erase, ne_eq]
  constructor
  · rintro ⟨j,hj⟩
    by_cases h : j=i
    · subst j; exact Or.inl (by simpa using hj.symm)
    · exact Or.inr ⟨j,⟨h,trivial⟩,by simpa [Function.update_of_ne h] using hj⟩
  · rintro (rfl | ⟨j,⟨hj,_⟩,he⟩)
    · exact ⟨i,by simp⟩
    · exact ⟨j,by simpa [Function.update_of_ne hj] using he⟩

theorem remainder_card {d : ℕ} (s : State V d) (hi : Function.Injective s.coords)
    (i : Fin d) : (s.remainder i).card = d-1 := by
  classical
  rw [State.remainder, card_image_of_injective _ hi, card_erase_of_mem (mem_univ i)]
  simp

theorem replacePrivate_injective {d : ℕ} (s : State V d)
    (hi : Function.Injective s.coords) (i : Fin d) (v : V)
    (hv : v ∉ s.remainder i) : Function.Injective (s.replacePrivate i v).coords := by
  classical
  intro a b hab
  change Function.update s.coords i v a = Function.update s.coords i v b at hab
  by_cases ha : a=i <;> by_cases hb : b=i
  · exact ha.trans hb.symm
  · subst a
    simp only [Function.update_self, Function.update_of_ne hb] at hab
    exact False.elim (hv (mem_image.mpr ⟨b,mem_erase.mpr ⟨hb,mem_univ _⟩,hab.symm⟩))
  · subst b
    simp only [Function.update_self, Function.update_of_ne ha] at hab
    exact False.elim (hv (mem_image.mpr ⟨a,mem_erase.mpr ⟨ha,mem_univ _⟩,hab⟩))
  · exact hi (by simpa [Function.update_of_ne ha,Function.update_of_ne hb] using hab)

/-- The schedule is defined on every history, including unsuccessful ones. -/
@[expose] def advance {d : ℕ} (k : ℕ) (s : State V d) (v : V) : State V d :=
  if hk : k<d then s.replacePrivate ⟨k,hk⟩ v
  else if k=d then s.replaceFirst v else s.replaceSecond v

@[expose] def stateAt {d : ℕ} (s : State V d) : (k : ℕ) → ChoicePath V k → State V d
  | 0, _ => s
  | k+1, p => advance k (stateAt s k p.1) p.2

@[simp] theorem stateAt_zero {d : ℕ} (s : State V d) (p : ChoicePath V 0) :
    stateAt s 0 p = s := rfl

@[simp] theorem stateAt_succ {d : ℕ} (s : State V d) (k : ℕ)
    (p : ChoicePath V k) (v : V) :
    stateAt s (k+1) (p,v) = advance k (stateAt s k p) v := rfl

/-- Legality after an endpoint move follows from avoiding the fixed ports,
private vertices and the retained endpoint. -/
theorem replaceFirst_valid {d r : ℕ} (s : State V d) (M : SimpleHypergraph V)
    (hs : s.Valid (r := r) M) (v : V)
    (hv : v ∉ s.block ∪ originalPorts M ∪ {s.second}) :
    (s.replaceFirst v).Valid (r := r) M := by
  refine ⟨hs.1,hs.2.private_card,?_,?_,?_⟩
  · have hn : v ≠ s.second := by intro he; apply hv; simp [he]
    simp [State.replaceFirst, hn]
  · apply disjoint_left.mpr
    intro x hx hxq
    change x ∈ {v,s.second} at hxq
    rcases mem_insert.mp hxq with rfl | hh
    · exact hv (mem_union_left _ (mem_union_left _ hx))
    · exact disjoint_left.mp hs.2.private_pair_disjoint hx (mem_insert_of_mem hh)
  · apply disjoint_left.mpr
    intro x hx hxM
    change x ∈ s.block ∪ {v,s.second} at hx
    rcases mem_union.mp hx with hp | hq
    · exact disjoint_left.mp hs.2.ports_disjoint (mem_union_left _ hp) hxM
    · rcases mem_insert.mp hq with rfl | hh
      · exact hv (mem_union_left _ (mem_union_right _ hxM))
      · exact disjoint_left.mp hs.2.ports_disjoint (by simp only [mem_union, mem_insert]; exact Or.inr (Or.inr hh)) hxM

theorem replacePrivate_valid {r : ℕ} (hr : 3 ≤ r) (s : State V (r-2))
    (M : SimpleHypergraph V) (hs : s.Valid (r := r) M) (i : Fin (r-2)) (v : V)
    (hv : LegalPrivateCompletion r M (insert v (s.remainder i)) {s.first,s.second}) :
    (s.replacePrivate i v).Valid (r := r) M := by
  have hn : v ∉ s.remainder i := by
    intro hm
    have hcard := hv.private_card
    rw [insert_eq_of_mem hm, remainder_card s hs.1 i] at hcard
    omega
  refine ⟨replacePrivate_injective s hs.1 i v hn,?_⟩
  change LegalPrivateCompletion r M (s.replacePrivate i v).block {s.first,s.second}
  rw [replacePrivate_block]
  exact hv

@[expose] def State.swap {d : ℕ} (s : State V d) : State V d := ⟨s.coords,s.second,s.first⟩

theorem swap_valid {d r : ℕ} (s : State V d) (M : SimpleHypergraph V)
    (hs : s.Valid (r := r) M) : s.swap.Valid (r := r) M := by
  simpa only [State.Valid,State.swap,State.block,pair_comm] using hs

theorem replaceSecond_valid {d r : ℕ} (s : State V d) (M : SimpleHypergraph V)
    (hs : s.Valid (r := r) M) (v : V)
    (hv : v ∉ s.block ∪ originalPorts M ∪ {s.first}) :
    (s.replaceSecond v).Valid (r := r) M := by
  have hh := replaceFirst_valid s.swap M (swap_valid s M hs) v hv
  exact swap_valid (s.swap.replaceFirst v) M hh

end LooseHamilton.SequentialCompletion
