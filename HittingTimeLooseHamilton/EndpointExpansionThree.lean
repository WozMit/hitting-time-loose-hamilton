module

public import HittingTimeLooseHamilton.EndpointExpansionOne
public import HittingTimeLooseHamilton.EndpointExpansionSlots

public section
noncomputable section
open Finset
namespace LooseHamilton
variable {α : Type*} [DecidableEq α]
@[expose] def twoAddedShuffle (A : Type*) : (A ⊕ Fin 2) ≃ ((A ⊕ Fin 1) ⊕ Fin 1) where
  toFun s := match s with
    | .inl a => .inl (.inl a)
    | .inr i => if i = 0 then .inr 0 else .inl (.inr 0)
  invFun s := match s with
    | .inl (.inl a) => .inl a
    | .inl (.inr _) => .inr 1
    | .inr _ => .inr 0
  left_inv s := by
    rcases s with a | i
    · rfl
    · fin_cases i <;> simp
  right_inv s := by
    rcases s with ((a | i) | j)
    · rfl
    · fin_cases i; rfl
    · fin_cases j; rfl

@[expose] def twoEdgeInsertEquiv (E : Finset α) (e₁ e₂ : α)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) :
    (↥E ⊕ Fin 2) ≃ ↥(insert e₁ (insert e₂ E)) :=
  (twoAddedShuffle _).trans
    ((Equiv.sumCongr (edgeInsertEquiv E e₂ he₂) (Equiv.refl _)).trans
      (edgeInsertEquiv (insert e₂ E) e₁ he₁))
@[simp] theorem twoEdgeInsertEquiv_old (E : Finset α) (e₁ e₂ : α)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) (e : ↥E) :
    twoEdgeInsertEquiv E e₁ e₂ he₂ he₁ (.inl e) =
      ⟨e,mem_insert_of_mem (mem_insert_of_mem e.property)⟩ := rfl
@[simp] theorem twoEdgeInsertEquiv_zero (E : Finset α) (e₁ e₂ : α)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) :
    twoEdgeInsertEquiv E e₁ e₂ he₂ he₁ (.inr 0) = ⟨e₁,mem_insert_self _ _⟩ := rfl
@[simp] theorem twoEdgeInsertEquiv_one (E : Finset α) (e₁ e₂ : α)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) :
    twoEdgeInsertEquiv E e₁ e₂ he₂ he₁ (.inr 1) =
      ⟨e₂,mem_insert_of_mem (mem_insert_self _ _)⟩ := rfl

namespace MixedCycleOnWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {M E : Finset (Finset V)}
variable {z a y u v : V} {R₁ R₂ : Finset V}

@[expose] def threePathSlots (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (ho : {u,v} ∉ insert {z,y} M)
    (he₂ : {v,a} ∪ R₂ ∉ E) (he₁ : {y,u} ∪ R₁ ∉ insert ({v,a} ∪ R₂) E) :
    Fin (C.length+3) ≃
      (↥(insert {z,y} (insert {u,v} M)) ⊕ ↥(insert ({y,u} ∪ R₁) (insert ({v,a} ∪ R₂) E))) :=
  (endpointInsertEquiv C.length 3 (by have := C.length_ge; omega)).symm |>.trans
    ((Equiv.sumCongr C.slot (Equiv.refl (Fin 3))).trans
      (spliceSlotsII M E {z,a} {z,y} {u,v} ({y,u} ∪ R₁) ({v,a} ∪ R₂) hp hq ho he₂ he₁))

set_option maxHeartbeats 800000 in
@[simp] theorem threePathSlots_old (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (ho : {u,v} ∉ insert {z,y} M)
    (he₂ : {v,a} ∪ R₂ ∉ E) (he₁ : {y,u} ∪ R₁ ∉ insert ({v,a} ∪ R₂) E)
    (i : Fin C.length) :
    (C.threePathSlots (V := V) (r := r) (S := S) (M := M) (E := E) (z := z) (a := a) (y := y) (u := u) (v := v)
      (R₁ := R₁) (R₂ := R₂) hp hq ho he₂ he₁) (endpointKeep C.length 3 i) =
      spliceSlotsII M E {z,a} {z,y} {u,v} ({y,u} ∪ R₁) ({v,a} ∪ R₂)
        hp hq ho he₂ he₁ (Sum.inl (C.slot i) : (↥(insert {z,a} M) ⊕ ↥E) ⊕ Fin 3) := by
  have hi : (endpointInsertEquiv C.length 3 (by have := C.length_ge; omega)).symm
      (endpointKeep C.length 3 i) = .inl i :=
    (endpointInsertEquiv C.length 3 (by have := C.length_ge; omega)).symm_apply_apply (.inl i)
  simp only [threePathSlots, Equiv.trans_apply, hi]
  rfl

set_option maxHeartbeats 800000 in
@[simp] theorem threePathSlots_new (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (ho : {u,v} ∉ insert {z,y} M)
    (he₂ : {v,a} ∪ R₂ ∉ E) (he₁ : {y,u} ∪ R₁ ∉ insert ({v,a} ∪ R₂) E)
    (i : Fin 3) :
    (C.threePathSlots (V := V) (r := r) (S := S) (M := M) (E := E) (z := z) (a := a) (y := y) (u := u) (v := v)
      (R₁ := R₁) (R₂ := R₂) hp hq ho he₂ he₁) ⟨i.val+1,by have := C.length_ge; omega⟩ =
      spliceSlotsII M E {z,a} {z,y} {u,v} ({y,u} ∪ R₁) ({v,a} ∪ R₂)
        hp hq ho he₂ he₁ (Sum.inr i : (↥(insert {z,a} M) ⊕ ↥E) ⊕ Fin 3) := by
  have hi : (endpointInsertEquiv C.length 3 (by have := C.length_ge; omega)).symm
      ⟨i.val+1,by have := C.length_ge; omega⟩ = .inr i :=
    (endpointInsertEquiv C.length 3 (by have := C.length_ge; omega)).symm_apply_apply (.inr i)
  simp only [threePathSlots, Equiv.trans_apply, hi]
  rfl

/-- Replace the rooted marker by the alternating path `zy, yu, uv, va`. -/
@[expose] def insertThreePath (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (ho : {u,v} ∉ insert {z,y} M)
    (he₂ : {v,a} ∪ R₂ ∉ E) (he₁ : {y,u} ∪ R₁ ∉ insert ({v,a} ∪ R₂) E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hA : Function.Injective ![y,u,v])
    (hAS : ∀ i : Fin 3, ![y,u,v] i ∉ S)
    (hB : ∀ i : Fin 2, (![R₁,R₂] i).card = r-2)
    (hBB : Pairwise (fun i j : Fin 2 => Disjoint (![R₁,R₂] i) (![R₁,R₂] j)))
    (hBS : ∀ i : Fin 2, Disjoint S (![R₁,R₂] i))
    (hAB : ∀ (i : Fin 3) (j : Fin 2), ![y,u,v] i ∉ ![R₁,R₂] j)
    (hM : (↑(insert {z,y} (insert {u,v} M)) : Set (Finset V)).PairwiseDisjoint id) :
    MixedCycleOnWitness r (S ∪ {y,u,v} ∪ (R₁ ∪ R₂))
      (insert {z,y} (insert {u,v} M)) (insert ({y,u} ∪ R₁) (insert ({v,a} ∪ R₂) E)) := by
  let A : Fin 3 → V := ![y,u,v]
  let B : Fin 2 → Finset V := ![R₁,R₂]
  let EE := twoEdgeInsertEquiv E ({y,u} ∪ R₁) ({v,a} ∪ R₂) he₂ he₁
  let SS := C.threePathSlots (V := V) (r := r) (S := S) (M := M) (E := E) (z := z) (a := a) (y := y) (u := u) (v := v)
      (R₁ := R₁) (R₂ := R₂) hp hq ho he₂ he₁
  have hslot : ∀ i, match SS i with
      | .inl e => e.val =
          {endpointInsertedJunction (by have := C.length_ge; omega) C.junction A i,
          endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
            (finRotate (C.length+3) i)}
      | .inr e => e.val =
          {endpointInsertedJunction (by have := C.length_ge; omega) C.junction A i,
          endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
            (finRotate (C.length+3) i)} ∪ C.insertedPrivate EE B e := by
    intro i
    obtain ⟨j,rfl⟩ := (endpointInsertEquiv C.length 3 (by have := C.length_ge; omega)).surjective i
    cases j with
    | inl j =>
      simp only [endpointInsertEquiv_inl]
      dsimp only [SS]
      rw [threePathSlots_old]
      by_cases hj : j.val = 0
      · have hj' : j = ⟨0,by have := C.length_ge; omega⟩ := Fin.ext hj
        rw [hj']
        rw [hzero, spliceSlotsII_marker]
        change ((replaceInsertedEquiv M {z,a} {z,y} hp hq)
          ⟨{z,a}, mem_insert_self _ _⟩).val = _
        rw [replaceInsertedEquiv_new]
        simp only [endpointKeep, Fin.val_zero, ite_true]
        rw [endpointInsertedJunction_zero, endpointInsertedJunction_first_next
          (by have := C.length_ge; omega) (by decide)]
        simp [hz,A]
      · rw [← endpointKeep_rotate (by have := C.length_ge; omega) j hj]
        rw [endpointInsertedJunction_old, endpointInsertedJunction_old]
        cases hs : C.slot j with
        | inl m =>
          have hmp : m.val ≠ {z,a} := by
            intro hh
            have hm : m = ⟨{z,a},mem_insert_self _ _⟩ := Subtype.ext hh
            have heq := C.slot.injective (hs.trans (hm ▸ hzero.symm))
            exact hj (congrArg Fin.val heq)
          have hmM : m.val ∈ M := (mem_insert.mp m.property).resolve_left hmp
          have hmcast : m = ⟨m.val,mem_insert_of_mem hmM⟩ := rfl
          rw [spliceSlotsII_marker]
          have hr := replaceInsertedEquiv_old M {z,a} {z,y} hp hq ⟨m.val,hmM⟩
          change ((replaceInsertedEquiv M {z,a} {z,y} hp hq) m).val = _
          rw [hr]
          simpa [hs] using C.slot_edge j
        | inr e =>
          rw [spliceSlotsII_edge]
          have hb : C.insertedPrivate EE B
              ⟨e.val,mem_insert_of_mem (mem_insert_of_mem e.property)⟩ = C.privateBlock e :=
            C.insertedPrivate_old EE B e
          dsimp only
          rw [hb]
          simpa [hs] using C.slot_edge j
    | inr j =>
      simp only [endpointInsertEquiv_inr]
      dsimp only [SS]
      rw [threePathSlots_new]
      have hJ₁ : endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
          ⟨1,by omega⟩ = y := endpointInsertedJunction_added _ _ A (0 : Fin 3)
      have hJ₂ : endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
          ⟨2,by omega⟩ = u := endpointInsertedJunction_added _ _ A (1 : Fin 3)
      have hJ₃ : endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
          ⟨3,by have := C.length_ge; omega⟩ = v := endpointInsertedJunction_added _ _ A (2 : Fin 3)
      have hn₁ : finRotate (C.length+3) ⟨1,by omega⟩ = (⟨2,by omega⟩ : Fin (C.length+3)) := by
        exact finRotate_of_lt (n := C.length+2) (k := 1) (by omega)
      have hn₂ : finRotate (C.length+3) ⟨2,by omega⟩ = (⟨3,by have := C.length_ge; omega⟩ : Fin (C.length+3)) := by
        exact finRotate_of_lt (n := C.length+2) (k := 2) (by have := C.length_ge; omega)
      fin_cases j
      · change {y,u} ∪ R₁ =
          {endpointInsertedJunction (by have := C.length_ge; omega) C.junction A ⟨1,by omega⟩,
           endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
             (finRotate (C.length+3) ⟨1,by omega⟩)} ∪
           C.insertedPrivate EE B ⟨{y,u} ∪ R₁,mem_insert_self _ _⟩
        rw [hn₁,hJ₁,hJ₂]
        have hb : C.insertedPrivate EE B ⟨{y,u} ∪ R₁,mem_insert_self _ _⟩ = R₁ :=
          C.insertedPrivate_new EE B (0 : Fin 2)
        rw [hb]
      · change {u,v} =
          {endpointInsertedJunction (by have := C.length_ge; omega) C.junction A ⟨2,by omega⟩,
           endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
             (finRotate (C.length+3) ⟨2,by omega⟩)}
        rw [hn₂,hJ₂,hJ₃]
      · change {v,a} ∪ R₂ =
          {endpointInsertedJunction (by have := C.length_ge; omega) C.junction A ⟨3,by have := C.length_ge; omega⟩,
           endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
             (finRotate (C.length+3) ⟨3,by have := C.length_ge; omega⟩)} ∪
           C.insertedPrivate EE B ⟨{v,a} ∪ R₂,mem_insert_of_mem (mem_insert_self _ _)⟩
        rw [hJ₃,endpointInsertedJunction_last_next (by have := C.length_ge; omega)]
        have hb : C.insertedPrivate EE B
            ⟨{v,a} ∪ R₂,mem_insert_of_mem (mem_insert_self _ _)⟩ = R₂ :=
          C.insertedPrivate_new EE B (1 : Fin 2)
        rw [hb,ha]
  have D := C.insertPath A B hA hAS hB hBB hBS hAB EE SS hM (by
    intro i
    cases hsi : SS i <;> simpa only [hsi] using hslot i)
  exact { D with cover := by simpa [A,B,Fin.univ_succ, image_insert, biUnion_insert] using D.cover }

@[simp] theorem insertThreePath_private_first (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (ho : {u,v} ∉ insert {z,y} M)
    (he₂ : {v,a} ∪ R₂ ∉ E) (he₁ : {y,u} ∪ R₁ ∉ insert ({v,a} ∪ R₂) E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hA : Function.Injective ![y,u,v])
    (hAS : ∀ i : Fin 3, ![y,u,v] i ∉ S)
    (hB : ∀ i : Fin 2, (![R₁,R₂] i).card = r-2)
    (hBB : Pairwise (fun i j : Fin 2 => Disjoint (![R₁,R₂] i) (![R₁,R₂] j)))
    (hBS : ∀ i : Fin 2, Disjoint S (![R₁,R₂] i))
    (hAB : ∀ (i : Fin 3) (j : Fin 2), ![y,u,v] i ∉ ![R₁,R₂] j)
    (hM : (↑(insert {z,y} (insert {u,v} M)) : Set (Finset V)).PairwiseDisjoint id) :
    (C.insertThreePath hp hq ho he₂ he₁ hzero hz ha hA hAS hB hBB hBS hAB hM).privateBlock
      ⟨{y,u} ∪ R₁,mem_insert_self _ _⟩ = R₁ := by
  change C.insertedPrivate (twoEdgeInsertEquiv E ({y,u} ∪ R₁) ({v,a} ∪ R₂) he₂ he₁)
    ![R₁,R₂] ((twoEdgeInsertEquiv E ({y,u} ∪ R₁) ({v,a} ∪ R₂) he₂ he₁) (.inr 0)) = R₁
  exact C.insertedPrivate_new _ _ 0

@[simp] theorem insertThreePath_private_second (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (ho : {u,v} ∉ insert {z,y} M)
    (he₂ : {v,a} ∪ R₂ ∉ E) (he₁ : {y,u} ∪ R₁ ∉ insert ({v,a} ∪ R₂) E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hA : Function.Injective ![y,u,v])
    (hAS : ∀ i : Fin 3, ![y,u,v] i ∉ S)
    (hB : ∀ i : Fin 2, (![R₁,R₂] i).card = r-2)
    (hBB : Pairwise (fun i j : Fin 2 => Disjoint (![R₁,R₂] i) (![R₁,R₂] j)))
    (hBS : ∀ i : Fin 2, Disjoint S (![R₁,R₂] i))
    (hAB : ∀ (i : Fin 3) (j : Fin 2), ![y,u,v] i ∉ ![R₁,R₂] j)
    (hM : (↑(insert {z,y} (insert {u,v} M)) : Set (Finset V)).PairwiseDisjoint id) :
    (C.insertThreePath hp hq ho he₂ he₁ hzero hz ha hA hAS hB hBB hBS hAB hM).privateBlock
      ⟨{v,a} ∪ R₂,mem_insert_of_mem (mem_insert_self _ _)⟩ = R₂ := by
  change C.insertedPrivate (twoEdgeInsertEquiv E ({y,u} ∪ R₁) ({v,a} ∪ R₂) he₂ he₁)
    ![R₁,R₂] ((twoEdgeInsertEquiv E ({y,u} ∪ R₁) ({v,a} ∪ R₂) he₂ he₁) (.inr 1)) = R₂
  exact C.insertedPrivate_new _ _ 1

theorem insertThreePath_endpoint_role_first (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (ho : {u,v} ∉ insert {z,y} M)
    (he₂ : {v,a} ∪ R₂ ∉ E) (he₁ : {y,u} ∪ R₁ ∉ insert ({v,a} ∪ R₂) E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hA : Function.Injective ![y,u,v])
    (hAS : ∀ i : Fin 3, ![y,u,v] i ∉ S)
    (hB : ∀ i : Fin 2, (![R₁,R₂] i).card = r-2)
    (hBB : Pairwise (fun i j : Fin 2 => Disjoint (![R₁,R₂] i) (![R₁,R₂] j)))
    (hBS : ∀ i : Fin 2, Disjoint S (![R₁,R₂] i))
    (hAB : ∀ (i : Fin 3) (j : Fin 2), ![y,u,v] i ∉ ![R₁,R₂] j)
    (hM : (↑(insert {z,y} (insert {u,v} M)) : Set (Finset V)).PairwiseDisjoint id) (hr : 3 ≤ r) :
    edgeEndpointPair (insert {z,y} (insert {u,v} M))
      (insert ({y,u} ∪ R₁) (insert ({v,a} ∪ R₂) E)) ({y,u} ∪ R₁) = {y,u} := by
  let D := C.insertThreePath hp hq ho he₂ he₁ hzero hz ha hA hAS hB hBB hBS hAB hM
  rw [D.edgeEndpointPair_eq hr ⟨{y,u} ∪ R₁,mem_insert_self _ _⟩, D.endpointPair_eq_sdiff_privateBlock]
  rw [insertThreePath_private_first]
  ext w
  simp only [mem_sdiff, mem_union, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hw,hwR⟩
    exact hw.resolve_right hwR
  · intro hw
    exact ⟨Or.inl hw, by rcases hw with rfl | rfl; exact hAB 0 0; exact hAB 1 0⟩

theorem insertThreePath_endpoint_role_second (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (ho : {u,v} ∉ insert {z,y} M)
    (he₂ : {v,a} ∪ R₂ ∉ E) (he₁ : {y,u} ∪ R₁ ∉ insert ({v,a} ∪ R₂) E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hA : Function.Injective ![y,u,v])
    (hAS : ∀ i : Fin 3, ![y,u,v] i ∉ S)
    (hB : ∀ i : Fin 2, (![R₁,R₂] i).card = r-2)
    (hBB : Pairwise (fun i j : Fin 2 => Disjoint (![R₁,R₂] i) (![R₁,R₂] j)))
    (hBS : ∀ i : Fin 2, Disjoint S (![R₁,R₂] i))
    (hAB : ∀ (i : Fin 3) (j : Fin 2), ![y,u,v] i ∉ ![R₁,R₂] j)
    (hM : (↑(insert {z,y} (insert {u,v} M)) : Set (Finset V)).PairwiseDisjoint id) (hr : 3 ≤ r) :
    edgeEndpointPair (insert {z,y} (insert {u,v} M))
      (insert ({y,u} ∪ R₁) (insert ({v,a} ∪ R₂) E)) ({v,a} ∪ R₂) = {v,a} := by
  let D := C.insertThreePath hp hq ho he₂ he₁ hzero hz ha hA hAS hB hBB hBS hAB hM
  rw [D.edgeEndpointPair_eq hr ⟨{v,a} ∪ R₂,mem_insert_of_mem (mem_insert_self _ _)⟩, D.endpointPair_eq_sdiff_privateBlock]
  rw [insertThreePath_private_second]
  have haS : a ∈ S := ha ▸ C.junction_mem ⟨1,by have := C.length_ge; omega⟩
  have haR : a ∉ R₂ := fun hh => disjoint_left.mp (hBS 1) haS hh
  ext w
  simp only [mem_sdiff, mem_union, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hw,hwR⟩
    exact hw.resolve_right hwR
  · intro hw
    exact ⟨Or.inl hw, by rcases hw with rfl | rfl; exact hAB 2 1; exact haR⟩
end MixedCycleOnWitness
end LooseHamilton
