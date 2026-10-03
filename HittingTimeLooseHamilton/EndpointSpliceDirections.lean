module

public import HittingTimeLooseHamilton.EndpointExpansionThree
public import HittingTimeLooseHamilton.SurgeryDirections

public section
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleOnWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {M E : Finset (Finset V)}
variable {z a y u v : V} {R R₁ R₂ : Finset V}
theorem insertOnePath_old_marker_start (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (he : {y,a} ∪ R ∉ E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hyS : y ∉ S) (hRS : Disjoint S R) (hyR : y ∉ R)
    (hR : R.card = r-2)
    (hM : (↑(insert {z,y} M) : Set (Finset V)).PairwiseDisjoint id) (m : ↥M) :
    (C.insertOnePath hp hq he hzero hz ha hyS hRS hyR hR hM).junction
      ((C.insertOnePath hp hq he hzero hz ha hyS hRS hyR hR hM).slot.symm
        (.inl ⟨m.val, mem_insert_of_mem m.property⟩)) =
    C.junction (C.slot.symm (.inl ⟨m.val, mem_insert_of_mem m.property⟩)) := by
  let i := C.slot.symm (.inl ⟨m.val,mem_insert_of_mem m.property⟩)
  have hs : C.onePathSlots hp hq he (endpointKeep C.length 1 i) =
      .inl ⟨m.val,mem_insert_of_mem m.property⟩ := by
    rw [onePathSlots_old]
    simp only [i, Equiv.apply_symm_apply, spliceSlotsI_marker, replaceInsertedEquiv_old]
  have hi := (C.onePathSlots hp hq he).symm_apply_apply (endpointKeep C.length 1 i)
  rw [hs] at hi
  change endpointInsertedJunction _ C.junction (fun _ : Fin 1 => y) ((C.onePathSlots hp hq he).symm _) = _
  rw [hi, endpointInsertedJunction_old]

set_option maxHeartbeats 800000 in
theorem insertThreePath_old_marker_start (C : MixedCycleOnWitness r S (insert {z,a} M) E)
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
    (hM : (↑(insert {z,y} (insert {u,v} M)) : Set (Finset V)).PairwiseDisjoint id) (m : ↥M) :
    (C.insertThreePath hp hq ho he₂ he₁ hzero hz ha hA hAS hB hBB hBS hAB hM).junction
      ((C.insertThreePath hp hq ho he₂ he₁ hzero hz ha hA hAS hB hBB hBS hAB hM).slot.symm
        (.inl ⟨m.val, mem_insert_of_mem (mem_insert_of_mem m.property)⟩)) =
    C.junction (C.slot.symm (.inl ⟨m.val, mem_insert_of_mem m.property⟩)) := by
  let i := C.slot.symm (.inl ⟨m.val,mem_insert_of_mem m.property⟩)
  have hs : C.threePathSlots hp hq ho he₂ he₁ (endpointKeep C.length 3 i) =
      .inl ⟨m.val,mem_insert_of_mem (mem_insert_of_mem m.property)⟩ := by
    rw [threePathSlots_old]
    simp only [i, Equiv.apply_symm_apply, spliceSlotsII_marker, replaceInsertedEquiv_old]
  have hi := (C.threePathSlots hp hq ho he₂ he₁).symm_apply_apply (endpointKeep C.length 3 i)
  rw [hs] at hi
  change endpointInsertedJunction _ C.junction ![y,u,v] ((C.threePathSlots hp hq ho he₂ he₁).symm _) = _
  rw [hi, endpointInsertedJunction_old]

theorem insertOnePath_path_starts (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (he : {y,a} ∪ R ∉ E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hyS : y ∉ S) (hRS : Disjoint S R) (hyR : y ∉ R)
    (hR : R.card = r-2)
    (hM : (↑(insert {z,y} M) : Set (Finset V)).PairwiseDisjoint id) :
    let D := C.insertOnePath hp hq he hzero hz ha hyS hRS hyR hR hM
    D.junction (D.slot.symm (.inl ⟨{z,y},mem_insert_self _ _⟩)) = z ∧
    D.junction (D.slot.symm (.inr ⟨{y,a} ∪ R,mem_insert_self _ _⟩)) = y := by
  dsimp only
  constructor
  · have hs : C.onePathSlots hp hq he ⟨0,by have := C.length_ge; omega⟩ =
        .inl ⟨{z,y},mem_insert_self _ _⟩ := by
      have h := C.onePathSlots_old hp hq he ⟨0,by have := C.length_ge; omega⟩
      simpa only [endpointKeep, Fin.val_zero, ite_true, hzero,
        spliceSlotsI_marker, replaceInsertedEquiv_new] using h
    have hi := (C.onePathSlots hp hq he).symm_apply_apply ⟨0,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction (fun _ : Fin 1 => y) ((C.onePathSlots hp hq he).symm _) = _
    rw [hi]
    rw [endpointInsertedJunction_zero, hz]
  · have hs : C.onePathSlots hp hq he ⟨1,by have := C.length_ge; omega⟩ =
        .inr ⟨{y,a} ∪ R,mem_insert_self _ _⟩ := by
      exact C.onePathSlots_new hp hq he
    have hi := (C.onePathSlots hp hq he).symm_apply_apply ⟨1,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction (fun _ : Fin 1 => y) ((C.onePathSlots hp hq he).symm _) = _
    rw [hi]
    exact endpointInsertedJunction_added _ _ _ (0 : Fin 1)

theorem insertThreePath_path_starts (C : MixedCycleOnWitness r S (insert {z,a} M) E)
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
    let D := C.insertThreePath hp hq ho he₂ he₁ hzero hz ha hA hAS hB hBB hBS hAB hM
    D.junction (D.slot.symm (.inl ⟨{z,y},mem_insert_self _ _⟩)) = z ∧
    D.junction (D.slot.symm (.inr ⟨{y,u} ∪ R₁,mem_insert_self _ _⟩)) = y ∧
    D.junction (D.slot.symm (.inl ⟨{u,v},mem_insert_of_mem (mem_insert_self _ _)⟩)) = u ∧
    D.junction (D.slot.symm (.inr ⟨{v,a} ∪ R₂,mem_insert_of_mem (mem_insert_self _ _)⟩)) = v := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : C.threePathSlots hp hq ho he₂ he₁ ⟨0,by have := C.length_ge; omega⟩ =
        .inl ⟨{z,y},mem_insert_self _ _⟩ := by
      have h := C.threePathSlots_old hp hq ho he₂ he₁ ⟨0,by have := C.length_ge; omega⟩
      simpa only [endpointKeep, Fin.val_zero, ite_true, hzero,
        spliceSlotsII_marker, replaceInsertedEquiv_new] using h
    have hi := (C.threePathSlots hp hq ho he₂ he₁).symm_apply_apply ⟨0,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction ![y,u,v] ((C.threePathSlots hp hq ho he₂ he₁).symm _) = _
    rw [hi]
    rw [endpointInsertedJunction_zero, hz]
  · have hs : C.threePathSlots hp hq ho he₂ he₁ ⟨1,by have := C.length_ge; omega⟩ =
        .inr ⟨{y,u} ∪ R₁,mem_insert_self _ _⟩ := by
      exact C.threePathSlots_new hp hq ho he₂ he₁ (0 : Fin 3)
    have hi := (C.threePathSlots hp hq ho he₂ he₁).symm_apply_apply ⟨1,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction ![y,u,v] ((C.threePathSlots hp hq ho he₂ he₁).symm _) = _
    rw [hi]
    exact endpointInsertedJunction_added _ _ _ (0 : Fin 3)
  · have hs : C.threePathSlots hp hq ho he₂ he₁ ⟨2,by have := C.length_ge; omega⟩ =
        .inl ⟨{u,v},mem_insert_of_mem (mem_insert_self _ _)⟩ := by
      exact C.threePathSlots_new hp hq ho he₂ he₁ (1 : Fin 3)
    have hi := (C.threePathSlots hp hq ho he₂ he₁).symm_apply_apply ⟨2,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction ![y,u,v] ((C.threePathSlots hp hq ho he₂ he₁).symm _) = _
    rw [hi]
    exact endpointInsertedJunction_added _ _ _ (1 : Fin 3)
  · have hs : C.threePathSlots hp hq ho he₂ he₁ ⟨3,by have := C.length_ge; omega⟩ =
        .inr ⟨{v,a} ∪ R₂,mem_insert_of_mem (mem_insert_self _ _)⟩ := by
      exact C.threePathSlots_new hp hq ho he₂ he₁ (2 : Fin 3)
    have hi := (C.threePathSlots hp hq ho he₂ he₁).symm_apply_apply ⟨3,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction ![y,u,v] ((C.threePathSlots hp hq ho he₂ he₁).symm _) = _
    rw [hi]
    exact endpointInsertedJunction_added _ _ _ (2 : Fin 3)

theorem shift_slot_start (C : MixedCycleOnWitness r S M E) (i : Fin C.length)
    (e : ↥M ⊕ ↥E) :
    (C.shift i).junction ((C.shift i).slot.symm e) = C.junction (C.slot.symm e) := by
  letI : NeZero C.length := ⟨by have := C.length_ge; omega⟩
  change C.junction (((Equiv.addRight i).trans C.slot).symm e + i) = _
  simp only [Equiv.symm_trans_apply]
  congr 1
  exact (Equiv.addRight i).apply_symm_apply _

theorem expand_old_ordinary_start (C : MixedCycleOnWitness r S M E) (p : ↥M)
    (P : Finset V) (hP : P.card = r - 2) (hPS : Disjoint P S)
    (hE : p.val ∪ P ∉ E) (e : ↥E) :
    (C.expand p P hP hPS hE).junction
      ((C.expand p P hP hPS hE).slot.symm
        (.inr ⟨e.val, mem_insert_of_mem e.property⟩)) =
    C.junction (C.slot.symm (.inr e)) := by
  have hs : (C.expand p P hP hPS hE).slot.symm
      (.inr ⟨e.val, mem_insert_of_mem e.property⟩) = C.slot.symm (.inr e) := by
    apply (C.expand p P hP hPS hE).slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = (Equiv.sumComm _ _) (slotTransfer E M (p.val ∪ P) p.val hE p.property
      ((Equiv.sumComm _ _) (C.slot (C.slot.symm (.inr e)))))
    rw [Equiv.apply_symm_apply]
    rfl
  exact congrArg C.junction hs

theorem expand_old_ordinary_end (C : MixedCycleOnWitness r S M E) (p : ↥M)
    (P : Finset V) (hP : P.card = r - 2) (hPS : Disjoint P S)
    (hE : p.val ∪ P ∉ E) (e : ↥E) :
    (C.expand p P hP hPS hE).junction
      (finRotate (C.expand p P hP hPS hE).length
        ((C.expand p P hP hPS hE).slot.symm
          (.inr ⟨e.val, mem_insert_of_mem e.property⟩))) =
    C.junction (finRotate C.length (C.slot.symm (.inr e))) := by
  have hs := C.junction_injective (C.expand_old_ordinary_start p P hP hPS hE e)
  exact congrArg (fun i => C.junction (finRotate C.length i)) hs

theorem expand_new_ordinary_end (C : MixedCycleOnWitness r S M E) (p : ↥M)
    (P : Finset V) (hP : P.card = r - 2) (hPS : Disjoint P S)
    (hE : p.val ∪ P ∉ E) :
    (C.expand p P hP hPS hE).junction
      (finRotate (C.expand p P hP hPS hE).length
        ((C.expand p P hP hPS hE).slot.symm
          (.inr ⟨p.val ∪ P, mem_insert_self _ _⟩))) =
    C.junction (finRotate C.length (C.slot.symm (.inl p))) := by
  have hs := C.junction_injective (C.expand_new_ordinary_start p P hP hPS hE)
  exact congrArg (fun i => C.junction (finRotate C.length i)) hs

theorem insertOnePath_path_ends (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (he : {y,a} ∪ R ∉ E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hyS : y ∉ S) (hRS : Disjoint S R) (hyR : y ∉ R)
    (hR : R.card = r-2)
    (hM : (↑(insert {z,y} M) : Set (Finset V)).PairwiseDisjoint id) :
    let D := C.insertOnePath hp hq he hzero hz ha hyS hRS hyR hR hM
    D.junction (finRotate D.length (D.slot.symm (.inl ⟨{z,y},mem_insert_self _ _⟩))) = y ∧
    D.junction (finRotate D.length (D.slot.symm (.inr ⟨{y,a} ∪ R,mem_insert_self _ _⟩))) = a := by
  dsimp only
  constructor
  · have hs : C.onePathSlots hp hq he ⟨0,by have := C.length_ge; omega⟩ =
        .inl ⟨{z,y},mem_insert_self _ _⟩ := by
      have h := C.onePathSlots_old hp hq he ⟨0,by have := C.length_ge; omega⟩
      simpa only [endpointKeep, Fin.val_zero, ite_true, hzero,
        spliceSlotsI_marker, replaceInsertedEquiv_new] using h
    have hi := (C.onePathSlots hp hq he).symm_apply_apply ⟨0,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction (fun _ : Fin 1 => y) (finRotate (C.length+1) ((C.onePathSlots hp hq he).symm _)) = _
    rw [hi]
    rw [rotate_mk_succ (by have := C.length_ge; omega)]
    exact endpointInsertedJunction_added _ _ _ (0 : Fin 1)
  · have hs : C.onePathSlots hp hq he ⟨1,by have := C.length_ge; omega⟩ =
        .inr ⟨{y,a} ∪ R,mem_insert_self _ _⟩ := by
      exact C.onePathSlots_new hp hq he
    have hi := (C.onePathSlots hp hq he).symm_apply_apply ⟨1,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction (fun _ : Fin 1 => y) (finRotate (C.length+1) ((C.onePathSlots hp hq he).symm _)) = _
    rw [hi]
    rw [endpointInsertedJunction_last_next (by have := C.length_ge; omega), ha]

theorem insertThreePath_path_ends (C : MixedCycleOnWitness r S (insert {z,a} M) E)
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
    let D := C.insertThreePath hp hq ho he₂ he₁ hzero hz ha hA hAS hB hBB hBS hAB hM
    D.junction (finRotate D.length (D.slot.symm (.inl ⟨{z,y},mem_insert_self _ _⟩))) = y ∧
    D.junction (finRotate D.length (D.slot.symm (.inr ⟨{y,u} ∪ R₁,mem_insert_self _ _⟩))) = u ∧
    D.junction (finRotate D.length (D.slot.symm (.inl ⟨{u,v},mem_insert_of_mem (mem_insert_self _ _)⟩))) = v ∧
    D.junction (finRotate D.length (D.slot.symm (.inr ⟨{v,a} ∪ R₂,mem_insert_of_mem (mem_insert_self _ _)⟩))) = a := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : C.threePathSlots hp hq ho he₂ he₁ ⟨0,by have := C.length_ge; omega⟩ =
        .inl ⟨{z,y},mem_insert_self _ _⟩ := by
      have h := C.threePathSlots_old hp hq ho he₂ he₁ ⟨0,by have := C.length_ge; omega⟩
      simpa only [endpointKeep, Fin.val_zero, ite_true, hzero,
        spliceSlotsII_marker, replaceInsertedEquiv_new] using h
    have hi := (C.threePathSlots hp hq ho he₂ he₁).symm_apply_apply ⟨0,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction ![y,u,v] (finRotate (C.length+3) ((C.threePathSlots hp hq ho he₂ he₁).symm _)) = _
    rw [hi]
    rw [rotate_mk_succ (by have := C.length_ge; omega)]
    exact endpointInsertedJunction_added _ _ _ (0 : Fin 3)
  · have hs : C.threePathSlots hp hq ho he₂ he₁ ⟨1,by have := C.length_ge; omega⟩ =
        .inr ⟨{y,u} ∪ R₁,mem_insert_self _ _⟩ := by
      exact C.threePathSlots_new hp hq ho he₂ he₁ (0 : Fin 3)
    have hi := (C.threePathSlots hp hq ho he₂ he₁).symm_apply_apply ⟨1,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction ![y,u,v] (finRotate (C.length+3) ((C.threePathSlots hp hq ho he₂ he₁).symm _)) = _
    rw [hi]
    rw [rotate_mk_succ (by have := C.length_ge; omega)]
    exact endpointInsertedJunction_added _ _ _ (1 : Fin 3)
  · have hs : C.threePathSlots hp hq ho he₂ he₁ ⟨2,by have := C.length_ge; omega⟩ =
        .inl ⟨{u,v},mem_insert_of_mem (mem_insert_self _ _)⟩ := by
      exact C.threePathSlots_new hp hq ho he₂ he₁ (1 : Fin 3)
    have hi := (C.threePathSlots hp hq ho he₂ he₁).symm_apply_apply ⟨2,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction ![y,u,v] (finRotate (C.length+3) ((C.threePathSlots hp hq ho he₂ he₁).symm _)) = _
    rw [hi]
    rw [rotate_mk_succ (by have := C.length_ge; omega)]
    exact endpointInsertedJunction_added _ _ _ (2 : Fin 3)
  · have hs : C.threePathSlots hp hq ho he₂ he₁ ⟨3,by have := C.length_ge; omega⟩ =
        .inr ⟨{v,a} ∪ R₂,mem_insert_of_mem (mem_insert_self _ _)⟩ := by
      exact C.threePathSlots_new hp hq ho he₂ he₁ (2 : Fin 3)
    have hi := (C.threePathSlots hp hq ho he₂ he₁).symm_apply_apply ⟨3,by have := C.length_ge; omega⟩
    rw [hs] at hi
    change endpointInsertedJunction _ C.junction ![y,u,v] (finRotate (C.length+3) ((C.threePathSlots hp hq ho he₂ he₁).symm _)) = _
    rw [hi]
    rw [endpointInsertedJunction_last_next (by have := C.length_ge; omega), ha]

end LooseHamilton.MixedCycleOnWitness
