module

public import HittingTimeLooseHamilton.EndpointExpansion
public import HittingTimeLooseHamilton.EndpointExpansionSlots
public import HittingTimeLooseHamilton.ActiveCycleNormalization
public import HittingTimeLooseHamilton.ActiveCycleRoles

public section

noncomputable section
open Finset
namespace LooseHamilton.MixedCycleOnWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {M E : Finset (Finset V)} {z a y : V} {R : Finset V}

@[expose] def onePathSlots (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (he : {y,a} ∪ R ∉ E) :
    Fin (C.length+1) ≃ (↥(insert {z,y} M) ⊕ ↥(insert ({y,a} ∪ R) E)) :=
  (endpointInsertEquiv C.length 1 (by have := C.length_ge; omega)).symm |>.trans
    ((Equiv.sumCongr C.slot (Equiv.refl (Fin 1))).trans
      (spliceSlotsI M E {z,a} {z,y} ({y,a} ∪ R) hp hq he))

@[simp] theorem onePathSlots_old (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (he : {y,a} ∪ R ∉ E) (i : Fin C.length) :
    C.onePathSlots hp hq he (endpointKeep C.length 1 i) =
      spliceSlotsI M E {z,a} {z,y} ({y,a} ∪ R) hp hq he (.inl (C.slot i)) := by
  have hi : (endpointInsertEquiv C.length 1 (by have := C.length_ge; omega)).symm
      (endpointKeep C.length 1 i) = .inl i :=
    (endpointInsertEquiv C.length 1 (by have := C.length_ge; omega)).symm_apply_apply (.inl i)
  simp only [onePathSlots, Equiv.trans_apply, hi]
  rfl

@[simp] theorem onePathSlots_new (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (he : {y,a} ∪ R ∉ E) :
    C.onePathSlots hp hq he ⟨1, by have := C.length_ge; omega⟩ =
      .inr ⟨{y,a} ∪ R, mem_insert_self _ _⟩ := by
  have hi : (endpointInsertEquiv C.length 1 (by have := C.length_ge; omega)).symm
      ⟨1,by have := C.length_ge; omega⟩ = .inr (0 : Fin 1) :=
    (endpointInsertEquiv C.length 1 (by have := C.length_ge; omega)).symm_apply_apply (.inr (0 : Fin 1))
  simp only [onePathSlots, Equiv.trans_apply, hi]
  rfl

/-- Replace the rooted marker `za` by the two-slot path `zy, ya ∪ R`. -/
@[expose] def insertOnePath (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (he : {y,a} ∪ R ∉ E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hyS : y ∉ S) (hRS : Disjoint S R) (hyR : y ∉ R)
    (hR : R.card = r-2)
    (hM : (↑(insert {z,y} M) : Set (Finset V)).PairwiseDisjoint id) :
    MixedCycleOnWitness r (S ∪ {y} ∪ R) (insert {z,y} M) (insert ({y,a} ∪ R) E) := by
  let A : Fin 1 → V := fun _ => y
  let B : Fin 1 → Finset V := fun _ => R
  let EE := edgeInsertEquiv E ({y,a} ∪ R) he
  let SS := C.onePathSlots hp hq he
  have hslot : ∀ i, match SS i with
      | .inl e => e.val =
          {endpointInsertedJunction (by have := C.length_ge; omega) C.junction A i,
          endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
            (finRotate (C.length+1) i)}
      | .inr e => e.val =
          {endpointInsertedJunction (by have := C.length_ge; omega) C.junction A i,
          endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
            (finRotate (C.length+1) i)} ∪ C.insertedPrivate EE B e := by
    intro i
    obtain ⟨j,rfl⟩ := (endpointInsertEquiv C.length 1 (by have := C.length_ge; omega)).surjective i
    cases j with
    | inl j =>
      simp only [endpointInsertEquiv_inl]
      dsimp only [SS]
      rw [onePathSlots_old]
      by_cases hj : j.val = 0
      · have hj' : j = ⟨0,by have := C.length_ge; omega⟩ := Fin.ext hj
        rw [hj']
        rw [hzero, spliceSlotsI_marker, replaceInsertedEquiv_new]
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
          rw [spliceSlotsI_marker]
          have hr := replaceInsertedEquiv_old M {z,a} {z,y} hp hq ⟨m.val,hmM⟩
          rw [hr]
          dsimp only
          simpa [hs] using C.slot_edge j
        | inr e =>
          rw [spliceSlotsI_edge]
          have hb : C.insertedPrivate EE B ⟨e.val,mem_insert_of_mem e.property⟩ = C.privateBlock e :=
            C.insertedPrivate_old EE B e
          dsimp only
          rw [hb]
          simpa [hs] using C.slot_edge j
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [endpointInsertEquiv_inr]
      dsimp only [SS]
      simp only [Fin.val_zero, Nat.zero_add]
      rw [onePathSlots_new]
      dsimp only
      have hy : endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
          ⟨1,by have := C.length_ge; omega⟩ = y := by
        simpa [A] using endpointInsertedJunction_added
          (by have := C.length_ge; omega) C.junction A (0 : Fin 1)
      rw [hy]
      rw [endpointInsertedJunction_last_next (by have := C.length_ge; omega)]
      have hb : C.insertedPrivate EE B ⟨{y,a} ∪ R,mem_insert_self _ _⟩ = R :=
        C.insertedPrivate_new EE B (0 : Fin 1)
      rw [hb,ha]
  have D := C.insertPath A B (fun i j _ => Subsingleton.elim _ _) (fun _ => hyS)
    (fun _ => hR) (fun i j hij => False.elim (hij (Subsingleton.elim _ _)))
    (fun _ => hRS) (fun _ _ => hyR) EE SS hM (by
      intro i
      cases hsi : SS i <;> simpa only [hsi] using hslot i)
  exact { D with cover := by simpa [A,B] using D.cover }

@[simp] theorem insertOnePath_private (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (he : {y,a} ∪ R ∉ E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hyS : y ∉ S) (hRS : Disjoint S R) (hyR : y ∉ R)
    (hR : R.card = r-2)
    (hM : (↑(insert {z,y} M) : Set (Finset V)).PairwiseDisjoint id) :
    (C.insertOnePath hp hq he hzero hz ha hyS hRS hyR hR hM).privateBlock
      ⟨{y,a} ∪ R,mem_insert_self _ _⟩ = R := by
  change C.insertedPrivate (edgeInsertEquiv E ({y,a} ∪ R) he) (fun _ : Fin 1 => R)
    ((edgeInsertEquiv E ({y,a} ∪ R) he) (.inr 0)) = R
  exact C.insertedPrivate_new _ _ 0

theorem endpointPair_eq_sdiff_privateBlock {M : Finset (Finset V)}
    (C : MixedCycleOnWitness r S M E) (e : ↥E) :
    C.endpointPair e = e.val \ C.privateBlock e := by
  have h := C.edge_eq_endpointPair e
  have hd := C.endpointPair_private_disjoint e
  rw [h]
  ext v
  simp only [mem_sdiff, mem_union]
  constructor
  · intro hv
    exact ⟨Or.inl hv, fun hb => disjoint_left.mp hd hv hb⟩
  · rintro ⟨hv,hb⟩
    exact hv.resolve_right hb

theorem insertOnePath_endpoint_role (C : MixedCycleOnWitness r S (insert {z,a} M) E)
    (hr : 3 ≤ r)
    (hp : {z,a} ∉ M) (hq : {z,y} ∉ M) (he : {y,a} ∪ R ∉ E)
    (hzero : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{z,a},mem_insert_self _ _⟩)
    (hz : C.junction ⟨0,by have := C.length_ge; omega⟩ = z)
    (ha : C.junction ⟨1,by have := C.length_ge; omega⟩ = a)
    (hyS : y ∉ S) (hRS : Disjoint S R) (hyR : y ∉ R)
    (hR : R.card = r-2)
    (hM : (↑(insert {z,y} M) : Set (Finset V)).PairwiseDisjoint id) :
    edgeEndpointPair (insert {z,y} M) (insert ({y,a} ∪ R) E) ({y,a} ∪ R) = {y,a} := by
  let D := C.insertOnePath hp hq he hzero hz ha hyS hRS hyR hR hM
  rw [D.edgeEndpointPair_eq hr ⟨{y,a} ∪ R,mem_insert_self _ _⟩,
    D.endpointPair_eq_sdiff_privateBlock]
  rw [insertOnePath_private]
  have haS : a ∈ S := ha ▸ C.junction_mem ⟨1,by have := C.length_ge; omega⟩
  have haR : a ∉ R := fun hh => disjoint_left.mp hRS haS hh
  ext v
  simp only [mem_sdiff, mem_union, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hv,hvR⟩
    exact hv.resolve_right hvR
  · intro hv
    exact ⟨Or.inl hv, by rcases hv with rfl | rfl; exact hyR; exact haR⟩
end LooseHamilton.MixedCycleOnWitness
