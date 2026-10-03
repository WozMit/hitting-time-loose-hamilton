module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

public section
noncomputable section
open scoped BigOperators
namespace LooseHamilton.Allocation
variable (U : Type*) [Fintype U] [DecidableEq U] (k d : ℕ)
/-- Assign vertices to labelled blocks, each containing exactly `d` vertices. -/
@[expose] def Balanced := {f : U → Fin k // ∀ i, Fintype.card {x // f x = i} = d}
@[expose] instance : Fintype (Balanced U k d) := by unfold Balanced; infer_instance
abbrev Ordered := Σ f : Balanced U k d, ∀ i, {x // f.val x = i} ≃ Fin d
@[expose] def assemble (a : Ordered U k d) : U ≃ Fin k × Fin d where
  toFun x := ⟨a.1.val x, a.2 (a.1.val x) ⟨x, rfl⟩⟩
  invFun y := ((a.2 y.1).symm y.2).val
  left_inv x := by simp
  right_inv y := by
    rcases y with ⟨i,j⟩
    have hj : a.2 i ((a.2 i).symm j) = j := (a.2 i).apply_symm_apply j
    rcases hz : (a.2 i).symm j with ⟨x,hx⟩
    rw [hz] at hj
    dsimp only
    rw [hz]
    dsimp only
    subst i
    simpa using congrArg (Prod.mk (a.1.val x)) hj
omit [DecidableEq U] in
lemma assemble_injective : Function.Injective (assemble U k d) := by
  intro a b h
  have hf : a.1 = b.1 := by
    apply Subtype.ext
    funext x
    exact congrArg Prod.fst (Equiv.congr_fun h x)
  rcases a with ⟨a, ea⟩
  rcases b with ⟨b, eb⟩
  dsimp at hf
  subst b
  congr 1
  funext i
  apply Equiv.ext
  intro x
  have he := congrArg Prod.snd (Equiv.congr_fun h x.val)
  dsimp [assemble] at he
  obtain ⟨x,hx⟩ := x
  dsimp at hx ⊢ he
  subst i
  exact he
@[expose] def fibreEquiv (e : U ≃ Fin k × Fin d) (i : Fin k) :
    {x // (e x).1 = i} ≃ Fin d where
  toFun x := (e x.val).2
  invFun j := ⟨e.symm (i,j), by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext x.property.symm rfl
  right_inv j := by simp
@[expose] def disassemble (e : U ≃ Fin k × Fin d) : Ordered U k d :=
  ⟨⟨fun x => (e x).1, fun i => by
    rw [Fintype.card_congr (fibreEquiv U k d e i), Fintype.card_fin]⟩,
    fibreEquiv U k d e⟩
omit [DecidableEq U] in
lemma assemble_disassemble (e : U ≃ Fin k × Fin d) :
    assemble U k d (disassemble U k d e) = e := by ext x <;> rfl
@[expose] def orderedEquiv : Ordered U k d ≃ (U ≃ Fin k × Fin d) :=
  Equiv.ofBijective (assemble U k d) ⟨assemble_injective U k d,
    fun e => ⟨disassemble U k d e, assemble_disassemble U k d e⟩⟩
/-- Exact allocation count with factorial division cleared. -/
theorem card_mul_factorial_pow (h : Fintype.card U = k * d) :
    Fintype.card (Balanced U k d) * d.factorial ^ k = (k*d).factorial := by
  have hc : Fintype.card (Ordered U k d) =
      Fintype.card (Balanced U k d) * d.factorial ^ k := by
    rw [Fintype.card_sigma]
    have he (f : Balanced U k d) (i : Fin k) :
        Fintype.card ({x // f.val x = i} ≃ Fin d) = d.factorial := by
      rw [Fintype.card_equiv (Fintype.equivOfCardEq (f.property i |>.trans (Fintype.card_fin d).symm)),
        f.property i]
    simp only [Fintype.card_pi, he, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  rw [← hc, Fintype.card_congr (orderedEquiv U k d),
    Fintype.card_equiv (Fintype.equivOfCardEq (by simp [h])), h]
theorem card_eq (h : Fintype.card U = k*d) :
    Fintype.card (Balanced U k d) = (k*d).factorial / d.factorial ^ k := by
  rw [← card_mul_factorial_pow U k d h]
  exact (Nat.mul_div_cancel _ (pow_pos (Nat.factorial_pos d) k)).symm

/-- Labelled, unordered private blocks: uniform size and unique membership
express respectively uniformity and disjoint covering of the vertex set. -/
@[expose] def Blocks := {P : Fin k → Finset U //
  (∀ i, (P i).card = d) ∧ ∀ x, ∃! i, x ∈ P i}
@[expose] instance : Fintype (Blocks U k d) := by
  classical
  unfold Blocks
  infer_instance

@[expose] def toBlocks (f : Balanced U k d) : Blocks U k d :=
  ⟨fun i => Finset.univ.filter (fun x => f.val x = i), by
    constructor
    · intro i
      simpa only [Fintype.card_subtype] using f.property i
    · intro x
      exact ⟨f.val x, by simp, fun j hj => by simpa using (Finset.mem_filter.mp hj).2.symm⟩⟩

@[expose] def blockLabel (P : Blocks U k d) (x : U) : Fin k :=
  Classical.choose (P.property.2 x)

omit [Fintype U] [DecidableEq U] in
lemma blockLabel_spec (P : Blocks U k d) (x : U) (i : Fin k) :
    blockLabel U k d P x = i ↔ x ∈ P.val i := by
  have h := Classical.choose_spec (P.property.2 x)
  constructor
  · intro he; rw [← he]; exact h.1
  · intro hi; exact (h.2 i hi).symm

@[expose] def ofBlocks (P : Blocks U k d) : Balanced U k d :=
  ⟨blockLabel U k d P, fun i => by
    have he : {x // blockLabel U k d P x = i} ≃ {x // x ∈ P.val i} :=
      Equiv.subtypeEquivRight (fun x => blockLabel_spec U k d P x i)
    rw [Fintype.card_congr he, Fintype.card_coe, P.property.1 i]⟩

@[expose] def blocksEquiv : Balanced U k d ≃ Blocks U k d where
  toFun := toBlocks U k d
  invFun := ofBlocks U k d
  left_inv f := by
    apply Subtype.ext
    funext x
    apply (blockLabel_spec U k d (toBlocks U k d f) x (f.val x)).mpr
    simp [toBlocks]
  right_inv P := by
    apply Subtype.ext
    funext i
    apply Finset.ext
    intro x
    change x ∈ Finset.univ.filter (fun x => blockLabel U k d P x = i) ↔ x ∈ P.val i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using blockLabel_spec U k d P x i

theorem blocks_card_mul_factorial_pow (h : Fintype.card U = k*d) :
    Fintype.card (Blocks U k d) * d.factorial ^ k = (k*d).factorial := by
  rw [← Fintype.card_congr (blocksEquiv U k d)]
  exact card_mul_factorial_pow U k d h

theorem blocks_card_eq (h : Fintype.card U = k*d) :
    Fintype.card (Blocks U k d) = (k*d).factorial / d.factorial ^ k := by
  rw [← Fintype.card_congr (blocksEquiv U k d)]
  exact card_eq U k d h

omit [Fintype U] [DecidableEq U] in
lemma blocks_disjoint (P : Blocks U k d) {i j : Fin k} (hij : i ≠ j) :
    Disjoint (P.val i) (P.val j) := by
  apply Finset.disjoint_left.mpr
  intro x hi hj
  have h := (P.property.2 x).unique hi hj
  exact hij h

lemma blocks_cover (P : Blocks U k d) :
    Finset.univ.biUnion P.val = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨i, hi, _⟩ := P.property.2 x
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
end LooseHamilton.Allocation
