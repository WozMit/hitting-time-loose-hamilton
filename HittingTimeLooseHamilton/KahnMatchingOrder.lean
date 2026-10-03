module

public import HittingTimeLooseHamilton.KahnMatchingCoordinates
public import HittingTimeLooseHamilton.KahnRevealCard
public import HittingTimeLooseHamilton.KahnConditionalOrder

public section

/-! Transport of block-order symmetry to perfect matchings. -/
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace Kahn.PerfectMatching
open Kahn.Ordering
variable {n r : ℕ} (M : Kahn.PerfectMatching n r)

abbrev Block := {B // B ∈ M.val}

/-- The same vertex ordering written in matching-block coordinates. -/
@[expose] def coordinateOrder (σ : Equiv.Perm (Fin n)) : (M.Block × Fin r) ≃ Fin n :=
  M.vertexCoordinates.symm.trans σ

/-- Changing coordinates bijects the two finite spaces of vertex orders. -/
@[expose] def coordinateOrderEquiv : Equiv.Perm (Fin n) ≃ ((M.Block × Fin r) ≃ Fin n) where
  toFun := M.coordinateOrder
  invFun ρ := M.vertexCoordinates.trans ρ
  left_inv σ := by ext x; simp [coordinateOrder]
  right_inv ρ := by ext x; simp [coordinateOrder]

@[simp] lemma coordinateOrder_coordinates (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    M.coordinateOrder σ (M.vertexCoordinates v) = σ v := by simp [coordinateOrder]

lemma mem_block_iff_coordinates (B : M.Block) (v : Fin n) :
    v ∈ B.val ↔ (M.vertexCoordinates v).1 = B := by
  constructor
  · intro h
    apply Subtype.ext
    exact (M.eq_edge_of_mem B.property h).symm
  · intro h
    have he : M.edge v = B.val := congrArg Subtype.val h
    simpa only [he] using M.mem_edge v

lemma coordinates_symm_mem (B : M.Block) (a : Fin r) :
    M.vertexCoordinates.symm (B, a) ∈ B.val := by
  apply (M.mem_block_iff_coordinates B _).mpr
  simp

/-- Lift a collection of matching blocks to the type of blocks. -/
@[expose] def blockLift (S : Finset (Finset (Fin n))) : Finset M.Block :=
  Finset.univ.filter fun B => B.val ∈ S

lemma card_blockLift (S : Finset (Finset (Fin n))) (hS : S ⊆ M.val) :
    (M.blockLift S).card = S.card := by
  classical
  apply Finset.card_bij (fun B _ => B.val)
  · intro B hB
    exact (Finset.mem_filter.mp hB).2
  · intro B hB C hC he
    exact Subtype.ext he
  · intro B hB
    exact ⟨⟨B, hS hB⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩, rfl⟩

variable [NeZero r]

/-- The first-in-own-block condition in the original and product coordinates agrees. -/
lemma unknown_iff_blockFirstRank (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    v ∉ M.earlierEdges σ v ↔
      σ v = blockFirstRank (M.coordinateOrder σ) (M.vertexCoordinates v).1 := by
  constructor
  · intro h
    apply le_antisymm
    · obtain ⟨a, ha⟩ := blockFirstRank_mem (M.coordinateOrder σ) (M.vertexCoordinates v).1
      rw [ha]
      exact ((M.unknown_iff_first σ v).mp h) _ (M.coordinates_symm_mem _ a)
    · have hh := blockFirstRank_le (M.coordinateOrder σ)
        (M.vertexCoordinates v).1 (M.vertexCoordinates v).2
      simpa only [Prod.eta, M.coordinateOrder_coordinates] using hh
  · intro h
    apply (M.unknown_iff_first σ v).mpr
    intro w hw
    have hb : (M.vertexCoordinates w).1 = (M.vertexCoordinates v).1 :=
      (M.mem_block_iff_coordinates ⟨M.edge v, M.edge_mem v⟩ w).mp hw
    have hh := blockFirstRank_le (M.coordinateOrder σ)
      (M.vertexCoordinates v).1 (M.vertexCoordinates w).2
    rw [← h, ← hb] at hh
    simpa only [Prod.eta, M.coordinateOrder_coordinates] using hh

lemma mem_lateBlocks_iff_rank_le (σ : Equiv.Perm (Fin n)) (v : Fin n) (B : M.Block) :
    B.val ∈ M.lateBlocks σ v ↔ σ v ≤ blockFirstRank (M.coordinateOrder σ) B := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := blockFirstRank_mem (M.coordinateOrder σ) B
    rw [ha]
    exact (Finset.mem_filter.mp h).2 _ (M.coordinates_symm_mem B a)
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨B.property, ?_⟩
    intro w hw
    have hb := (M.mem_block_iff_coordinates B w).mp hw
    have hh := blockFirstRank_le (M.coordinateOrder σ) B (M.vertexCoordinates w).2
    rw [← hb] at hh
    have hh' : blockFirstRank (M.coordinateOrder σ) (M.vertexCoordinates w).1 ≤ σ w := by
      simpa only [Prod.eta, M.coordinateOrder_coordinates] using hh
    rw [hb] at hh'
    exact h.trans hh'

lemma lateBlocks_lift_of_selected (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (k : Fin (Fintype.card M.Block))
    (hsel : blockOrderVertex (M.coordinateOrder σ) k = M.vertexCoordinates v) :
    M.blockLift (M.lateBlocks σ v) =
      insert (M.vertexCoordinates v).1 (laterBlocks (M.coordinateOrder σ) k) := by
  classical
  have hfirst := blockOrderVertex_first (M.coordinateOrder σ) k
  rw [hsel, M.coordinateOrder_coordinates] at hfirst
  ext B
  simp only [blockLift, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    M.mem_lateBlocks_iff_rank_le, mem_laterBlocks_iff, hsel, M.coordinateOrder_coordinates]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl ((blockFirstRank_injective (M.coordinateOrder σ)) (heq.symm.trans hfirst.symm))
  · rintro (rfl | hlt)
    · exact hfirst.ge
    · exact hlt.le

lemma lateBlocks_card_of_selected (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (k : Fin (Fintype.card M.Block))
    (hsel : blockOrderVertex (M.coordinateOrder σ) k = M.vertexCoordinates v) :
    (M.lateBlocks σ v).card = Fintype.card M.Block - k := by
  classical
  rw [← M.card_blockLift (M.lateBlocks σ v) (Finset.filter_subset _ _),
    M.lateBlocks_lift_of_selected σ v k hsel]
  have hnot := blockOrderVertex_not_mem_laterBlocks (M.coordinateOrder σ) k
  rw [hsel] at hnot
  rw [Finset.card_insert_of_notMem hnot, card_laterBlocks]
  have hk := k.isLt
  omega

/-- The block-order atom agrees with the unknown branch and its number of late blocks. -/
lemma selected_iff_unknown_card (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (k : Fin (Fintype.card M.Block)) :
    blockOrderVertex (M.coordinateOrder σ) k = M.vertexCoordinates v ↔
      v ∉ M.earlierEdges σ v ∧ (M.lateBlocks σ v).card = Fintype.card M.Block - k := by
  constructor
  · intro hsel
    refine ⟨?_, M.lateBlocks_card_of_selected σ v k hsel⟩
    apply (M.unknown_iff_blockFirstRank σ v).mpr
    have h := (blockOrderVertex_eq_iff (M.coordinateOrder σ) k (M.vertexCoordinates v)).mp hsel
    simpa only [M.coordinateOrder_coordinates] using h.1
  · rintro ⟨hu, hc⟩
    let j := (blockOrderEquiv (M.coordinateOrder σ)).symm (M.vertexCoordinates v).1
    have hselj : blockOrderVertex (M.coordinateOrder σ) j = M.vertexCoordinates v := by
      apply (blockOrderVertex_eq_iff _ _ _).mpr
      exact ⟨by simpa only [M.coordinateOrder_coordinates] using
        (M.unknown_iff_blockFirstRank σ v).mp hu, rfl⟩
    have hjc := M.lateBlocks_card_of_selected σ v j hselj
    have heq : j = k := by
      apply Fin.ext
      have hj := j.isLt
      have hk := k.isLt
      omega
    rwa [heq] at hselj

section ProbabilityQ
local instance : Fintype ((M.Block × Fin r) ≃ Fin n) :=
  @Equiv.instFintype (M.Block × Fin r) (Fin n) inferInstance
    (@LinearOrder.toDecidableEq (Fin n) (Fin.instLinearOrder)) inferInstance inferInstance

/-- Equation (35), with the index represented by the number of untouched blocks. -/
theorem unknown_card_probability (v : Fin n) (k : Fin (Fintype.card M.Block)) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      v ∉ M.earlierEdges σ v ∧ (M.lateBlocks σ v).card = Fintype.card M.Block - k)).card : ℝ) /
        Fintype.card (Equiv.Perm (Fin n)) = 1 / (n : ℝ) := by
  classical
  letI : Nonempty ((M.Block × Fin r) ≃ Fin n) := ⟨M.vertexCoordinates.symm⟩
  have hc : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      v ∉ M.earlierEdges σ v ∧ (M.lateBlocks σ v).card = Fintype.card M.Block - k)).card =
      (Finset.univ.filter (fun ρ : (M.Block × Fin r) ≃ Fin n =>
        blockOrderVertex ρ k = M.vertexCoordinates v)).card := by
    apply Finset.card_equiv M.coordinateOrderEquiv
    intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (M.selected_iff_unknown_card σ v k).symm
  rw [hc, Fintype.card_congr M.coordinateOrderEquiv]
  have hp := blockOrderVertex_uniform (B := M.Block) (R := Fin r) (L := Fin n) k (M.vertexCoordinates v)
  have hn : (Fintype.card M.Block : ℝ) * Fintype.card (Fin r) = n := by
    exact_mod_cast (by simpa using M.card_blocks_mul.symm :
      Fintype.card M.Block * Fintype.card (Fin r) = n)
  rw [hn] at hp
  exact hp

end ProbabilityQ

lemma own_not_mem_touchingLift (v : Fin n) (Y : Finset (Fin n)) :
    (M.vertexCoordinates v).1 ∉ M.blockLift (M.touching v Y) := by
  intro h
  have ht := (Finset.mem_filter.mp h).2
  exact (Finset.mem_filter.mp ht).2.1 rfl

lemma touchingLift_card (v : Fin n) (Y : Finset (Fin n)) :
    (M.blockLift (M.touching v Y)).card = M.tau v Y :=
  M.card_blockLift _ (Finset.filter_subset _ _)

lemma touchingLift_subset_later_iff (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (k : Fin (Fintype.card M.Block)) (Y : Finset (Fin n)) (hvY : v ∉ Y)
    (hsel : blockOrderVertex (M.coordinateOrder σ) k = M.vertexCoordinates v) :
    M.blockLift (M.touching v Y) ⊆ laterBlocks (M.coordinateOrder σ) k ↔
      Y ⊆ M.available σ v := by
  classical
  have hu := ((M.selected_iff_unknown_card σ v k).mp hsel).1
  rw [M.subset_available_iff_touching σ v Y hvY hu]
  have he := M.lateBlocks_lift_of_selected σ v k hsel
  constructor
  · intro h B hB w hw
    let b : M.Block := ⟨B, (Finset.mem_filter.mp hB).1⟩
    have hb : b ∈ M.blockLift (M.touching v Y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩
    have hlate : b ∈ M.blockLift (M.lateBlocks σ v) := by
      rw [he]
      exact Finset.mem_insert_of_mem (h hb)
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hlate).2).2 w hw
  · intro h b hb
    have ht := (Finset.mem_filter.mp hb).2
    have hlate : b ∈ M.blockLift (M.lateBlocks σ v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨b.property, h b.val ht⟩⟩
    rw [he] at hlate
    rcases Finset.mem_insert.mp hlate with heq | hlater
    · subst b
      exact False.elim (M.own_not_mem_touchingLift v Y hb)
    · exact hlater

section ProbabilityS
local instance : Fintype ((M.Block × Fin r) ≃ Fin n) :=
  @Equiv.instFintype (M.Block × Fin r) (Fin n) inferInstance
    (@LinearOrder.toDecidableEq (Fin n) (Fin.instLinearOrder)) inferInstance inferInstance

/-- Exact survival probability for a fixed matching; the exponent is the number
of other blocks touched by `Y`, without a genericity assumption. -/
theorem unknown_card_survival_probability (v : Fin n) (k : Fin (Fintype.card M.Block))
    (Y : Finset (Fin n)) (hvY : v ∉ Y) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (v ∉ M.earlierEdges σ v ∧ (M.lateBlocks σ v).card = Fintype.card M.Block - k) ∧
        Y ⊆ M.available σ v)).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) =
      (1 / (n : ℝ)) * ((Fintype.card M.Block - 1 - k).descFactorial (M.tau v Y) : ℝ) /
        (Fintype.card M.Block - 1).descFactorial (M.tau v Y) := by
  classical
  letI : Nonempty ((M.Block × Fin r) ≃ Fin n) := ⟨M.vertexCoordinates.symm⟩
  have hc : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (v ∉ M.earlierEdges σ v ∧ (M.lateBlocks σ v).card = Fintype.card M.Block - k) ∧
        Y ⊆ M.available σ v)).card =
      (Finset.univ.filter (fun ρ : (M.Block × Fin r) ≃ Fin n =>
        blockOrderVertex ρ k = M.vertexCoordinates v ∧
          M.blockLift (M.touching v Y) ⊆ laterBlocks ρ k)).card := by
    apply Finset.card_equiv M.coordinateOrderEquiv
    intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hu, hy⟩
      have hs := (M.selected_iff_unknown_card σ v k).mpr hu
      exact ⟨hs, (M.touchingLift_subset_later_iff σ v k Y hvY hs).mpr hy⟩
    · rintro ⟨hs, hy⟩
      exact ⟨(M.selected_iff_unknown_card σ v k).mp hs,
        (M.touchingLift_subset_later_iff σ v k Y hvY hs).mp hy⟩
  rw [hc, Fintype.card_congr M.coordinateOrderEquiv]
  have hp := first_survivor_probability_descFactorial (B := M.Block) (R := Fin r) (L := Fin n)
      k (M.vertexCoordinates v)
      (M.blockLift (M.touching v Y)) (M.own_not_mem_touchingLift v Y)
  rw [M.touchingLift_card] at hp
  have hn : (Fintype.card M.Block : ℝ) * Fintype.card (Fin r) = n := by
    exact_mod_cast (by simpa using M.card_blocks_mul.symm :
      Fintype.card M.Block * Fintype.card (Fin r) = n)
  rw [hn] at hp
  exact hp

end ProbabilityS

end Kahn.PerfectMatching
