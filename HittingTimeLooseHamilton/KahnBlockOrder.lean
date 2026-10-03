module

public import HittingTimeLooseHamilton.KahnOrdering
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Interval.Finset.Fin

public section

/-! Exact finite symmetry behind equation (35) of Kahn's paper. -/

namespace Kahn.Ordering

open Finset

variable {B R L : Type*} [Fintype B] [Fintype R] [Nonempty R]
  [Fintype L] [DecidableEq B] [DecidableEq R] [LinearOrder L]

theorem blockRanks_nonempty (σ : (B × R) ≃ L) (b : B) :
    (univ.image (fun a : R => σ (b, a))).Nonempty :=
  univ_nonempty.image _

/-- Rank at which block `b` is first encountered. -/
@[expose] noncomputable def blockFirstRank (σ : (B × R) ≃ L) (b : B) : L :=
  (univ.image (fun a : R => σ (b, a))).min' (blockRanks_nonempty σ b)

theorem blockFirstRank_mem (σ : (B × R) ≃ L) (b : B) :
    ∃ a : R, blockFirstRank σ b = σ (b, a) := by
  obtain ⟨a, _, ha⟩ := mem_image.mp
    ((univ.image (fun a : R => σ (b, a))).min'_mem (blockRanks_nonempty σ b))
  exact ⟨a, ha.symm⟩

theorem blockFirstRank_le (σ : (B × R) ≃ L) (b : B) (a : R) :
    blockFirstRank σ b ≤ σ (b, a) :=
  min'_le _ _ (mem_image.mpr ⟨a, mem_univ _, rfl⟩)

theorem blockFirstRank_injective (σ : (B × R) ≃ L) :
    Function.Injective (blockFirstRank σ) := by
  intro b c h
  obtain ⟨a, ha⟩ := blockFirstRank_mem σ b
  obtain ⟨d, hd⟩ := blockFirstRank_mem σ c
  rw [ha, hd] at h
  exact congrArg Prod.fst (σ.injective h)

theorem blockFirstRank_relabel (σ : (B × R) ≃ L)
    (g : Equiv.Perm B) (h : Equiv.Perm R) (b : B) :
    blockFirstRank ((Equiv.prodCongr g h).trans σ) b =
      blockFirstRank σ (g b) := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := blockFirstRank_mem σ (g b)
    rw [ha]
    simpa using blockFirstRank_le ((Equiv.prodCongr g h).trans σ) b (h.symm a)
  · obtain ⟨a, ha⟩ := blockFirstRank_mem ((Equiv.prodCongr g h).trans σ) b
    rw [ha]
    exact blockFirstRank_le σ (g b) (h a)

/-- The ranks where previously unseen blocks are encountered. -/
@[expose] noncomputable def blockFirstRanks (σ : (B × R) ≃ L) : Finset L :=
  univ.image (blockFirstRank σ)

theorem card_blockFirstRanks (σ : (B × R) ≃ L) :
    (blockFirstRanks σ).card = Fintype.card B := by
  unfold blockFirstRanks
  rw [card_image_of_injective _ (blockFirstRank_injective σ), card_univ]

theorem blockFirstRanks_relabel (σ : (B × R) ≃ L)
    (g : Equiv.Perm B) (h : Equiv.Perm R) :
    blockFirstRanks ((Equiv.prodCongr g h).trans σ) = blockFirstRanks σ := by
  ext x
  simp only [blockFirstRanks, mem_image, mem_univ, true_and, blockFirstRank_relabel]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨g b, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨g.symm b, by simpa using hb⟩

/-- Vertex at which the `k`th new block is encountered, with blocks numbered
from zero. The rank is obtained by sorting first-occurrence ranks. -/
@[expose] noncomputable def blockOrderVertex (σ : (B × R) ≃ L)
    (k : Fin (Fintype.card B)) : B × R :=
  σ.symm ((blockFirstRanks σ).orderEmbOfFin (card_blockFirstRanks σ) k)

theorem blockOrderVertex_rank (σ : (B × R) ≃ L) (k : Fin (Fintype.card B)) :
    σ (blockOrderVertex σ k) =
      (blockFirstRanks σ).orderEmbOfFin (card_blockFirstRanks σ) k := by
  simp [blockOrderVertex]

theorem blockOrderVertex_first (σ : (B × R) ≃ L) (k : Fin (Fintype.card B)) :
    blockFirstRank σ (blockOrderVertex σ k).1 = σ (blockOrderVertex σ k) := by
  have hmem := (blockFirstRanks σ).orderEmbOfFin_mem (card_blockFirstRanks σ) k
  obtain ⟨b, _, hb⟩ := mem_image.mp hmem
  obtain ⟨a, ha⟩ := blockFirstRank_mem σ b
  have hba : (b, a) = blockOrderVertex σ k := by
    apply σ.injective
    rw [← ha, hb, blockOrderVertex_rank]
  rw [← hba, ← ha]

theorem blockOrderVertex_is_first (σ : (B × R) ≃ L) (k : Fin (Fintype.card B))
    (a : R) : σ (blockOrderVertex σ k) ≤ σ ((blockOrderVertex σ k).1, a) := by
  rw [← blockOrderVertex_first]
  exact blockFirstRank_le σ _ a

theorem blockOrderVertex_block_injective (σ : (B × R) ≃ L) :
    Function.Injective (fun k : Fin (Fintype.card B) => (blockOrderVertex σ k).1) := by
  intro i j hij
  change (blockOrderVertex σ i).1 = (blockOrderVertex σ j).1 at hij
  apply (blockFirstRanks σ).orderEmbOfFin (card_blockFirstRanks σ) |>.injective
  rw [← blockOrderVertex_rank, ← blockOrderVertex_rank,
    ← blockOrderVertex_first, ← blockOrderVertex_first, hij]

/-- The order of the blocks, obtained from their first-occurrence ranks. -/
@[expose] noncomputable def blockOrderEquiv (σ : (B × R) ≃ L) : Fin (Fintype.card B) ≃ B :=
  Equiv.ofBijective (fun k => (blockOrderVertex σ k).1)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨blockOrderVertex_block_injective σ, Fintype.card_fin _⟩)

/-- Deterministic characterization of the vertex opening the `k`th block. -/
theorem blockOrderVertex_eq_iff (σ : (B × R) ≃ L) (k : Fin (Fintype.card B))
    (v : B × R) : blockOrderVertex σ k = v ↔
      σ v = blockFirstRank σ v.1 ∧ (blockOrderEquiv σ).symm v.1 = k := by
  constructor
  · rintro rfl
    refine ⟨(blockOrderVertex_first σ k).symm, ?_⟩
    exact (blockOrderEquiv σ).symm_apply_apply k
  · rintro ⟨hfirst, hindex⟩
    have hb : (blockOrderVertex σ k).1 = v.1 := by
      change blockOrderEquiv σ k = v.1
      rw [← hindex, Equiv.apply_symm_apply]
    apply σ.injective
    rw [← blockOrderVertex_first, hb, ← hfirst]

/-- Later blocks really have later first-occurrence ranks. -/
theorem blockOrderEquiv_lt_iff (σ : (B × R) ≃ L)
    (i j : Fin (Fintype.card B)) :
    blockFirstRank σ (blockOrderEquiv σ i) < blockFirstRank σ (blockOrderEquiv σ j) ↔
      i < j := by
  change blockFirstRank σ (blockOrderVertex σ i).1 <
    blockFirstRank σ (blockOrderVertex σ j).1 ↔ _
  rw [blockOrderVertex_first, blockOrderVertex_first,
    blockOrderVertex_rank, blockOrderVertex_rank]
  exact (blockFirstRanks σ).orderEmbOfFin (card_blockFirstRanks σ) |>.lt_iff_lt

theorem blockOrderVertex_relabel (σ : (B × R) ≃ L)
    (g : Equiv.Perm B) (h : Equiv.Perm R) (k : Fin (Fintype.card B)) :
    blockOrderVertex ((Equiv.prodCongr g h).trans σ) k =
      (Equiv.prodCongr g h).symm (blockOrderVertex σ k) := by
  unfold blockOrderVertex
  simp only [Equiv.symm_trans_apply]
  simp only [blockFirstRanks_relabel]

theorem blockOrderEquiv_relabel (σ : (B × R) ≃ L)
    (g : Equiv.Perm B) (h : Equiv.Perm R) (k : Fin (Fintype.card B)) :
    blockOrderEquiv ((Equiv.prodCongr g h).trans σ) k =
      g.symm (blockOrderEquiv σ k) := by
  change (blockOrderVertex ((Equiv.prodCongr g h).trans σ) k).1 =
    g.symm (blockOrderVertex σ k).1
  rw [blockOrderVertex_relabel]
  rfl

/-- Blocks whose first vertex appears strictly after the `k`th block. -/
@[expose] noncomputable def laterBlocks (σ : (B × R) ≃ L) (k : Fin (Fintype.card B)) : Finset B :=
  (Ioi k).image (blockOrderEquiv σ)

theorem card_laterBlocks (σ : (B × R) ≃ L) (k : Fin (Fintype.card B)) :
    (laterBlocks σ k).card = Fintype.card B - 1 - k := by
  rw [laterBlocks, card_image_of_injective _ (blockOrderEquiv σ).injective, Fin.card_Ioi]

theorem mem_laterBlocks_iff (σ : (B × R) ≃ L) (k : Fin (Fintype.card B)) (b : B) :
    b ∈ laterBlocks σ k ↔ σ (blockOrderVertex σ k) < blockFirstRank σ b := by
  constructor
  · intro hb
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
    rw [← blockOrderVertex_first]
    exact (blockOrderEquiv_lt_iff σ k j).mpr (mem_Ioi.mp hj)
  · intro hb
    refine mem_image.mpr ⟨(blockOrderEquiv σ).symm b, ?_, by simp⟩
    apply mem_Ioi.mpr
    apply (blockOrderEquiv_lt_iff σ k ((blockOrderEquiv σ).symm b)).mp
    rw [(blockOrderEquiv σ).apply_symm_apply]
    change blockFirstRank σ (blockOrderVertex σ k).1 < blockFirstRank σ b
    rwa [blockOrderVertex_first]

theorem blockOrderVertex_not_mem_laterBlocks (σ : (B × R) ≃ L)
    (k : Fin (Fintype.card B)) : (blockOrderVertex σ k).1 ∉ laterBlocks σ k := by
  rw [mem_laterBlocks_iff, blockOrderVertex_first]
  exact lt_irrefl _

theorem laterBlocks_relabel (σ : (B × R) ≃ L)
    (g : Equiv.Perm B) (h : Equiv.Perm R) (k : Fin (Fintype.card B)) :
    laterBlocks ((Equiv.prodCongr g h).trans σ) k = (laterBlocks σ k).image g.symm := by
  simp only [laterBlocks, image_image]
  congr 1
  funext i
  exact blockOrderEquiv_relabel σ g h i

/-- Conditional on a specified vertex opening the `k`th block, all survivor
sets of the same cardinality have the same number of vertex orderings. -/
theorem card_first_later_eq (k : Fin (Fintype.card B)) (v : B × R)
    (S T : Finset B) (hcard : S.card = T.card) (hvS : v.1 ∉ S) (hvT : v.1 ∉ T) :
    (univ.filter (fun σ : (B × R) ≃ L =>
      blockOrderVertex σ k = v ∧ laterBlocks σ k = S)).card =
    (univ.filter (fun σ : (B × R) ≃ L =>
      blockOrderVertex σ k = v ∧ laterBlocks σ k = T)).card := by
  classical
  obtain ⟨g, hg, hmem⟩ := exists_perm_fix_maps_subsets T S hcard.symm v.1 hvT hvS
  have himage : S.image g.symm = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact (hmem (g.symm y)).mpr (by simpa using hy)
    · intro hx
      exact mem_image.mpr ⟨g x, (hmem x).mp hx, by simp⟩
  let τ := Equiv.prodCongr g (Equiv.refl R)
  have hτ : τ v = v := by
    apply Prod.ext
    · exact hg
    · rfl
  let e : ((B × R) ≃ L) ≃ ((B × R) ≃ L) :=
    { toFun := fun σ => τ.trans σ
      invFun := fun σ => τ.symm.trans σ
      left_inv := by intro σ; ext x; simp
      right_inv := by intro σ; ext x; simp }
  apply card_event_eq_of_equiv _ _ e
  intro σ
  change (blockOrderVertex σ k = v ∧ laterBlocks σ k = S) ↔
    (blockOrderVertex (τ.trans σ) k = v ∧ laterBlocks (τ.trans σ) k = T)
  rw [blockOrderVertex_relabel, laterBlocks_relabel]
  constructor
  · rintro ⟨hfirst, hlater⟩
    constructor
    · rw [hfirst]
      exact τ.symm_apply_eq.mpr hτ.symm
    · rw [hlater, himage]
  · rintro ⟨hfirst, hlater⟩
    constructor
    · have hh := congrArg τ hfirst
      change τ (τ.symm (blockOrderVertex σ k)) = τ v at hh
      simpa only [Equiv.apply_symm_apply, hτ] using hh
    · apply image_injective g.symm.injective
      rw [himage]
      exact hlater

/-- The first vertex of the `k`th encountered block is uniform on all
vertices. This is the joint `1/n` probability in Kahn's equation (35).
The vertex ordering is uniform on all bijections from vertices to ranks. -/
theorem blockOrderVertex_uniform [Nonempty ((B × R) ≃ L)]
    (k : Fin (Fintype.card B)) (v : B × R) :
    ((univ.filter (fun σ : (B × R) ≃ L => blockOrderVertex σ k = v)).card : ℝ) /
        Fintype.card ((B × R) ≃ L) = 1 / (Fintype.card B * Fintype.card R) := by
  classical
  have h := uniform_fibre_probability (fun σ : (B × R) ≃ L => blockOrderVertex σ k) v
  rw [Fintype.card_prod, Nat.cast_mul] at h
  apply h
  intro w
  let g := Equiv.swap v.1 w.1
  let h := Equiv.swap v.2 w.2
  let τ := Equiv.prodCongr g h
  have hτv : τ v = w := by
    apply Prod.ext <;> simp [τ, g, h]
  let e : ((B × R) ≃ L) ≃ ((B × R) ≃ L) :=
    { toFun := fun σ => τ.trans σ
      invFun := fun σ => τ.symm.trans σ
      left_inv := by intro σ; ext x; simp
      right_inv := by intro σ; ext x; simp }
  apply card_event_eq_of_equiv _ _ e
  intro σ
  change blockOrderVertex σ k = w ↔ blockOrderVertex (τ.trans σ) k = v
  rw [blockOrderVertex_relabel]
  constructor
  · intro hs
    rw [hs]
    change τ.symm w = v
    exact τ.symm_apply_eq.mpr hτv.symm
  · intro hs
    change τ.symm (blockOrderVertex σ k) = v at hs
    have hh := congrArg τ hs
    simpa only [Equiv.apply_symm_apply, hτv] using hh

end Kahn.Ordering
