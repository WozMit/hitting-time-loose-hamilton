module

public import HittingTimeLooseHamilton.PermutationCycle

public section
noncomputable section
open Finset
namespace LooseHamilton
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {r : ℕ} {markers : Finset (Finset V)}
/-- A marked block has a start and an end junction, an ordinary block only one. -/
abbrev BlockJunctions (markers : Finset (Finset V)) (J : Type*) := (↥markers ⊕ J) ⊕ ↥markers
/-- Marker starts carry marked slots; block ends carry the succeeding ordinary slots. -/
@[expose] def blockSlot (markers : Finset (Finset V)) (J : Type*) :
    BlockJunctions markers J ≃ (↥markers ⊕ (↥markers ⊕ J)) where
  toFun := fun x => match x with
    | .inl (.inl m) => .inl m
    | .inl (.inr j) => .inr (.inr j)
    | .inr m => .inr (.inl m)
  invFun := fun x => match x with
    | .inl m => .inl (.inl m)
    | .inr (.inl m) => .inr m
    | .inr (.inr j) => .inl (.inr j)
  left_inv := by intro x; rcases x with (m|j)|m <;> rfl
  right_inv := by intro x; rcases x with m|(m|j) <;> rfl

@[expose] def markerEmbedding (markers : Finset (Finset V)) (J : Type*) :
    ↥markers ↪ (↥markers ⊕ J) := ⟨Sum.inl, Sum.inl_injective⟩

/-- Decode a cyclic block order and allocation once its actual junction placement is given. -/
@[expose] def blockCycleData
    (σ : Equiv.Perm (↥markers ⊕ J)) (hσ : σ.IsCycleOn Set.univ)
    (hcard : 3 ≤ Fintype.card (BlockJunctions markers J))
    (root : ↥markers ⊕ J)
    (j : BlockJunctions markers J ↪ V)
    (P : (↥markers ⊕ J) → Finset V)
    (hPcard : ∀ b, (P b).card = r - 2)
    (hPdisj : Pairwise (fun b c => Disjoint (P b) (P c)))
    (hJP : ∀ b, Disjoint (univ.image j) (P b))
    (hcover : univ = univ.image j ∪ univ.biUnion P)
    (hmatching : (markers : Set (Finset V)).PairwiseDisjoint id)
    (hpairs : ∀ m : ↥markers, m.val = {j (.inl (.inl m)), j (.inr m)}) :
    PermutationCycleData r markers (BlockJunctions markers J) (↥markers ⊕ J) where
  card_ge := hcard
  successor := BlockEnumeration.gapPermutation σ (markerEmbedding markers J)
  cyclic := BlockEnumeration.gapPermutation_isCycleOn σ _ hσ
  root := .inl root
  junction := j
  slot := blockSlot markers J
  privateBlock := P
  private_card := hPcard
  private_disjoint := hPdisj
  junction_private_disjoint := hJP
  cover := hcover
  marked_matching := hmatching
  marked_edge := by
    intro m
    change m.val = {j (.inl (.inl m)), j (BlockEnumeration.gapPermutation σ
      (markerEmbedding markers J) (.inl (.inl m)))}
    change m.val = {j (.inl (.inl m)), j (BlockEnumeration.gapNext σ
      (markerEmbedding markers J) (.inl (markerEmbedding markers J m)))}
    rw [BlockEnumeration.gapNext_gap]
    exact hpairs m
end LooseHamilton
