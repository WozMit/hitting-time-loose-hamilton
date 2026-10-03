module

public import HittingTimeLooseHamilton.Models
public import HittingTimeLooseHamilton.UniformEvents

public section

/-! Fixed hypergraphs as subsets of the complete-edge sample space. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- The same edges, now represented in the complete-edge subtype. -/
@[expose] def liftEdges (r : ℕ) (F : SimpleHypergraph V) : Finset (Edge V r) :=
  univ.filter (fun e => e.val ∈ F)

@[simp] theorem mem_liftEdges (F : SimpleHypergraph V) (e : Edge V r) :
    e ∈ liftEdges r F ↔ e.val ∈ F := by simp [liftEdges]

theorem liftEdges_image {F : SimpleHypergraph V} (hF : F ⊆ completeEdges V r) :
    (liftEdges r F).image Subtype.val = F := by
  ext e
  simp only [mem_image, mem_liftEdges]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro he; exact ⟨⟨e, hF he⟩, he, rfl⟩

theorem liftEdges_card {F : SimpleHypergraph V} (hF : F ⊆ completeEdges V r) :
    (liftEdges r F).card = F.card := by
  calc
    (liftEdges r F).card = ((liftEdges r F).image Subtype.val).card :=
      (card_image_iff.mpr (fun a _ b _ h => Subtype.ext h)).symm
    _ = F.card := congrArg Finset.card (liftEdges_image hF)

/-- Prefix equality in rank coordinates is precisely the existing process event. -/
theorem processState_eq_iff_rank_prefix {F : SimpleHypergraph V}
    (hF : F ⊆ completeEdges V r) (σ : EdgeOrder V r) (m : ℕ) :
    processState σ m = F ↔
      univ.filter (fun e : Edge V r => ((orderRankEquiv (Edge V r) σ) e).val < m) =
        liftEdges r F := by
  have hsame : ∀ e : Edge V r, e.val ∈ processState σ m ↔ edgeRank σ e < m := by
    intro e
    simp only [processState, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, he⟩
      have : a = e := Subtype.ext he
      simpa [this] using ha
    · intro he; exact ⟨e, he, rfl⟩
  constructor
  · intro h
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_liftEdges]
    change edgeRank σ e < m ↔ e.val ∈ F
    rw [← h, hsame]
  · intro h
    apply Finset.Subset.antisymm
    · intro e he
      have hc := processState_subset σ m he
      have hx := (hsame ⟨e,hc⟩).mp he
      have : (⟨e,hc⟩ : Edge V r) ∈ liftEdges r F := by
        rw [← h]
        exact mem_filter.mpr ⟨mem_univ _, hx⟩
      exact (mem_liftEdges F _).mp this
    · intro e he
      apply (hsame ⟨e,hF he⟩).mpr
      have : (⟨e,hF he⟩ : Edge V r) ∈ liftEdges r F := (mem_liftEdges F _).mpr he
      rw [← h] at this
      exact (mem_filter.mp this).2
end LooseHamilton
