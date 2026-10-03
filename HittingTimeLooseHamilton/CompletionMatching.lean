module

public import HittingTimeLooseHamilton.CompletionDirections
public import HittingTimeLooseHamilton.CompletionParameters

public section

/-! # Pair matchings and complete hosts after private deletion -/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restricting supported marked pairs preserves their matching property. -/
theorem IsPairMatching.restrict {markers : Finset (Finset V)}
    (hM : IsPairMatching markers) (S : Finset V)
    (hS : ∀ e ∈ markers, e ⊆ S) : IsPairMatching (restrictEdges S markers) := by
  constructor
  · intro e he
    obtain ⟨m, hm, rfl⟩ := mem_image.mp he
    rw [← liftEdge_card, lift_restrictEdge S m (hS m hm)]
    exact hM.1 m hm
  · intro e he f hf hef
    obtain ⟨m, hm, rfl⟩ := mem_image.mp he
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hf
    change Disjoint (restrictEdge S m) (restrictEdge S n)
    apply (liftEdge_disjoint S _ _).mp
    rw [lift_restrictEdge S m (hS m hm), lift_restrictEdge S n (hS n hn)]
    apply hM.2 hm hn
    intro h
    exact hef (congrArg (restrictEdge S) h)

/-- Deleting vertices from the complete host gives the complete surviving host. -/
theorem inducedHost_completeEdges (S : Finset V) (r : ℕ) :
    inducedHost S (completeEdges V r) = completeEdges ↥S r := by
  ext e
  simp only [mem_inducedHost, mem_completeEdges, ambientEdge_card]

namespace LegalPrivateCompletion
variable {r : ℕ} {markers : Finset (Finset V)} {P pair : Finset V}

theorem augmented_matching (h : LegalPrivateCompletion r markers P pair)
    (hM : IsPairMatching markers) : IsPairMatching (insert pair markers) := by
  constructor
  · intro m hm
    rcases mem_insert.mp hm with rfl | hm
    · exact h.pair_card
    · exact hM.1 m hm
  · intro a ha b hb hab
    have ha' : a = pair ∨ a ∈ markers := mem_insert.mp ha
    have hb' : b = pair ∨ b ∈ markers := mem_insert.mp hb
    rcases ha' with rfl | haM <;> rcases hb' with rfl | hbM
    · exact (hab rfl).elim
    · apply h.ports_disjoint.mono
      · exact subset_union_right
      · intro v hv
        exact mem_biUnion.mpr ⟨b, hbM, hv⟩
    · apply Disjoint.symm
      apply h.ports_disjoint.mono
      · exact subset_union_right
      · intro v hv
        exact mem_biUnion.mpr ⟨a, haM, hv⟩
    · exact hM.2 haM hbM hab

theorem restricted_matching (h : LegalPrivateCompletion r markers P pair)
    (hM : IsPairMatching markers) :
    IsPairMatching (restrictEdges (univ \ P) (insert pair markers)) :=
  (h.augmented_matching hM).restrict _ h.augmented_subset_active

/-- The retained old root and the newly inserted pair remain distinct. -/
theorem restricted_root_ne_pair (h : LegalPrivateCompletion r markers P pair)
    (root : ↥markers) :
    completionRestrictedRoot markers P pair root ≠ completionRestrictedPair markers P pair := by
  intro he
  have he' := congrArg (fun e : ↥(restrictEdges (univ \ P) (insert pair markers)) =>
    liftEdge (univ \ P) e.val) he
  change liftEdge (univ \ P) (restrictEdge (univ \ P) root.val) =
    liftEdge (univ \ P) (restrictEdge (univ \ P) pair) at he'
  rw [lift_restrictEdge _ _ (h.marker_subset_active root.property),
    lift_restrictEdge _ _ h.pair_subset_active] at he'
  exact h.pair_not_mem (he' ▸ root.property)
end LegalPrivateCompletion
end LooseHamilton
