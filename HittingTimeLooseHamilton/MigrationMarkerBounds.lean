module

public import HittingTimeLooseHamilton.EndpointCutModels

public section

/-! # Marker changes in migration frames

All budgets are measured against the original marker family. Erasures count old
markers lost; insertions count genuinely new markers. No disjointness or
matching assumption is needed for these upper bounds.
-/
namespace LooseHamilton
open Finset
variable {α : Type*} [DecidableEq α]

/-- At most two original markers disappear, and at most two new markers appear. -/
structure MarkerBudget (original current : Finset α) : Prop where
  removed_le : (original \ current).card ≤ 2
  introduced_le : (current \ original).card ≤ 2

/-- A bound by explicit deleted and inserted label sets allows arbitrary overlap. -/
theorem markerBudget_of_changes (original deleted added : Finset α)
    (hd : deleted.card ≤ 2) (ha : added.card ≤ 2) :
    MarkerBudget original ((original \ deleted) ∪ added) := by
  constructor
  · apply (card_le_card (show original \ ((original \ deleted) ∪ added) ⊆ deleted from ?_)).trans hd
    intro x hx
    simp only [mem_sdiff, mem_union] at hx
    by_contra hn
    exact hx.2 (Or.inl ⟨hx.1,hn⟩)
  · apply (card_le_card (show ((original \ deleted) ∪ added) \ original ⊆ added from ?_)).trans ha
    intro x hx
    simp only [mem_sdiff, mem_union] at hx
    rcases hx.1 with hx' | hx'
    · exact False.elim (hx.2 hx'.1)
    · exact hx'

/-- The raw two-erasure, two-insertion form used by the largest migration frame. -/
theorem markerBudget_erase_two_insert_two (original : Finset α) (p q a b : α) :
    MarkerBudget original (insert a (insert b ((original.erase p).erase q))) := by
  have hd : ({p,q} : Finset α).card ≤ 2 := (card_insert_le _ _).trans (by simp)
  have ha : ({a,b} : Finset α).card ≤ 2 := (card_insert_le _ _).trans (by simp)
  have he : (original \ {p,q}) ∪ {a,b} = insert a (insert b ((original.erase p).erase q)) := by
    ext x
    simp only [mem_union, mem_sdiff, mem_insert, mem_singleton, mem_erase]
    tauto
  simpa only [he] using markerBudget_of_changes original {p,q} {a,b} hd ha

/-- A single old-marker erasure is included, even if its label is absent. -/
theorem markerBudget_erase_insert_two (original : Finset α) (p a b : α) :
    MarkerBudget original (insert a (insert b (original.erase p))) := by
  simpa only [erase_idem] using markerBudget_erase_two_insert_two original p p a b

/-- The ordinary-vertex frame keeps every original marker. -/
theorem markerBudget_insert_two (original : Finset α) (a b : α) :
    MarkerBudget original (insert a (insert b original)) := by
  have ha : ({a,b} : Finset α).card ≤ 2 := (card_insert_le _ _).trans (by simp)
  have he : (original \ ∅) ∪ {a,b} = insert a (insert b original) := by
    ext x
    simp only [sdiff_empty, mem_union, mem_insert, mem_singleton]
    tauto
  simpa only [he] using markerBudget_of_changes original ∅ {a,b} (by simp) ha

/-- Final output cycles have only one newly inserted marker. -/
theorem markerBudget_insert (original : Finset α) (a : α) :
    MarkerBudget original (insert a original) := by
  simpa only [insert_idem] using markerBudget_insert_two original a a

theorem markerBudget_erase_insert (original : Finset α) (p a : α) :
    MarkerBudget original (insert a (original.erase p)) := by
  simpa only [insert_idem] using markerBudget_erase_insert_two original p a a

section CutFrames
variable {V : Type*} [DecidableEq V]

/-- Type I directed inputs in the ordinary-vertex frame introduce at most two markers. -/
theorem markerBudget_cutI (original : Finset (Finset V)) (l : EndpointCutLabelI V)
    (z v t : V) :
    MarkerBudget original (insert {v,t} (l.markers original z)) :=
  markerBudget_insert_two original {v,t} {l.1,z}

/-- Type II ordinary-frame inputs remove one old marker and introduce at most two. -/
theorem markerBudget_cutII (original : Finset (Finset V)) (l : EndpointCutLabelII V)
    (z v t : V) :
    MarkerBudget original (insert {v,t} (l.markers original z)) :=
  markerBudget_erase_insert_two original l.oldMarker {v,t} {l.2.2.1,z}

/-- If the frame begins at an original port, its own old pair has already been removed. -/
theorem markerBudget_port_cutI (original : Finset (Finset V)) (oldPair : Finset V)
    (l : EndpointCutLabelI V) (z v t : V) :
    MarkerBudget original (insert {v,t} (l.markers (original.erase oldPair) z)) :=
  markerBudget_erase_insert_two original oldPair {v,t} {l.1,z}

/-- The original-port Type II frame is the maximal case: two removals and two insertions. -/
theorem markerBudget_port_cutII (original : Finset (Finset V)) (oldPair : Finset V)
    (l : EndpointCutLabelII V) (z v t : V) :
    MarkerBudget original (insert {v,t} (l.markers (original.erase oldPair) z)) :=
  markerBudget_erase_two_insert_two original oldPair l.oldMarker {v,t} {l.2.2.1,z}

/-- A private-coordinate input is also covered by the ordinary-frame budget. -/
theorem markerBudget_private_input (original : Finset (Finset V)) (uv yz : Finset V) :
    MarkerBudget original (insert uv (insert yz original)) :=
  markerBudget_insert_two original uv yz

/-- Private-coordinate migration after deleting the original root marker. -/
theorem markerBudget_port_private_input (original : Finset (Finset V))
    (oldPair uv yz : Finset V) :
    MarkerBudget original (insert uv (insert yz (original.erase oldPair))) :=
  markerBudget_erase_insert_two original oldPair uv yz

/-- The temporary two-opt pairs obey the same budget as the directed input. -/
theorem markerBudget_twoOpt (original : Finset (Finset V)) (p q : Finset V)
    (a z v t : V) :
    MarkerBudget original (insert {v,a} (insert {t,z} ((original.erase p).erase q))) :=
  markerBudget_erase_two_insert_two original p q {v,a} {t,z}

end CutFrames
end LooseHamilton
