module

public import HittingTimeLooseHamilton.BootstrapEndpointMatching
public import HittingTimeLooseHamilton.BootstrapActualDeletionBounds
public import HittingTimeLooseHamilton.BootstrapActualFrameRealization

public section

/-! Literal endpoint cores and directed splice candidates in both original bases.
Only the named new endpoints must survive the initial base deletion; retention
of old markers follows from the original matching. All filters remain original. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointFrames
open Finset BootstrapBases AuxiliaryFrame
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original G : Finset (Finset V)} {P : Finset V} {y z t : V}

private theorem retained_union {D E m : Finset V}
    (hD : m ⊆ univ \ D) (hE : m ⊆ univ \ E) : m ⊆ univ \ (D ∪ E) := by
  intro v hv
  have hd := (mem_sdiff.mp (hD hv)).2
  have he := (mem_sdiff.mp (hE hv)).2
  simpa only [mem_sdiff, mem_univ, mem_union, true_and, not_or] using And.intro hd he

theorem endpointI_core_exists (ho : IsPairMatching original) (b : Base original)
    (hr : 3 ≤ r) (hs : LegalPrivateCompletion r (markers ho b) P {y,z})
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r (markers ho b) G P y z l)
    (hroot : ({l.1,z} : Finset V) ⊆ active b)
    : ∃ F : Frame r original, F.val.deleted = deleted b ∪ (P ∪ l.deleted y) ∧
      F.val.markers original = l.markers (markers ho b) z ∧
      F.val.root = (l.1,z) ∧ F.val.relative = none := by
  have hm := markers_matching ho b
  have hmatch := endpointCutI_pairMatching hs hm hl
  have hlocal := endpointCutI_markers_survive hs hl
  have hbase : ∀ m ∈ l.markers (markers ho b) z, m ⊆ active b := by
    intro m hmem
    rcases mem_insert.mp hmem with rfl | hmem
    · exact hroot
    · exact markers_retained ho b hmem
  have hb : MarkerBudget original (l.markers (markers ho b) z) := by
    cases b with
    | none =>
      simpa only [EndpointCutLabelI.markers, markers_none, insert_idem] using
        markerBudget_cutI original l z l.1 z
    | some a =>
      simpa only [EndpointCutLabelI.markers, markers_some, insert_idem] using
        markerBudget_port_cutI original {a.val, OriginalPortPartner.partner ho a} l z l.1 z
  have hd := BootstrapActualDeletionBounds.endpointI_core_budget b P y l hr
    hs.private_card hl.private_card
  apply exists_frame r original (l.markers (markers ho b) z)
    (deleted b ∪ (P ∪ l.deleted y)) (l.1,z) (none) ho hmatch (by omega) hb
  · intro m hmem
    exact retained_union (hbase m hmem) (hlocal m hmem)
  · exact mem_insert_self _ _
  · simp

theorem endpointI_candidate_exists (ho : IsPairMatching original) (b : Base original)
    (hr : 3 ≤ r) (hs : LegalPrivateCompletion r (markers ho b) P {y,z})
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r (markers ho b) G P y z l)
    (hroot : ({l.1,z} : Finset V) ⊆ active b)
    {q : EndpointSpliceInnerLabel V} (hq : EndpointSpliceLegalI r (markers ho b) G P y z t l q)
    (hpair : ({q.2,t} : Finset V) ⊆ active b)
    : ∃ F : Frame r original, F.val.deleted = deleted b ∪ (P ∪ l.deleted y ∪ q.1) ∧
      F.val.markers original = insert {q.2,t} (l.markers (markers ho b) z) ∧
      F.val.root = (l.1,z) ∧ F.val.relative = some (q.2,t) := by
  have hm := markers_matching ho b
  have hmatch := endpointSpliceI_pairMatching hs hm hl hq
  have hlocal := endpointSpliceI_markers_survive hs hl hq
  have hbase : ∀ m ∈ insert {q.2,t} (l.markers (markers ho b) z), m ⊆ active b := by
    intro m hmem
    rcases mem_insert.mp hmem with rfl | hmem
    · exact hpair
    · rcases mem_insert.mp hmem with rfl | hmem
      · exact hroot
      · exact markers_retained ho b hmem
  have hb : MarkerBudget original (insert {q.2,t} (l.markers (markers ho b) z)) := by
    cases b with
    | none =>
      exact markerBudget_cutI original l z q.2 t
    | some a =>
      exact markerBudget_port_cutI original {a.val, OriginalPortPartner.partner ho a} l z q.2 t
  have hd := BootstrapActualDeletionBounds.endpointI_candidate_budget b P y l q hr
    hs.private_card hl.private_card hq.private_card
  apply exists_frame r original (insert {q.2,t} (l.markers (markers ho b) z))
    (deleted b ∪ (P ∪ l.deleted y ∪ q.1)) (l.1,z) (some (q.2,t)) ho hmatch (by omega) hb
  · intro m hmem
    exact retained_union (hbase m hmem) (hlocal m hmem)
  · exact mem_insert_of_mem (mem_insert_self _ _)
  · intro p hp; cases Option.mem_some_iff.mp hp; exact mem_insert_self _ _

theorem endpointII_core_exists (ho : IsPairMatching original) (b : Base original)
    (hr : 3 ≤ r) (hs : LegalPrivateCompletion r (markers ho b) P {y,z})
    {l : EndpointCutLabelII V} (hl : EndpointCutLegalII r (markers ho b) G P y z l)
    (hroot : ({l.2.2.1,z} : Finset V) ⊆ active b)
    : ∃ F : Frame r original, F.val.deleted = deleted b ∪ (P ∪ l.deleted y) ∧
      F.val.markers original = l.markers (markers ho b) z ∧
      F.val.root = (l.2.2.1,z) ∧ F.val.relative = none := by
  have hm := markers_matching ho b
  have hmatch := endpointCutII_pairMatching hs hm hl
  have hlocal := endpointCutII_markers_survive hs hm.2 hl
  have hbase : ∀ m ∈ l.markers (markers ho b) z, m ⊆ active b := by
    intro m hmem
    rcases mem_insert.mp hmem with rfl | hmem
    · exact hroot
    · exact markers_retained ho b (mem_erase.mp hmem).2
  have hb : MarkerBudget original (l.markers (markers ho b) z) := by
    cases b with
    | none =>
      simpa only [EndpointCutLabelII.markers, markers_none, insert_idem] using
        markerBudget_cutII original l z l.2.2.1 z
    | some a =>
      simpa only [EndpointCutLabelII.markers, markers_some, insert_idem] using
        markerBudget_port_cutII original {a.val, OriginalPortPartner.partner ho a} l z l.2.2.1 z
  have hd := BootstrapActualDeletionBounds.endpointII_core_budget b P y l hr
    hs.private_card hl.first_private_card hl.second_private_card
  apply exists_frame r original (l.markers (markers ho b) z)
    (deleted b ∪ (P ∪ l.deleted y)) (l.2.2.1,z) (none) ho hmatch (by omega) hb
  · intro m hmem
    exact retained_union (hbase m hmem) (hlocal m hmem)
  · exact mem_insert_self _ _
  · simp

theorem endpointII_candidate_exists (ho : IsPairMatching original) (b : Base original)
    (hr : 3 ≤ r) (hs : LegalPrivateCompletion r (markers ho b) P {y,z})
    {l : EndpointCutLabelII V} (hl : EndpointCutLegalII r (markers ho b) G P y z l)
    (hroot : ({l.2.2.1,z} : Finset V) ⊆ active b)
    {q : EndpointSpliceInnerLabel V} (hq : EndpointSpliceLegalII r (markers ho b) G P y z t l q)
    (hpair : ({q.2,t} : Finset V) ⊆ active b)
    : ∃ F : Frame r original, F.val.deleted = deleted b ∪ (P ∪ l.deleted y ∪ q.1) ∧
      F.val.markers original = insert {q.2,t} (l.markers (markers ho b) z) ∧
      F.val.root = (l.2.2.1,z) ∧ F.val.relative = some (q.2,t) := by
  have hm := markers_matching ho b
  have hmatch := endpointSpliceII_pairMatching hs hm hl hq
  have hlocal := endpointSpliceII_markers_survive hs hm.2 hl hq
  have hbase : ∀ m ∈ insert {q.2,t} (l.markers (markers ho b) z), m ⊆ active b := by
    intro m hmem
    rcases mem_insert.mp hmem with rfl | hmem
    · exact hpair
    · rcases mem_insert.mp hmem with rfl | hmem
      · exact hroot
      · exact markers_retained ho b (mem_erase.mp hmem).2
  have hb : MarkerBudget original (insert {q.2,t} (l.markers (markers ho b) z)) := by
    cases b with
    | none =>
      exact markerBudget_cutII original l z q.2 t
    | some a =>
      exact markerBudget_port_cutII original {a.val, OriginalPortPartner.partner ho a} l z q.2 t
  have hd := BootstrapActualDeletionBounds.endpointII_candidate_budget b P y l q hr
    hs.private_card hl.first_private_card hl.second_private_card hq.private_card
  apply exists_frame r original (insert {q.2,t} (l.markers (markers ho b) z))
    (deleted b ∪ (P ∪ l.deleted y ∪ q.1)) (l.2.2.1,z) (some (q.2,t)) ho hmatch (by omega) hb
  · intro m hmem
    exact retained_union (hbase m hmem) (hlocal m hmem)
  · exact mem_insert_of_mem (mem_insert_self _ _)
  · intro p hp; cases Option.mem_some_iff.mp hp; exact mem_insert_self _ _

end LooseHamilton.BootstrapEndpointFrames
