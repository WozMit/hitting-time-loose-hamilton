module

public import HittingTimeLooseHamilton.BootstrapActualFrameRealization
public import HittingTimeLooseHamilton.BootstrapBases
public import HittingTimeLooseHamilton.MigrationReturns

public section

/-! Actual completion sources over the ordinary and original-port bases.
The original forbidden ports are retained throughout. -/
noncomputable section
namespace LooseHamilton.BootstrapActualSourceFrames
open Finset BootstrapBases
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

omit [Fintype V] in
theorem source_marker_budget (hM : IsPairMatching M) (b : Base M) (q : Finset V) :
    MarkerBudget M (insert q (markers hM b)) := by
  cases b with
  | none => exact markerBudget_insert M q
  | some a => exact markerBudget_erase_insert M _ q

omit [Fintype V] in
theorem candidate_marker_budget (hM : IsPairMatching M) (b : Base M)
    (q p : Finset V) : MarkerBudget M (insert p (insert q (markers hM b))) := by
  cases b with
  | none => exact markerBudget_insert_two M p q
  | some a => exact markerBudget_erase_insert_two M _ p q

/-- Source labels themselves construct a legal frame. Fresh-pair legality gives
matching; the base restriction is imposed before the private deletion. -/
theorem exists_source (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    (P : Finset V) (u v : V)
    (hs : LegalPrivateCompletion r (markers hM b) P {u,v})
    (hp : ({u,v} : Finset V) ⊆ active b) :
    ∃ F : AuxiliaryFrame.Frame r M,
      F.val.deleted = deleted b ∪ P ∧ F.markers = insert {u,v} (markers hM b) ∧
      F.val.root = (u,v) ∧ F.val.relative = none := by
  apply AuxiliaryFrame.exists_frame r M _ _ (u,v) none hM
    (hs.augmented_matching (markers_matching hM b))
  · have h := card_union_le (deleted b) P
    have hδ := deleted_card_le b
    rw [hs.private_card] at h
    omega
  · exact source_marker_budget hM b {u,v}
  · intro e he w hw
    have hP := (mem_sdiff.mp (hs.augmented_subset_active e he hw)).2
    have hb : w ∈ active b := by
      rcases mem_insert.mp he with rfl | he
      · exact hp hw
      · exact markers_retained hM b he hw
    have hD := (mem_sdiff.mp hb).2
    exact mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim hD hP⟩
  · exact mem_insert_self _ _
  · simp

/-- The source count is the actual completion count after the base and private
blocks are deleted. No surviving port is dropped from the prohibition. -/
theorem source_count (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (P : Finset V) (u v : V)
    (hD : F.val.deleted = deleted b ∪ P)
    (hM' : F.markers = insert {u,v} (markers hM b))
    (hrel : F.val.relative = none) (H : SimpleHypergraph V) :
    F.cycleCount H = completionCount r (markers hM b)
      (H ∩ allowedEdges r (originalPorts M)) (deleted b ∪ P) {u,v} :=
  F.cycleCount_private_source hrel H (markers hM b) _ _ hD hM'

/-- For a source frame every legal fresh candidate has the required two-marker
budget, and so is realized by its own actual one-relative-direction frame. -/
theorem exists_source_candidate (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (q : Finset V)
    (hm : F.markers = insert q (markers hM b))
    (c : Finset V × V × V) (hc : F.LegalCandidate c)
    (hd : (F.val.deleted ∪ c.1).card ≤ 4*r) :
    ∃ G : AuxiliaryFrame.Frame r M, G.val.deleted = F.val.deleted ∪ c.1 ∧
      G.markers = insert {c.2.1,c.2.2} F.markers ∧ G.val.root = F.val.root ∧
      G.val.relative = some c.2 := by
  apply F.exists_actual_candidate hM c hc hd
  rw [hm]
  exact candidate_marker_budget hM b q _

/-- Frame existence and the count dictionary hold simultaneously for every host.
The construction therefore never chooses a tag in place of the actual family. -/
theorem source_realization (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    (P : Finset V) (u v : V)
    (hs : LegalPrivateCompletion r (markers hM b) P {u,v})
    (hp : ({u,v} : Finset V) ⊆ active b) :
    ∃ F : AuxiliaryFrame.Frame r M,
      F.val.deleted = deleted b ∪ P ∧ F.markers = insert {u,v} (markers hM b) ∧
      F.val.root = (u,v) ∧ F.val.relative = none ∧
      ∀ H, F.cycleCount H = completionCount r (markers hM b)
        (H ∩ allowedEdges r (originalPorts M)) (deleted b ∪ P) {u,v} := by
  obtain ⟨F,hd,hm,hr',hq⟩ := exists_source hM b hr P u v hs hp
  exact ⟨F,hd,hm,hr',hq,fun H => source_count hM b F P u v hd hm hq H⟩

/-- Candidate realization also identifies the direction-sensitive count for
all hosts, with one additional relative label and no extra factor. -/
theorem source_candidate_realization (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (q : Finset V)
    (hm : F.markers = insert q (markers hM b)) (hrel : F.val.relative = none)
    (c : Finset V × V × V) (hc : F.LegalCandidate c)
    (hd : (F.val.deleted ∪ c.1).card ≤ 4*r) :
    ∃ G : AuxiliaryFrame.Frame r M, G.val.deleted = F.val.deleted ∪ c.1 ∧
      G.markers = insert {c.2.1,c.2.2} F.markers ∧ G.val.root = F.val.root ∧
      G.val.relative = some c.2 ∧ ∀ H, G.cycleCount H = F.completionCount H c := by
  obtain ⟨G,hd',hm',hp,hq⟩ := exists_source_candidate hM b F q hm c hc hd
  exact ⟨G,hd',hm',hp,hq,fun H => F.actual_candidate_count G hrel c hd' hm' hp hq H⟩

/-- In the actual surviving vertex type, arbitrary histories return to the
same fixed base, with only their current private block still deleted. -/
theorem moves_return_to_base (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    (G : SimpleHypergraph ↥(active b)) (n : ℕ)
    (P q : Fin n → Finset ↥(active b))
    (E : Fin n → SimpleHypergraph ↥(active b))
    (moves : ∀ i, MigrationReturn r (restrictEdges (active b) (markers hM b))
      G (P i) (q i) (E i)) :
    ∀ i, E i ∈ completionFamily r (restrictEdges (active b) (markers hM b))
      G (P i) (q i) ∧ (univ \ (univ \ P i)).card = r-2 :=
  migration_returns_do_not_accumulate hr P q E moves

end LooseHamilton.BootstrapActualSourceFrames
