module

public import HittingTimeLooseHamilton.Setup

public section

/-! The deterministic last-edge characterization of the minimum-degree-one
stopping state. Counts are over actual edge sets in the fixed complete host. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges containing a vertex whose final degree is exactly one. -/
@[expose] def criticalEdges (F : SimpleHypergraph V) : SimpleHypergraph V :=
  F.filter (fun e => ∃ v ∈ e, vertexDegree F v = 1)

@[simp] theorem mem_criticalEdges (F : SimpleHypergraph V) (e : Finset V) :
    e ∈ criticalEdges F ↔ e ∈ F ∧ ∃ v ∈ e, vertexDegree F v = 1 := by
  simp [criticalEdges]

/-- The process stops at the actual edge set `F`. -/
@[expose] def stoppingStateEvent {r : ℕ} (σ : EdgeOrder V r) (F : SimpleHypergraph V) : Prop :=
  ∃ m : ℕ, tauOne σ = (m : WithTop ℕ) ∧ processState σ m = F

theorem noIsolated_mono {F G : SimpleHypergraph V} (hFG : F ⊆ G)
    (hF : NoIsolated F) : NoIsolated G := by
  intro v
  exact (hF v).trans (card_le_card (filter_subset_filter _ hFG))

theorem vertexDegree_erase_of_mem {F : SimpleHypergraph V} {e : Finset V} {v : V}
    (he : e ∈ F) (hv : v ∈ e) :
    vertexDegree (F.erase e) v = vertexDegree F v - 1 := by
  unfold vertexDegree
  rw [filter_erase, card_erase_of_mem (mem_filter.mpr ⟨he,hv⟩)]

theorem vertexDegree_erase_of_not_mem {F : SimpleHypergraph V} {e : Finset V} {v : V}
    (hv : v ∉ e) : vertexDegree (F.erase e) v = vertexDegree F v := by
  unfold vertexDegree
  rw [filter_erase, erase_eq_of_notMem]
  simp [hv]

/-- Deleting an edge creates an isolated vertex exactly when that edge is critical. -/
theorem mem_criticalEdges_iff_delete_not_noIsolated {F : SimpleHypergraph V}
    (hF : NoIsolated F) {e : Finset V} (he : e ∈ F) :
    e ∈ criticalEdges F ↔ ¬ NoIsolated (F.erase e) := by
  classical
  rw [mem_criticalEdges]
  constructor
  · rintro ⟨_,v,hv,hd⟩ hNI
    have hh := hNI v
    rw [vertexDegree_erase_of_mem he hv,hd] at hh
    omega
  · intro hNI
    have hex : ∃ v, ¬ 1 ≤ vertexDegree (F.erase e) v := by
      simpa only [NoIsolated,not_forall] using hNI
    obtain ⟨v,hv⟩ := hex
    have hve : v ∈ e := by
      by_contra hn
      rw [vertexDegree_erase_of_not_mem hn] at hv
      exact hv (hF v)
    refine ⟨he,v,hve,?_⟩
    rw [vertexDegree_erase_of_mem he hve] at hv
    have hh := hF v
    omega

@[simp] theorem processState_mem_edge {r : ℕ} (σ : EdgeOrder V r) (m : ℕ)
    (e : Edge V r) : e.val ∈ processState σ m ↔ edgeRank σ e < m := by
  constructor
  · intro he
    obtain ⟨f,hf,hfe⟩ := mem_image.mp he
    have hfe' : f = e := Subtype.ext hfe
    subst f
    exact (mem_filter.mp hf).2
  · intro he
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,he⟩,rfl⟩

theorem edgeRank_exists {r : ℕ} (σ : EdgeOrder V r) {k : ℕ}
    (hk : k < (completeEdges V r).card) : ∃ e : Edge V r, edgeRank σ e = k := by
  have hk' : k < Fintype.card (Edge V r) := by simpa using hk
  refine ⟨σ.symm ((Fintype.equivFin (Edge V r)).symm ⟨k,hk'⟩),?_⟩
  simp [edgeRank]

/-- The previous state is obtained by deleting the uniquely ranked final edge. -/
theorem processState_erase_last {r : ℕ} (σ : EdgeOrder V r) {m : ℕ} (hm : 0 < m)
    (e : Edge V r) (he : edgeRank σ e = m - 1) :
    processState σ (m - 1) = (processState σ m).erase e.val := by
  ext f
  by_cases hf : f ∈ completeEdges V r
  · let f' : Edge V r := ⟨f,hf⟩
    have hne : f ≠ e.val ↔ edgeRank σ f' ≠ edgeRank σ e := by
      constructor
      · intro hn hh
        exact hn (congrArg Subtype.val (edgeRank_injective σ hh))
      · intro hn hh
        exact hn (congrArg (edgeRank σ) (Subtype.ext hh))
    change f'.val ∈ processState σ (m - 1) ↔ _
    rw [processState_mem_edge,mem_erase]
    change edgeRank σ f' < m - 1 ↔ f ≠ e.val ∧ f'.val ∈ processState σ m
    rw [processState_mem_edge]
    change edgeRank σ f' < m - 1 ↔ f ≠ e.val ∧ edgeRank σ f' < m
    rw [hne,he]
    omega
  · have hleft : f ∉ processState σ (m - 1) := fun hh => hf (processState_subset σ _ hh)
    have hright : f ∉ processState σ m := fun hh => hf (processState_subset σ _ hh)
    simp [hleft,hright]

/-- Exact finite-time characterization, with every earlier time excluded. -/
theorem tauOne_eq_iff_first {r : ℕ} (σ : EdgeOrder V r) (m : ℕ) :
    tauOne σ = (m : WithTop ℕ) ↔ m ≤ (completeEdges V r).card ∧
      NoIsolated (processState σ m) ∧ ∀ k < m, ¬ NoIsolated (processState σ k) := by
  classical
  constructor
  · intro h
    obtain ⟨hm,hNI⟩ := firstTime_spec (completeEdges V r).card (processState σ) NoIsolated (t := m) h
    refine ⟨hm,hNI,?_⟩
    intro k hk
    apply not_before_firstTime _ _ _ (Nat.le_trans (Nat.le_of_lt hk) hm)
    change (k : WithTop ℕ) < tauOne σ
    rw [h]
    exact WithTop.coe_lt_coe.mpr hk
  · rintro ⟨hm,hNI,hprev⟩
    apply le_antisymm (firstTime_le _ _ _ hm hNI)
    unfold firstTime
    apply Finset.le_min
    intro k hk
    have hNI' := (mem_filter.mp hk).2
    apply WithTop.coe_le_coe.mpr
    by_contra hn
    exact hprev k (Nat.lt_of_not_ge hn) hNI'

/-- Monotonicity reduces all earlier-time exclusions to the predecessor. -/
theorem tauOne_eq_iff_predecessor {r : ℕ} (σ : EdgeOrder V r) {m : ℕ} (hm : 0 < m)
    (hbound : m ≤ (completeEdges V r).card) :
    tauOne σ = (m : WithTop ℕ) ↔ NoIsolated (processState σ m) ∧
      ¬ NoIsolated (processState σ (m - 1)) := by
  rw [tauOne_eq_iff_first]
  constructor
  · rintro ⟨_,hNI,hprev⟩
    exact ⟨hNI,hprev _ (by omega)⟩
  · rintro ⟨hNI,hprev⟩
    refine ⟨hbound,hNI,?_⟩
    intro k hk hNk
    exact hprev (noIsolated_mono (processState_mono σ (show k ≤ m - 1 by omega)) hNk)

/-- Nonempty vertex sets cannot be covered by an empty edge family. -/
theorem NoIsolated.card_pos [Nonempty V] {F : SimpleHypergraph V} (hF : NoIsolated F) :
    0 < F.card := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have h := (hF v).trans (card_le_card (filter_subset (fun e => v ∈ e) F))
  exact h

/-- At a stopping state the time is exactly its number of edges. -/
theorem stoppingStateEvent_iff_time_card {r : ℕ} (σ : EdgeOrder V r)
    (F : SimpleHypergraph V) :
    stoppingStateEvent σ F ↔ tauOne σ = (F.card : WithTop ℕ) ∧ processState σ F.card = F := by
  constructor
  · rintro ⟨m,hm,hstate⟩
    have hbound := (firstTime_spec (completeEdges V r).card (processState σ) NoIsolated (t := m) hm).1
    have hc : F.card = m := by
      rw [← hstate,processState_card,min_eq_left hbound]
    simpa only [hc] using And.intro hm hstate
  · rintro ⟨hm,hstate⟩
    exact ⟨F.card,hm,hstate⟩

/-- The deterministic event underlying the stopping-bias probability formula. -/
theorem stoppingStateEvent_iff_last_critical [Nonempty V] {r : ℕ}
    (σ : EdgeOrder V r) (F : SimpleHypergraph V)
    (hF : F ⊆ completeEdges V r) (hNI : NoIsolated F) :
    stoppingStateEvent σ F ↔ processState σ F.card = F ∧
      ∃ e : Edge V r, e.val ∈ criticalEdges F ∧ edgeRank σ e = F.card - 1 := by
  have hm := hNI.card_pos
  have hbound := card_le_card hF
  rw [stoppingStateEvent_iff_time_card]
  constructor
  · rintro ⟨ht,hstate⟩
    obtain ⟨e,he⟩ := edgeRank_exists σ (show F.card - 1 < (completeEdges V r).card by omega)
    have heF : e.val ∈ F := by
      rw [← hstate,processState_mem_edge,he]
      omega
    have hprev := ((tauOne_eq_iff_predecessor σ hm hbound).mp ht).2
    rw [processState_erase_last σ hm e he,hstate] at hprev
    exact ⟨hstate,e,(mem_criticalEdges_iff_delete_not_noIsolated hNI heF).mpr hprev,he⟩
  · rintro ⟨hstate,e,hcrit,he⟩
    have heF := (mem_criticalEdges F e.val).mp hcrit |>.1
    have hprev := (mem_criticalEdges_iff_delete_not_noIsolated hNI heF).mp hcrit
    refine ⟨(tauOne_eq_iff_predecessor σ hm hbound).mpr ⟨?_,?_⟩,hstate⟩
    · simpa only [hstate] using hNI
    · simpa only [processState_erase_last σ hm e he,hstate] using hprev
end LooseHamilton
