module

public import HittingTimeLooseHamilton.PortContractionRootEdges
public import HittingTimeLooseHamilton.BootstrapAmbientDensityNormalization
public import HittingTimeLooseHamilton.SequentialMobilityCounting

public section

/-! Reconstruction of actual original-port links, including every collision.
The score is the literal sum of actual deleted-root completion counts. -/
noncomputable section
namespace LooseHamilton.BootstrapPortLinkDensity
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All ambient labels with the surviving old partner fixed, avoiding the
removed root. No legality restriction is imposed on this counting family. -/
@[expose] def labels (r : ℕ) (y z : V) : Finset (Finset V × V × V) :=
  univ.filter (fun l => l.1.card = r-2 ∧ y ∉ l.1 ∧ l.2.1 ≠ y ∧ l.2.2 = z)

@[expose] def failed (r : ℕ) (M G : SimpleHypergraph V) (y z : V) (T : ℝ) :
    Finset (Finset V × V × V) :=
  (labels r y z).filter (fun l =>
    (rootFreePortCompletion r M G y z l.1 {l.2.1,l.2.2} : ℝ) < T)

/-- Avoiding the other original ports removes all forbidden and colliding
labels in the registered test, simultaneously for every junction. -/
theorem legal_of_no_collision {r : ℕ} (hr : 3 ≤ r)
    (M : SimpleHypergraph V) (y z : V) (hm : {y,z} ∈ M)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (e : Finset V) (he : e ∈ rootEdgeUniverse r y)
    (hn : e ∉ deletedRootCollisions r y ((originalPorts M).erase y)) :
    e ∈ allowedEdges r (originalPorts M) ∧
    ∀ v ∈ e.erase y, LegalPrivateCompletion r (M.erase {y,z}) ((e.erase y).erase v) {v,z} := by
  classical
  obtain ⟨hcard,hy⟩ := (mem_rootEdgeUniverse r y e).mp he
  have havoid : e ⊆ univ \ (originalPorts M).erase y := by
    simpa only [deletedRootCollisions,mem_filter,he,true_and,not_not] using hn
  have hd : Disjoint (e.erase y) (originalPorts M) := by
    apply disjoint_left.mpr
    intro v hv hp
    exact (mem_sdiff.mp (havoid (mem_erase.mp hv).2)).2 (mem_erase.mpr ⟨(mem_erase.mp hv).1,hp⟩)
  have hz : z ∈ originalPorts M := mem_biUnion.mpr ⟨{y,z},hm,by simp⟩
  have hrem := port_pair_disjoint_remainder M y z hM hm
  constructor
  · apply (mem_allowedEdges r _ e).mpr
    refine ⟨hcard,?_⟩
    have hsub : e ∩ originalPorts M ⊆ {y} := by
      intro v hv
      by_contra h
      have hne : v ≠ y := by simpa using h
      exact disjoint_left.mp hd (mem_erase.mpr ⟨hne,(mem_inter.mp hv).1⟩) (mem_inter.mp hv).2
    exact (card_le_card hsub).trans (by simp)
  · intro v hv
    have hvz : v ≠ z := fun h => disjoint_left.mp hd hv (h.symm ▸ hz)
    refine ⟨?_,card_pair hvz,?_,?_⟩
    · rw [card_erase_of_mem hv,card_erase_of_mem hy,hcard]
      omega
    · apply disjoint_left.mpr
      intro a ha hb
      rcases mem_insert.mp hb with rfl | hb
      · exact (mem_erase.mp ha).1 rfl
      · have haz := mem_singleton.mp hb
        exact disjoint_left.mp hd (mem_erase.mp ha).2 (haz ▸ hz)
    · apply disjoint_left.mpr
      intro a ha hp
      rcases mem_union.mp ha with ha | ha
      · exact disjoint_left.mp hd (mem_erase.mp ha).2 (by
          obtain ⟨f,hf,haf⟩ := mem_biUnion.mp hp
          exact mem_biUnion.mpr ⟨f,(mem_erase.mp hf).2,haf⟩)
      · rcases mem_insert.mp ha with rfl | ha
        · exact disjoint_left.mp hd hv (by
            obtain ⟨f,hf,hvf⟩ := mem_biUnion.mp hp
            exact mem_biUnion.mpr ⟨f,(mem_erase.mp hf).2,hvf⟩)
        · exact disjoint_left.mp hrem (mem_insert_of_mem ha) hp

/-- A bad noncolliding root edge reconstructs from a failed label. Taking one
summand loses no extra factor, since all completion counts are nonnegative. -/
theorem bad_card_le {r : ℕ} (hr : 3 ≤ r)
    (M G : SimpleHypergraph V) (P : Finset V) (y z u : V)
    (hm : {y,z} ∈ M) (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (c T : ℝ) (hT : c * rootFreePortSource r M G y z P u ≤ T) :
    (rootFreePortBadSet r M G (originalPorts M) P y z u c).card ≤
      (failed r M G y z T).card +
      ((originalPorts M).erase y).card * (Fintype.card V-2).choose (r-2) := by
  classical
  let bad := rootFreePortBadSet r M G (originalPorts M) P y z u c
  let collisions := deletedRootCollisions r y ((originalPorts M).erase y)
  have hc : (bad \ collisions).card ≤ (failed r M G y z T).card := by
    apply Migration.bad_links_card_le_failed_labels (bad \ collisions) (failed r M G y z T)
      (fun l => insert y (insert l.2.1 l.1))
    intro e he
    obtain ⟨heb,hen⟩ := mem_sdiff.mp he
    obtain ⟨he,htest⟩ := mem_filter.mp heb
    have hlegal := legal_of_no_collision hr M y z hm hM e he hen
    have hlow : (rootFreePortScore r M G y z (e.erase y):ℝ) < T := by
      rcases htest with hf | hf | hf
      · exact False.elim (hf hlegal.1)
      · exact False.elim (hf hlegal.2)
      · exact hf.trans_le hT
    have hey := ((mem_rootEdgeUniverse r y e).mp he).2
    have hcard := ((mem_rootEdgeUniverse r y e).mp he).1
    have hnon : (e.erase y).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem hey,hcard]
      omega
    obtain ⟨v,hv⟩ := hnon
    refine ⟨((e.erase y).erase v,v,z),?_,?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_univ _,?_,by simp,(mem_erase.mp hv).1,rfl⟩,?_⟩
      · rw [card_erase_of_mem hv,card_erase_of_mem hey,hcard]; omega
      · have hs : rootFreePortCompletion r M G y z ((e.erase y).erase v) {v,z} ≤
            rootFreePortScore r M G y z (e.erase y) := by
          unfold rootFreePortScore
          exact single_le_sum (f := fun v => rootFreePortCompletion r M G y z ((e.erase y).erase v) {v,z}) (fun a ha => Nat.zero_le _) hv
        exact (Nat.cast_le.mpr hs).trans_lt hlow
    · simp only [insert_erase hv,insert_erase hey]
  have htotal : bad.card ≤ (bad \ collisions).card + collisions.card := by
    have hsub : bad ⊆ (bad \ collisions) ∪ collisions := by
      intro e he; by_cases h : e ∈ collisions
      · exact mem_union_right _ h
      · exact mem_union_left _ (mem_sdiff.mpr ⟨he,h⟩)
    exact (card_le_card hsub).trans (card_union_le _ _)
  exact htotal.trans (Nat.add_le_add hc (deletedRootCollisions_card_le (by omega) y _ (by simp)))

/-- The finite density estimate in the ambient root universe. -/
theorem density_le {r : ℕ} (hr : 3 ≤ r) (hN : 2*r ≤ Fintype.card V)
    (M G : SimpleHypergraph V) (P : Finset V) (y z u : V)
    (hm : {y,z} ∈ M) (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (c T β : ℝ) (hβ : 0 ≤ β)
    (hT : c * rootFreePortSource r M G y z P u ≤ T)
    (hfailed : ((failed r M G y z T).card:ℝ) ≤ β*(Fintype.card V:ℝ)^(r-1)) :
    rootLinkDensity r y (rootFreePortBadSet r M G (originalPorts M) P y z u c) ≤
      ((2:ℝ)^(r-1)*((r-1).factorial:ℝ))*β +
        (((originalPorts M).erase y).card:ℝ)*(r-1:ℕ)/(Fintype.card V-1:ℕ) := by
  apply BootstrapAmbientDensityNormalization.density_le hr hN y _ β
    (((originalPorts M).erase y).card:ℝ) hβ
  have hc := bad_card_le hr M G P y z u hm hM c T hT
  have hcR : ((rootFreePortBadSet r M G (originalPorts M) P y z u c).card:ℝ) ≤
      ((failed r M G y z T).card:ℝ) +
      (((originalPorts M).erase y).card:ℝ)*((Fintype.card V-2).choose (r-2):ℝ) := by
    exact_mod_cast hc
  exact hcR.trans (add_le_add_left hfailed _)

end LooseHamilton.BootstrapPortLinkDensity
