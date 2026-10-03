module

public import HittingTimeLooseHamilton.HypergraphIncidenceCounts
public import HittingTimeLooseHamilton.RootLinkCoordinates
public import HittingTimeLooseHamilton.RootSamplingModels

public section

/-! Root edges lost on deleting a fixed vertex set. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def deletedRootCollisions (r : ℕ) (x : V) (D : Finset V) : SimpleHypergraph V :=
  (rootEdgeUniverse r x).filter (fun e => ¬ e ⊆ univ \ D)

theorem deletedRootCollisions_subset (r : ℕ) (x : V) (D : Finset V) :
    deletedRootCollisions r x D ⊆ rootEdgeUniverse r x := filter_subset _ _

theorem deletedRootCollisions_eq_biUnion (r : ℕ) (x : V) (D : Finset V) :
    deletedRootCollisions r x D =
      D.biUnion (fun z => (rootEdgeUniverse r x).filter (fun e => z ∈ e)) := by
  ext e
  simp only [deletedRootCollisions, mem_filter, mem_biUnion]
  constructor
  · rintro ⟨he, hn⟩
    have hex : ∃ z ∈ e, z ∈ D := by
      by_contra h
      apply hn
      intro z hz
      simp only [mem_sdiff, mem_univ, true_and]
      intro hzD
      exact h ⟨z, hz, hzD⟩
    obtain ⟨z, hz, hzD⟩ := hex
    exact ⟨z, hzD, he, hz⟩
  · rintro ⟨z, hzD, he, hz⟩
    exact ⟨he, fun h => (mem_sdiff.mp (h hz)).2 hzD⟩

theorem rootEdgeUniverse_filter_card {r : ℕ} (hr : 2 ≤ r) {x z : V} (hxz : x ≠ z) :
    ((rootEdgeUniverse r x).filter (fun e => z ∈ e)).card =
      (Fintype.card V - 2).choose (r - 2) := by
  rw [← pairIncidences_card hr hxz]
  apply card_bij (fun e _ => (⟨e, (mem_completeEdges r e).mpr
    ((mem_rootEdgeUniverse r x e).mp (mem_filter.mp ‹_›).1).1⟩ : Edge V r))
  · intro e he
    simp only [mem_pairIncidences]
    exact ⟨((mem_rootEdgeUniverse r x e).mp (mem_filter.mp he).1).2,
      (mem_filter.mp he).2⟩
  · intro e he f hf h
    exact congrArg Subtype.val h
  · intro e he
    refine ⟨e.val, ?_, ?_⟩
    · exact mem_filter.mpr ⟨(mem_rootEdgeUniverse r x e.val).mpr
        ⟨(mem_completeEdges r e.val).mp e.property, (mem_pairIncidences.mp he).1⟩,
        (mem_pairIncidences.mp he).2⟩
    · exact Subtype.ext rfl

theorem deletedRootCollisions_card_le {r : ℕ} (hr : 2 ≤ r) (x : V)
    (D : Finset V) (hx : x ∉ D) :
    (deletedRootCollisions r x D).card ≤ D.card * (Fintype.card V - 2).choose (r - 2) := by
  rw [deletedRootCollisions_eq_biUnion]
  calc
    _ ≤ ∑ z ∈ D, ((rootEdgeUniverse r x).filter (fun e => z ∈ e)).card := card_biUnion_le
    _ = _ := by
      rw [sum_congr rfl (fun z hz => rootEdgeUniverse_filter_card hr (by
        intro h; exact hx (h.symm ▸ hz)))]
      simp

theorem deletedRootCollisions_density_le {r : ℕ} (hr : 2 ≤ r)
    (hN : 2 ≤ Fintype.card V) (x : V) (D : Finset V) (hx : x ∉ D) :
    rootLinkDensity r x (deletedRootCollisions r x D) ≤
      (D.card : ℝ) * (r - 1 : ℕ) / (Fintype.card V - 1 : ℕ) := by
  have hc := deletedRootCollisions_card_le hr x D hx
  have hid := Nat.add_one_mul_choose_eq (Fintype.card V - 2) (r - 2)
  have hN' : (Fintype.card V - 2)+1 = Fintype.card V - 1 := by omega
  have hr' : (r - 2)+1 = r - 1 := by omega
  rw [hN', hr'] at hid
  have hidR : (Fintype.card V - 1 : ℕ) *
      ((Fintype.card V - 2).choose (r - 2) : ℝ) =
      ((Fintype.card V - 1).choose (r - 1) : ℝ) * (r - 1 : ℕ) := by
    exact_mod_cast hid
  rw [rootLinkDensity, rootEdgeUniverse_card r (by omega)]
  by_cases hz : (Fintype.card V - 1).choose (r - 1) = 0
  · rw [hz]
    simp only [Nat.cast_zero, div_zero]
    positivity
  · have hb : (0 : ℝ) < ((Fintype.card V - 1).choose (r - 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    have hn : (0 : ℝ) < (Fintype.card V - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
    apply (div_le_div_iff₀ hb hn).mpr
    have hcR : ((deletedRootCollisions r x D).card : ℝ) ≤
        (D.card : ℝ) * ((Fintype.card V - 2).choose (r - 2) : ℝ) := by
      exact_mod_cast hc
    calc
      _ ≤ ((D.card : ℝ) * ((Fintype.card V - 2).choose (r - 2) : ℝ)) *
          (Fintype.card V - 1 : ℕ) := mul_le_mul_of_nonneg_right hcR (le_of_lt hn)
      _ = _ := by nlinarith [congrArg (fun a : ℝ => (D.card : ℝ) * a) hidR]

end LooseHamilton
