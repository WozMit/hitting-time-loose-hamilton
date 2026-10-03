module

public import HittingTimeLooseHamilton.BiasedRoleStatement
public import HittingTimeLooseHamilton.BiasedRoleJunctions

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Finset FiniteEntropy
variable {r : ℕ}

lemma cycle_nonempty (D : BiasedRoleInstance r) : Nonempty (BiasedCycleState r D.markers D.host) := by
  by_contra h
  haveI : IsEmpty (BiasedCycleState r D.markers D.host) := not_nonempty_iff.mp h
  have ht := D.cycleLaw.total
  simp at ht

@[expose] def sampleCycle (D : BiasedRoleInstance r) : BiasedCycleState r D.markers D.host :=
  Classical.choice D.cycle_nonempty

lemma sampleCycle_properties (D : BiasedRoleInstance r) :
    IsMixedCycle r D.markers D.sampleCycle.val ∧ D.sampleCycle.val ⊆ D.host := by
  have h := (mem_cycleFamily _ _ _ _ _).mp D.sampleCycle.property
  exact ⟨h.1,h.2.1⟩

lemma s_pos (D : BiasedRoleInstance r) : 0 < D.s :=
  card_pos.mpr ⟨D.root.val,D.root.property⟩

lemma N_pos (D : BiasedRoleInstance r) : 0 < D.N :=
  Nat.zero_lt_of_lt D.initial.val.isLt

lemma k_pos (D : BiasedRoleInstance r) (hr : 3 ≤ r) : 0 < D.k := by
  have hc := D.sampleCycle_properties.1.edges_card_pos
  rw [D.sampleCycle_properties.1.edge_card hr] at hc
  exact hc

lemma vertex_bookkeeping (D : BiasedRoleInstance r) (hr : 3 ≤ r) :
    D.N = (r-1)*D.k+D.s := by
  have h := D.sampleCycle_properties.1.vertex_card hr
  rw [D.sampleCycle_properties.1.edge_card hr] at h
  simpa [k,s,Fintype.card_fin,ordinaryEdgeCount] using h

lemma host_card_pos (D : BiasedRoleInstance r) : 0 < D.host.card :=
  lt_of_lt_of_le D.sampleCycle_properties.1.edges_card_pos (card_le_card D.sampleCycle_properties.2)

lemma μ_pos (D : BiasedRoleInstance r) (hr : 3 ≤ r) : 0 < D.μ := by
  unfold μ meanDegree
  apply div_pos
  · exact mul_pos (by exact_mod_cast (show 0<r by omega)) (Nat.cast_pos.mpr D.host_card_pos)
  · simpa only [Fintype.card_fin] using Nat.cast_pos.mpr D.N_pos

lemma maxPairDegree_pos (D : BiasedRoleInstance r) (hr : 3 ≤ r) : 0 < maxPairDegree D.host := by
  obtain ⟨e,he⟩ := card_pos.mp D.host_card_pos
  have hcard := (mem_completeEdges _ _).mp (D.host_uniform he)
  have ht : 1 < e.card := by omega
  obtain ⟨u,hu,v,hv,hne⟩ := one_lt_card.mp ht
  have hpair : 0 < pairDegree D.host u v := card_pos.mpr ⟨e,mem_filter.mpr ⟨he,hu,hv⟩⟩
  exact lt_of_lt_of_le hpair (le_sup (f := fun p => pairDegree D.host p.1 p.2)
    (mem_filter.mpr ⟨mem_univ (u,v),hne⟩))

lemma η_pos (D : BiasedRoleInstance r) (hr : 3 ≤ r) : 0 < D.η :=
  div_pos (Nat.cast_pos.mpr (D.maxPairDegree_pos hr)) (D.μ_pos hr)

/-- A coarse finite ambient-size bound, sufficient to force N to infinity
from divergence of the mean degree. -/
lemma μ_le_exponential (D : BiasedRoleInstance r) : D.μ ≤ (r:ℝ)*2^D.N := by
  have hm : D.host.card ≤ 2^D.N := by
    have h := card_le_card (subset_univ D.host)
    simpa only [card_univ, Fintype.card_finset, Fintype.card_fin] using h
  have hN : (1:ℝ) ≤ D.N := by exact_mod_cast D.N_pos
  calc
    D.μ = (r:ℝ)*D.host.card/D.N := by simp [μ,meanDegree]
    _ ≤ (r:ℝ)*D.host.card := div_le_self (by positivity) hN
    _ ≤ (r:ℝ)*2^D.N := mul_le_mul_of_nonneg_left (by exact_mod_cast hm) (Nat.cast_nonneg _)

lemma partitionBound_nonneg (D : BiasedRoleInstance r) (hr : 3 ≤ r)
    {δ : ℝ} (hδ : D.partitionBound δ) : 0 ≤ δ := by
  let C := D.sampleCycle_properties.1.some
  have hp : originalPorts D.markers ⊆ univ.image C.junction :=
    C.marked_vertices_subset_junctions
  have hc : (univ.image C.junction).card=D.k+D.s := by
    rw [C.junction_card,C.length_eq,D.sampleCycle_properties.1.edge_card hr]
    simp only [k,s,ordinaryEdgeCount,Nat.add_comm]
  have h := hδ (univ.image C.junction) hp hc
  have hn : (0:ℝ)<D.N := Nat.cast_pos.mpr D.N_pos
  have hm := D.μ_pos hr
  have hh : 0 ≤ δ*(D.N:ℝ)*D.μ := (abs_nonneg _).trans h
  exact nonneg_of_mul_nonneg_left (nonneg_of_mul_nonneg_left hh hm) hn

end LooseHamilton.BiasedRoleInstance
