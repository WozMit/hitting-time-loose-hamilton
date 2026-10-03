module

public import HittingTimeLooseHamilton.CandidateBalanceSpecification
public import HittingTimeLooseHamilton.PathPerturbationBounds
public import HittingTimeLooseHamilton.FrameSurvivalAsymptotic

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- A conservative loss bound: deleting every original port certainly enforces
its prohibition. It is used only for density estimates, never for sampling. -/
theorem surviving_subset_raw (f : Frame r original) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) :
    survivingHost H (f.val.deleted ∪ originalPorts original) ⊆ f.rawHost H := by
  intro e he
  obtain ⟨he,hd⟩ := mem_filter.mp he
  have hd' := Finset.disjoint_union_right.mp hd
  apply mem_filter.mpr
  refine ⟨mem_inter.mpr ⟨he, (mem_allowedEdges _ _ _).mpr ⟨(mem_completeEdges _ _).mp (hH he), ?_⟩⟩, ?_⟩
  · rw [Finset.disjoint_iff_inter_eq_empty.mp hd'.2]
    simp
  · intro x hx
    exact mem_sdiff.mpr ⟨mem_univ _, fun hz => Finset.disjoint_left.mp hd'.1 hx hz⟩

theorem raw_edge_loss (f : Frame r original) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (d : ℝ)
    (hd : ∀ v, (vertexDegree H v:ℝ) ≤ d) :
    (H.card:ℝ) - f.m H ≤ (f.val.deleted ∪ originalPorts original).card*d := by
  have hl := deleteVertices_edge_loss_real H (f.val.deleted ∪ originalPorts original) d hd
  rw [deleteVertices_card] at hl
  have hc : ((survivingHost H (f.val.deleted ∪ originalPorts original)).card:ℝ) ≤ f.m H :=
    Nat.cast_le.mpr (card_le_card (surviving_subset_raw f H hH))
  linarith

/-- Boundary restriction removes precisely the raw edges meeting the boundary. -/
theorem unexposed_eq_surviving (f : Frame r original) (D : Finset V)
    (H : SimpleHypergraph V) :
    unexposed f D H = survivingHost (f.rawHost H) D := by
  ext e
  simp [unexposed, samplingUniverse, survivingHost, rawHost_eq_inter, and_assoc]

theorem boundary_edge_loss (f : Frame r original) (D : Finset V)
    (H : SimpleHypergraph V) (d : ℝ)
    (hd : ∀ v, (vertexDegree H v:ℝ) ≤ d) :
    (f.m H:ℝ) - (unexposed f D H).card ≤ D.card*d := by
  rw [unexposed_eq_surviving]
  have hl := deleteVertices_edge_loss_real (f.rawHost H) D d (fun v =>
    (Nat.cast_le.mpr (vertexDegree_mono (by
      intro e he; exact (mem_inter.mp (mem_filter.mp he).1).1) v)).trans (hd v))
  rwa [deleteVertices_card] at hl

/-- Original N controls k uniformly once the imposed budget ensures a cycle. -/
theorem frame_k_comparison (f : Frame r original) (hr : 3 ≤ r)
    (hN : 8*r ≤ Fintype.card V) {H : SimpleHypergraph V}
    (hc : (f.cycleFamily H).Nonempty) :
    (Fintype.card V:ℝ) ≤ (4*((r:ℝ)-1))*f.k ∧
      (f.k:ℝ) ≤ Fintype.card V := by
  have hv := f.vertex_identity hr hc
  have hs := f.twice_s_le_n
  have hn := f.n_add_deleted
  have hd := f.val.deleted_card_le
  have ha : Fintype.card V ≤ 2*f.n := by omega
  have hb : f.n ≤ 2*(r-1)*f.k := by nlinarith
  have hh : Fintype.card V ≤ 4*(r-1)*f.k := by nlinarith
  constructor
  · have hhR : (Fintype.card V:ℝ) ≤ (4:ℝ)*(r-1:ℕ)*f.k := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] using hhR
  · exact_mod_cast (f.k_le_n.trans (by omega : f.n ≤ Fintype.card V))

/-- Explicit finite relative loss, subsequently discharged uniformly in N. -/
theorem boundary_relative_loss (f : Frame r original) (D : Finset V)
    (H : SimpleHypergraph V) (C : ℝ) (hN : 0 < (Fintype.card V:ℝ))
    (hm : 0 < (f.m H:ℝ)) (hC : 0 ≤ C)
    (hd : ∀ v, (vertexDegree H v:ℝ) ≤ C*meanDegree (V:=V) r H.card)
    (hretain : (H.card:ℝ) ≤ 2*f.m H) :
    0 ≤ 1-(unexposed f D H).card/(f.m H:ℝ) ∧
    1-(unexposed f D H).card/(f.m H:ℝ) ≤
      2*(D.card:ℝ)*C*r/Fintype.card V := by
  have hl := boundary_edge_loss f D H _ hd
  have hsub : (unexposed f D H).card ≤ f.m H := by
    rw [unexposed_eq_surviving]
    exact card_le_card (filter_subset _ _)
  constructor
  · exact sub_nonneg.mpr ((div_le_one hm).mpr (Nat.cast_le.mpr hsub))
  · apply (le_div_iff₀ hN).mpr
    apply (mul_le_mul_iff_left₀ hm).mp
    have hb := mul_le_mul_of_nonneg_left hretain
      (show 0 ≤ (D.card:ℝ)*C*r by positivity)
    unfold meanDegree at hl
    have hl' := (le_div_iff₀ hN).mp (show (f.m H:ℝ)-(unexposed f D H).card ≤
      (D.card:ℝ)*C*r*H.card/Fintype.card V by simpa [mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using hl)
    field_simp
    nlinarith
end LooseHamilton.CandidateBalance
