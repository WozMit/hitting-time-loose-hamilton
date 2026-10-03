module

public import HittingTimeLooseHamilton.PathPerturbationInduced

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma sum_degree_le_card_mul (F : SimpleHypergraph V) (S : Finset V) (D : ℝ)
    (hD : ∀ v, (vertexDegree F v : ℝ) ≤ D) :
    ((∑ v ∈ S, vertexDegree F v : ℕ) : ℝ) ≤ S.card * D := by
  push_cast
  calc
    _ ≤ ∑ v ∈ S, D := sum_le_sum (fun v hv => hD v)
    _ = _ := by simp

theorem deleteVertices_edge_loss_real (F : SimpleHypergraph V) (Z : Finset V) (D : ℝ)
    (hD : ∀ v, (vertexDegree F v : ℝ) ≤ D) :
    (F.card : ℝ) - (deleteVertices Z F).card ≤ Z.card * D := by
  rw [deleteVertices_card]
  have hc : (survivingHost F Z).card ≤ F.card := card_le_card (filter_subset _ _)
  have hl : ((F.card - (survivingHost F Z).card : ℕ) : ℝ) ≤
      ((∑ v ∈ Z, vertexDegree F v : ℕ) : ℝ) := by exact_mod_cast deletion_edge_loss_le F Z
  rw [Nat.cast_sub hc] at hl
  exact hl.trans (sum_degree_le_card_mul F Z D hD)

theorem deleteVertices_degree_bounds (F : SimpleHypergraph V) (Z : Finset V)
    (d D p : ℝ) (hlo : ∀ v, d ≤ (vertexDegree F v : ℝ))
    (hhi : ∀ v, (vertexDegree F v : ℝ) ≤ D)
    (hp : ∀ v w, v ≠ w → (pairDegree F v w : ℝ) ≤ p)
    (v : ↥(univ \ Z)) :
    d - Z.card * p ≤ (vertexDegree (deleteVertices Z F) v : ℝ) ∧
      (vertexDegree (deleteVertices Z F) v : ℝ) ≤ D := by
  rw [vertexDegree_deleteVertices]
  have hm := vertexDegree_mono (filter_subset (fun e => Disjoint e Z) F) v.val
  change vertexDegree (survivingHost F Z) v.val ≤ vertexDegree F v.val at hm
  have hl := deletion_degree_loss_le F Z v.val
  have hr : ((vertexDegree F v.val - vertexDegree (survivingHost F Z) v.val : ℕ) : ℝ) ≤
      ((∑ y ∈ Z, pairDegree F v.val y : ℕ) : ℝ) := by exact_mod_cast hl
  rw [Nat.cast_sub hm] at hr
  have hs : ((∑ y ∈ Z, pairDegree F v.val y : ℕ) : ℝ) ≤ Z.card * p := by
    push_cast
    calc
      _ ≤ ∑ y ∈ Z, p := sum_le_sum (fun y hy => hp _ _ (by
        intro he; have hv := (mem_sdiff.mp v.property).2; exact hv (he ▸ hy)))
      _ = _ := by simp
  have hlo' := hlo v.val
  have hhi' := hhi v.val
  have hm' : (vertexDegree (survivingHost F Z) v.val : ℝ) ≤ vertexDegree F v.val := by exact_mod_cast hm
  constructor <;> linarith

theorem deleteVertices_pair_degree_le (F : SimpleHypergraph V) (Z : Finset V)
    (p : ℝ) (hp : ∀ v w, v ≠ w → (pairDegree F v w : ℝ) ≤ p)
    (v w : ↥(univ \ Z)) (hvw : v ≠ w) :
    (pairDegree (deleteVertices Z F) v w : ℝ) ≤ p := by
  rw [pairDegree_deleteVertices]
  apply le_trans (Nat.cast_le.mpr (pairDegree_mono (filter_subset _ _) v.val w.val))
  exact hp _ _ (fun he => hvw (Subtype.ext he))

theorem port_filter_edge_loss_real (F : SimpleHypergraph V) (U : Finset V) (D : ℝ)
    (hD : ∀ v, (vertexDegree F v : ℝ) ≤ D) :
    (F.card : ℝ) - (portFilteredHost U F).card ≤ U.card * D := by
  have hc := card_le_card (portFilteredHost_subset U F)
  have hl : ((F.card - (portFilteredHost U F).card : ℕ) : ℝ) ≤
      ((∑ v ∈ U, vertexDegree F v : ℕ) : ℝ) := by exact_mod_cast port_filter_edge_loss_le U F
  rw [Nat.cast_sub hc] at hl
  exact hl.trans (sum_degree_le_card_mul F U D hD)

end LooseHamilton
