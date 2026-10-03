module

public import HittingTimeLooseHamilton.PathPortRegularity

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Finite deterministic deletion transport; the scalar side conditions are
uniformly eventual for bounded deletions, independently of the host graph. -/
theorem path_regular_deletion_transport {r : ℕ} {c C L : ℝ} {F : SimpleHypergraph V}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hr : 2 ≤ r)
    (hF : PathGraphRegular r c C (L+1) F) (Z : Finset V)
    (hmean : meanDegree (V:=V) r F.card ≤
      2*meanDegree (V:=↥(univ \ Z)) r (deleteVertices Z F).card)
    (hmean' : meanDegree (V:=↥(univ \ Z)) r (deleteVertices Z F).card ≤
      2*meanDegree (V:=V) r F.card)
    (hcard : (Fintype.card V:ℝ) ≤ 2*Fintype.card ↥(univ \ Z))
    (hlog1 : (Real.log (Fintype.card V:ℝ))^(-1/4:ℝ) ≤
      (Real.log (Fintype.card ↥(univ \ Z):ℝ))^(-1/4:ℝ))
    (hlog2 : (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ) ≤
      (Real.log (Fintype.card ↥(univ \ Z):ℝ))^(-1/8:ℝ))
    (hsmall : (Z.card:ℝ)*C*(Real.log (Fintype.card V:ℝ))^(-1/4:ℝ) ≤ c/2)
    (hloss : (1+partitionDensity r)*(Z.card:ℝ) ≤
      Fintype.card V*(Real.log (Fintype.card V:ℝ))^(-1/8:ℝ))
    (hwindow : ∀ A : Finset ↥(univ \ Z),
      |(A.card:ℝ)-junctionFraction r*Fintype.card ↥(univ \ Z)| ≤
        L*(Fintype.card ↥(univ \ Z):ℝ)^(1/10:ℝ) →
      |(A.card:ℝ)-junctionFraction r*Fintype.card V| ≤
        (L+1)*(Fintype.card V:ℝ)^(1/10:ℝ)) :
    PathGraphRegular r (c/4) (8*C) L (deleteVertices Z F) := by
  let μ := meanDegree (V:=V) r F.card
  let ν := meanDegree (V:=↥(univ \ Z)) r (deleteVertices Z F).card
  let N : ℝ := Fintype.card V
  let N' : ℝ := Fintype.card ↥(univ \ Z)
  let f := (Real.log N)^(-1/8:ℝ)
  let f' := (Real.log N')^(-1/8:ℝ)
  let g := (Real.log N)^(-1/4:ℝ)
  let g' := (Real.log N')^(-1/4:ℝ)
  have hμ : 0 ≤ μ := by unfold μ meanDegree; positivity
  have hν : 0 ≤ ν := by unfold ν meanDegree; positivity
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hN' : 0 ≤ N' := Nat.cast_nonneg _
  have hf : 0 ≤ f := Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  have hf' : 0 ≤ f' := Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  have hg : 0 ≤ g := Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  have hg' : 0 ≤ g' := Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  have hm : μ ≤ 2*ν := hmean
  have hm' : ν ≤ 2*μ := hmean'
  have hn : N ≤ 2*N' := hcard
  have hfg : f ≤ f' := hlog2
  have hgg : g ≤ g' := hlog1
  have hmuC : C*μ ≤ 8*C*ν := by nlinarith
  refine { upper_degree := ?_, codegree := ?_, partitions := ?_, lower_degree := ?_ }
  · intro v
    exact ((deleteVertices_degree_bounds F Z (c*μ) (C*μ) (C*μ*g)
      hF.lower_degree hF.upper_degree hF.codegree v).2).trans hmuC
  · intro v w hvw
    have hd := deleteVertices_pair_degree_le F Z (C*μ*g) hF.codegree v w hvw
    have hp := mul_le_mul hmuC hgg hg (by positivity : 0 ≤ 8*C*ν)
    exact hd.trans hp
  · intro A hA
    have hw := hwindow A hA
    have hbase := hF.partitions (liftEdge (univ \ Z) A) (by simpa only [liftEdge_card] using hw)
    have ht := filter_discrepancy_transfer (filter_subset (fun e => Disjoint e Z) F)
      (fun e => (e∩liftEdge (univ \ Z) A).card=2) (partitionDensity r)
      (C*N*μ*f) (partitionDensity_nonneg hr) hbase
    have hsize : (survivingHost F Z).card ≤ F.card := card_le_card (filter_subset _ _)
    have heq := induced_partition_count F Z A
    have hdc := deleteVertices_card F Z
    change |(((survivingHost F Z).filter (fun e => (e∩liftEdge (univ \ Z) A).card=2)).card:ℝ)-
      partitionDensity r*(survivingHost F Z).card| ≤ C*N*μ*f+
      (1+partitionDensity r)*((F.card-(survivingHost F Z).card:ℕ):ℝ) at ht
    rw [Nat.cast_sub hsize, ← heq, ← hdc] at ht
    have hl := deleteVertices_edge_loss_real F Z (C*μ) hF.upper_degree
    have hθ := partitionDensity_nonneg hr
    have he := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ 1+partitionDensity r)
    have hs := mul_le_mul_of_nonneg_right hloss (mul_nonneg hC hμ)
    have hNμ : N*μ ≤ 4*N'*ν := by nlinarith only [mul_le_mul hn hm hμ (by positivity : 0 ≤ 2*N')]
    have hbig := mul_le_mul hNμ hfg hf (by positivity : 0 ≤ 4*N'*ν)
    have hbig' := mul_le_mul_of_nonneg_left hbig (by positivity : 0 ≤ 2*C)
    change |(partitionCount (deleteVertices Z F) A:ℝ)-partitionDensity r*(deleteVertices Z F).card| ≤ 8*C*N'*ν*f'
    change |(partitionCount (deleteVertices Z F) A:ℝ)-partitionDensity r*(deleteVertices Z F).card| ≤ _ at ht
    change (1+partitionDensity r)*(Z.card:ℝ) ≤ N*f at hloss
    change (F.card:ℝ)-(deleteVertices Z F).card ≤ (Z.card:ℝ)*(C*μ) at hl
    change (1+partitionDensity r)*(Z.card:ℝ)*(C*μ) ≤ N*f*(C*μ) at hs
    nlinarith only [ht,he,hs,hbig']
  · intro v
    have hd := (deleteVertices_degree_bounds F Z (c*μ) (C*μ) (C*μ*g)
      hF.lower_degree hF.upper_degree hF.codegree v).1
    have hs := mul_le_mul_of_nonneg_right hsmall hμ
    change (Z.card:ℝ)*C*g ≤ c/2 at hsmall
    change (c/4)*ν ≤ _
    change (Z.card:ℝ)*C*g*μ ≤ c/2*μ at hs
    nlinarith only [hd,hs,mul_le_mul_of_nonneg_left hm' hc]

end LooseHamilton
