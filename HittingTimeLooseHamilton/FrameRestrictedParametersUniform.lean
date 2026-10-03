module

public import HittingTimeLooseHamilton.FrameRestrictedParameters
public import HittingTimeLooseHamilton.TerminalFeasibilityScales
public import HittingTimeLooseHamilton.CoreParameterBounds

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame Filter

lemma eventually_frame_loss_coefficient (r b : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, 0 < (N:ℝ) ∧
      ((4*(r:ℝ)+2*(N:ℝ)^(1/10:ℝ)+b)*C*r)/(N:ℝ) ≤ 1/4 := by
  have hp : Tendsto (fun N : ℕ => (N:ℝ)^(1/10:ℝ)/(N:ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_nat_rpow_ratio (by norm_num : (1/10:ℝ)<1)
  have hi : Tendsto (fun N : ℕ => (1:ℝ)/(N:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (((hi.const_mul (4*(r:ℝ)+b)).add (hp.const_mul 2)).mul_const C).mul_const (r:ℝ)
  have ht : Tendsto (fun N : ℕ => ((4*(r:ℝ)+2*(N:ℝ)^(1/10:ℝ)+b)*C*r)/(N:ℝ)) atTop (nhds 0) := by
    convert hh using 1 <;> try simp only [mul_zero, zero_add, zero_mul]
    ext N
    ring
  filter_upwards [eventually_ge_atTop (1:ℕ), ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))] with N hN ht
  exact ⟨by exact_mod_cast (show 0<N by omega), ht.le⟩

/-- One threshold works for all hosts, frames, times and boundary records.
The only host hypotheses are its original density and upper degrees. -/
theorem frame_density_eventually (r b : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ {original : Finset (Finset (Fin N))},
      IsPairMatching original → (original.card:ℝ) ≤ (N:ℝ)^(1/10:ℝ) →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ H : SimpleHypergraph (Fin N), H ⊆ completeEdges (Fin N) r →
      (3/4:ℝ)*Real.log N ≤ meanDegree (V:=Fin N) r H.card →
      (∀ v, (vertexDegree H v:ℝ) ≤ C*meanDegree (V:=Fin N) r H.card) →
      (H.card:ℝ) ≤ 2*f.m H ∧
      (N:ℝ)*Real.log N/(2*(r:ℝ)) ≤ (unexposed f D H).card ∧
      Real.log N/2 ≤ f.mu H := by
  filter_upwards [eventually_frame_loss_coefficient r b C,
    FrameScales.L1_tendsto.eventually (eventually_gt_atTop 0)] with N hsmall hlog
  intro original hmatch hports f D hD H hH hdense hdeg
  have hNp := hsmall.1
  have hr : 0 < (r:ℝ) := by
    by_contra hr
    have hz : (r:ℝ)=0 := le_antisymm (not_lt.mp hr) (Nat.cast_nonneg _)
    simp only [meanDegree, hz, zero_mul, zero_div] at hdense
    change 0 < Real.log (N:ℝ) at hlog
    linarith
  have hdc : ((f.val.deleted ∪ originalPorts original).card:ℝ) ≤
      4*(r:ℝ)+2*(N:ℝ)^(1/10:ℝ) := by
    have hu := Nat.cast_le (α:=ℝ).mpr (card_union_le f.val.deleted (originalPorts original))
    have hd := Nat.cast_le (α:=ℝ).mpr f.val.deleted_card_le
    have hp := hmatch.ports_card
    rw [hp] at hu
    push_cast at hu hd
    linarith
  have hDb : (D.card:ℝ) ≤ b := by exact_mod_cast hD
  have hmu : 0 ≤ meanDegree (V:=Fin N) r H.card := by unfold meanDegree; positivity
  have hraw := raw_edge_loss f H hH _ hdeg
  have hbound := boundary_edge_loss f D H _ hdeg
  have hloss : (H.card:ℝ)-(unexposed f D H).card ≤
      (4*(r:ℝ)+2*(N:ℝ)^(1/10:ℝ)+b)*C*meanDegree (V:=Fin N) r H.card := by
    nlinarith [mul_le_mul_of_nonneg_right hdc (mul_nonneg hC hmu),
      mul_le_mul_of_nonneg_right hDb (mul_nonneg hC hmu)]
  have hloss' : (H.card:ℝ)-(unexposed f D H).card ≤ (H.card:ℝ)/4 := by
    have hcoeff := mul_le_mul_of_nonneg_right hsmall.2 (Nat.cast_nonneg H.card : (0:ℝ)≤H.card)
    unfold meanDegree at hloss
    simp only [Fintype.card_fin] at hloss
    calc
      _ ≤ _ := hloss
      _ = (((4*(r:ℝ)+2*(N:ℝ)^(1/10:ℝ)+b)*C*r)/(N:ℝ)) * H.card := by ring
      _ ≤ _ := by linarith
  have hsub : ((unexposed f D H).card:ℝ) ≤ f.m H := by
    rw [unexposed_eq_surviving]
    exact Nat.cast_le.mpr (card_le_card (filter_subset _ _))
  have hden : (3/4:ℝ)*Real.log N*(N:ℝ) ≤ (r:ℝ)*H.card := by
    exact (le_div_iff₀ hNp).mp (by simpa [meanDegree] using hdense)
  have hd0 : (N:ℝ)*Real.log N/(2*(r:ℝ)) ≤ (unexposed f D H).card := by
    apply (div_le_iff₀ (by positivity : 0<2*(r:ℝ))).mpr
    nlinarith [mul_nonneg hr.le (show 0 ≤ (unexposed f D H).card-(3/4:ℝ)*H.card by linarith)]
  refine ⟨by linarith,hd0,?_⟩
  have hn : 0 < (f.n:ℝ) := by
    have hs := f.twice_s_le_n
    have hsp : 0 < f.s := card_pos.mpr f.markers_nonempty
    exact_mod_cast (show 0<f.n by omega)
  have hnN : (f.n:ℝ) ≤ N := by
    have hh := f.n_add_deleted
    simp only [Fintype.card_fin] at hh
    exact_mod_cast (show f.n ≤ N by omega)
  apply (le_div_iff₀ hn).mpr
  change Real.log N/2*f.n ≤ (r:ℝ)*f.m H
  have hh := (div_le_iff₀ (by positivity : 0<2*(r:ℝ))).mp hd0
  change 0 < Real.log (N:ℝ) at hlog
  nlinarith [mul_le_mul_of_nonneg_left hnN hlog.le, mul_le_mul_of_nonneg_left hsub hr.le]

/-- The finite estimates apply to the exact Q host on inherited regularity.
No new lower-density or retention hypothesis is added to the source event. -/
theorem inherited_frame_density_eventually (r b : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
      M ≤ j → j ≤ (completeEdges (Fin N) r).card →
      InheritedRegularity original j h c C L ω →
      let H := extensionState ω.1 ω.2 j
      (H.card:ℝ) ≤ 2*f.m H ∧
      (N:ℝ)*Real.log N/(2*(r:ℝ)) ≤ (unexposed f D H).card ∧
      Real.log N/2 ≤ f.mu H := by
  filter_upwards [frame_density_eventually r b C hC,
    eventually_feasibility_parameters 0] with N hframe hwindow
  intro M ell original offset hadm f D hD j h c L ω hMj hj hreg
  apply hframe hadm.marker_matching (by simpa using hadm.markers_small) f D hD
    (extensionState ω.1 ω.2 j) (extensionState_subset _ _ _)
  · have hd := hwindow.2.1 (meanDegree (V:=Fin N) r M)
      (by simpa using hadm.density_window)
    have hm : meanDegree (V:=Fin N) r M ≤ meanDegree (V:=Fin N) r j := by
      unfold meanDegree
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hMj) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    rw [extensionState_card _ _ _ hMj hj]
    linarith [hwindow.1]
  · exact hreg.2.1.upper_degree


/-- Uniform explicit O(1/N) loss for every bounded boundary, including retained
vertices. The bound uses the original host degree regularity. -/
theorem inherited_boundary_ratio_eventually (r b : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
      M ≤ j → j ≤ (completeEdges (Fin N) r).card →
      InheritedRegularity original j h c C L ω →
      let H := extensionState ω.1 ω.2 j
      0 ≤ 1-(unexposed f D H).card/(f.m H:ℝ) ∧
      1-(unexposed f D H).card/(f.m H:ℝ) ≤ 2*(b:ℝ)*C*r/N := by
  filter_upwards [inherited_frame_density_eventually r b C hC,
    eventually_ge_atTop (1:ℕ), FrameScales.L1_tendsto.eventually (eventually_gt_atTop 0)]
    with N hh hN hl
  intro M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hr : 0 < (r:ℝ) := by exact_mod_cast (show 0<r by have := hadm.uniformity; omega)
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hd := hh M ell original offset hadm f D hD j h c L ω hMj hj hreg
  let H := extensionState ω.1 ω.2 j
  have hm : 0 < (f.m H:ℝ) := by
    have hu : (unexposed f D H).card ≤ f.m H := by
      rw [unexposed_eq_surviving]
      exact card_le_card (filter_subset _ _)
    have hpos : 0 < (N:ℝ)*Real.log N/(2*(r:ℝ)) := by
      change 0<Real.log (N:ℝ) at hl
      positivity
    exact hpos.trans_le (hd.2.1.trans (Nat.cast_le.mpr hu))
  have hb := boundary_relative_loss f D H C (by simpa using hn) hm hC hreg.2.1.upper_degree hd.1
  refine ⟨hb.1, hb.2.trans ?_⟩
  simp only [Fintype.card_fin]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hD) (by norm_num : (0:ℝ)≤2)) hC)
      hr.le) hn.le

end LooseHamilton.CandidateBalance
