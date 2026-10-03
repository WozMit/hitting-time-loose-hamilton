module

public import HittingTimeLooseHamilton.HypergeometricProcessTail
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

/-! Two-sided additive concentration, obtained from lower tails of a test and its complement. -/
noncomputable section
open scoped BigOperators
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

lemma chernoff_lower_additive_algebra (μ m a : ℝ) (hm : 0<m) (hμ : 0≤μ)
    (hμm : μ≤m) (ha : 0<a) (haμ : a≤μ) :
    -μ*(1-(1+a/(2*m))⁻¹) - (μ-a)*Real.log ((1+a/(2*m))⁻¹) ≤ -a^2/(4*m) := by
  let x := a/(2*m)
  have hx : 0≤x := by dsimp [x]; positivity
  have hd : 0<1+x := by positivity
  have hl : Real.log (1+x) ≤ x := by
    have := Real.log_le_sub_one_of_pos hd
    linarith
  change -μ*(1-(1+x)⁻¹) - (μ-a)*Real.log ((1+x)⁻¹) ≤ _
  rw [Real.log_inv]
  have hb := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr haμ)
  have hi : (1+x)*(1+x)⁻¹=1 := mul_inv_cancel₀ hd.ne'
  have hxi : 0≤(1+x)⁻¹ := inv_nonneg.mpr hd.le
  have hbound : (1+x)⁻¹ ≤ 1 := (inv_le_one₀ hd).mpr (by linarith)
  have he : -μ*(1-(1+x)⁻¹)+(μ-a)*x = -a*x+μ*x^2*(1+x)⁻¹ := by
    field_simp <;> ring
  have hmx : μ*x^2*(1+x)⁻¹ ≤ m*x^2 := by
    have h1 := mul_le_mul_of_nonneg_left hbound (mul_nonneg hμ (sq_nonneg x))
    have h2 := mul_le_mul_of_nonneg_right hμm (sq_nonneg x)
    nlinarith
  have hex : -a*x+m*x^2 = -a^2/(4*m) := by
    dsimp [x]
    field_simp <;> ring
  nlinarith

lemma process_intersection_lower_additive (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (hm0 : 0<m) (D : SimpleHypergraph V) (hD : D ⊆ completeEdges V r)
    (a : ℝ) (ha : 0<a) :
    (processLaw V r).event (fun σ =>
      ((processState σ m ∩ D).card:ℝ) ≤ (m:ℝ)/(completeEdges V r).card*D.card-a) ≤
      Real.exp (-a^2/(4*m)) := by
  let μ : ℝ := (m:ℝ)/(completeEdges V r).card*D.card
  have hm' : (0:ℝ)<m := by exact_mod_cast hm0
  have hK : 0<(completeEdges V r).card := hm0.trans_le hm
  have hK' : (0:ℝ)<(completeEdges V r).card := by exact_mod_cast hK
  have hμ : 0≤μ := by dsimp [μ]; positivity
  have hμm : μ≤m := by
    have hDc : (D.card:ℝ)≤(completeEdges V r).card := by exact_mod_cast card_le_card hD
    have hh := mul_le_mul_of_nonneg_left hDc (show 0≤(m:ℝ)/(completeEdges V r).card by positivity)
    simpa [μ,div_mul_cancel₀ _ hK'.ne'] using hh
  by_cases hal : a≤μ
  · let q : ℝ := (1+a/(2*m))⁻¹
    have hden : 0<(1:ℝ)+a/(2*m) := by positivity
    have hq0 : 0<q := inv_pos.mpr hden
    have hq1 : q≤1 := (inv_le_one₀ hden).mpr (by
      have : 0≤a/(2*m) := by positivity
      linarith)
    have hnon : 0≤μ-a := sub_nonneg.mpr hal
    have hm_event := (processLaw V r).event_mono (fun σ
      (h : ((processState σ m ∩ D).card:ℝ)≤μ-a) => (Nat.le_floor_iff hnon).mpr h)
    have ht := process_intersection_lower_tail_exp m hm hK D hD q hq0 hq1 ⌊μ-a⌋₊
    apply (hm_event.trans ht).trans
    apply Real.exp_le_exp.mpr
    have hf := Nat.floor_le hnon
    have hlog : Real.log q ≤ 0 := Real.log_nonpos hq0.le hq1
    have he := mul_le_mul_of_nonpos_right hf hlog
    have hc := chernoff_lower_additive_algebra μ m a hm' hμ hμm ha hal
    calc
      _ = -μ*(1-q) - (⌊μ-a⌋₊:ℝ)*Real.log q := by dsimp [μ]; ring
      _ ≤ -μ*(1-q) - (μ-a)*Real.log q := by linarith
      _ ≤ _ := hc
  · have hfalse : (fun σ : EdgeOrder V r =>
        ((processState σ m ∩ D).card:ℝ) ≤ μ-a) = (fun _ => False) := by
      funext σ
      apply propext
      simp only [iff_false]
      intro h
      have : (0:ℝ)≤(processState σ m ∩ D).card := Nat.cast_nonneg _
      linarith
    change (processLaw V r).event (fun σ => ((processState σ m ∩ D).card:ℝ) ≤ μ-a) ≤ _
    rw [hfalse]
    simpa [FiniteEntropy.Law.event] using (Real.exp_pos (-a^2/(4*m))).le

lemma process_complement_intersection_card (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (D : SimpleHypergraph V) (σ : EdgeOrder V r) :
    (processState σ m ∩ (completeEdges V r \ D)).card +
      (processState σ m ∩ D).card = m := by
  have he : processState σ m ∩ (completeEdges V r \ D) = processState σ m \ D := by
    ext e
    simp only [mem_inter,mem_sdiff]
    constructor
    · tauto
    · rintro ⟨he,hn⟩
      exact ⟨he,processState_subset σ m he,hn⟩
  rw [he,card_sdiff_add_card_inter,processState_card,Nat.min_eq_left hm]

lemma process_intersection_upper_additive (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (hm0 : 0<m) (D : SimpleHypergraph V) (hD : D ⊆ completeEdges V r)
    (a : ℝ) (ha : 0<a) :
    (processLaw V r).event (fun σ =>
      (m:ℝ)/(completeEdges V r).card*D.card+a ≤ ((processState σ m ∩ D).card:ℝ)) ≤
      Real.exp (-a^2/(4*m)) := by
  have hK : 0<(completeEdges V r).card := hm0.trans_le hm
  have hK' : (0:ℝ)<(completeEdges V r).card := by exact_mod_cast hK
  have hcomp : ((completeEdges V r \ D).card:ℝ) = (completeEdges V r).card-D.card := by
    rw [card_sdiff_of_subset hD,Nat.cast_sub (card_le_card hD)]
  have hmean : (m:ℝ)/(completeEdges V r).card*(completeEdges V r \ D).card =
      m-(m:ℝ)/(completeEdges V r).card*D.card := by
    rw [hcomp,mul_sub,div_mul_cancel₀ _ hK'.ne']
  have hm_event := (processLaw V r).event_mono (E:=fun σ =>
      (m:ℝ)/(completeEdges V r).card*D.card+a ≤ ((processState σ m ∩ D).card:ℝ))
    (F:=fun σ => ((processState σ m ∩ (completeEdges V r \ D)).card:ℝ) ≤
      (m:ℝ)/(completeEdges V r).card*(completeEdges V r \ D).card-a) (by
      intro σ hσ
      have hc : ((processState σ m ∩ (completeEdges V r \ D)).card:ℝ)+
          ((processState σ m ∩ D).card:ℝ) = m := by
        exact_mod_cast process_complement_intersection_card m hm D σ
      rw [hmean]
      linarith)
  exact hm_event.trans (process_intersection_lower_additive m hm hm0 _ sdiff_subset a ha)

/-- Uniform additive Chernoff concentration for any complete-edge test set.
The variance scale m suffices even when the test or its complement is sparse. -/
theorem process_intersection_concentration (m : ℕ) (hm : m ≤ (completeEdges V r).card)
    (hm0 : 0<m) (D : SimpleHypergraph V) (hD : D ⊆ completeEdges V r)
    (a : ℝ) (ha : 0<a) :
    (processLaw V r).event (fun σ => a ≤
      |((processState σ m ∩ D).card:ℝ)-(m:ℝ)/(completeEdges V r).card*D.card|) ≤
      2*Real.exp (-a^2/(4*m)) := by
  let E : Bool → EdgeOrder V r → Prop := fun b σ =>
    if b then ((processState σ m ∩ D).card:ℝ) ≤ (m:ℝ)/(completeEdges V r).card*D.card-a
    else (m:ℝ)/(completeEdges V r).card*D.card+a ≤ ((processState σ m ∩ D).card:ℝ)
  have hm_event := (processLaw V r).event_mono
    (E:=fun σ => a ≤ |((processState σ m ∩ D).card:ℝ)-(m:ℝ)/(completeEdges V r).card*D.card|)
    (F:=fun σ => ∃ b, E b σ) (by
    intro σ hσ
    rcases le_abs.mp hσ with h | h
    · exact ⟨false,by dsimp [E]; linarith⟩
    · exact ⟨true,by dsimp [E]; linarith⟩)
  apply (hm_event.trans ((processLaw V r).finite_union_bound E)).trans
  have h1 := process_intersection_lower_additive m hm hm0 D hD a ha
  have h2 := process_intersection_upper_additive m hm hm0 D hD a ha
  simp only [Fintype.sum_bool,E,Bool.false_eq_true,if_false,if_true]
  linarith
end LooseHamilton
