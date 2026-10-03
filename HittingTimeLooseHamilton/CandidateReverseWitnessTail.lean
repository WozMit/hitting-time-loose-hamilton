module

public import HittingTimeLooseHamilton.RootLinkUniformTail
public import HittingTimeLooseHamilton.FiniteAvoidanceTail

public section

/-! Finite lower-tail input for reverse witnesses. This is independent of any
unproved forward witness or entropy-preservation assertion. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [DecidableEq A]

lemma candidate_reverse_exponent_pos : 0 < (1-Real.log 2)/2 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
  linarith

lemma candidate_uniform_avoids (U D : Finset A) (hD : D ⊆ U)
    (τ : ℕ) [Nonempty ↥(U.powersetCard τ)] :
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard τ)).event
      (fun T => Disjoint T.val D) =
      ((U.card-D.card).choose τ:ℝ)/(U.card.choose τ:ℝ) := by
  classical
  rw [FiniteEntropy.Law.uniform_event,Fintype.card_coe,card_powersetCard]
  have hc : (univ.filter (fun T : ↥(U.powersetCard τ) => Disjoint T.val D)).card =
      ((U \ D).powersetCard τ).card := by
    apply card_bij (fun T _ => T.val)
    · intro T hT
      obtain ⟨hs,ht⟩ := mem_powersetCard.mp T.property
      exact mem_powersetCard.mpr ⟨subset_sdiff.mpr ⟨hs,(mem_filter.mp hT).2⟩,ht⟩
    · intro T hT S hS he
      exact Subtype.ext he
    · intro T hT
      obtain ⟨hs,ht⟩ := mem_powersetCard.mp hT
      obtain ⟨hU,hD⟩ := subset_sdiff.mp hs
      exact ⟨⟨T,mem_powersetCard.mpr ⟨hU,ht⟩⟩,mem_filter.mpr ⟨mem_univ _,hD⟩,rfl⟩
  rw [hc,card_powersetCard,card_sdiff_of_subset hD]

/-- A genuine uniform-subset lower tail, rather than an assumed probability
bound. The threshold is at most half a lower bound on the mean. -/
theorem candidate_uniform_lower_tail (U D : Finset A) (hD : D ⊆ U)
    (τ k : ℕ) (hτ : τ ≤ U.card) (hU : 0 < U.card)
    [Nonempty ↥(U.powersetCard τ)] (δ : ℝ) (_hδ : 0 ≤ δ)
    (hdensity : δ * U.card ≤ D.card) (hk : (k:ℝ) ≤ δ*τ/2) :
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard τ)).event
      (fun T => (T.val ∩ D).card ≤ k) ≤
      Real.exp (-((1-Real.log 2)/2)*δ*τ) := by
  classical
  let p : FiniteEntropy.Law ↥(U.powersetCard τ) := FiniteEntropy.uniform
  have hρ : (τ:ℝ)/U.card ≤ 1 :=
    (div_le_one (Nat.cast_pos.mpr hU)).mpr (Nat.cast_le.mpr hτ)
  have hav (S : Finset A) (hS : S ⊆ D) :
      p.event (fun T => True ∧ Disjoint T.val S) ≤
        1*(1-(τ:ℝ)/U.card)^S.card := by
    simp only [true_and,one_mul]
    rw [candidate_uniform_avoids U S (hS.trans hD) τ]
    exact Hypergeometric.avoidance_ratio_le hτ hU (card_le_card (hS.trans hD))
  have ht := Hypergeometric.lower_tail_exp_le_of_avoidance p (fun T => T.val) D
    (fun _ => True) (1/2) ((τ:ℝ)/U.card) 1 (by norm_num) (by norm_num)
    (by positivity) hρ (by norm_num) k hav
  simp only [true_and,one_mul] at ht
  apply ht.trans
  apply Real.exp_le_exp.mpr
  have hl : Real.log (1/2:ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  rw [hl]
  have hln : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hd : δ*τ ≤ (τ:ℝ)/U.card*D.card := by
    have hd' : δ ≤ (D.card:ℝ)/U.card := (le_div_iff₀ (Nat.cast_pos.mpr hU)).mpr hdensity
    have hh := mul_le_mul_of_nonneg_left hd' (show (0:ℝ)≤τ by positivity)
    convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_right hk hln
  nlinarith only [hd,hh]

end LooseHamilton
