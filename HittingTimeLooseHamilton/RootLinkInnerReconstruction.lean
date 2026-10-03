module

public import HittingTimeLooseHamilton.RootLinkReconstruction
public import HittingTimeLooseHamilton.RootUniformCountCoupling
public import HittingTimeLooseHamilton.UniformConditionalEquivalence

public section

/-! Typed reconstruction of the exact uniform count fibres by common independent orders. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev RootInnerState (A : Type*) [Fintype A] (b : ℕ) := ↥((univ:Finset A).powersetCard b)
abbrev RootInnerSeed (S : Finset A) := FiniteOrder ↥S × FiniteOrder ↥((univ:Finset A)\S)

@[expose] def rootInnerSeedLaw (S : Finset A) : FiniteEntropy.Law (RootInnerSeed S) :=
  (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder ↥S)).prod FiniteEntropy.uniform

@[expose] def RootCountValid (S : Finset A) (b : ℕ) (j : Fin (b+1)) : Prop :=
  j.val≤S.card ∧ b-j.val≤((univ:Finset A)\S).card

@[expose] def rootInnerReconstruct (S : Finset A) (b : ℕ) [Nonempty (RootInnerState A b)]
    (j : Fin (b+1)) (σ : RootInnerSeed S) : RootInnerState A b := by
  classical
  exact if hj : RootCountValid S b j then
    ⟨rootCountSet S b j.val σ,mem_powersetCard.mpr ⟨subset_univ _,
      rootCountSet_card S b j.val σ (by omega) hj.1 hj.2⟩⟩
    else Classical.choice inferInstance

lemma rootInnerReconstruct_val (S : Finset A) (b : ℕ) [Nonempty (RootInnerState A b)]
    (j : Fin (b+1)) (hj : RootCountValid S b j) (σ : RootInnerSeed S) :
    (rootInnerReconstruct S b j σ).val=rootCountSet S b j.val σ := by
  simp only [rootInnerReconstruct,dif_pos hj]

lemma rootInnerReconstruct_count (S : Finset A) (b : ℕ) [Nonempty (RootInnerState A b)]
    (j : Fin (b+1)) (hj : RootCountValid S b j) (σ : RootInnerSeed S) :
    rootIntersectionIndex univ S b (rootInnerReconstruct S b j σ)=j := by
  apply Fin.ext
  change ((rootInnerReconstruct S b j σ).val∩S).card=j.val
  rw [rootInnerReconstruct_val S b j hj σ]
  exact rootCountSet_hit_card S b j.val σ hj.1

lemma rootInnerCount_valid (S : Finset A) (b : ℕ) (T : RootInnerState A b) :
    RootCountValid S b (rootIntersectionIndex univ S b T) := by
  constructor
  · exact card_le_card inter_subset_right
  · have ht := (mem_powersetCard.mp T.property).2
    have hc := card_sdiff_add_card_inter T.val S
    have hs := card_le_card (sdiff_subset_sdiff (subset_univ T.val) (Subset.refl S))
    change b-(T.val∩S).card≤_ at *
    omega

lemma rootInnerCount_positive_valid (S : Finset A) (b : ℕ)
    [Nonempty (RootInnerState A b)] (j : Fin (b+1))
    (hj : 0<(rootOriginalCountLaw univ S b).mass j) : RootCountValid S b j := by
  obtain ⟨T,hT⟩ := exists_of_event_pos FiniteEntropy.uniform
    (fun T : RootInnerState A b => rootIntersectionIndex univ S b T=j) hj
  rw [←hT]
  exact rootInnerCount_valid S b T

/-- On every positive count fibre, the ordered-parts construction is exactly the
conditional uniform law of the original sampled subset. -/
theorem rootInnerReconstruct_law (S : Finset A) (b : ℕ)
    [Nonempty (RootInnerState A b)] (j : Fin (b+1))
    (hj : 0<(rootOriginalCountLaw univ S b).mass j) :
    (rootInnerSeedLaw S).map (rootInnerReconstruct S b j)=
      (FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState A b)).conditionOr
        (fun T => rootIntersectionIndex univ S b T=j) := by
  classical
  have hv := rootInnerCount_positive_valid S b j hj
  have hbj : j.val≤b := by omega
  have hpos : 0<(FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState A b)).event
      (fun T => rootIntersectionIndex univ S b T=j) := hj
  have hcnt : (FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState A b)).event
      (fun T => rootIntersectionIndex univ S b T=j) =
      ((S.card.choose j.val:ℝ)*((univ\S).card.choose (b-j.val):ℝ))/((univ:Finset A).card.choose b:ℝ) := by
    have he : (fun T : RootInnerState A b => rootIntersectionIndex univ S b T=j) =
        (fun T => (T.val∩S).card=j.val) := by
      funext T
      exact propext Fin.ext_iff
    rw [he]
    exact root_intersection_uniform_atom univ S (subset_univ _) b j.val hbj
  have hN : (((univ:Finset A).card.choose b):ℝ) ≠ 0 := by
    have h := Fintype.card_pos (α:=RootInnerState A b)
    simpa only [Fintype.card_coe,card_powersetCard,Nat.cast_ne_zero] using Nat.ne_of_gt h
  have hW : (S.card.choose j.val:ℝ)*((univ\S).card.choose (b-j.val):ℝ) ≠0 := by
    have hs := Nat.choose_pos hv.1
    have hc := Nat.choose_pos hv.2
    positivity
  apply FiniteEntropy.Law.ext_mass
  intro T
  rw [FiniteEntropy.Law.conditionOr,dif_pos hpos]
  by_cases hT : rootIntersectionIndex univ S b T=j
  · have ht : (T.val∩S).card=j.val := congrArg Fin.val hT
    have hprob := rootCountSet_probability S T.val b j.val hbj hv.1 hv.2
      (mem_powersetCard.mp T.property).2 ht
    have he : (fun σ : RootInnerSeed S => rootInnerReconstruct S b j σ=T) =
        (fun σ => rootCountSet S b j.val σ=T.val) := by
      funext σ
      rw [Subtype.ext_iff,rootInnerReconstruct_val S b j hv σ]
    change (rootInnerSeedLaw S).event (fun σ => rootInnerReconstruct S b j σ=T)=_
    rw [he]
    simp only [FiniteEntropy.Law.condition,if_pos hT]
    rw [hcnt]
    simp only [FiniteEntropy.uniform]
    rw [show (rootInnerSeedLaw S).event (fun σ=>rootCountSet S b j.val σ=T.val)=
      1/((S.card.choose j.val:ℝ)*((univ\S).card.choose (b-j.val):ℝ)) from hprob]
    simp only [Fintype.card_coe,card_powersetCard]
    have hN' : ((Fintype.card A).choose b:ℝ)≠0 := by simpa only [card_univ] using hN
    field_simp [hN',hW]
  · change (rootInnerSeedLaw S).event (fun σ => rootInnerReconstruct S b j σ=T)=_
    rw [(rootInnerSeedLaw S).event_eq_zero_of_false (by
      intro σ hσ
      have hc := rootInnerReconstruct_count S b j hv σ
      rw [hσ] at hc
      exact hT hc)]
    simp only [FiniteEntropy.Law.condition,if_neg hT]
end LooseHamilton
