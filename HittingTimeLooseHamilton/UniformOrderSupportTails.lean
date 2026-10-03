module

public import HittingTimeLooseHamilton.BernoulliFixedSizeTransfer
public import HittingTimeLooseHamilton.HypergeometricInclusionBounds
public import HittingTimeLooseHamilton.FiniteAvoidanceTail
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

/-! Hypergeometric support tails for a uniform order of an arbitrary finite population. -/
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]
local instance : Nonempty (FiniteOrder A) := ⟨Fintype.equivFin A⟩

lemma order_contains_probability (m : ℕ) (hm : m ≤ Fintype.card A)
    (D : Finset A) (hD : D.card ≤ m) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event
      (fun σ => D ⊆ orderPrefix σ m) =
      ((Fintype.card A-D.card).choose (m-D.card):ℝ)/((Fintype.card A).choose m) := by
  change BernoulliSubset.prefixProbability m (fun S => D ⊆ S) = _
  rw [BernoulliSubset.prefixProbability_eq m hm]
  congr 1
  norm_cast
  convert Kahn.Ordering.card_subsets_containing (univ : Finset A) D (subset_univ _) m hD using 1
  · congr 1
    ext S
    simp
  · simp

lemma order_avoids_probability (m : ℕ) (hm : m ≤ Fintype.card A) (D : Finset A) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event
      (fun σ => Disjoint (orderPrefix σ m) D) =
      ((Fintype.card A-D.card).choose m:ℝ)/((Fintype.card A).choose m) := by
  classical
  change BernoulliSubset.prefixProbability m (fun S => Disjoint S D) = _
  rw [BernoulliSubset.prefixProbability_eq m hm]
  have he : ((univ : Finset A).powersetCard m).filter (fun S => Disjoint S D) =
      (univ \ D).powersetCard m := by
    ext S
    simp only [mem_filter,mem_powersetCard,subset_sdiff]
    tauto
  congr 1
  have hh := congrArg Finset.card he
  simp only [card_powersetCard,card_sdiff_of_subset (subset_univ _),card_univ] at hh
  norm_cast
  convert hh using 1
  congr 1
  ext S
  simp

lemma order_support_upper_tail (m k : ℕ) (hm : m ≤ Fintype.card A)
    (hN : 0 < Fintype.card A) (D : Finset A) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event
      (fun σ => k ≤ (D ∩ orderPrefix σ m).card) ≤
      (D.card.choose k:ℝ)*((m:ℝ)/Fintype.card A)^k := by
  classical
  let p : FiniteEntropy.Law (FiniteOrder A) := FiniteEntropy.uniform
  by_cases hk : k ≤ m
  · let E : ↥(D.powersetCard k) → FiniteOrder A → Prop := fun T σ => T.val ⊆ orderPrefix σ m
    have hmono : p.event (fun σ => k ≤ (D ∩ orderPrefix σ m).card) ≤
        p.event (fun σ => ∃ T, E T σ) := by
      apply p.event_mono
      intro σ h
      obtain ⟨T,hT,hc⟩ := exists_subset_card_eq h
      exact ⟨⟨T,mem_powersetCard.mpr ⟨hT.trans inter_subset_left,hc⟩⟩,
        hT.trans inter_subset_right⟩
    have ht (T : ↥(D.powersetCard k)) : p.event (E T) ≤ ((m:ℝ)/Fintype.card A)^k := by
      have hc := (mem_powersetCard.mp T.property).2
      dsimp [p,E]
      rw [order_contains_probability m hm T.val (by omega),hc]
      exact Hypergeometric.inclusion_ratio_le hm hk hN
    calc
      _ ≤ ∑ T, p.event (E T) := hmono.trans (p.finite_union_bound E)
      _ ≤ ∑ _T : ↥(D.powersetCard k), ((m:ℝ)/Fintype.card A)^k :=
        sum_le_sum (fun T _ => ht T)
      _ = _ := by simp
  · rw [p.event_eq_zero_of_false (by
      intro σ h
      have hc := card_le_card (inter_subset_right : D ∩ orderPrefix σ m ⊆ orderPrefix σ m)
      rw [orderPrefix_card σ m hm] at hc
      omega)]
    positivity

lemma binomial_term_tilt_bound (D k : ℕ) (ρ t : ℝ) (hρ : 0 ≤ ρ) (ht : 0 < t) :
    (D.choose k:ℝ)*ρ^k ≤ Real.exp (t*D*ρ)/t^k := by
  have hterm : (D.choose k:ℝ)*(t*ρ)^k ≤ (t*ρ+1)^D := by
    by_cases hk : k ≤ D
    · rw [add_pow]
      have h := single_le_sum
        (f := fun i => (t*ρ)^i*(1:ℝ)^(D-i)*(D.choose i:ℝ))
        (fun i _ => by positivity) (mem_range.mpr (show k<D+1 by omega))
      simpa only [one_pow,mul_one,mul_comm] using h
    · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]; positivity
  have he : (t*ρ+1)^D ≤ Real.exp (t*D*ρ) := by
    calc
      _ ≤ (Real.exp (t*ρ))^D := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) D
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  apply (le_div_iff₀ (pow_pos ht _)).mpr
  calc
    _ = (D.choose k:ℝ)*(t*ρ)^k := by rw [mul_pow]; ring
    _ ≤ _ := hterm.trans he

lemma order_support_upper_exp (m k : ℕ) (hm : m ≤ Fintype.card A)
    (hN : 0 < Fintype.card A) (D : Finset A) (t : ℝ) (ht : 0 < t) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event
      (fun σ => k ≤ (D ∩ orderPrefix σ m).card) ≤
      Real.exp (t*(D.card:ℝ)*m/Fintype.card A)/t^k := by
  exact (order_support_upper_tail m k hm hN D).trans
    (by simpa only [mul_div_assoc] using
      binomial_term_tilt_bound D.card k ((m:ℝ)/Fintype.card A) t (by positivity) ht)

lemma order_support_lower_exp (m k : ℕ) (hm : m ≤ Fintype.card A)
    (hN : 0 < Fintype.card A) (D : Finset A) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event
      (fun σ => (orderPrefix σ m ∩ D).card ≤ k) ≤
      Real.exp (-(m:ℝ)/Fintype.card A*D.card*(1-q)-(k:ℝ)*Real.log q) := by
  let p : FiniteEntropy.Law (FiniteOrder A) := FiniteEntropy.uniform
  have hρ : (m:ℝ)/Fintype.card A ≤ 1 :=
    (div_le_one (Nat.cast_pos.mpr hN)).mpr (Nat.cast_le.mpr hm)
  have hav (T : Finset A) (_hT : T ⊆ D) :
      p.event (fun σ => True ∧ Disjoint (orderPrefix σ m) T) ≤
        1*(1-(m:ℝ)/Fintype.card A)^T.card := by
    simp only [true_and,one_mul]
    rw [order_avoids_probability m hm T]
    exact Hypergeometric.avoidance_ratio_le hm hN (card_le_univ T)
  have h := Hypergeometric.lower_tail_exp_le_of_avoidance p
    (fun σ => orderPrefix σ m) D (fun _ => True) q
    ((m:ℝ)/Fintype.card A) 1 hq hq1 (by positivity) hρ (by norm_num) k hav
  simpa only [true_and,one_mul,neg_div] using h
end LooseHamilton
