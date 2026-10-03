module

public import HittingTimeLooseHamilton.TerminalLowSetTest

public section

/-! A finite, exponentially small bound for a large set of low-degree vertices. -/
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma lowSet_binomial_fixed_test (r t k : ℕ) (hr : 1 ≤ r) (S : Finset V)
    (hS : S.card=t) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : (98/100:ℝ)*Real.log (Fintype.card V:ℝ) ≤
      p*((Fintype.card V-t).choose (r-1):ℝ))
    (hk : (k:ℝ) ≤ (3/100:ℝ)*Real.log (Fintype.card V:ℝ)) :
    (BernoulliSubset.law (A:=Edge V r) p hp0 hp1).event
      (fun F => ∀ v ∈ S, (F ∩ edgeIncidences r v).card ≤ k) ≤
      Real.exp (-(82/100:ℝ)*t*Real.log (Fintype.card V:ℝ)) := by
  have hm := (BernoulliSubset.law (A:=Edge V r) p hp0 hp1).event_mono
    (E:=fun F => ∀ v ∈ S, (F ∩ edgeIncidences r v).card ≤ k)
    (F:=fun F => (F ∩ lowSetTest r S).card ≤ t*k) (by
      intro F hF
      apply (lowSetTest_inter_card_le r S F).trans
      calc
        _ ≤ ∑ v ∈ S, k := sum_le_sum (fun v hv => hF v hv)
        _ = _ := by simp [hS])
  have ht := BernoulliSubset.lower_tail p (1/100) hp0 hp1
    (by norm_num) (by norm_num) (lowSetTest r S) (t*k)
  rw [lowSetTest_card hr,hS,Nat.cast_mul,Nat.cast_mul] at ht
  have hlog : Real.log (1/100:ℝ) = -Real.log 100 := by
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  rw [hlog] at ht
  apply (hm.trans ht).trans
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg t)
  have hk' := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg t)
  have hl := mul_le_mul_of_nonneg_left log_hundred_lt_five.le
    (mul_nonneg (Nat.cast_nonneg t) (Nat.cast_nonneg k))
  nlinarith

@[expose] def incidenceLowSetEvent (r t k : ℕ) (F : Finset (Edge V r)) : Prop :=
  t ≤ ((univ : Finset V).filter (fun v => (F ∩ edgeIncidences r v).card ≤ k)).card

lemma incidenceLowSetEvent_antitone (r t k : ℕ) :
    Antitone (incidenceLowSetEvent (V:=V) r t k) := by
  intro F G hFG hG
  apply hG.trans
  apply card_le_card
  intro v hv
  simp only [mem_filter,mem_univ,true_and] at hv ⊢
  exact (card_le_card (inter_subset_inter hFG (Subset.refl _))).trans hv

lemma lowSet_binomial_bound (r t k : ℕ) (hr : 1 ≤ r)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : (98/100:ℝ)*Real.log (Fintype.card V:ℝ) ≤
      p*((Fintype.card V-t).choose (r-1):ℝ))
    (hk : (k:ℝ) ≤ (3/100:ℝ)*Real.log (Fintype.card V:ℝ)) :
    (BernoulliSubset.law (A:=Edge V r) p hp0 hp1).event
      (incidenceLowSetEvent r t k) ≤
      ((Fintype.card V).choose t:ℝ)*
        Real.exp (-(82/100:ℝ)*t*Real.log (Fintype.card V:ℝ)) := by
  let T := (univ : Finset V).powersetCard t
  let E : ↥T → Finset (Edge V r) → Prop :=
    fun S F => ∀ v ∈ S.val, (F ∩ edgeIncidences r v).card ≤ k
  have hm := (BernoulliSubset.law (A:=Edge V r) p hp0 hp1).event_mono
    (E:=incidenceLowSetEvent r t k) (F:=fun F => ∃ S : ↥T, E S F) (by
      intro F hF
      obtain ⟨S,hS,hSc⟩ := exists_subset_card_eq hF
      refine ⟨⟨S,mem_powersetCard.mpr ⟨subset_univ _,hSc⟩⟩,?_⟩
      intro v hv
      exact (mem_filter.mp (hS hv)).2)
  apply hm.trans
  apply ((BernoulliSubset.law (A:=Edge V r) p hp0 hp1).finite_union_bound E).trans
  calc
    _ ≤ ∑ S : ↥T, Real.exp (-(82/100:ℝ)*t*Real.log (Fintype.card V:ℝ)) := by
      apply sum_le_sum
      intro S _
      exact lowSet_binomial_fixed_test r t k hr S.val (mem_powersetCard.mp S.property).2
        p hp0 hp1 hmean hk
    _ = _ := by simp [T]

lemma fixed_size_decreasing_transfer {A : Type*} [Fintype A] [DecidableEq A]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (M : ℕ) (P : Finset A → Prop) (hP : Antitone P) :
    BernoulliSubset.prefixProbability M P ≤
      (BernoulliSubset.law (A:=A) p hp0 hp1).event P +
        (BernoulliSubset.law (A:=A) p hp0 hp1).event (fun S => M<S.card) := by
  have h := BernoulliSubset.fixed_size_transfer p hp0 hp1 M
    (fun S => ¬P S) (fun S T hST hS hT => hS (hP hST hT))
  rw [FiniteEntropy.Law.event_compl] at h
  have hc : BernoulliSubset.prefixProbability M (fun S => ¬P S) =
      1-BernoulliSubset.prefixProbability M P := by
    exact FiniteEntropy.Law.event_compl _ _
  rw [hc] at h
  linarith

lemma lowSet_fixed_size_bound (r M t k : ℕ) (hr : 1 ≤ r)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hsize : p*Fintype.card (Edge V r)=(99/100:ℝ)*M)
    (hmean : (98/100:ℝ)*Real.log (Fintype.card V:ℝ) ≤
      p*((Fintype.card V-t).choose (r-1):ℝ))
    (hk : (k:ℝ) ≤ (3/100:ℝ)*Real.log (Fintype.card V:ℝ)) :
    BernoulliSubset.prefixProbability M (incidenceLowSetEvent (V:=V) r t k) ≤
      ((Fintype.card V).choose t:ℝ)*
        Real.exp (-(82/100:ℝ)*t*Real.log (Fintype.card V:ℝ)) +
          Real.exp (-(M:ℝ)/1010000) := by
  apply (fixed_size_decreasing_transfer p hp0 hp1 M _
    (incidenceLowSetEvent_antitone r t k)).trans
  exact add_le_add (lowSet_binomial_bound r t k hr p hp0 hp1 hmean hk)
    (BernoulliSubset.size_overflow_bound p hp0 hp1 M hsize)
end LooseHamilton
