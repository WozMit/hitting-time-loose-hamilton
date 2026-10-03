module

public import HittingTimeLooseHamilton.TerminalLowSetFinite
public import HittingTimeLooseHamilton.TerminalConditioning
public import HittingTimeLooseHamilton.TerminalRegularityModels

public section

/-! Transfer the low-set estimate to the degree-constrained terminal law. -/
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def terminalLowThreshold (n : ℕ) : ℕ := ⌊(3/100:ℝ)*Real.log n⌋₊

@[expose] def terminalLowSetTestSize (n : ℕ) : ℕ := ⌈(n:ℝ)^(1/4:ℝ)⌉₊

lemma terminalLowVertices_eq_filter (F : SimpleHypergraph V) (hn : 1 ≤ Fintype.card V) :
    terminalLowVertices F = univ.filter (fun v => vertexDegree F v ≤ terminalLowThreshold (Fintype.card V)) := by
  ext v
  simp only [mem_terminalLowVertices,mem_filter,mem_univ,true_and]
  rw [terminalLowThreshold,Nat.le_floor_iff (by
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hn)))]
  norm_num [epsilon]

lemma lowSet_prefix_probability_eq (r M t : ℕ) (hn : 1 ≤ Fintype.card V) :
    (processLaw V r).event (fun σ => t ≤ (terminalLowVertices (processState σ M)).card) =
      BernoulliSubset.prefixProbability M
        (incidenceLowSetEvent (V:=V) r t (terminalLowThreshold (Fintype.card V))) := by
  have h := FiniteEntropy.Law.uniform_event_equiv (orderRankEquiv (Edge V r))
    (fun σ => incidenceLowSetEvent r t (terminalLowThreshold (Fintype.card V)) (orderPrefix σ M))
  simp only [incidenceLowSetEvent,prefix_incidence_degree] at h
  simpa only [processLaw,BernoulliSubset.prefixProbability,incidenceLowSetEvent,
    terminalLowVertices_eq_filter _ hn] using h

lemma terminal_low_set_probability_finite (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (hr : 1 ≤ r) (hn : 1 ≤ Fintype.card V)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hsize : p*Fintype.card (Edge V r)=(99/100:ℝ)*M)
    (hmean : (98/100:ℝ)*Real.log (Fintype.card V:ℝ) ≤
      p*((Fintype.card V-terminalLowSetTestSize (Fintype.card V)).choose (r-1):ℝ))
    (hbeta : Real.exp (-(Fintype.card V:ℝ)^(1/10:ℝ)) ≤ terminalFeasibilityProbability r M ell) :
    (terminalLaw r M ell).event (fun F =>
      (Fintype.card V:ℝ)^(1/4:ℝ) < ((terminalLowVertices F.val).card:ℝ)) ≤
      (((Fintype.card V).choose (terminalLowSetTestSize (Fintype.card V)):ℝ)*
        Real.exp (-(82/100:ℝ)*terminalLowSetTestSize (Fintype.card V)*Real.log (Fintype.card V:ℝ)) +
          Real.exp (-(M:ℝ)/1010000)) * Real.exp ((Fintype.card V:ℝ)^(1/10:ℝ)) := by
  have hb : 0 < terminalFeasibilityProbability r M ell :=
    (Real.exp_pos _).trans_le hbeta
  have hm := (terminalLaw r M ell).event_mono (fun F
    (hF : (Fintype.card V:ℝ)^(1/4:ℝ) < ((terminalLowVertices F.val).card:ℝ)) =>
      (Nat.ceil_le.mpr hF.le : terminalLowSetTestSize (Fintype.card V) ≤ (terminalLowVertices F.val).card))
  have hc := terminal_event_le_prefix_div r M ell
    (fun F => terminalLowSetTestSize (Fintype.card V) ≤ (terminalLowVertices F).card) hb
  rw [lowSet_prefix_probability_eq r M _ hn] at hc
  have ht := lowSet_fixed_size_bound r M (terminalLowSetTestSize (Fintype.card V))
    (terminalLowThreshold (Fintype.card V)) hr p hp0 hp1 hsize hmean
    (Nat.floor_le (by exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hn))))
  apply (hm.trans hc).trans
  apply (div_le_div_of_nonneg_right ht hb.le).trans
  have hnon : 0 ≤ (((Fintype.card V).choose (terminalLowSetTestSize (Fintype.card V)):ℝ)*
        Real.exp (-(82/100:ℝ)*terminalLowSetTestSize (Fintype.card V)*Real.log (Fintype.card V:ℝ)) +
          Real.exp (-(M:ℝ)/1010000)) := by positivity
  calc
    _ ≤ _ / Real.exp (-(Fintype.card V:ℝ)^(1/10:ℝ)) :=
      div_le_div_of_nonneg_left hnon (Real.exp_pos _) hbeta
    _ = _ := by rw [Real.exp_neg,div_inv_eq_mul]
end LooseHamilton
