module

public import HittingTimeLooseHamilton.PathIncidenceError
public import HittingTimeLooseHamilton.ExtensionDegreeLower
public import HittingTimeLooseHamilton.ExtensionPairUpper

public section

/-! All-time incidence control conditional on a regular terminal graph. -/
noncomputable section
namespace LooseHamilton
open Filter

lemma path_incidence_conditional_eventually (r : ℕ) (hr : 3 ≤ r) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V=n →
      ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        CoreAdmissible r M ell markers B → ∀ F : TerminalState V r M ell,
        TerminalRegular terminalRegularityConstant F.val →
        (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event (fun σ =>
          ∃ j : ℕ, M ≤ j ∧ j ≤ (completeEdges V r).card ∧
            ¬PathIncidenceRegular r (pathDegreeLowerFactor r)
              (pathDegreeUpperFactor r terminalRegularityConstant) 4 (extensionState F σ j)) ≤
          6*(n:ℝ)^(-3:ℝ) := by
  filter_upwards [eventually_path_population (C:=terminalRegularityConstant) hr
      terminalRegularityConstant_pos.le,
    eventually_core_poisson_parameters B,eventually_feasibility_parameters B,
    eventually_terminal_lower_degree B,extension_pair_upper_eventually r hr]
    with n hpop hpois hfeas hlow hpairs
  intro V _ _ hcard M ell markers hadm F hreg
  obtain ⟨hlog,hμhi,_⟩ := hpois V hcard r M ell markers hadm
  have hμhi' : (r:ℝ)*M/n ≤ 2*Real.log n := by simpa [meanDegree,hcard] using hμhi
  have hμlo : (99/100:ℝ)*Real.log n ≤ (r:ℝ)*M/n :=
    hfeas.2.1 _ (by simpa [meanDegree,hcard] using hadm.density_window)
  have hl : 0<Real.log (n:ℝ) := by rw [hcard] at hlog; linarith
  have hhalf := hpop.2.2.2 M hμhi'
  have htail (j : ℕ) (hj : M ≤ j) (hjK : j ≤ (completeEdges V r).card)
      (i : IncidenceTestIndex V) :
      (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event (fun σ =>
        IncidenceTestFailure r (pathDegreeLowerFactor r)
          (pathDegreeUpperFactor r terminalRegularityConstant) 4 (extensionState F σ j) i) ≤
            (n:ℝ)^(-((r:ℝ)+5)) := by
    have hμj : (99/100:ℝ)*Real.log n ≤ (r:ℝ)*j/n := by
      apply hμlo.trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (Nat.cast_nonneg r)) (Nat.cast_nonneg n)
    have hcardj (σ : MissingOrder V r M) := extensionState_card F σ j hj hjK
    rcases i with v | v | ⟨u,v⟩
    · have hdlo : epsilon/2*Real.log n ≤ (vertexDegree F.val v:ℝ) := by
        have he := hlow (ell v) (by simpa [lowerDegreeBase,hcard] using hadm.offsets v)
        exact he.trans (by exact_mod_cast F.property.2.2 v)
      have hdmax : (vertexDegree F.val v:ℝ) ≤ terminalRegularityConstant*Real.log n := by
        simpa [hcard] using hreg.maximum_degree v
      have hdhi : (vertexDegree F.val v:ℝ) ≤ ((n-1).choose (r-1):ℝ)/2 :=
        hdmax.trans hpop.2.2.1
      have hh := extension_degree_lower_polynomial F hcard hr hpop.1 hl hhalf hj hjK hμlo hμhi' v hdlo hdhi
      simpa only [IncidenceTestFailure,meanDegree,hcardj,hcard] using hh
    · have hh := extension_degree_upper_polynomial F hcard hr hpop.1
        terminalRegularityConstant_pos.le hl.le hhalf hj hjK hμj v
        (by simpa [hcard] using hreg.maximum_degree v)
      simpa only [IncidenceTestFailure,meanDegree,hcardj,hcard] using hh
    · by_cases huv : u=v
      · subst v
        simp [IncidenceTestFailure,FiniteEntropy.Law.event]
        positivity
      · have hh := hpairs V hcard M ell F j hhalf hj hjK hμj u v huv (hreg.pair_degree u v huv)
        simpa [IncidenceTestFailure,huv,meanDegree,hcardj,hcard] using hh
  have hh := path_incidence_failure_le
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)) (fun σ => extensionState F σ)
    r M (completeEdges V r).card (pathDegreeLowerFactor r)
    (pathDegreeUpperFactor r terminalRegularityConstant) 4 ((n:ℝ)^(-((r:ℝ)+5)))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) htail
  apply hh.trans
  simpa only [hcard,completeEdges_card] using incidence_polynomial_union_bound n r (by omega)
end LooseHamilton
