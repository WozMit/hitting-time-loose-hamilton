module

public import HittingTimeLooseHamilton.NestedPairModels
public import HittingTimeLooseHamilton.ExtensionMarginalCompletion
public import HittingTimeLooseHamilton.KahnConditioning

public section

/-! The terminal/current pair at a fixed time is uniform over all feasible nested pairs. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma extension_nested_state_mass (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (p : NestedState V r M ell j) :
    ((extensionLaw r M ell).map (extensionNestedState r M ell j hMj hj)).mass p =
      1/((Fintype.card (TerminalState V r M ell):ℝ)*
        (((completeEdges V r).card-M).choose (j-M):ℝ)) := by
  classical
  change (extensionLaw r M ell).event (fun ω => extensionNestedState r M ell j hMj hj ω=p)=_
  simp_rw [extensionNestedState_eq_iff]
  rw [extensionLaw,FiniteEntropy.Law.event_prod_sum]
  simp_rw [FiniteEntropy.Law.event_const_and]
  rw [sum_eq_single p.val.1]
  · rw [if_pos rfl,extension_single_state_kernel _ j hMj hj p.val.2 p.property.2.1
      p.property.2.2,if_pos p.property.1,terminalLaw_mass]
    ring
  · intro F _ hF
    simp [hF]
  · simp

lemma nestedState_card (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card) :
    Fintype.card (NestedState V r M ell j) =
      Fintype.card (TerminalState V r M ell)*((completeEdges V r).card-M).choose (j-M) := by
  let ρ := (extensionLaw r M ell).map (extensionNestedState r M ell j hMj hj)
  have ht := ρ.total
  have hm (p : NestedState V r M ell j) := extension_nested_state_mass r M ell j hMj hj p
  dsimp only [ρ] at ht
  simp_rw [hm] at ht
  simp only [sum_const,card_univ,nsmul_eq_mul] at ht
  have hc : (0:ℝ)<(((completeEdges V r).card-M).choose (j-M):ℝ) := by
    exact_mod_cast Nat.choose_pos (show j-M ≤ (completeEdges V r).card-M by omega)
  have hT : (0:ℝ)<Fintype.card (TerminalState V r M ell) := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card (NestedState V r M ell j):ℝ) =
      (Fintype.card (TerminalState V r M ell):ℝ)*(((completeEdges V r).card-M).choose (j-M):ℝ) := by
    have hdiv : (Fintype.card (NestedState V r M ell j):ℝ) /
        ((Fintype.card (TerminalState V r M ell):ℝ)*(((completeEdges V r).card-M).choose (j-M):ℝ)) = 1 := by
      simpa only [mul_one_div] using ht
    have hh := (div_eq_iff (mul_pos hT hc).ne').mp hdiv
    simpa using hh
  exact_mod_cast he

/-- Exact pushforward equality under Q, including all nested pairs and no boundary conditioning yet. -/
theorem extension_nested_law_uniform (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card) :
    (extensionLaw r M ell).map (extensionNestedState r M ell j hMj hj) =
      @FiniteEntropy.uniform (NestedState V r M ell j) inferInstance
        (nestedState_nonempty r M ell j hMj hj) := by
  apply FiniteEntropy.Law.ext_mass
  intro p
  rw [extension_nested_state_mass]
  simp only [FiniteEntropy.uniform,←one_div]
  rw [nestedState_card r M ell j hMj hj,Nat.cast_mul]

/-- Every property of the observed pair therefore has its uniform finite counting probability. -/
theorem extension_nested_event_uniform (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (P : NestedState V r M ell j → Prop) :
    (extensionLaw r M ell).event (fun ω => P (extensionNestedState r M ell j hMj hj ω)) =
      (@FiniteEntropy.uniform (NestedState V r M ell j) inferInstance
        (nestedState_nonempty r M ell j hMj hj)).event P := by
  rw [←FiniteEntropy.Law.event_map,extension_nested_law_uniform]
end LooseHamilton
