module

public import HittingTimeLooseHamilton.PathRegularityModels
public import HittingTimeLooseHamilton.TerminalRegularityProbability
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! Finite aggregation of degree and codegree tails over all vertices and times. -/
noncomputable section
open scoped BigOperators
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The incidence part of path regularity, with separate upper constants. -/
structure PathIncidenceRegular (r : ℕ) (c Cdegree Cpair : ℝ) (F : SimpleHypergraph V) : Prop where
  lower_degree : ∀ v, c*meanDegree (V:=V) r F.card ≤ (vertexDegree F v:ℝ)
  upper_degree : ∀ v, (vertexDegree F v:ℝ) ≤ Cdegree*meanDegree (V:=V) r F.card
  codegree : ∀ u v, u ≠ v → (pairDegree F u v:ℝ) ≤
    Cpair*meanDegree (V:=V) r F.card*(Real.log (Fintype.card V:ℝ))^(-1/4:ℝ)

@[expose] def IncidenceTestIndex (V : Type*) := V ⊕ (V ⊕ (V×V))
@[expose] instance : Fintype (IncidenceTestIndex V) := inferInstanceAs (Fintype (V ⊕ (V ⊕ (V×V))))

@[expose] def IncidenceTestFailure (r : ℕ) (c Cdegree Cpair : ℝ) (F : SimpleHypergraph V) :
    IncidenceTestIndex V → Prop
  | .inl v => (vertexDegree F v:ℝ) < c*meanDegree (V:=V) r F.card
  | .inr (.inl v) => Cdegree*meanDegree (V:=V) r F.card < (vertexDegree F v:ℝ)
  | .inr (.inr (u,v)) => u ≠ v ∧
      Cpair*meanDegree (V:=V) r F.card*(Real.log (Fintype.card V:ℝ))^(-1/4:ℝ) < (pairDegree F u v:ℝ)

lemma incidence_failure_iff (r : ℕ) (c Cdegree Cpair : ℝ) (F : SimpleHypergraph V) :
    ¬PathIncidenceRegular r c Cdegree Cpair F ↔ ∃ i, IncidenceTestFailure r c Cdegree Cpair F i := by
  classical
  constructor
  · intro h
    by_contra hn
    simp only [not_exists] at hn
    apply h
    constructor
    · intro v
      exact le_of_not_gt (hn (.inl v))
    · intro v
      exact le_of_not_gt (hn (.inr (.inl v)))
    · intro u v huv
      have hh := hn (.inr (.inr (u,v)))
      exact le_of_not_gt (fun hp => hh ⟨huv,hp⟩)
  · rintro ⟨i,hi⟩ h
    rcases i with v | v | ⟨u,v⟩
    · exact not_lt_of_ge (h.lower_degree v) hi
    · exact not_lt_of_ge (h.upper_degree v) hi
    · exact not_lt_of_ge (h.codegree u v hi.1) hi.2

/-- Generic finite aggregation: no independence between times or vertices is needed. -/
lemma path_incidence_failure_le {Ω : Type*} [Fintype Ω] (ρ : FiniteEntropy.Law Ω)
    (F : Ω → ℕ → SimpleHypergraph V) (r M K : ℕ) (c Cdegree Cpair u : ℝ)
    (hu : 0 ≤ u)
    (htail : ∀ j, M ≤ j → j ≤ K → ∀ i : IncidenceTestIndex V,
      ρ.event (fun ω => IncidenceTestFailure r c Cdegree Cpair (F ω j) i) ≤ u) :
    ρ.event (fun ω => ∃ j : ℕ, M ≤ j ∧ j ≤ K ∧ ¬PathIncidenceRegular r c Cdegree Cpair (F ω j)) ≤
      (2*(Fintype.card V:ℝ)+(Fintype.card V:ℝ)^2)*(K+1)*u := by
  let J := Fin (K+1) × IncidenceTestIndex V
  let E : J → Ω → Prop := fun x ω => M ≤ x.1.val ∧
    IncidenceTestFailure r c Cdegree Cpair (F ω x.1.val) x.2
  have hmono := ρ.event_mono
    (E:=fun ω => ∃ j : ℕ, M ≤ j ∧ j ≤ K ∧ ¬PathIncidenceRegular r c Cdegree Cpair (F ω j))
    (F:=fun ω => ∃ x : J, E x ω) (by
      rintro ω ⟨j,hMj,hj,hf⟩
      obtain ⟨i,hi⟩ := (incidence_failure_iff r c Cdegree Cpair (F ω j)).mp hf
      exact ⟨⟨⟨j,by omega⟩,i⟩,hMj,hi⟩)
  apply (hmono.trans (ρ.finite_union_bound E)).trans
  calc
    _ ≤ ∑ x : J, u := by
      apply sum_le_sum
      intro x _
      by_cases hx : M ≤ x.1.val
      · exact (ρ.event_mono (fun ω (h : E x ω) => h.2)).trans
          (htail x.1.val hx (by have := x.1.isLt; omega) x.2)
      · simpa [E,hx,FiniteEntropy.Law.event] using hu
    _ = _ := by
      have hc : Fintype.card (IncidenceTestIndex V) =
          Fintype.card V + (Fintype.card V + Fintype.card V * Fintype.card V) := by
        change Fintype.card (V ⊕ V ⊕ V × V) = _
        simp
      simp only [sum_const, card_univ, J, Fintype.card_prod, Fintype.card_fin,
        hc, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- Product-law integration separates the exceptional terminal graphs once. -/
lemma extension_bad_event_le_terminal_plus (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (E : TerminalState V r M ell → MissingOrder V r M → Prop)
    (u : ℝ) (hu : 0 ≤ u)
    (hgood : ∀ F, TerminalRegular terminalRegularityConstant F.val →
      (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event (E F) ≤ u) :
    (extensionLaw r M ell).event (fun ω => E ω.1 ω.2) ≤
      1-(terminalLaw r M ell).event (fun F => TerminalRegular terminalRegularityConstant F.val)+u := by
  have h := FiniteEntropy.Law.event_prod_le_bad_good (terminalLaw r M ell)
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M))
    (fun F => ¬TerminalRegular terminalRegularityConstant F.val) E 1 u
    (fun F _ => FiniteEntropy.Law.event_le_one _ _) (fun F h => hgood F (not_not.mp h))
  rw [FiniteEntropy.Law.event_compl] at h
  change (extensionLaw r M ell).event _ ≤ _ at h
  have hp := (terminalLaw r M ell).event_le_one (fun F => TerminalRegular terminalRegularityConstant F.val)
  nlinarith
end LooseHamilton
