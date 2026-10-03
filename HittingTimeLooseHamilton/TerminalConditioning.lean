module

public import HittingTimeLooseHamilton.TerminalFeasibilityFinite
public import HittingTimeLooseHamilton.DisjointEventSum

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact conditioning identity for the uniform feasible terminal graph. -/
theorem terminal_event_mul_feasibility (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (P : SimpleHypergraph V → Prop) :
    (terminalLaw r M ell).event (fun F => P F.val) *
      terminalFeasibilityProbability r M ell =
    (processLaw V r).event (fun σ =>
      (∀ v, ell v ≤ vertexDegree (processState σ M) v) ∧ P (processState σ M)) := by
  classical
  let T := TerminalState V r M ell
  let c : ℝ := 1 / (((Fintype.card V).choose r).choose M : ℝ)
  have hM : M ≤ (completeEdges V r).card := by
    obtain ⟨F⟩ := ‹Nonempty (TerminalState V r M ell)›
    rw [← F.property.2.1]
    exact card_le_card F.property.1
  have hsum (Q : SimpleHypergraph V → Prop) :
      (processLaw V r).event (fun σ =>
        (∀ v, ell v ≤ vertexDegree (processState σ M) v) ∧ Q (processState σ M)) =
      ∑ F : T, if Q F.val then c else 0 := by
    let E : T → EdgeOrder V r → Prop := fun F σ => Q F.val ∧ processState σ M = F.val
    have he : (fun σ => (∀ v, ell v ≤ vertexDegree (processState σ M) v) ∧ Q (processState σ M)) =
        (fun σ => ∃ F : T, E F σ) := by
      funext σ; apply propext
      constructor
      · rintro ⟨hf,hq⟩
        exact ⟨⟨processState σ M, processState_subset σ M,
          by rw [processState_card,Nat.min_eq_left hM],hf⟩,hq,rfl⟩
      · rintro ⟨F,hq,hs⟩; rw [hs]; exact ⟨F.property.2.2,hq⟩
    rw [he,event_exists_eq_sum (processLaw V r) E (by
      intro σ F G hf hg; exact Subtype.ext (hf.2.symm.trans hg.2))]
    apply sum_congr rfl
    intro F _
    change (processLaw V r).event (fun σ => Q F.val ∧ processState σ M = F.val) = _
    rw [FiniteEntropy.Law.event_const_and]
    have hc : (processLaw V r).event (fun σ => processState σ M = F.val) = c := by
      simpa only [F.property.2.1] using process_prefix_probability F.property.1
    rw [hc]
  have hb : terminalFeasibilityProbability r M ell = (Fintype.card T : ℝ)*c := by
    simpa [terminalFeasibilityProbability] using hsum (fun _ => True)
  rw [hb,hsum]
  change (FiniteEntropy.uniform : FiniteEntropy.Law T).event (fun F => P F.val) * _ = _
  rw [FiniteEntropy.Law.uniform_event]
  have hn : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [div_mul_eq_mul_div]
  rw [show ((#{F : T | P F.val} : ℝ) * ((Fintype.card T : ℝ) * c)) /
      (Fintype.card T : ℝ) = (#{F : T | P F.val} : ℝ)*c by field_simp <;> ring]
  rw [← sum_filter]
  simp

/-- Conditioning costs at most the reciprocal feasibility probability. -/
theorem terminal_event_le_prefix_div (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (P : SimpleHypergraph V → Prop)
    (hb : 0 < terminalFeasibilityProbability r M ell) :
    (terminalLaw r M ell).event (fun F => P F.val) ≤
      (processLaw V r).event (fun σ => P (processState σ M)) /
        terminalFeasibilityProbability r M ell := by
  apply (le_div_iff₀ hb).mpr
  rw [terminal_event_mul_feasibility]
  exact (processLaw V r).event_mono (fun _ h => h.2)
end LooseHamilton
