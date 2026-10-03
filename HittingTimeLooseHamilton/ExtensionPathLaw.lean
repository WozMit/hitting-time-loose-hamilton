module

public import HittingTimeLooseHamilton.ProcessExtensionPathKernel
public import HittingTimeLooseHamilton.TerminalConditioning

public section

/-! Exact law of the entire conditioned extension path. -/
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem extension_path_event_mul_feasibility (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (P : (ℕ → SimpleHypergraph V) → Prop) :
    (extensionLaw r M ell).event (fun x => P (extensionState x.1 x.2)) *
      terminalFeasibilityProbability r M ell =
    (processLaw V r).event (fun σ =>
      (∀ v,ell v ≤ vertexDegree (processState σ M) v) ∧ P (fun j => processState σ (max M j))) := by
  classical
  let T := TerminalState V r M ell
  let c : ℝ := 1 / (((Fintype.card V).choose r).choose M : ℝ)
  let q (Q : (ℕ → SimpleHypergraph V) → Prop) (F : T) : ℝ :=
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => Q (extensionState F σ))
  have hp (F : T) (Q : (ℕ → SimpleHypergraph V) → Prop) :
      (processLaw V r).event (fun σ => processState σ M = F.val ∧ Q (fun j => processState σ (max M j))) =
      c*q Q F := by
    exact process_extension_path_kernel F Q
  have hsum (Q : (ℕ → SimpleHypergraph V) → Prop) :
      (processLaw V r).event (fun σ =>
        (∀ v,ell v ≤ vertexDegree (processState σ M) v) ∧ Q (fun j => processState σ (max M j))) =
      ∑ F : T, c*q Q F := by
    let E : T → EdgeOrder V r → Prop := fun F σ => processState σ M = F.val ∧ Q (fun j => processState σ (max M j))
    have he : (fun σ => (∀ v,ell v ≤ vertexDegree (processState σ M) v) ∧ Q (fun j => processState σ (max M j))) =
        (fun σ => ∃ F : T, E F σ) := by
      funext σ; apply propext
      constructor
      · rintro ⟨hf,hq⟩
        exact ⟨⟨processState σ M,processState_subset σ M,
          by rw [processState_card,Nat.min_eq_left (terminal_size_le (Classical.choice ‹Nonempty (TerminalState V r M ell)›))],hf⟩,rfl,hq⟩
      · rintro ⟨F,hf,hq⟩; exact ⟨by simpa only [hf] using F.property.2.2,hq⟩
    rw [he,event_exists_eq_sum (processLaw V r) E (by
      intro σ F G hf hg; exact Subtype.ext (hf.1.symm.trans hg.1))]
    exact sum_congr rfl (fun F _ => hp F Q)
  have htrue (F : T) : q (fun _ => True) F = 1 := by
    simp only [q,FiniteEntropy.Law.event,ite_true]
    simpa using (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).total
  have hb : terminalFeasibilityProbability r M ell = (Fintype.card T : ℝ)*c := by
    have ht := hsum (fun _ => True)
    simpa only [and_true,terminalFeasibilityProbability,htrue,mul_one,sum_const,card_univ,
      nsmul_eq_mul] using ht
  have hext : (extensionLaw r M ell).event (fun x => P (extensionState x.1 x.2)) =
      (∑ F : T, q P F) / Fintype.card T := by
    rw [extensionLaw,FiniteEntropy.Law.event_prod_sum]
    change (∑ F : T, ((Fintype.card T : ℝ)⁻¹)*q P F) = _
    rw [← mul_sum]
    ring
  rw [hext,hb,hsum,← mul_sum]
  have hn : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp <;> ring

end LooseHamilton
