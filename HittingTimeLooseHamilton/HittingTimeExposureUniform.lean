module

public import HittingTimeLooseHamilton.CoreTerminalUniform
public import HittingTimeLooseHamilton.DisjointEventSum
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! Exact conditional terminal law for arbitrary events of the surviving host.
The conditioning is only the exposed stopped trace. -/
noncomputable section
namespace LooseHamilton.HittingTimeExposure
open Finset

lemma event_eq_uniform_of_atoms {Ω X Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Γ]
    (p : FiniteEntropy.Law Ω) (f : Ω → X) (g : Γ → X) (hg : Function.Injective g)
    (hsupport : ∀ ω, p.mass ω ≠ 0 → ∃ γ, f ω = g γ)
    (hatom : ∀ γ, p.event (fun ω => f ω = g γ) = 1/(Fintype.card Γ : ℝ))
    (P : X → Prop) :
    p.event (fun ω => P (f ω)) =
      (FiniteEntropy.uniform : FiniteEntropy.Law Γ).event (fun γ => P (g γ)) := by
  classical
  have he : p.event (fun ω => P (f ω)) =
      p.event (fun ω => ∃ γ, f ω=g γ ∧ P (g γ)) := by
    unfold FiniteEntropy.Law.event
    apply sum_congr rfl
    intro ω _
    by_cases hm : p.mass ω=0
    · simp [hm]
    · obtain ⟨γ,hγ⟩ := hsupport ω hm
      have hh : P (f ω) ↔ ∃ γ, f ω=g γ ∧ P (g γ) :=
        ⟨fun hp => ⟨γ,hγ,hγ ▸ hp⟩,fun ⟨γ,hγ,hp⟩ => hγ.symm ▸ hp⟩
      by_cases hp : P (f ω)
      · simp [hp,hh.mp hp]
      · have hn : ¬ ∃ γ, f ω=g γ ∧ P (g γ) := fun h => hp (hh.mpr h)
        simp [hp,hn]
  rw [he,event_exists_eq_sum p _ (by intro ω a b ha hb; exact hg (ha.1.symm.trans hb.1))]
  unfold FiniteEntropy.Law.event FiniteEntropy.uniform
  apply sum_congr rfl
  intro γ _
  change p.event (fun ω => f ω=g γ ∧ P (g γ)) = _
  by_cases hp : P (g γ)
  · simp only [hp,and_true,ite_true,hatom,one_div]
  · simp [hp,FiniteEntropy.Law.event]

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Every positive-probability exposed fibre has a nonempty feasible terminal family. -/
theorem terminal_nonempty {r m : ℕ} {B D : Finset V} {T : SimpleHypergraph V}
    (hBD : B ⊆ D)
    (hE : 0 < (processLaw V r).event (coreExposureEvent r m B D T)) :
    Nonempty (TerminalState ↥(univ \ D) r (m-T.card) (fun w => coreLowerBound D T w.val)) := by
  classical
  have hex : ∃ σ, coreExposureEvent r m B D T σ := by
    by_contra hn
    push_neg at hn
    rw [(processLaw V r).event_eq_zero_of_false hn] at hE
    exact (lt_irrefl 0) hE
  obtain ⟨σ,hσ⟩ := hex
  exact ⟨coreCompletionToTerminal r m D T
    ⟨coreOutside D (processState σ m),coreOutside_mem_completion hBD (coreExposureEvent_mem_fiber hσ)⟩⟩

/-- Proposition 3.3's singleton formula extends to every property of the induced core. -/
theorem conditional_host_event {r m : ℕ} {B D : Finset V} {T : SimpleHypergraph V}
    (hbase : 1 ≤ lowerDegreeBase V) (hBD : B ⊆ D)
    (hE : 0 < (processLaw V r).event (coreExposureEvent r m B D T))
    [Nonempty (TerminalState ↥(univ \ D) r (m-T.card) (fun w => coreLowerBound D T w.val))]
    (P : SimpleHypergraph ↥(univ \ D) → Prop) :
    ((processLaw V r).condition (coreExposureEvent r m B D T) hE).event
      (fun σ => P (inducedHost (univ \ D) (processState σ m))) =
      (terminalLaw r (m-T.card) (fun w : ↥(univ \ D) => coreLowerBound D T w.val)).event
        (fun F => P F.val) := by
  classical
  apply event_eq_uniform_of_atoms (Γ := TerminalState ↥(univ \ D) r (m-T.card)
    (fun w => coreLowerBound D T w.val)) _ _ Subtype.val Subtype.val_injective
  · intro σ hσ
    have he : coreExposureEvent r m B D T σ := by
      by_contra hn
      simp [FiniteEntropy.Law.condition,hn] at hσ
    let G := coreCompletionToTerminal r m D T
      ⟨coreOutside D (processState σ m),coreOutside_mem_completion hBD (coreExposureEvent_mem_fiber he)⟩
    refine ⟨G,?_⟩
    exact (restricted_core_eq_inducedHost D (processState σ m)).symm
  · exact fun G => core_induced_uniform_of_feasible hbase hBD hE G

end LooseHamilton.HittingTimeExposure
