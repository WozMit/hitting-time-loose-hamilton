module

public import HittingTimeLooseHamilton.TerminalRegularityModels
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

/-! Finite union-bound assembly of the four terminal regularity conditions. -/
noncomputable section
namespace LooseHamilton
open scoped BigOperators
open Finset
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

/-- Pair and star failures only need estimating on controlled degree sequences. -/
theorem terminal_regular_failure_le (p : FiniteEntropy.Law Ω)
    (F : Ω → SimpleHypergraph V) (C : ℝ) :
    1-p.event (fun ω => TerminalRegular C (F ω)) ≤
      p.event (fun ω => ∃ v, C*Real.log (Fintype.card V:ℝ) < (vertexDegree (F ω) v:ℝ)) +
      p.event (fun ω => (Fintype.card V:ℝ)^(1/4:ℝ) < ((terminalLowVertices (F ω)).card:ℝ)) +
      p.event (fun ω => TerminalDegreeControls C (vertexDegree (F ω)) ∧
        ∃ u v, u ≠ v ∧ 3 ≤ pairDegree (F ω) u v) +
      p.event (fun ω => TerminalDegreeControls C (vertexDegree (F ω)) ∧
        ∃ y, 2 ≤ associationStatistic (F ω) y ((terminalLowVertices (F ω)).erase y)) := by
  classical
  let E : Fin 4 → Ω → Prop := ![
    (fun ω => ∃ v, C*Real.log (Fintype.card V:ℝ) < (vertexDegree (F ω) v:ℝ)),
    (fun ω => (Fintype.card V:ℝ)^(1/4:ℝ) < ((terminalLowVertices (F ω)).card:ℝ)),
    (fun ω => TerminalDegreeControls C (vertexDegree (F ω)) ∧
      ∃ u v, u ≠ v ∧ 3 ≤ pairDegree (F ω) u v),
    (fun ω => TerminalDegreeControls C (vertexDegree (F ω)) ∧
      ∃ y, 2 ≤ associationStatistic (F ω) y ((terminalLowVertices (F ω)).erase y))]
  rw [← p.event_compl]
  calc
    _ ≤ p.event (fun ω => ∃ i, E i ω) := p.event_mono (by
      intro ω hnot
      by_cases hm : ∀ v, (vertexDegree (F ω) v:ℝ) ≤ C*Real.log (Fintype.card V:ℝ)
      · by_cases hl : ((terminalLowVertices (F ω)).card:ℝ) ≤ (Fintype.card V:ℝ)^(1/4:ℝ)
        · have hg : TerminalDegreeControls C (vertexDegree (F ω)) := ⟨hm,hl⟩
          by_cases hp : ∀ u v, u ≠ v → pairDegree (F ω) u v ≤ 2
          · have hs : ∃ y, 2 ≤ associationStatistic (F ω) y ((terminalLowVertices (F ω)).erase y) := by
              by_contra hn
              apply hnot
              refine ⟨hm,hl,hp,?_⟩
              intro y
              have hh : ¬ 2 ≤ associationStatistic (F ω) y ((terminalLowVertices (F ω)).erase y) :=
                fun hy => hn ⟨y,hy⟩
              omega
            exact ⟨3,hg,hs⟩
          · push_neg at hp
            obtain ⟨u,v,huv,hpair⟩ := hp
            exact ⟨2,hg,u,v,huv,by omega⟩
        · exact ⟨1,lt_of_not_ge hl⟩
      · push_neg at hm
        exact ⟨0,hm⟩)
    _ ≤ ∑ i, p.event (E i) := p.finite_union_bound E
    _ = _ := by simp [E,Fin.sum_univ_succ]; ring
end LooseHamilton
