module

public import HittingTimeLooseHamilton.PathIncidenceProbability
public import HittingTimeLooseHamilton.PathPartitionProbability
public import HittingTimeLooseHamilton.PathRegularityMonotone

public section

/-! Assemble the incidence and partition bounds under the genuine law Q. -/
noncomputable section
namespace LooseHamilton
open Filter

@[expose] def pathRegularityConstant (r : ℕ) : ℝ := pathDegreeUpperFactor r terminalRegularityConstant

lemma pathRegularityConstant_ge_four (r : ℕ) : 4 ≤ pathRegularityConstant r := by
  unfold pathRegularityConstant pathDegreeUpperFactor
  nlinarith [terminalRegularityConstant_pos, Nat.cast_nonneg (α:=ℝ) r]

lemma pathRegularityConstant_pos (r : ℕ) : 0 < pathRegularityConstant r :=
  lt_of_lt_of_le (by norm_num) (pathRegularityConstant_ge_four r)

lemma path_regular_of_incidence_partition {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {L : ℝ} {F : SimpleHypergraph V}
    (hi : PathIncidenceRegular r (pathDegreeLowerFactor r) (pathRegularityConstant r) 4 F)
    (hp : PathPartitionRegular r 2 L F) :
    PathGraphRegular r (pathDegreeLowerFactor r) (pathRegularityConstant r) L F := by
  have hC := pathRegularityConstant_ge_four r
  have hμ : 0 ≤ meanDegree (V:=V) r F.card := by unfold meanDegree; positivity
  have hl : 0 ≤ (Real.log (Fintype.card V:ℝ))^(-1/4:ℝ) :=
    Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  refine { upper_degree := hi.upper_degree
           lower_degree := hi.lower_degree
           partitions := hp.mono (by linarith) le_rfl
           codegree := ?_ }
  intro u v huv
  exact (hi.codegree u v huv).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hμ) hl)

@[expose] def pathRegularityError (r n : ℕ) : ℝ := pathIncidenceError r n + partitionSamplingError r n

lemma pathRegularityError_tendsto {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (pathRegularityError r) atTop (nhds 0) := by
  have h := (pathIncidenceError_tendsto r).add (partitionSamplingError_tendsto (by omega : 1≤r))
  simp only [add_zero] at h
  exact h

lemma path_regular_failure_eventually (r : ℕ) (hr : 3 ≤ r)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V=n →
      ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        (hadm : CoreAdmissible r M ell markers B) →
        letI := hadm.feasible
        1-(extensionLaw r M ell).event
          (PathRegularityEvent r M ell (pathDegreeLowerFactor r) (pathRegularityConstant r) L) ≤
            pathRegularityError r n := by
  classical
  filter_upwards [path_incidence_failure_eventually r hr B hB,
    path_partition_failure_eventually r hr B L hB hL] with n hi hp
  intro V _ _ hV M ell markers hadm
  letI := hadm.feasible
  let I := fun ω : TerminalState V r M ell × MissingOrder V r M =>
    ∃ j, M ≤ j ∧ j ≤ (completeEdges V r).card ∧
      ¬PathIncidenceRegular r (pathDegreeLowerFactor r) (pathRegularityConstant r) 4
        (extensionState ω.1 ω.2 j)
  let P := fun ω : TerminalState V r M ell × MissingOrder V r M =>
    ¬ ∀ j, M ≤ j → j ≤ (completeEdges V r).card →
      PathPartitionRegular r 2 L (extensionState ω.1 ω.2 j)
  let E : Bool → (TerminalState V r M ell × MissingOrder V r M) → Prop :=
    fun b => if b then I else P
  have hmono : (extensionLaw r M ell).event
      (fun ω => ¬PathRegularityEvent r M ell (pathDegreeLowerFactor r) (pathRegularityConstant r) L ω) ≤
      (extensionLaw r M ell).event (fun ω => ∃ b, E b ω) := by
    apply FiniteEntropy.Law.event_mono
    intro ω hbad
    by_cases hI : I ω
    · exact ⟨true,hI⟩
    by_cases hP : P ω
    · exact ⟨false,hP⟩
    exfalso
    apply hbad
    intro j hj hjK
    exact path_regular_of_incidence_partition
      (not_not.mp (fun hf => hI ⟨j,hj,hjK,hf⟩)) (not_not.mp hP j hj hjK)
  have hu := (extensionLaw r M ell).finite_union_bound E
  have hs : (∑ b : Bool, (extensionLaw r M ell).event (E b)) =
      (extensionLaw r M ell).event I + (extensionLaw r M ell).event P := by
    simp [E,add_comm]
  rw [hs] at hu
  rw [← FiniteEntropy.Law.event_compl]
  exact (hmono.trans hu).trans (add_le_add (hi V hV M ell markers hadm) (hp V hV M ell markers hadm))
end LooseHamilton
