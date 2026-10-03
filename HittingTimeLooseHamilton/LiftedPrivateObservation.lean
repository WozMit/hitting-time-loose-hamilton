module

public import HittingTimeLooseHamilton.LiftedPrivateMobility
public import HittingTimeLooseHamilton.BootstrapSamplingGates

public section

/-! Lifted private tests use the observed root-free hosts for density, but
mobility counts the full current host. These predicates agree exactly. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lifted_private_observation (r h time : ℕ) (D : Finset V)
    (markers : SimpleHypergraph ↥(univ \ D)) (F H : SimpleHypergraph V)
    (S q U : Finset ↥(univ \ D)) (x t : ↥(univ \ D)) (c : ℝ) :
    (((registerPrivateRootTest r h time markers S q U x t c).liftDeleted D).badSet
      (rootFreeEdges x.val F, rootFreeEdges x.val H)) =
    (((registerPrivateRootTest r h time markers S q U x t c).liftDeleted D).badSet (F,H)) := by
  have ho := registerPrivateRootTest_observation r h time markers
    (inducedHost (univ \ D) F) (inducedHost (univ \ D) H) S q U x t c
  simp only [RegisteredRootTest.liftDeleted, inducedHost_rootFree_commute, ho]

theorem private_fixed_factor_of_lifted_failure_nonoccurrence
    {r h M : ℕ} {ell : V → ℕ} (time : ℕ) (D : Finset V)
    (markers : SimpleHypergraph ↥(univ \ D))
    (S q U : Finset ↥(univ \ D)) (x t : ↥(univ \ D)) (c cRoot : ℝ)
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (hr : 3 ≤ r)
    (hpass : ¬ ((registerPrivateRootTest r h time markers S q U x t
      (BootstrapConstants.rootThreshold r)).liftDeleted D).failure M ell cRoot ω)
    (ht : M ≤ time) (hK : time ≤ (completeEdges V r).card)
    (hdef : (∑ v, rootAdjustedDeficit x.val ell
      (rootFreePairObservation r M ell time x.val ω).1 v) ≤ 1)
    (hdeg : cRoot * FrameScales.L1 (Fintype.card V) ≤
      ((time - (rootFreePairObservation r M ell time x.val ω).2.card : ℕ) : ℝ))
    (hdens : rootLinkDensity r x.val
      (((registerPrivateRootTest r h time markers S q U x t
        (BootstrapConstants.rootThreshold r)).liftDeleted D).badSet
          (rootFreePairObservation r M ell time x.val ω)) ≤ FrameScales.rho (Fintype.card V))
    (hH : (rootSamplingPair r M ell time ω).2 ⊆ completeEdges V r)
    (htarget : LegalPrivateCompletion r markers (insert t S) q)
    (hμ : 0 < privateRootSourceMean r
      (inducedHost (univ \ D) (rootSamplingPair r M ell time ω).2) S x)
    (hratio : c/2 ≤ (vertexDegree (rootSamplingPair r M ell time ω).2 x.val : ℝ) /
      privateRootSourceMean r (inducedHost (univ \ D) (rootSamplingPair r M ell time ω).2) S x) :
    BootstrapConstants.privateFactor r c *
      (completionCount r markers
        (fixedPortHost (inducedHost (univ \ D) (rootSamplingPair r M ell time ω).2) U)
        (insert x S) q : ℝ) ≤
    completionCount r markers
      (fixedPortHost (inducedHost (univ \ D) (rootSamplingPair r M ell time ω).2) U)
      (insert t S) q := by
  have hn := (registerPrivateRootTest r h time markers S q U x t
    (BootstrapConstants.rootThreshold r)).liftDeleted_passes D cRoot ω hpass ht hK
      (by simp [RegisteredRootTest.liftDeleted, registerPrivateRootTest]) hdef hdeg hdens
  have hdegree := BootstrapCatalogue.sampling_degree_eq ω ht hK x.val
  change ¬ RootLinkBad
    (((registerPrivateRootTest r h time markers S q U x t
      (BootstrapConstants.rootThreshold r)).liftDeleted D).badSet
        (rootFreePairObservation r M ell time x.val ω))
    (time - (rootFreePairObservation r M ell time x.val ω).2.card)
    (rootSamplingPair r M ell time ω) at hn
  rw [hdegree] at hn
  have heq : (((registerPrivateRootTest r h time markers S q U x t
      (BootstrapConstants.rootThreshold r)).liftDeleted D).badSet
        (rootFreePairObservation r M ell time x.val ω)) =
      (((registerPrivateRootTest r h time markers S q U x t
      (BootstrapConstants.rootThreshold r)).liftDeleted D).badSet
        (rootSamplingPair r M ell time ω)) := by
    apply lifted_private_observation
  rw [heq] at hn
  exact private_fixed_factor_of_lifted_root_test r h time D markers
    (rootSamplingPair r M ell time ω).1 (rootSamplingPair r M ell time ω).2
    S q U x t c hr hH htarget hμ hratio hn

end LooseHamilton
