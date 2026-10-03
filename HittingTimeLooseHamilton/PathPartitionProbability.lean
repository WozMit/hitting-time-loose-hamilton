module

public import HittingTimeLooseHamilton.PartitionBiasTransfer
public import HittingTimeLooseHamilton.PartitionSamplingCore

public section

/-! Uniform partition regularity along the actual extension path. -/
noncomputable section
namespace LooseHamilton
open Filter

lemma path_partition_failure_eventually (r : ℕ) (hr : 3 ≤ r)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V=n →
      ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        (hadm : CoreAdmissible r M ell markers B) →
        letI := hadm.feasible
        (extensionLaw r M ell).event (fun ω => ¬ ∀ j, M ≤ j →
          j ≤ (completeEdges V r).card →
          PathPartitionRegular r 2 L (extensionState ω.1 ω.2 j)) ≤
            partitionSamplingError r n := by
  filter_upwards [partition_sampling_tail_eventually r hr B hB,
    completePartitionRatio_bias_eventually hr L hL,eventually_ge_atTop 1] with n hs hb hn
  intro V _ _ hV M ell markers hadm
  letI := hadm.feasible
  apply le_trans _ (hs V hV M ell markers hadm)
  apply FiniteEntropy.Law.event_mono
  intro ω hbad
  by_contra hgood
  apply hbad
  apply path_partitions_of_no_sampling_failure r hr M ell L
    (by omega : 0<Fintype.card V) _ ω
  · simpa only [hV] using hgood
  · simpa only [hV] using hb
end LooseHamilton
