module

public import HittingTimeLooseHamilton.FirstFailureCycleFamily
public import HittingTimeLooseHamilton.StoppedCountingStatement
public import HittingTimeLooseHamilton.BenchmarkAlgebra

public section
noncomputable section
namespace LooseHamilton.FirstFailure
open Finset

lemma baseline_eq {N : ℕ} (r k j : ℕ) (markers : SimpleHypergraph (Fin N)) :
    StoppedCounting.baseline (family r markers (originalPorts markers)) k j =
      logarithmicBaseline r k j markers := by
  simp only [StoppedCounting.baseline,familyCount_eq,host_univ,logarithmicBaseline,
    Fintype.card_coe,completeEdges_card,Fintype.card_fin]

lemma full_family_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (markers : SimpleHypergraph V) (ports : Finset V)
    (h : 0 < cycleCount r markers (completeEdges V r) ports) :
    (family r markers ports).Nonempty := by
  have hp := full_count_pos markers ports h
  simpa only [StoppedCounting.familyCount,StoppedCounting.survivingFamily,
    FiniteFamily.count,Finset.filter_true_of_mem (fun _ _ => Finset.subset_univ _),Finset.card_pos] using hp

lemma state_count_eq {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (markers : SimpleHypergraph V) (ports : Finset V)
    (σ : FiniteOrder (Edge V r)) (t : ℕ) :
    StoppedCounting.familyCount (family r markers ports) (StoppedCounting.state σ t) =
      cycleCount r markers (host (orderPrefix σ (Fintype.card (Edge V r)-t))) ports :=
  familyCount_eq markers ports _
end LooseHamilton.FirstFailure
