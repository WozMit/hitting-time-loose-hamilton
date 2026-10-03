module

public import HittingTimeLooseHamilton.ExtensionPartitionSampling
public import HittingTimeLooseHamilton.PartitionConcentrationScales
public import HittingTimeLooseHamilton.TerminalFeasibility

public section

/-! The uniform, vanishing partition sampling error under the conditioned core setup. -/
noncomputable section
namespace LooseHamilton
open Filter Topology

@[expose] def partitionSamplingError (r n : ℕ) : ℝ :=
  4*partitionUnionError r (1/(8*(r:ℝ))) n

lemma partitionSamplingError_tendsto {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (partitionSamplingError r) atTop (𝓝 0) := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  unfold partitionSamplingError
  simpa only [mul_zero] using
    (partitionUnionError_tendsto r (c:=1/(8*(r:ℝ))) (by positivity)).const_mul 4

lemma partition_sampling_tail_eventually (r : ℕ) (hr : 3 ≤ r) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V=n →
      ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        (hadm : CoreAdmissible r M ell markers B) →
        letI := hadm.feasible
        (extensionLaw r M ell).event (fun ω => PartitionSamplingFailure r M
          ((Real.log n)^(-1/8:ℝ)) (extensionState ω.1 ω.2)) ≤ partitionSamplingError r n := by
  obtain ⟨N₀,hN₀⟩ := terminal_feasibility_core r hr B hB
  filter_upwards [eventually_ge_atTop N₀,eventually_feasibility_parameters 0,
    partition_concentration_prefactor_eventually (show 1 ≤ r by omega)] with n hn hp hs
  intro V _ _ hV M ell markers hadm
  letI := hadm.feasible
  have hd : |(r:ℝ)*M/n-Real.log n| ≤ 3*Real.log (Real.log n) := by
    simpa [meanDegree,hV] using hadm.density_window
  have hμ := hp.2.1 ((r:ℝ)*M/n) hd
  have hl : 0<Real.log (n:ℝ) := by linarith [hp.1]
  have hM : 0<M := by
    by_contra hh
    have hzero : M=0 := by omega
    rw [hzero,Nat.cast_zero,mul_zero,zero_div] at hμ
    nlinarith
  have hδ : 0<(Real.log n)^(-1/8:ℝ) := Real.rpow_pos_of_pos hl _
  have hb := hN₀ V (by omega) M ell markers hadm
  have hf := extension_partition_sampling_beta_bound r M ell hM _ hδ hb
  apply hf.trans
  have hh := hs M hd
  rw [Real.exp_add] at hh
  simpa only [hV,completeEdges_card,mul_assoc,partitionSamplingError] using hh
end LooseHamilton
