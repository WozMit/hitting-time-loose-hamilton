module

public import HittingTimeLooseHamilton.FrameSurvivalAuxiliary
public import HittingTimeLooseHamilton.HostBatchVarianceProbability

public section

/-! A full-host batch is compatible with the exact conditioned-path reverse law.
The counted frame families still obey the original allowed-edge prohibition. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset FrameSurvival
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- The retained current host before the original-port edge prohibition. -/
@[expose] def fullHost (F : Frame r original) (host : Finset (Finset V)) : Finset (Finset V) :=
  host.filter (fun e => e⊆F.active)

lemma rawHost_subset_fullHost (F : Frame r original) (host : Finset (Finset V)) :
    F.rawHost host⊆F.fullHost host := by
  intro e he
  obtain ⟨he,ha⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨(mem_inter.mp he).1,ha⟩

lemma fullHost_delete (F : Frame r original) (host T : Finset (Finset V)) :
    F.fullHost (host\T)=F.fullHost host\T := by
  ext e
  simp only [fullHost,mem_filter,mem_sdiff]
  tauto

/-- The exact survival center for frame cycles under a full-current-host batch. -/
theorem full_cycle_survival_mean (F : Frame r original) (hr : 3≤r)
    (host : Finset (Finset V)) {τ : ℕ} (hτ : τ≤(F.fullHost host).card) :
    (∑T,(hostBatchLaw hτ).mass T*(F.cycleCount (host\T.val):ℝ)) =
      zeta (F.fullHost host).card τ F.k*(F.cycleCount host:ℝ) := by
  simp_rw [F.cycleCount_delete]
  have hf : ∀E∈F.cycleFamily host,E⊆F.fullHost host ∧ E.card=F.k := by
    intro E hE
    exact ⟨((F.mem_cycleFamily host E).mp hE).1.trans (F.rawHost_subset_fullHost host),F.edge_card hr hE⟩
  simpa only [zeta,cycleCount,mul_div_assoc,mul_comm] using
    host_survival_mean hτ (F.cycleFamily host) hf

/-- The completion family uses k−1 edges even when some sampled edges are forbidden. -/
theorem full_completion_survival_mean (F : Frame r original) (hr : 3≤r)
    (host : Finset (Finset V)) (hX : (F.cycleFamily host).Nonempty)
    {c : Finset V×V×V} (hc : F.LegalCandidate c) {τ : ℕ}
    (hτ : τ≤(F.fullHost host).card) :
    (∑T,(hostBatchLaw hτ).mass T*(F.completionCount (host\T.val) c:ℝ)) =
      zeta (F.fullHost host).card τ (F.k-1)*(F.completionCount host c:ℝ) := by
  simp_rw [F.completionCount_delete]
  have hf : ∀E∈F.completionFamily host c,E⊆F.fullHost host ∧ E.card=F.k-1 := by
    intro E hE
    exact ⟨((F.mem_completionFamily host c E).mp hE).1.trans (F.rawHost_subset_fullHost host),
      F.completion_edge_card hr hX hc hE⟩
  simpa only [zeta,completionCount,mul_div_assoc,mul_comm] using
    host_survival_mean hτ (F.completionFamily host c) hf

/-- Conditional completion survival retains the known-deleted-candidate correction. -/
theorem full_completion_conditional_mean (F : Frame r original) (hr : 3≤r)
    (host : Finset (Finset V)) (hX : (F.cycleFamily host).Nonempty)
    {c : Finset V×V×V} (hc : F.LegalCandidate c)
    (he : c.1∪{c.2.1,c.2.2}∈F.fullHost host) {τ : ℕ}
    (hτ : 1≤τ) (ht : τ≤(F.fullHost host).card) :
    (∑T,(hostBatchLaw (show τ-1≤((F.fullHost host).erase
      (c.1∪{c.2.1,c.2.2})).card by rw [card_erase_of_mem he];omega)).mass T *
      (F.completionCount (host\insert (c.1∪{c.2.1,c.2.2}) T.val) c:ℝ)) =
      conditionedZeta (F.fullHost host).card τ F.k*(F.completionCount host c:ℝ) := by
  simp_rw [F.completionCount_delete]
  have hf : ∀E∈F.completionFamily host c,E⊆F.fullHost host ∧ E.card=F.k-1 := by
    intro E hE
    exact ⟨((F.mem_completionFamily host c E).mp hE).1.trans (F.rawHost_subset_fullHost host),
      F.completion_edge_card hr hX hc hE⟩
  have ha : ∀E∈F.completionFamily host c,c.1∪{c.2.1,c.2.2}∉E := fun _ hE =>F.candidate_absent hr hc hE
  have hk := F.k_pos hr hX
  have hs : (F.fullHost host).card-1-(F.k-1)=(F.fullHost host).card-F.k := by omega
  simpa only [hs,conditionedZeta,completionCount,mul_div_assoc,mul_comm] using
    conditional_survival_mean he hτ ht (F.completionFamily host c) hf ha
end LooseHamilton.AuxiliaryFrame.Frame
