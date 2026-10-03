module

public import HittingTimeLooseHamilton.FrameSurvivalConditioned
public import HittingTimeLooseHamilton.FrameSurvivalRatios
public import HittingTimeLooseHamilton.AuxiliaryFrameParameters

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
open scoped BigOperators
open LooseHamilton.FrameSurvival
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma rawHost_delete (F : Frame r original) (host T : Finset (Finset V)) :
    F.rawHost (host \ T) = F.rawHost host \ T := by
  ext e
  simp only [rawHost, mem_filter, mem_inter, mem_sdiff]
  tauto

lemma cycleFamily_delete (F : Frame r original) (host T : Finset (Finset V)) :
    F.cycleFamily (host \ T) =
      (F.cycleFamily host).filter (fun E => Disjoint T E) := by
  ext E
  simp only [mem_cycleFamily, rawHost_delete, subset_sdiff, mem_filter]
  constructor
  · rintro ⟨⟨hH,hD⟩,hC⟩
    exact ⟨⟨hH,hC⟩,hD.symm⟩
  · rintro ⟨⟨hH,hC⟩,hD⟩
    exact ⟨⟨hH,hD.symm⟩,hC⟩

lemma completionFamily_delete (F : Frame r original) (host T : Finset (Finset V))
    (c : Finset V × V × V) :
    F.completionFamily (host \ T) c =
      (F.completionFamily host c).filter (fun E => Disjoint T E) := by
  classical
  ext E
  simp only [completionFamily, rawHost_delete, mem_filter, mem_powerset, subset_sdiff]
  constructor
  · rintro ⟨⟨hH,hD⟩,hC⟩
    exact ⟨⟨hH,hC⟩,hD.symm⟩
  · rintro ⟨⟨hH,hC⟩,hD⟩
    exact ⟨⟨hH,hD.symm⟩,hC⟩

lemma candidate_absent (F : Frame r original) (hr : 3 ≤ r)
    {host : Finset (Finset V)} {c : Finset V × V × V}
    (hc : F.LegalCandidate c) {E : Finset (Finset V)}
    (hE : E ∈ F.completionFamily host c) : c.1 ∪ {c.2.1,c.2.2} ∉ E := by
  classical
  obtain ⟨_,C,_⟩ := (mem_filter.mp hE)
  obtain ⟨v,hv⟩ : c.1.Nonempty := card_pos.mp (by rw [hc.1.private_card]; omega)
  intro he
  have hx := C.edge_subset_active he (mem_union_left _ hv)
  exact (mem_sdiff.mp hx).2 hv

lemma cycleCount_delete (F : Frame r original) (host T : Finset (Finset V)) :
    F.cycleCount (host \ T) = survivorCount (F.cycleFamily host) T := by
  unfold cycleCount
  rw [cycleFamily_delete]
  rfl

lemma completionCount_delete (F : Frame r original) (host T : Finset (Finset V))
    (c : Finset V × V × V) :
    F.completionCount (host \ T) c = survivorCount (F.completionFamily host c) T := by
  unfold completionCount
  rw [completionFamily_delete]
  rfl

/-- The simultaneous frame directions are retained in this exact main-family mean. -/
theorem cycle_survival_mean (F : Frame r original) (hr : 3 ≤ r)
    (host : Finset (Finset V)) {τ : ℕ} (hτ : τ ≤ F.m host) :
    (∑ T, (hostBatchLaw hτ).mass T * (F.cycleCount (host \ T.val) : ℝ)) =
      zeta (F.m host) τ F.k * (F.cycleCount host : ℝ) := by
  simp_rw [cycleCount_delete]
  have hF : ∀ E ∈ F.cycleFamily host, E ⊆ F.rawHost host ∧ E.card = F.k := by
    intro E hE
    exact ⟨(F.mem_cycleFamily host E).mp hE |>.1,F.edge_card hr hE⟩
  simpa only [zeta, cycleCount, m, mul_div_assoc, mul_comm] using
    host_survival_mean hτ (F.cycleFamily host) hF

/-- Candidate completions preserve the root, relative, and fresh-pair directions. -/
theorem completion_survival_mean (F : Frame r original) (hr : 3 ≤ r)
    (host : Finset (Finset V)) {c : Finset V × V × V}
    (hNonempty : (F.cycleFamily host).Nonempty) (hc : F.LegalCandidate c)
    {τ : ℕ} (hτ : τ ≤ F.m host) :
    (∑ T, (hostBatchLaw hτ).mass T * (F.completionCount (host \ T.val) c : ℝ)) =
      zeta (F.m host) τ (F.k-1) * (F.completionCount host c : ℝ) := by
  simp_rw [completionCount_delete]
  have hF : ∀ E ∈ F.completionFamily host c,
      E ⊆ F.rawHost host ∧ E.card = F.k-1 := by
    intro E hE
    exact ⟨(F.mem_completionFamily host c E).mp hE |>.1,
      F.completion_edge_card hr hNonempty hc hE⟩
  simpa only [zeta, completionCount, m, mul_div_assoc, mul_comm] using
    host_survival_mean hτ (F.completionFamily host c) hF

/-- The reverse-witness experiment conditions on the candidate being deleted. -/
theorem completion_conditional_survival_mean (F : Frame r original) (hr : 3 ≤ r)
    (host : Finset (Finset V)) {c : Finset V × V × V}
    (hNonempty : (F.cycleFamily host).Nonempty) (hc : F.LegalCandidate c)
    (he : c.1 ∪ {c.2.1,c.2.2} ∈ F.rawHost host)
    {τ : ℕ} (hτ : 1 ≤ τ) (hτH : τ ≤ F.m host) :
    (∑ T, (hostBatchLaw (show τ-1 ≤ ((F.rawHost host).erase
        (c.1 ∪ {c.2.1,c.2.2})).card by
        rw [card_erase_of_mem he]; exact Nat.sub_le_sub_right hτH 1)).mass T *
      (F.completionCount (host \ insert (c.1 ∪ {c.2.1,c.2.2}) T.val) c : ℝ)) =
      conditionedZeta (F.m host) τ F.k * (F.completionCount host c : ℝ) := by
  simp_rw [completionCount_delete]
  have hF : ∀ E ∈ F.completionFamily host c,
      E ⊆ F.rawHost host ∧ E.card = F.k-1 := by
    intro E hE
    exact ⟨(F.mem_completionFamily host c E).mp hE |>.1,
      F.completion_edge_card hr hNonempty hc hE⟩
  have ha : ∀ E ∈ F.completionFamily host c, c.1 ∪ {c.2.1,c.2.2} ∉ E :=
    fun _ hE => F.candidate_absent hr hc hE
  have hk := F.k_pos hr hNonempty
  have hsub : (F.rawHost host).card-1-(F.k-1) = (F.rawHost host).card-F.k := by omega
  simpa only [hsub, conditionedZeta, completionCount, m, mul_div_assoc, mul_comm] using
    conditional_survival_mean he hτ hτH (F.completionFamily host c) hF ha
end LooseHamilton.AuxiliaryFrame.Frame
