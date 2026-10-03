module

public import HittingTimeLooseHamilton.FrameSurvivalCounting

public section

noncomputable section
namespace LooseHamilton.FrameSurvival
open Finset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

abbrev CandidateBatch (H : Finset α) (τ : ℕ) (e : α) :=
  {T : HostBatch H τ // e ∈ T.val}

/-- Removing the distinguished deleted edge is a bijection onto smaller batches. -/
@[expose] def candidateBatchEquiv {H : Finset α} {τ : ℕ} {e : α}
    (he : e ∈ H) (hτ : 1 ≤ τ) :
    CandidateBatch H τ e ≃ HostBatch (H.erase e) (τ-1) where
  toFun T := ⟨T.val.val.erase e, mem_powersetCard.mpr ⟨erase_subset_erase e
    (mem_powersetCard.mp T.val.property).1, by
      rw [card_erase_of_mem T.property, (mem_powersetCard.mp T.val.property).2]⟩⟩
  invFun T := ⟨⟨insert e T.val, mem_powersetCard.mpr ⟨insert_subset he
    ((mem_powersetCard.mp T.property).1.trans (erase_subset _ _)), by
      rw [card_insert_of_notMem (fun h => (mem_erase.mp
        ((mem_powersetCard.mp T.property).1 h)).1 rfl),
        (mem_powersetCard.mp T.property).2]
      omega⟩⟩, mem_insert_self _ _⟩
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    exact insert_erase T.property
  right_inv T := by
    apply Subtype.ext
    exact erase_insert (fun h => (mem_erase.mp
      ((mem_powersetCard.mp T.property).1 h)).1 rfl)

/-- This is exactly conditioning a uniform batch on containing the candidate. -/
theorem candidate_conditioning {H : Finset α} {τ : ℕ} {e : α}
    (he : e ∈ H) (hτ : 1 ≤ τ) (hτH : τ ≤ H.card)
    (P : Finset α → Prop) :
    (hostBatchLaw hτH).event (fun T => e ∈ T.val ∧ P T.val) =
      (hostBatchLaw hτH).event (fun T => e ∈ T.val) *
        (hostBatchLaw (show τ-1 ≤ (H.erase e).card by
          rw [card_erase_of_mem he]; omega)).event (fun T => P (insert e T.val)) := by
  classical
  letI := hostBatch_nonempty hτH
  have hsmall : τ-1 ≤ (H.erase e).card := by rw [card_erase_of_mem he]; omega
  letI := hostBatch_nonempty hsmall
  let E := candidateBatchEquiv he hτ
  letI : Nonempty (CandidateBatch H τ e) := ⟨E.symm (Classical.choice (hostBatch_nonempty hsmall))⟩
  have hc := FiniteEntropy.Law.uniform_subtype_conditioning
    (fun T : HostBatch H τ => e ∈ T.val) (fun T => P T.val)
  have hu := FiniteEntropy.Law.uniform_event_equiv E
    (fun T => P (insert e T.val))
  have hback (T : CandidateBatch H τ e) : insert e (E T).val = T.val.val :=
    insert_erase T.property
  simp_rw [hback] at hu
  exact hc.trans (congrArg (fun x =>
    (hostBatchLaw hτH).event (fun T => e ∈ T.val) * x) hu)

lemma survivorCount_insert {F : Finset (Finset α)} {e : α} (T : Finset α)
    (he : ∀ A ∈ F, e ∉ A) :
    survivorCount F (insert e T) = survivorCount F T := by
  unfold survivorCount
  congr 1
  apply filter_congr
  intro A hA
  simp [disjoint_insert_left, he A hA]

/-- The conditional deletion experiment chooses the remaining batch uniformly
from the host with the distinguished edge removed. -/
theorem conditional_survival_mean {H : Finset α} {q τ : ℕ} {e : α}
    (he : e ∈ H) (hτ : 1 ≤ τ) (hτH : τ ≤ H.card)
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A ⊆ H ∧ A.card = q)
    (havoid : ∀ A ∈ F, e ∉ A) :
    (∑ T, (hostBatchLaw (show τ-1 ≤ (H.erase e).card by
        rw [card_erase_of_mem he]; omega)).mass T *
        (survivorCount F (insert e T.val) : ℝ)) =
      (F.card : ℝ) * (((H.card-1)-q).choose (τ-1) : ℝ) /
        ((H.card-1).choose (τ-1) : ℝ) := by
  simp_rw [survivorCount_insert _ havoid]
  have hsmall : τ-1 ≤ (H.erase e).card := by rw [card_erase_of_mem he]; omega
  have hsub : ∀ A ∈ F, A ⊆ H.erase e ∧ A.card = q := by
    intro A hA
    exact ⟨subset_erase.mpr ⟨(hF A hA).1,havoid A hA⟩,(hF A hA).2⟩
  simpa [card_erase_of_mem he] using host_survival_mean hsmall F hsub

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem completion_conditional_survival_mean {r k τ : ℕ} (hr : 3 ≤ r)
    {markers host : Finset (Finset V)} {P pair : Finset V}
    (h : LegalPrivateCompletion r markers P pair)
    (hN : Fintype.card V = (r-1)*k + markers.card)
    (he : P ∪ pair ∈ host) (hk : 1 ≤ k) (hτ : 1 ≤ τ) (hτH : τ ≤ host.card) :
    (∑ T, (hostBatchLaw (show τ-1 ≤ (host.erase (P ∪ pair)).card by
        rw [card_erase_of_mem he]; omega)).mass T *
      (completionCount r markers (host \ insert (P ∪ pair) T.val) P pair : ℝ)) =
    (completionCount r markers host P pair : ℝ) *
      ((host.card-k).choose (τ-1) : ℝ) / ((host.card-1).choose (τ-1) : ℝ) := by
  simp_rw [completionCount_delete]
  have hF : ∀ E ∈ completionFamily r markers host P pair,
      E ⊆ host ∧ E.card = k-1 := by
    intro E hE
    obtain ⟨hC,hH⟩ := (mem_completionFamily _ _ _ _ _ _).mp hE
    exact ⟨hH,h.completion_edge_card hr hN hC⟩
  have ha : ∀ E ∈ completionFamily r markers host P pair, P ∪ pair ∉ E :=
    fun _ hE => completion_candidate_absent hr h hE
  have hc : host.card-1-(k-1) = host.card-k := by omega
  simpa only [hc, completionCount, cycleOnCount, completionFamily] using conditional_survival_mean he hτ hτH
    (completionFamily r markers host P pair) hF ha
end LooseHamilton.FrameSurvival
