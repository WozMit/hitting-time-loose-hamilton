module

public import HittingTimeLooseHamilton.BatchVarianceCounting
public import HittingTimeLooseHamilton.CompletionParameters

public section

noncomputable section
namespace LooseHamilton.FrameSurvival
open Finset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

abbrev HostBatch (H : Finset α) (τ : ℕ) := ↥(H.powersetCard τ)

omit [DecidableEq α] in
lemma hostBatch_nonempty {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card) :
    Nonempty (HostBatch H τ) := by
  apply Fintype.card_pos_iff.mp
  simpa [HostBatch] using Nat.choose_pos hτ

@[expose] def hostBatchLaw {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card) :
    FiniteEntropy.Law (HostBatch H τ) :=
  @FiniteEntropy.uniform _ inferInstance (hostBatch_nonempty hτ)

lemma host_avoidance_probability {H : Finset α} {τ : ℕ} (hτ : τ ≤ H.card)
    (A : Finset α) (hA : A ⊆ H) :
    (hostBatchLaw hτ).event (fun T => Disjoint T.val A) =
      ((H.card - A.card).choose τ : ℝ) / (H.card.choose τ : ℝ) := by
  classical
  letI := hostBatch_nonempty hτ
  change (FiniteEntropy.uniform : FiniteEntropy.Law (HostBatch H τ)).event _ = _
  rw [FiniteEntropy.Law.uniform_event, ← Fintype.card_subtype]
  have hc : Fintype.card {T : HostBatch H τ // Disjoint T.val A} =
      ((H \ A).powersetCard τ).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    refine ⟨(fun T => ⟨T.val.val, ?_⟩), (fun T => ⟨⟨T.val, ?_⟩, ?_⟩),
      (fun T => rfl), (fun T => rfl)⟩
    · rcases mem_powersetCard.mp T.val.property with ⟨hs,hc⟩
      exact mem_powersetCard.mpr ⟨subset_sdiff.mpr ⟨hs,T.property⟩,hc⟩
    · rcases mem_powersetCard.mp T.property with ⟨hs,hc⟩
      exact mem_powersetCard.mpr ⟨hs.trans sdiff_subset,hc⟩
    · exact (subset_sdiff.mp (mem_powersetCard.mp T.property).1).2
  rw [hc]
  simp [HostBatch, card_powersetCard, card_sdiff_of_subset hA]

@[expose] def survivorCount (F : Finset (Finset α)) (T : Finset α) : ℕ :=
  (F.filter fun A => Disjoint T A).card

theorem host_survival_mean {H : Finset α} {q τ : ℕ} (hτ : τ ≤ H.card)
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A ⊆ H ∧ A.card = q) :
    (∑ T, (hostBatchLaw hτ).mass T * (survivorCount F T.val : ℝ)) =
      (F.card : ℝ) * ((H.card-q).choose τ : ℝ) / (H.card.choose τ : ℝ) := by
  classical
  have hs (T : HostBatch H τ) : (survivorCount F T.val : ℝ) =
      ∑ A ∈ F, if Disjoint T.val A then (1:ℝ) else 0 := by
    simp [survivorCount, ← sum_filter]
  simp_rw [hs, mul_sum]
  rw [sum_comm]
  have he (A : Finset α) :
      (∑ T, (hostBatchLaw hτ).mass T * (if Disjoint T.val A then (1:ℝ) else 0)) =
        (hostBatchLaw hτ).event (fun T => Disjoint T.val A) := by
    unfold FiniteEntropy.Law.event
    apply sum_congr rfl
    intro T _
    split_ifs <;> simp
  simp_rw [he]
  calc
    _ = ∑ _A ∈ F, ((H.card-q).choose τ : ℝ) / (H.card.choose τ : ℝ) := by
      apply sum_congr rfl
      intro A hA
      rw [host_avoidance_probability hτ A (hF A hA).1, (hF A hA).2]
    _ = _ := by simp [mul_div_assoc]

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma completion_candidate_absent {r : ℕ} {markers host : Finset (Finset V)}
    {P pair : Finset V} (hr : 3 ≤ r)
    (h : LegalPrivateCompletion r markers P pair)
    {E : Finset (Finset V)} (hE : E ∈ completionFamily r markers host P pair) :
    P ∪ pair ∉ E := by
  obtain ⟨C⟩ := (mem_completionFamily _ _ _ _ _ _).mp hE |>.1
  obtain ⟨v,hv⟩ : P.Nonempty := card_pos.mp (by rw [h.private_card]; omega)
  intro he
  have hx := C.edge_subset_active he (mem_union_left pair hv)
  exact (mem_sdiff.mp hx).2 hv

lemma completionFamily_delete (r : ℕ) (markers host : Finset (Finset V))
    (P pair : Finset V) (T : Finset (Finset V)) :
    completionFamily r markers (host \ T) P pair =
      (completionFamily r markers host P pair).filter (fun E => Disjoint T E) := by
  ext E
  simp only [mem_completionFamily, mem_filter, subset_sdiff]
  constructor
  · rintro ⟨hC,hH,hD⟩
    exact ⟨⟨hC,hH⟩,hD.symm⟩
  · rintro ⟨⟨hC,hH⟩,hD⟩
    exact ⟨hC,hH,hD.symm⟩

lemma completionCount_delete (r : ℕ) (markers host : Finset (Finset V))
    (P pair : Finset V) (T : Finset (Finset V)) :
    completionCount r markers (host \ T) P pair =
      survivorCount (completionFamily r markers host P pair) T := by
  change (completionFamily r markers (host \ T) P pair).card = _
  rw [completionFamily_delete]
  rfl

theorem completion_survival_mean {r k τ : ℕ} (hr : 3 ≤ r)
    {markers host : Finset (Finset V)} {P pair : Finset V}
    (h : LegalPrivateCompletion r markers P pair)
    (hN : Fintype.card V = (r-1)*k + markers.card) (hτ : τ ≤ host.card) :
    (∑ T, (hostBatchLaw hτ).mass T *
      (completionCount r markers (host \ T.val) P pair : ℝ)) =
    (completionCount r markers host P pair : ℝ) *
      ((host.card-(k-1)).choose τ : ℝ) / (host.card.choose τ : ℝ) := by
  simp_rw [completionCount_delete]
  apply host_survival_mean
  intro E hE
  obtain ⟨hC,hH⟩ := (mem_completionFamily _ _ _ _ _ _).mp hE
  exact ⟨hH,h.completion_edge_card hr hN hC⟩
end LooseHamilton.FrameSurvival
