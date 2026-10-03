module

public import HittingTimeLooseHamilton.BatchSelectionUniform
public import HittingTimeLooseHamilton.UniformOrderSupportTails

public section

/-! Hypergeometric incidence tails for a uniform batch from an arbitrary fixed host. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [DecidableEq V]

lemma batch_support_upper_tail (H : SimpleHypergraph V) (m : ℕ) (hH : H.card=m)
    (τ : ℕ) (hτ : τ ≤ m) (hm : 0 < m)
    (D : SimpleHypergraph V) (hD : D ⊆ H) (k : ℕ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event
      (fun σ => k ≤ (D ∩ batchSelection H m hH τ σ).card) ≤
        (D.card.choose k:ℝ)*((τ:ℝ)/m)^k := by
  classical
  let S : Finset ↥H := univ.filter (fun e => e.val∈D)
  have himage : S.image Subtype.val=D := by
    ext e
    simp only [S,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro he
      exact ⟨⟨e,hD he⟩,he,rfl⟩
  have hSc : S.card=D.card := by rw [←card_image_of_injective _ Subtype.val_injective,himage]
  have hcard (σ : BatchOrder m) :
      (D ∩ batchSelection H m hH τ σ).card =
        (S ∩ orderPrefix (batchOrderEquiv H m hH σ) τ).card := by
    have heq : (S ∩ orderPrefix (batchOrderEquiv H m hH σ) τ).image Subtype.val =
        D ∩ batchSelection H m hH τ σ := by
      rw [image_inter _ _ Subtype.val_injective,himage]
      rfl
    rw [←heq,card_image_of_injective _ Subtype.val_injective]
  simp_rw [hcard]
  rw [FiniteEntropy.Law.uniform_event_equiv (batchOrderEquiv H m hH)
    (fun ρ => k ≤ (S ∩ orderPrefix ρ τ).card)]
  have hh := order_support_upper_tail τ k (by simpa [hH] using hτ)
    (by simpa [hH] using hm) S
  simpa only [Fintype.card_coe,hH,hSc] using hh

lemma batch_vertex_loss_upper_tail (H F : SimpleHypergraph V) (m : ℕ) (hH : H.card=m)
    (τ : ℕ) (hτ : τ ≤ m) (hm : 0 < m) (hFH : F ⊆ H) (v : V) (k : ℕ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event
      (fun σ => k ≤ vertexDegree (F ∩ batchSelection H m hH τ σ) v) ≤
        ((vertexDegree F v).choose k:ℝ)*((τ:ℝ)/m)^k := by
  have htail := batch_support_upper_tail H m hH τ hτ hm
    (F.filter (fun e => v∈e)) ((filter_subset _ _).trans hFH) k
  have heq (T : SimpleHypergraph V) : (F.filter (fun e => v∈e)) ∩ T =
      (F ∩ T).filter (fun e => v∈e) := by ext e; simp; tauto
  simpa only [heq,vertexDegree] using htail
end LooseHamilton
