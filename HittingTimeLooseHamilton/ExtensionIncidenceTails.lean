module

public import HittingTimeLooseHamilton.ExtensionSupportTails
public import HittingTimeLooseHamilton.HypergraphDegreeBounds

public section

/-! Degree and codegree conditional tails at a fixed extension time. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ}

lemma missingSupport_card (F : TerminalState V r M ell) (P : Finset V → Prop) [DecidablePred P] :
    (missingSupport F P).card = ((completeEdges V r).filter P).card-(F.val.filter P).card := by
  have he : (missingSupport F P).image Subtype.val =
      (completeEdges V r).filter P \ F.val.filter P := by
    ext e
    simp only [mem_image,missingSupport,mem_filter,mem_univ,true_and,mem_sdiff]
    constructor
    · rintro ⟨x,hp,rfl⟩
      exact ⟨⟨(mem_sdiff.mp x.property).1,hp⟩,fun h => (mem_sdiff.mp x.property).2 h.1⟩
    · rintro ⟨⟨he,hp⟩,hf⟩
      exact ⟨⟨e,mem_sdiff.mpr ⟨he,fun hf' => hf ⟨hf',hp⟩⟩⟩,hp,rfl⟩
  have hc := congrArg Finset.card he
  rw [card_image_of_injective _ Subtype.val_injective,card_sdiff_of_subset] at hc
  · exact hc
  · exact filter_subset_filter _ F.property.1

lemma missing_vertex_support_card (F : TerminalState V r M ell) (hr : 1 ≤ r) (v : V) :
    (missingSupport F (fun e => v∈e)).card =
      (Fintype.card V-1).choose (r-1)-vertexDegree F.val v := by
  rw [missingSupport_card,incidentSupport_card hr]
  rfl

lemma missing_pair_support_card (F : TerminalState V r M ell) (hr : 2 ≤ r)
    {u v : V} (huv : u≠v) :
    (missingSupport F (fun e => u∈e ∧ v∈e)).card =
      (Fintype.card V-2).choose (r-2)-pairDegree F.val u v := by
  rw [missingSupport_card,pairSupport_card hr huv]
  rfl

lemma extension_vertex_upper_tail (F : TerminalState V r M ell) (hr : 1 ≤ r)
    (j k : ℕ) (hj : j ≤ (completeEdges V r).card) (hN : M < (completeEdges V r).card)
    (v : V) (t : ℝ) (ht : 0<t) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => vertexDegree F.val v+k ≤ vertexDegree (extensionState F σ j) v) ≤
      Real.exp (t*((Fintype.card V-1).choose (r-1)-vertexDegree F.val v:ℕ)*(j-M:ℕ)/
        ((completeEdges V r).card-M:ℕ))/t^k := by
  have he (σ : MissingOrder V r M) : vertexDegree (extensionState F σ j) v =
      vertexDegree F.val v+
        (missingSupport F (fun e => v∈e) ∩ missingPrefix F σ (j-M)).card :=
    extension_filter_card F σ j (fun e => v∈e)
  simp_rw [he,Nat.add_le_add_iff_left]
  have h := missing_support_upper_exp F (j-M) k (Nat.sub_le_sub_right hj M) hN
    (missingSupport F (fun e => v∈e)) t ht
  simpa only [missing_vertex_support_card F hr v] using h

lemma extension_pair_upper_tail (F : TerminalState V r M ell) (hr : 2 ≤ r)
    (j k : ℕ) (hj : j ≤ (completeEdges V r).card) (hN : M < (completeEdges V r).card)
    {u v : V} (huv : u≠v) (t : ℝ) (ht : 0<t) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => pairDegree F.val u v+k ≤ pairDegree (extensionState F σ j) u v) ≤
      Real.exp (t*((Fintype.card V-2).choose (r-2)-pairDegree F.val u v:ℕ)*(j-M:ℕ)/
        ((completeEdges V r).card-M:ℕ))/t^k := by
  have he (σ : MissingOrder V r M) : pairDegree (extensionState F σ j) u v =
      pairDegree F.val u v+
        (missingSupport F (fun e => u∈e ∧ v∈e) ∩ missingPrefix F σ (j-M)).card :=
    extension_filter_card F σ j (fun e => u∈e ∧ v∈e)
  simp_rw [he,Nat.add_le_add_iff_left]
  have h := missing_support_upper_exp F (j-M) k (Nat.sub_le_sub_right hj M) hN
    (missingSupport F (fun e => u∈e ∧ v∈e)) t ht
  simpa only [missing_pair_support_card F hr huv] using h

lemma extension_vertex_lower_tail (F : TerminalState V r M ell) (hr : 1 ≤ r)
    (j k : ℕ) (hj : j ≤ (completeEdges V r).card) (hN : M < (completeEdges V r).card)
    (v : V) (q : ℝ) (hq : 0<q) (hq1 : q≤1) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => vertexDegree (extensionState F σ j) v ≤ k) ≤
      Real.exp (-((j-M:ℕ):ℝ)/((completeEdges V r).card-M:ℕ)*
        ((Fintype.card V-1).choose (r-1)-vertexDegree F.val v:ℕ)*(1-q)-(k:ℝ)*Real.log q) := by
  have hmono : (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => vertexDegree (extensionState F σ j) v ≤ k) ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => (missingPrefix F σ (j-M) ∩ missingSupport F (fun e => v∈e)).card ≤ k) := by
    apply FiniteEntropy.Law.event_mono
    intro σ hσ
    have he := extension_filter_card F σ j (fun e => v∈e)
    change vertexDegree (extensionState F σ j) v = _ at he
    rw [inter_comm] at he
    omega
  have h := missing_support_lower_exp F (j-M) k (Nat.sub_le_sub_right hj M) hN
    (missingSupport F (fun e => v∈e)) q hq hq1
  exact hmono.trans (by simpa only [missing_vertex_support_card F hr v] using h)
end LooseHamilton
