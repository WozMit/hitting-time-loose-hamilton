module

public import HittingTimeLooseHamilton.NoDeficitSamplingSupport
public import HittingTimeLooseHamilton.NoDeficitDeterministic

public section

/-! Finite no-deficit sampling bounds, before any regularity or asymptotic specialization. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma noDeficitSampling_union_bound (H F : SimpleHypergraph V) (hFH : F ⊆ H)
    (m : ℕ) (hH : H.card=m) (τ : ℕ) (hτ : τ ≤ m) (hm : 0 < m)
    (B : Finset V) (a dmax : ℕ) (hd : ∀ v, vertexDegree F v ≤ dmax) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event (fun σ =>
      (∃ v ∈ B, 1 ≤ vertexDegree (F ∩ batchSelection H m hH τ σ) v) ∨
        (∃ v, a ≤ vertexDegree (F ∩ batchSelection H m hH τ σ) v)) ≤
      (B.card:ℝ)*dmax*((τ:ℝ)/m) +
        (Fintype.card V:ℝ)*(dmax.choose a:ℝ)*((τ:ℝ)/m)^a := by
  classical
  let ρ : FiniteEntropy.Law (BatchOrder m) := FiniteEntropy.uniform
  let I := ↥B ⊕ V
  let E : I → BatchOrder m → Prop := fun i σ => match i with
    | .inl v => 1 ≤ vertexDegree (F ∩ batchSelection H m hH τ σ) v.val
    | .inr v => a ≤ vertexDegree (F ∩ batchSelection H m hH τ σ) v
  have hmono := ρ.event_mono
    (E:=fun σ => (∃ v ∈ B, 1 ≤ vertexDegree (F ∩ batchSelection H m hH τ σ) v) ∨
        (∃ v, a ≤ vertexDegree (F ∩ batchSelection H m hH τ σ) v))
    (F:=fun σ => ∃ i : I, E i σ) (by
      intro σ hh
      rcases hh with ⟨v,hv,hd⟩ | ⟨v,hd⟩
      · exact ⟨.inl ⟨v,hv⟩,hd⟩
      · exact ⟨.inr v,hd⟩)
  have htail (v : V) (k : ℕ) :
      ρ.event (fun σ => k ≤ vertexDegree (F ∩ batchSelection H m hH τ σ) v) ≤
        (dmax.choose k:ℝ)*((τ:ℝ)/m)^k := by
    apply (batch_vertex_loss_upper_tail H F m hH τ hτ hm hFH v k).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.choose_le_choose k (hd v)
  apply (hmono.trans (ρ.finite_union_bound E)).trans
  calc
    _ ≤ ∑ i : I, (match i with
      | .inl _ => (dmax:ℝ)*((τ:ℝ)/m)
      | .inr _ => (dmax.choose a:ℝ)*((τ:ℝ)/m)^a) := by
      apply sum_le_sum
      intro i _
      rcases i with v | v
      · simpa only [E,Nat.choose_one_right,pow_one] using htail v.val 1
      · exact htail v a
    _ = _ := by simp [I]; ring

/-- Actual failure probability for any feasible fixed graph with protected vertices and slack elsewhere. -/
theorem no_deficit_sampling_failure_bound (H F : SimpleHypergraph V) (hFH : F ⊆ H)
    (m : ℕ) (hH : H.card=m) (τ : ℕ) (hτ : τ ≤ m) (hm : 0 < m)
    (ell : V → ℕ) (B : Finset V) (a dmax : ℕ)
    (hell : ∀ v, ell v ≤ vertexDegree F v)
    (hslack : ∀ v ∉ B, ell v+a ≤ vertexDegree F v)
    (hd : ∀ v, vertexDegree F v ≤ dmax) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event (fun σ =>
      ∃ v, vertexDegree (F \ batchSelection H m hH τ σ) v < ell v) ≤
      (B.card:ℝ)*dmax*((τ:ℝ)/m) +
        (Fintype.card V:ℝ)*(dmax.choose a:ℝ)*((τ:ℝ)/m)^a := by
  have hmono := (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event_mono
    (fun σ (hfail : ∃ v, vertexDegree (F \ batchSelection H m hH τ σ) v < ell v) =>
      no_deficit_failure_split F ell B (batchSelection H m hH τ σ) a hell hslack hfail)
  exact hmono.trans (noDeficitSampling_union_bound H F hFH m hH τ hτ hm B a dmax hd)

/-- Equivalent success-probability formulation used in Lemma 5.3. -/
theorem no_deficit_sampling_success_bound (H F : SimpleHypergraph V) (hFH : F ⊆ H)
    (m : ℕ) (hH : H.card=m) (τ : ℕ) (hτ : τ ≤ m) (hm : 0 < m)
    (ell : V → ℕ) (B : Finset V) (a dmax : ℕ)
    (hell : ∀ v, ell v ≤ vertexDegree F v)
    (hslack : ∀ v ∉ B, ell v+a ≤ vertexDegree F v)
    (hd : ∀ v, vertexDegree F v ≤ dmax) :
    1-((B.card:ℝ)*dmax*((τ:ℝ)/m) +
        (Fintype.card V:ℝ)*(dmax.choose a:ℝ)*((τ:ℝ)/m)^a) ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event (fun σ =>
        ∀ v, ell v ≤ vertexDegree (F \ batchSelection H m hH τ σ) v) := by
  have h := no_deficit_sampling_failure_bound H F hFH m hH τ hτ hm ell B a dmax hell hslack hd
  have he : (fun σ : BatchOrder m => ∃ v, vertexDegree (F \ batchSelection H m hH τ σ) v < ell v) =
      (fun σ => ¬∀ v, ell v ≤ vertexDegree (F \ batchSelection H m hH τ σ) v) := by
    funext σ
    simp
  rw [he,FiniteEntropy.Law.event_compl] at h
  linarith
end LooseHamilton
