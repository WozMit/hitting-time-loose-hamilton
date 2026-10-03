module

public import HittingTimeLooseHamilton.NoDeficitSamplingUnion

public section

/-! No-deficit sampling from an arbitrary restricted host. The terminal graph
need not be contained in the sampling host: only its intersecting incidences
can be sampled. All lower bounds remain on the original vertex type. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma restricted_batch_terminal_inter (H F : SimpleHypergraph V)
    (m : ℕ) (hH : H.card=m) (τ : ℕ) (σ : BatchOrder m) :
    F ∩ batchSelection H m hH τ σ = (F ∩ H) ∩ batchSelection H m hH τ σ := by
  ext e
  have hs := batchSelection_subset H m hH τ σ
  simp only [mem_inter]
  tauto

/-- Pointwise finite failure bound without the false requirement `F ⊆ H`. -/
theorem restricted_no_deficit_sampling_failure_bound (H F : SimpleHypergraph V)
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
    (fun σ (hfail : ∃ v, vertexDegree (F \ batchSelection H m hH τ σ) v < ell v) => by
      have hs := no_deficit_failure_split F ell B (batchSelection H m hH τ σ) a hell hslack hfail
      rw [restricted_batch_terminal_inter H F m hH τ σ] at hs
      exact hs)
  exact hmono.trans (noDeficitSampling_union_bound H (F ∩ H) inter_subset_right
    m hH τ hτ hm B a dmax (fun v => (vertexDegree_mono inter_subset_left v).trans (hd v)))

/-- Restricted-host success probability, retaining the original terminal bounds. -/
theorem restricted_no_deficit_sampling_success_bound (H F : SimpleHypergraph V)
    (m : ℕ) (hH : H.card=m) (τ : ℕ) (hτ : τ ≤ m) (hm : 0 < m)
    (ell : V → ℕ) (B : Finset V) (a dmax : ℕ)
    (hell : ∀ v, ell v ≤ vertexDegree F v)
    (hslack : ∀ v ∉ B, ell v+a ≤ vertexDegree F v)
    (hd : ∀ v, vertexDegree F v ≤ dmax) :
    1-((B.card:ℝ)*dmax*((τ:ℝ)/m) +
        (Fintype.card V:ℝ)*(dmax.choose a:ℝ)*((τ:ℝ)/m)^a) ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event (fun σ =>
        ∀ v, ell v ≤ vertexDegree (F \ batchSelection H m hH τ σ) v) := by
  have h := restricted_no_deficit_sampling_failure_bound H F m hH τ hτ hm
    ell B a dmax hell hslack hd
  have he : (fun σ : BatchOrder m => ∃ v, vertexDegree (F \ batchSelection H m hH τ σ) v < ell v) =
      (fun σ => ¬∀ v, ell v ≤ vertexDegree (F \ batchSelection H m hH τ σ) v) := by
    funext σ
    simp
  rw [he,FiniteEntropy.Law.event_compl] at h
  linarith
end LooseHamilton
