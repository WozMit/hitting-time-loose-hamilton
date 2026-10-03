module

public import HittingTimeLooseHamilton.TerminalCompletionCount
public import HittingTimeLooseHamilton.ExtensionSubsetKernel
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! The exact terminal-completion weighting of an intermediate extension state. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma extension_single_state_kernel {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (j : ℕ) (hMj : M≤j)
    (hj : j≤(completeEdges V r).card) (H : SimpleHypergraph V)
    (hH : H⊆completeEdges V r) (hHcard : H.card=j) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => extensionState F σ j=H) =
      if F.val⊆H then 1/(((completeEdges V r).card-M).choose (j-M):ℝ) else 0 := by
  rw [extension_subset_kernel F j hMj hj (fun G => G=H)]
  by_cases hFH : F.val⊆H
  · rw [if_pos hFH]
    have he : (((completeEdges V r\F.val).powersetCard (j-M)).filter
        (fun S => F.val∪S=H)) = {H\F.val} := by
      ext S
      simp only [mem_filter,mem_powersetCard,mem_singleton]
      constructor
      · rintro ⟨⟨hS,hc⟩,hU⟩
        ext e
        constructor
        · intro he
          have hs := mem_sdiff.mp (hS he)
          exact mem_sdiff.mpr ⟨hU ▸ mem_union_right F.val he,hs.2⟩
        · intro he
          obtain ⟨heH,heF⟩ := mem_sdiff.mp he
          rw [←hU] at heH
          exact (mem_union.mp heH).resolve_left heF
      · rintro rfl
        refine ⟨⟨sdiff_subset_sdiff hH (Subset.refl _),?_⟩,?_⟩
        · rw [card_sdiff_of_subset hFH,hHcard,F.property.2.1]
        · exact union_sdiff_of_subset hFH
    have hc := congrArg (fun S : Finset (SimpleHypergraph V) => (S.card:ℝ)) he
    simp only [card_singleton,Nat.cast_one] at hc
    congr 1
    convert hc using 1
    congr 1
    congr 1
    ext S
    simp
  · rw [if_neg hFH]
    have he : (((completeEdges V r\F.val).powersetCard (j-M)).filter
        (fun S => F.val∪S=H)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro S hS
      have he := (mem_filter.mp hS).2
      exact hFH (he ▸ subset_union_left)
    have hc := congrArg (fun S : Finset (SimpleHypergraph V) => (S.card:ℝ)) he
    simp only [card_empty,Nat.cast_zero] at hc
    have hz : (#{S ∈ (completeEdges V r\F.val).powersetCard (j-M) | F.val∪S=H}:ℝ)=0 := hc
    convert div_eq_zero_iff.mpr (Or.inl hz) using 1
    congr 2
    congr 1
    ext S
    simp

theorem extension_marginal_completion_probability (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (H : SimpleHypergraph V)
    (hH : H⊆completeEdges V r) (hHcard : H.card=j)
    (hMj : M≤j) (hj : j≤(completeEdges V r).card) :
    (extensionLaw r M ell).event (fun ω => extensionState ω.1 ω.2 j=H) =
      (terminalCompletionCount r M ell H:ℝ)/
      ((Fintype.card (TerminalState V r M ell):ℝ)*
        (((completeEdges V r).card-M).choose (j-M):ℝ)) := by
  rw [extensionLaw,FiniteEntropy.Law.event_prod_sum]
  simp_rw [extension_single_state_kernel _ j hMj hj H hH hHcard]
  simp only [terminalLaw,FiniteEntropy.uniform]
  have he (F : TerminalState V r M ell) :
      (1/(Fintype.card (TerminalState V r M ell):ℝ)) *
      (if F.val⊆H then 1/(((completeEdges V r).card-M).choose (j-M):ℝ) else 0) =
      if F.val⊆H then 1/((Fintype.card (TerminalState V r M ell):ℝ)*
        (((completeEdges V r).card-M).choose (j-M):ℝ)) else 0 := by
    split_ifs <;> ring
  simp only [←one_div] at *
  simp_rw [he]
  rw [←sum_filter]
  simp only [sum_const,nsmul_eq_mul,terminalCompletionCount,mul_one_div]
end LooseHamilton
