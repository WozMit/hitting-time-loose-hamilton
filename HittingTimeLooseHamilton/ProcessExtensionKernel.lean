module

public import HittingTimeLooseHamilton.OrderedExtensionKernel
public import HittingTimeLooseHamilton.TerminalConditioning

public section
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact transition kernel of the unconditioned process from a specified prefix. -/
theorem process_extension_kernel {r : ℕ} (F : SimpleHypergraph V)
    (hF : F ⊆ completeEdges V r) (j : ℕ) (hFj : F.card ≤ j)
    (hj : j ≤ (completeEdges V r).card) (P : SimpleHypergraph V → Prop) :
    (processLaw V r).event (fun σ => processState σ F.card = F ∧ P (processState σ j)) =
      (1 / (((Fintype.card V).choose r).choose F.card : ℝ)) *
      ((((completeEdges V r \ F).powersetCard (j-F.card)).filter
        (fun S => P (F ∪ S))).card : ℝ) /
      (((completeEdges V r).card-F.card).choose (j-F.card) : ℝ) := by
  classical
  let K := liftEdges r F
  let val : Edge V r ↪ Finset V := ⟨Subtype.val,Subtype.val_injective⟩
  let Q : Finset (Edge V r) → Prop := fun S => P (S.map val)
  have hK : K.card = F.card := liftEdges_card hF
  have hmap : K.map val = F := by simpa [K,val,map_eq_image] using liftEdges_image hF
  have hcomp : (univ \ K).map val = completeEdges V r \ F := by
    ext e
    simp only [mem_map,mem_sdiff,mem_univ,true_and,mem_liftEdges,K,val,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ⟨a.property,ha⟩
    · rintro ⟨he,hne⟩; exact ⟨⟨e,he⟩,hne,rfl⟩
  have hc : (((univ \ K).powersetCard (j-K.card)).filter
      (fun S => Q (K ∪ S))).card =
      (((completeEdges V r \ F).powersetCard (j-F.card)).filter
        (fun S => P (F ∪ S))).card := by
    rw [← hcomp,powersetCard_map,filter_map,card_map]
    simp only [Function.comp_apply,Finset.mapEmbedding_apply,RelEmbedding.coe_toEmbedding,
      Q,map_union,hmap,hK]
    rfl
  have ht := FiniteEntropy.Law.uniform_event_equiv (orderRankEquiv (Edge V r))
    (fun σ => orderPrefix σ F.card = K ∧ Q (orderPrefix σ j))
  have he : (fun σ : EdgeOrder V r => processState σ F.card = F ∧ P (processState σ j)) =
      (fun σ => orderPrefix (orderRankEquiv (Edge V r) σ) F.card = K ∧
        Q (orderPrefix (orderRankEquiv (Edge V r) σ) j)) := by
    funext σ; apply propext
    apply and_congr (processState_eq_iff_rank_prefix hF σ F.card)
    simp only [Q,val,map_eq_image,processState,orderPrefix,orderRankEquiv,edgeRank]
    rfl
  change (FiniteEntropy.uniform : FiniteEntropy.Law (EdgeOrder V r)).event _ = _
  rw [he,ht,FiniteEntropy.Law.uniform_event]
  have hker := ordered_extension_kernel K j (by simpa [hK] using hFj)
    (by simpa using hj) Q
  have hp := uniform_order_prefix_probability K.card (by simpa [hK] using hFj.trans hj) K rfl
  rw [hp,hc,card_powersetCard,card_sdiff_of_subset (subset_univ K),card_univ] at hker
  simpa only [hK,FiniteOrder,Fintype.card_coe,completeEdges_card] using hker
end LooseHamilton
