module

public import HittingTimeLooseHamilton.PrivateFrameSourceScale

public section

/-! Finite averaging of actual frame candidate balance into root-test density.
The remaining geometric collision error is displayed explicitly as `g`; it is
not silently absorbed into a root-link sampling assumption. -/
noncomputable section
namespace LooseHamilton
open Finset AuxiliaryFrame
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At most `N^r` legal directed private-block/endpoints labels. -/
theorem frame_candidates_card_le_pow {r : ℕ} (hr : 3 ≤ r)
    {original : SimpleHypergraph V} (f : Frame r original) :
    f.candidates.card ≤ (Fintype.card V)^r := by
  have hs : f.candidates ⊆ (univ.powersetCard (r-2)) ×ˢ (univ ×ˢ univ) := by
    intro a ha
    have hlegal : f.LegalCandidate a := (mem_filter.mp ha).2
    exact mem_product.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,hlegal.1.private_card⟩,
      mem_product.mpr ⟨mem_univ _,mem_univ _⟩⟩
  have hc := card_le_card hs
  simp only [card_product, card_powersetCard, card_univ] at hc
  calc
    _ ≤ (Fintype.card V).choose (r-2) * (Fintype.card V * Fintype.card V) := hc
    _ ≤ (Fintype.card V)^(r-2) * (Fintype.card V * Fintype.card V) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
    _ = (Fintype.card V)^r := by
      rw [← pow_two, ← pow_add]
      congr 1
      omega

/-- Actual normalized candidate balance yields small registered private-test
bad sets for most target coordinates. Source count and mean comparisons are
proved by the concrete source-frame dictionary. The explicit geometric error
`g` is the cardinality bound for links with no legal structural split. -/
theorem private_root_density_most_targets {r : ℕ} (hr : 3 ≤ r)
    (h time : ℕ) (markers original F H : SimpleHypergraph V) (S q : Finset V) (x : V)
    (targets : Finset V) (f : Frame r original)
    (hH : H ⊆ completeEdges V r) (hrel : f.val.relative = none)
    (hdel : f.val.deleted = insert x S) (hmarkers : f.markers = insert q markers)
    (htports : ∀ t ∈ targets, t ∉ originalPorts original)
    (hsourcepos : 0 < f.cycleCount H) (hμ : 0 < f.mu H)
    (α c g : ℝ) (hαpos : 0 < α) (hα : α ≤ 1)
    (hc : c ≤ (1-α)/((r:ℝ)-1)^2)
    (hbalance : ¬ f.candidateBad H α)
    (hgeom : ∀ t ∈ targets,
      ((privateRootInvalidEdges r markers (allowedEdges r (originalPorts original)) S q x t).card : ℝ) ≤ g)
    (hN : 0 < Fintype.card V) :
    ∃ exceptional : Finset V,
      (exceptional.card : ℝ) ≤ Real.sqrt ((r-2 : ℕ)*α) * (Fintype.card V : ℝ) ∧
      ∀ t ∈ targets, t ∉ exceptional →
        rootLinkDensity r x
          ((registerPrivateRootTest r h time markers S q (originalPorts original) x t c).badSet (F,H)) ≤
          (Real.sqrt ((r-2 : ℕ)*α) * (Fintype.card V : ℝ)^(r-1) + g) /
            (rootEdgeUniverse r x).card := by
  let bad := frameAbnormalCandidates f H α
  have hactive : f.active = univ \ insert x S := by
    simp only [Frame.active, Code.active, hdel]
  have hbcard : (bad.card : ℝ) ≤ α * (Fintype.card V : ℝ)^r := by
    have hb := frameAbnormalCandidates_card_le f H α hbalance
    have hcan : (f.candidates.card : ℝ) ≤ (Fintype.card V : ℝ)^r := by
      exact_mod_cast frame_candidates_card_le_pow hr f
    exact hb.trans (mul_le_mul_of_nonneg_left hcan hαpos.le)
  have hsize : ∀ a ∈ bad, a.1.card ≤ r-2 := by
    intro a ha
    have ha' : a ∈ f.candidates := (mem_filter.mp ha).1
    exact ((mem_filter.mp ha').2.1.private_card).le
  have hNreal : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  let E := privateExceptionalTargets bad (Real.sqrt ((r-2 : ℕ)*α)) (Fintype.card V) r
  refine ⟨E, private_candidate_target_averaging hr bad α _ hαpos hNreal hsize hbcard, ?_⟩
  intro t ht hnot
  have hfiber : ((privateBadCandidateFiber bad t).card : ℝ) ≤
      Real.sqrt ((r-2 : ℕ)*α) * (Fintype.card V : ℝ)^(r-1) := by
    simpa only [E, privateExceptionalTargets, mem_filter, mem_univ, true_and, not_lt] using hnot
  have hcount := private_bad_root_edges_le_frame_fiber hr h time markers original F H S q x t
    f hactive hmarkers (htports t ht)
    (private_frame_source_eq f H markers S q x hH hrel hdel hmarkers)
    hsourcepos hμ (private_frame_mean_le f H S x hactive) α c hα hc
  have hcountR :
      (((registerPrivateRootTest r h time markers S q (originalPorts original) x t c).badSet (F,H)).card : ℝ) ≤
        (privateBadCandidateFiber bad t).card +
          (privateRootInvalidEdges r markers (allowedEdges r (originalPorts original)) S q x t).card := by
    exact_mod_cast hcount
  exact div_le_div_of_nonneg_right (hcountR.trans (add_le_add hfiber (hgeom t ht)))
    (Nat.cast_nonneg _)

end LooseHamilton
