module

public import HittingTimeLooseHamilton.PrivateFrameCandidateCapture
public import HittingTimeLooseHamilton.BootstrapFrameCounts
public import HittingTimeLooseHamilton.CoreRestrictionDegrees

public section

/-! Exact private source dictionary and the favorable mean comparison. -/
noncomputable section
namespace LooseHamilton
open Finset AuxiliaryFrame
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem inter_allowed_eq_fixedPortHost {r : ℕ} (H : SimpleHypergraph V) (U : Finset V)
    (hH : H ⊆ completeEdges V r) : H ∩ allowedEdges r U = fixedPortHost H U := by
  ext e
  simp only [mem_inter,mem_allowedEdges,fixedPortHost,mem_filter]
  constructor
  · rintro ⟨he,_,hp⟩; exact ⟨he,hp⟩
  · rintro ⟨he,hp⟩; exact ⟨he,(mem_completeEdges _ _).mp (hH he),hp⟩

theorem private_frame_source_eq {r : ℕ} {original : SimpleHypergraph V}
    (f : Frame r original) (H markers : SimpleHypergraph V) (S q : Finset V) (x : V)
    (hH : H ⊆ completeEdges V r) (hrel : f.val.relative = none)
    (hdel : f.val.deleted = insert x S) (hmarkers : f.markers = insert q markers) :
    f.cycleCount H = completionCount r markers (fixedPortHost H (originalPorts original))
      (insert x S) q := by
  rw [f.cycleCount_private_source hrel H markers (insert x S) q hdel hmarkers,
    inter_allowed_eq_fixedPortHost H (originalPorts original) hH]

/-- Filtering forbidden edges cannot increase the surviving mean. -/
theorem private_frame_mean_le {r : ℕ} {original : SimpleHypergraph V}
    (f : Frame r original) (H : SimpleHypergraph V) (S : Finset V) (x : V)
    (hactive : f.active = univ \ insert x S) :
    f.mu H ≤ privateRootSourceMean r H S x := by
  have hs : ∀ e ∈ f.rawHost H, e ⊆ f.active := fun e he => (mem_filter.mp he).2
  have hsub : restrictEdges f.active (f.rawHost H) ⊆ inducedHost f.active H :=
    restrictEdges_subset_inducedHost _ _ _ hs (by
      intro e he
      exact (mem_inter.mp (mem_filter.mp he).1).1)
  have hcard : (f.rawHost H).card ≤ (inducedHost f.active H).card := by
    rw [← restrictEdges_card_of_supported f.active (f.rawHost H) hs]
    exact card_le_card hsub
  unfold Frame.mu Frame.m Frame.n privateRootSourceMean
  rw [← hactive]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

end LooseHamilton
