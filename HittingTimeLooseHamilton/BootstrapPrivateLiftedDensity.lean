module

public import HittingTimeLooseHamilton.BootstrapPrivateLiftedBadSet
public import HittingTimeLooseHamilton.BootstrapPrivateCollisionBounds
public import HittingTimeLooseHamilton.BootstrapAmbientDensityNormalization
public import HittingTimeLooseHamilton.PrivateReconstructionInjection

public section

/-! Item 33.15.6: the literal lifted registered bad set is controlled in the
ambient root universe. All geometric and count-capture gates are discharged. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateLiftedDensity
open Finset BootstrapBases BootstrapPrivateLinkGeometry BootstrapPrivateLiftedBadSet
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}
attribute [local instance] Classical.propDecidable

theorem badSet_subset (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x t : ↥(active b))
    (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none) (ht : t.val ∉ exclusions b S q x)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (α : ℝ) (hα : α ≤ 1/2) :
    registeredBadSet r h time hM b S q x t J H ⊆
      (privateBadCandidateFiber (frameAbnormalCandidates F H α) t.val).image
        (privateCandidateRootEdge x.val t.val) ∪ deletedRootCollisions r x.val ((exclusions b S q t).erase x.val) := by
  apply subset_fiber_image_union h time hM b F hr J H hH S q x t hd hm hrel
    (target_legal hM hr b S q x t hS hs ht).2.1 hW α hα
  intro e he hn
  simpa only [restrictEdge_erase] using surviving_split hM hr b S q x t hS hs ht e he hn

theorem badSet_noncolliding_injection (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x t : ↥(active b))
    (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none) (ht : t.val ∉ exclusions b S q x)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (α : ℝ) (hα : α ≤ 1/2) :
    ∃ f : ↥(registeredBadSet r h time hM b S q x t J H \ deletedRootCollisions r x.val ((exclusions b S q t).erase x.val)) → ↥(privateBadCandidateFiber (frameAbnormalCandidates F H α) t.val),
      Function.Injective f ∧ ∀ e,
        privateCandidateRootEdge x.val t.val (f e).val = e.val := by
  exact exists_private_reconstruction_injection x.val t.val _ _ _
    (badSet_subset h time hM b F hr J H hH S q x t hS hs hd hm hrel ht hW α hα)

theorem badSet_card_le (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x t : ↥(active b))
    (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none) (ht : t.val ∉ exclusions b S q x)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (α : ℝ) (hα : α ≤ 1/2) (β : ℝ)
    (hfiber : ((privateBadCandidateFiber (frameAbnormalCandidates F H α) t.val).card : ℝ) ≤ β*(Fintype.card V:ℝ)^(r-1)) :
    ((registeredBadSet r h time hM b S q x t J H).card : ℝ) ≤
      β*(Fintype.card V:ℝ)^(r-1) +
        (2*M.card+r+1 : ℕ)*((Fintype.card V-2).choose (r-2) : ℝ) := by
  have hsub := badSet_subset h time hM b F hr J H hH S q x t hS hs hd hm hrel ht hW α hα
  have hc : (registeredBadSet r h time hM b S q x t J H).card ≤
      (privateBadCandidateFiber (frameAbnormalCandidates F H α) t.val).card + (deletedRootCollisions r x.val ((exclusions b S q t).erase x.val)).card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right card_image_le _))
  have hcR : ((registeredBadSet r h time hM b S q x t J H).card : ℝ) ≤
      ((privateBadCandidateFiber (frameAbnormalCandidates F H α) t.val).card : ℝ) + ((deletedRootCollisions r x.val ((exclusions b S q t).erase x.val)).card : ℝ) := by exact_mod_cast hc
  have hcoll : ((deletedRootCollisions r x.val ((exclusions b S q t).erase x.val)).card : ℝ) ≤
      (2*M.card+r+1 : ℕ)*((Fintype.card V-2).choose (r-2) : ℝ) := by
    exact_mod_cast collisions_card_le hM hr b S q x t hS hs.pair_card
  exact hcR.trans (add_le_add hfiber hcoll)

theorem badSet_density_le (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x t : ↥(active b))
    (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none) (ht : t.val ∉ exclusions b S q x)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (α : ℝ) (hα : α ≤ 1/2) (hN : 2*r ≤ Fintype.card V) (β : ℝ) (hβ : 0 ≤ β)
    (hfiber : ((privateBadCandidateFiber (frameAbnormalCandidates F H α) t.val).card : ℝ) ≤
      β*(Fintype.card V:ℝ)^(r-1)) :
    rootLinkDensity r x.val (registeredBadSet r h time hM b S q x t J H) ≤
      ((2:ℝ)^(r-1)*((r-1).factorial:ℝ))*β +
        (2*M.card+r+1 : ℕ)*(r-1 : ℕ)/(Fintype.card V-1 : ℕ) := by
  exact BootstrapAmbientDensityNormalization.density_le hr hN x.val _ β _ hβ
    (badSet_card_le h time hM b F hr J H hH S q x t hS hs hd hm hrel ht hW α hα β hfiber)

theorem observed_badSet_density_le (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x t : ↥(active b))
    (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none) (ht : t.val ∉ exclusions b S q x)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (α : ℝ) (hα : α ≤ 1/2) (hN : 2*r ≤ Fintype.card V) (β : ℝ) (hβ : 0 ≤ β)
    (hfiber : ((privateBadCandidateFiber (frameAbnormalCandidates F H α) t.val).card : ℝ) ≤
      β*(Fintype.card V:ℝ)^(r-1)) :
    rootLinkDensity r x.val (registeredBadSet r h time hM b S q x t
      (rootFreeEdges x.val J) (rootFreeEdges x.val H)) ≤
      ((2:ℝ)^(r-1)*((r-1).factorial:ℝ))*β +
        (2*M.card+r+1 : ℕ)*(r-1 : ℕ)/(Fintype.card V-1 : ℕ) := by
  rw [observation_eq]
  exact badSet_density_le h time hM b F hr J H hH S q x t hS hs hd hm hrel ht hW α hα hN β hβ hfiber

end LooseHamilton.BootstrapPrivateLiftedDensity
