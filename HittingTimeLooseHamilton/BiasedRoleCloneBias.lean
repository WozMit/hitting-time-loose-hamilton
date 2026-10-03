module

public import HittingTimeLooseHamilton.BiasedEntropyEnsemble
public import HittingTimeLooseHamilton.BiasedCloneConditionalAverage
public import HittingTimeLooseHamilton.BiasedRoleCloneFibre
public import HittingTimeLooseHamilton.BiasedRoleAveraging

public section

/-! Averaging the actual conditional clone laws bounds the first projection
error, from clone-edge marginals to the junction-role compatibility marginals. -/
noncomputable section
open Finset FiniteEntropy
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers G : SimpleHypergraph V}
namespace BiasedEnsemble
variable (root : ↥markers) (a : ↥root.val) (p : Law (BiasedCycleState r markers G))

lemma fibreLaw_event (z : Index root a p) (W : BiasedCycleState r markers G → Prop) :
    (fibreLaw root a p z).event (fun C => W C.val) =
      (p.conditionOr (fun C => biasedCloneRole root a C=z.val)).event W := by
  classical
  have h := congrArg (fun q : Law (BiasedCycleState r markers G) => q.event W)
    (positiveEventLaw_map p _ (fibre_pos root a p z))
  rw [Law.event_map] at h
  change (fibreLaw root a p z).event (fun C => W C.val) = _ at h
  rw [h]
  have hz : 0 < p.event (fun C => biasedCloneRole root a C=z.val) := z.property
  simp only [reference_role, Law.conditionOr, dif_pos hz]

lemma event_average (W : BiasedCycleState r markers G → Prop) :
    p.event W = ∑ z, (law root a p).mass z *
      (fibreLaw root a p z).event (fun C => W C.val) := by
  rw [event_eq_positive_fibre_average p (biasedCloneRole root a) W]
  apply sum_congr rfl
  intro z _
  rw [fibreLaw_event]
  rfl

lemma compatibility_average (i : EligibleRoleCoordinate markers G) (lam : ℝ) :
    (∑ z, (law root a p).mass z *
      (if roleCloneEdge i ⊆ biasedCloneUniverse root a (reference root a p z) then 1/lam else 0)) =
    ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle)
      i.1.val i.2.val.1 i.2.val.2 / lam := by
  classical
  let Q := fun z : Finset V × (↥markers → V) =>
    ∀ w∈i.1.val, w∈z.1 ↔ w=i.2.val.1 ∨ w=i.2.val.2
  have he (z : Index root a p) :
      roleCloneEdge i ⊆ biasedCloneUniverse root a (reference root a p z) ↔ Q z.val := by
    rw [biasedCloneUniverse, roleCloneEdge_subset_iff]
    change Q (biasedCloneRole root a (reference root a p z)) ↔ Q z.val
    rw [reference_role]
  simp_rw [he]
  have hs : (∑ z, (law root a p).mass z * (if Q z.val then 1/lam else 0)) =
      (law root a p).event (fun z => Q z.val) / lam := by
    rw [Law.event, sum_div]
    apply sum_congr rfl
    intro z _
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hs]
  congr 1
  have hm := congrArg (fun q => q.event Q) (supportedLaw_map (p.map (biasedCloneRole root a)))
  rw [Law.event_map, Law.event_map] at hm
  rw [ConnectedCloneCycle.junctionRoleProbability, Law.event_map]
  exact hm

/-- The first projection bound for the actual cycle distribution and its exact
positive-role conditional Kahn ensemble. -/
theorem role_clone_bias_le (hr : 3≤r) (hG : ∀ B∈G,B.card=r) (lam : ℝ) :
    (∑ i : EligibleRoleCoordinate markers G,
      |directedRoleProbability r markers G root a p i.1.val i.2.val.1 i.2.val.2 -
        ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle)
          i.1.val i.2.val.1 i.2.val.2 / lam|) ≤
    ∑ z, (law root a p).mass z *
      ∑ f ∈ (host hr hG root a p z).edges,
        |(matchingLaw hr hG root a p z).event (fun M => f∈M.val.val)-1/lam| := by
  classical
  let f := fun (z : Index root a p) (i : EligibleRoleCoordinate markers G) =>
    (fibreLaw root a p z).event (fun C => roleCloneEdge i∈biasedCloneLift root a C.val)
  let g := fun (z : Index root a p) (i : EligibleRoleCoordinate markers G) =>
    if roleCloneEdge i ⊆ biasedCloneUniverse root a (reference root a p z) then 1/lam else 0
  have hf (i : EligibleRoleCoordinate markers G) :
      (∑ z, (law root a p).mass z * f z i) =
        directedRoleProbability r markers G root a p i.1.val i.2.val.1 i.2.val.2 := by
    rw [directedRoleProbability_eq_clone_event hr root a p _ _ _
      (mem_offDiag.mp i.2.property).1 (mem_offDiag.mp i.2.property).2.1, Law.event_map]
    exact (event_average root a p (fun C => roleCloneEdge i∈biasedCloneLift root a C)).symm
  have hg (i : EligibleRoleCoordinate markers G) :
      (∑ z, (law root a p).mass z * g z i) =
        ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle)
          i.1.val i.2.val.1 i.2.val.2 / lam := compatibility_average root a p i lam
  have h := role_average_l1_le (law root a p) f g
  simp_rw [hf, hg] at h
  apply h.trans
  apply sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ ((law root a p).nonneg z)
  exact roleCloneFibre_l1_le hr hG root a (reference root a p z)
    (labels hr root a p z) (fibreLaw root a p z) lam

/-- The manuscript's nested sum over eligible edges and their directed roles. -/
theorem role_clone_bias_edges_le (hr : 3≤r) (hG : ∀ B∈G,B.card=r) (lam : ℝ) :
    (∑ e∈eligibleRoleEdges markers G, ∑ uv∈e.offDiag,
      |directedRoleProbability r markers G root a p e uv.1 uv.2 -
        ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle)
          e uv.1 uv.2 / lam|) ≤
    ∑ z, (law root a p).mass z *
      ∑ f ∈ (host hr hG root a p z).edges,
        |(matchingLaw hr hG root a p z).event (fun M => f∈M.val.val)-1/lam| := by
  have h := role_clone_bias_le root a p hr hG lam
  rw [Fintype.sum_sigma] at h
  have hs : (∑ e : ↥(eligibleRoleEdges markers G), ∑ uv : ↥e.val.offDiag,
      |directedRoleProbability r markers G root a p e.val uv.val.1 uv.val.2 -
        ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle)
          e.val uv.val.1 uv.val.2 / lam|) =
    ∑ e∈eligibleRoleEdges markers G, ∑ uv∈e.offDiag,
      |directedRoleProbability r markers G root a p e uv.1 uv.2 -
        ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle)
          e uv.1 uv.2 / lam| := by
    rw [sum_subtype (p := fun e => e∈eligibleRoleEdges markers G) (eligibleRoleEdges markers G) (by simp)
      (fun e => ∑ uv∈e.offDiag,
        |directedRoleProbability r markers G root a p e uv.1 uv.2 -
          ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle)
            e uv.1 uv.2 / lam|)]
    apply sum_congr rfl
    intro e _
    exact (sum_subtype (p := fun uv => uv∈e.val.offDiag) e.val.offDiag (by simp)
      (fun uv => |directedRoleProbability r markers G root a p e.val uv.1 uv.2 -
        ConnectedCloneCycle.junctionRoleProbability root a (p.map biasedConnectedCycle)
          e.val uv.1 uv.2 / lam|)).symm
  rw [hs] at h
  exact h

end BiasedEnsemble
end LooseHamilton
