module

public import HittingTimeLooseHamilton.BiasedCloneConditionalKahn
public import HittingTimeLooseHamilton.BiasedCloneConditionalSupport
public import HittingTimeLooseHamilton.UniformConditionalEquivalence

public section

/-! The genuine role-indexed ensemble of conditional Kahn laws, omitting exactly
zero-probability fibres. Every host has r*k vertices. -/
noncomputable section
namespace LooseHamilton
open Finset FiniteEntropy
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers G : SimpleHypergraph V}
namespace BiasedEnsemble
variable (hr : 3 ≤ r) (hG : ∀ B∈G,B.card=r)
variable (root : ↥markers) (a : ↥root.val) (p : Law (BiasedCycleState r markers G))

abbrev Index := {z // 0 < (p.map (biasedCloneRole root a)).mass z}

@[expose] def law : Law (Index root a p) := supportedLaw (p.map (biasedCloneRole root a))

@[expose] def reference (z : Index root a p) : BiasedCycleState r markers G :=
  Classical.choose (exists_of_event_pos p (fun C => biasedCloneRole root a C=z.val) z.property)

lemma reference_role (z : Index root a p) :
    biasedCloneRole root a (reference root a p z)=z.val :=
  Classical.choose_spec (exists_of_event_pos p (fun C => biasedCloneRole root a C=z.val) z.property)

lemma fibre_pos (z : Index root a p) :
    0 < p.event (fun C => biasedCloneRole root a C=biasedCloneRole root a (reference root a p z)) := by
  rw [reference_role]
  exact z.property

include hr in
lemma universe_card (z : Index root a p) :
    Fintype.card ↥(biasedCloneUniverse root a (reference root a p z)) =
      r*ordinaryEdgeCount r markers := by
  rw [Fintype.card_coe]
  change ((biasedConnectedCycle (reference root a p z)).directedWitness root a).cloneVertices.card=_
  rw [MixedCycleWitness.cloneVertices_card _ hr]
  congr 1
  exact (biasedConnectedCycle (reference root a p z)).property.edge_card hr

@[expose] def labels (z : Index root a p) :
    ↥(biasedCloneUniverse root a (reference root a p z)) ≃ Fin (r*ordinaryEdgeCount r markers) :=
  Fintype.equivFinOfCardEq (universe_card hr root a p z)

@[expose] def host (z : Index root a p) : Kahn.Hypergraph (r*ordinaryEdgeCount r markers) r :=
  biasedCloneKahnHost hG root a (reference root a p z) (labels hr root a p z)

@[expose] def fibreLaw (z : Index root a p) : Law (BiasedCloneFibre root a (reference root a p z)) := by
  classical
  exact positiveEventLaw p _ (fibre_pos root a p z)

@[expose] def matchingLaw (z : Index root a p) : Law (Kahn.MatchingIn (host hr hG root a p z)) :=
  (fibreLaw root a p z).map
    (biasedCloneKahnMatching hr hG root a (reference root a p z) (labels hr root a p z))

lemma matchingLaw_entropy (z : Index root a p) :
    entropy (matchingLaw hr hG root a p z).mass =
      entropy (p.conditionOr (fun C => biasedCloneRole root a C=z.val)).mass := by
  classical
  change entropy ((fibreLaw root a p z).map
    (biasedCloneKahnMatching hr hG root a (reference root a p z) (labels hr root a p z))).mass = _
  rw [biasedCloneKahn_entropy]
  change entropy (positiveEventLaw p _ (fibre_pos root a p z)).mass=_
  rw [positiveEventLaw_entropy]
  have hz : 0 < p.event (fun C => biasedCloneRole root a C=z.val) := z.property
  simp only [Law.conditionOr, dif_pos hz]
  congr 1
  funext C
  simp only [Law.condition, reference_role]
  split_ifs <;> rfl

/-- The complete conditional ensemble recovers the source entropy exactly. -/
theorem entropy_chain :
    entropy p.mass = entropy (p.map (biasedCloneRole root a)).mass +
      ∑ z, (law root a p).mass z * entropy (matchingLaw hr hG root a p z).mass := by
  have hc := p.entropy_chain (biasedCloneRole root a)
  rw [Law.conditionalEntropy_eq_sum] at hc
  rw [hc]
  congr 1
  simp_rw [matchingLaw_entropy]
  have hm := supportedLaw_map (p.map (biasedCloneRole root a))
  have hs := Law.sum_map_mul (supportedLaw (p.map (biasedCloneRole root a)))
    Subtype.val (fun z => entropy (p.conditionOr (fun C => biasedCloneRole root a C=z)).mass)
  rw [hm] at hs
  exact hs
end BiasedEnsemble
end LooseHamilton
