module

public import HittingTimeLooseHamilton.BiasedRoleSupport
public import HittingTimeLooseHamilton.BiasedShearerFixedCount

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Only vertices outside the fixed marked ports are random role coordinates. -/
abbrev NonPortVertex (markers : SimpleHypergraph V) :=
  ↥((univ : Finset V) \ originalPorts markers)

namespace ConnectedCloneCycle
variable {r : ℕ} {markers : SimpleHypergraph V}

@[expose] def junctionBits (root : ↥markers) (a : ↥root.val)
    (C : ConnectedCloneCycle r markers) : NonPortVertex markers → Bool :=
  fun v => decide (v.val ∈ (role root a C).1)

lemma role_junction_mem_choices (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (C : ConnectedCloneCycle r markers) :
    (role root a C).1 ∈ ordinaryJunctionChoices markers (ordinaryEdgeCount r markers) :=
  (configuration hr root a C).1.property

lemma junctionBits_recovers (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (C : ConnectedCloneCycle r markers) :
    (univ.filter (fun v : NonPortVertex markers => junctionBits root a C v = true)).image
      Subtype.val = (role root a C).1 := by
  classical
  have hs := (mem_ordinaryJunctionChoices _ _ _).mp (role_junction_mem_choices hr root a C)
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    simpa [junctionBits] using (mem_filter.mp hw).2
  · intro hv
    exact mem_image.mpr ⟨⟨v,hs.1 hv⟩,mem_filter.mpr ⟨mem_univ _,by simpa [junctionBits] using hv⟩,rfl⟩

lemma junctionBits_fixed_count (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (C : ConnectedCloneCycle r markers) :
    (univ.filter (fun v : NonPortVertex markers => junctionBits root a C v = true)).card =
      ordinaryEdgeCount r markers-markers.card := by
  have hc := congrArg Finset.card (junctionBits_recovers hr root a C)
  rw [card_image_of_injective _ Subtype.val_injective] at hc
  exact hc.trans ((mem_ordinaryJunctionChoices _ _ _).mp (role_junction_mem_choices hr root a C)).2

/-- Restricting ordinary junction indicators to nonports loses no information. -/
lemma junctionBits_entropy (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (p : Law (ConnectedCloneCycle r markers)) :
    entropy (p.map (junctionBits root a)).mass =
      entropy (p.map (fun C => (role root a C).1)).mass := by
  classical
  apply entropy_eq_of_mutual_determination p (junctionBits root a)
    (fun C => (role root a C).1)
    (fun x => (univ.filter (fun v : NonPortVertex markers => x v = true)).image Subtype.val)
    (fun J v => decide (v.val ∈ J))
  · exact junctionBits_recovers hr root a
  · intro C; rfl

lemma nonPortVertex_card (hM : IsPairMatching markers) :
    Fintype.card (NonPortVertex markers) = Fintype.card V-2*markers.card := by
  rw [Fintype.card_coe, card_sdiff_of_subset (subset_univ _), card_univ, hM.ports_card]

/-- Actual role law has a Bernoulli deficit equal to a fixed weight cross
entropy minus the entropy of its ordinary junction set. -/
theorem junctionBits_deficit (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (root : ↥markers) (a : ↥root.val) (p : Law (ConnectedCloneCycle r markers))
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    coordinateDeficit p (junctionBits root a)
      (coordinateCrossEntropy p (junctionBits root a) (fun _ => bernoulliBitLaw b hb0 hb1)) univ =
      -(((ordinaryEdgeCount r markers-markers.card:ℕ):ℝ)*Real.log b +
        (((Fintype.card V-2*markers.card)-(ordinaryEdgeCount r markers-markers.card):ℕ):ℝ)*Real.log (1-b)) -
      entropy (p.map (fun C => (role root a C).1)).mass := by
  rw [bernoulli_deficit_fixed_count p (junctionBits root a) b hb0 hb1 _
    (junctionBits_fixed_count hr root a), junctionBits_entropy hr root a p, nonPortVertex_card hM]

/-- The complete role entropy deficit controls the Bernoulli deficit, up to
exactly the fixed-weight cross entropy gap. -/
theorem junctionBits_deficit_le_role_deficit (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (root : ↥markers) (a : ↥root.val) (p : Law (ConnectedCloneCycle r markers))
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (S : ℝ) :
    coordinateDeficit p (junctionBits root a)
      (coordinateCrossEntropy p (junctionBits root a) (fun _ => bernoulliBitLaw b hb0 hb1)) univ ≤
      (S-entropy (p.map (role root a)).mass) +
      (-(((ordinaryEdgeCount r markers-markers.card:ℕ):ℝ)*Real.log b +
        (((Fintype.card V-2*markers.card)-(ordinaryEdgeCount r markers-markers.card):ℕ):ℝ)*Real.log (1-b)) +
        ((markers.card-1:ℕ):ℝ)*Real.log 2-S) := by
  rw [junctionBits_deficit hr hM root a p b hb0 hb1]
  have h := role_entropy_le_junction_entropy hr hM root a p
  linarith

end ConnectedCloneCycle
end LooseHamilton
