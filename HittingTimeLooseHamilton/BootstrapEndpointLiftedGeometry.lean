module

public import HittingTimeLooseHamilton.BootstrapEndpointLinkGeometry
public import HittingTimeLooseHamilton.BootstrapPrivateLinkGeometry

public section

/-! Endpoint structural errors in the ambient root universe, including the
base deletion and every fixed original port. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointLiftedGeometry
open Finset BootstrapBases BootstrapEndpointLinkGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

/-- Ambient obstruction set: deleted base vertices and all residual obstructions. -/
@[expose] def exclusions (hM : IsPairMatching M) (b : Base M)
    (P : Finset ↥(active b)) (y z t : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) : Finset V :=
  deleted b ∪ liftEdge (active b)
    (BootstrapEndpointLinkGeometry.exclusions (restrictEdges (active b) (markers hM b))
      P (fixedPorts b) y z t l)

theorem root_not_excluded (hM : IsPairMatching M) (b : Base M)
    (P : Finset ↥(active b)) (y z t : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) : y.val ∉ exclusions hM b P y z t l := by
  intro hy
  rcases mem_union.mp hy with hd | hl
  · exact (mem_sdiff.mp y.property).2 hd
  · obtain ⟨v,hv,he⟩ := mem_image.mp hl
    have hvy : v = y := Subtype.ext he
    subst v
    exact notMem_erase _ _ hv

/-- Avoiding ambient collisions supplies survival and a genuine residual
counterfactual split. No membership of the candidate edge in H is assumed. -/
theorem surviving_split (hM : IsPairMatching M) (b : Base M) (hr : 2 ≤ r)
    (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b))
    (y z t : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (ht : t ∉ P ∪ cutDeleted y l ∪
      originalPorts (restrictEdges (active b) (markers hM b)) ∪ {y,z,cutEndpoint l})
    (e : Finset V) (he : e ∈ rootEdgeUniverse r y.val)
    (hc : e ∉ deletedRootCollisions r y.val (exclusions hM b P y z t l)) :
    e ⊆ active b ∧ restrictEdge (active b) e ∈ allowedEdges r (fixedPorts b) ∧
      ∃ q, RootFreeEndpointSplit r (restrictEdges (active b) (markers hM b))
        G P y z t (restrictEdge (active b) e) l q := by
  have havoid : e ⊆ univ \ exclusions hM b P y z t l := by
    simpa only [deletedRootCollisions,mem_filter,he,true_and,not_not] using hc
  have hs : e ⊆ active b := by
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun hd =>
      (mem_sdiff.mp (havoid hv)).2 (mem_union_left _ hd)⟩
  have heroot : restrictEdge (active b) e ∈ rootEdgeUniverse r y := by
    apply (mem_rootEdgeUniverse _ _ _).mpr
    constructor
    · rw [← liftEdge_card, lift_restrictEdge _ _ hs]
      exact ((mem_rootEdgeUniverse _ _ _).mp he).1
    · exact (mem_restrictEdge _ _ _).mpr ((mem_rootEdgeUniverse _ _ _).mp he).2
  have hn : restrictEdge (active b) e ∉ deletedRootCollisions r y
      (BootstrapEndpointLinkGeometry.exclusions (restrictEdges (active b) (markers hM b))
        P (fixedPorts b) y z t l) := by
    intro hn
    apply (mem_filter.mp hn).2
    intro v hv
    apply mem_sdiff.mpr
    refine ⟨mem_univ _,?_⟩
    intro hz
    exact (mem_sdiff.mp (havoid ((mem_restrictEdge _ _ _).mp hv))).2
      (mem_union_right _ (mem_image_of_mem _ hz))
  exact ⟨hs,split_of_not_collision hr _ G P (fixedPorts b) y z t l ht _ heroot hn⟩

theorem fixedPorts_card_le (hM : IsPairMatching M) (b : Base M) :
    (fixedPorts b).card ≤ 2*M.card := by
  have hsub : liftEdge (active b) (fixedPorts b) ⊆ originalPorts M := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_fixedPorts b w).mp hw
  have hc := card_le_card hsub
  simpa only [liftEdge_card,hM.ports_card] using hc

/-- A common explicit obstruction bound covers Type I and Type II cuts. -/
theorem exclusions_card_le (hM : IsPairMatching M) (hr : 3 ≤ r) (b : Base M)
    (P : Finset ↥(active b)) (y z t : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) (hP : P.card = r-2)
    (hl : (cutDeleted y l).card ≤ 2*(r-2)+3) :
    (exclusions hM b P y z t l).card ≤ 2*M.card+3*r+2 := by
  have h0 := card_union_le (deleted b)
    (liftEdge (active b) (BootstrapEndpointLinkGeometry.exclusions
      (restrictEdges (active b) (markers hM b)) P (fixedPorts b) y z t l))
  have hd := deleted_card_le b
  have hg := BootstrapEndpointLinkGeometry.exclusions_card_le_of_ports_subset
    (restrictEdges (active b) (markers hM b)) P (fixedPorts b) y z t l
    (BootstrapPrivateLinkGeometry.marker_ports_subset hM b)
  have hp := fixedPorts_card_le hM b
  simp only [liftEdge_card] at h0
  unfold exclusions
  omega

theorem collisions_card_le (hM : IsPairMatching M) (hr : 3 ≤ r) (b : Base M)
    (P : Finset ↥(active b)) (y z t : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) (hP : P.card = r-2)
    (hl : (cutDeleted y l).card ≤ 2*(r-2)+3) :
    (deletedRootCollisions r y.val (exclusions hM b P y z t l)).card ≤
      (2*M.card+3*r+2)*(Fintype.card V-2).choose (r-2) :=
  (deletedRootCollisions_card_le (by omega) y.val _
    (root_not_excluded hM b P y z t l)).trans
    (Nat.mul_le_mul_right _ (exclusions_card_le hM hr b P y z t l hP hl))

theorem collisions_density_le (hM : IsPairMatching M) (hr : 3 ≤ r)
    (hN : 2 ≤ Fintype.card V) (b : Base M)
    (P : Finset ↥(active b)) (y z t : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) (hP : P.card = r-2)
    (hl : (cutDeleted y l).card ≤ 2*(r-2)+3) :
    rootLinkDensity r y.val (deletedRootCollisions r y.val (exclusions hM b P y z t l)) ≤
      (2*M.card+3*r+2:ℕ)*(r-1:ℕ)/(Fintype.card V-1:ℕ) :=
  (deletedRootCollisions_density_le (by omega) hN y.val _
    (root_not_excluded hM b P y z t l)).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
        (exclusions_card_le hM hr b P y z t l hP hl)) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))

end LooseHamilton.BootstrapEndpointLiftedGeometry
