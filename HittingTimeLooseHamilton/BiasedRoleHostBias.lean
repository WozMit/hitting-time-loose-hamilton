module

public import HittingTimeLooseHamilton.BiasedRoleJunctions
public import HittingTimeLooseHamilton.BiasedRoleShearer

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Host edges for which every role coordinate is outside the marked ports. -/
@[expose] def eligibleRoleEdges (markers G : SimpleHypergraph V) :=
  G.filter (fun e => Disjoint e (originalPorts markers))

/-- Regard an eligible edge as a set of nonport coordinates. -/
@[expose] def nonPortEdge (markers : SimpleHypergraph V) (e : Finset V) : Finset (NonPortVertex markers) :=
  univ.filter (fun v => v.val ∈ e)

lemma nonPortEdge_image {markers : SimpleHypergraph V} {e : Finset V}
    (he : Disjoint e (originalPorts markers)) :
    (nonPortEdge markers e).image Subtype.val = e := by
  classical
  ext v
  constructor
  · intro h
    obtain ⟨w,hw,rfl⟩ := mem_image.mp h
    simpa [nonPortEdge] using hw
  · intro hv
    have hp : v ∈ (univ : Finset V) \ originalPorts markers :=
      mem_sdiff.mpr ⟨mem_univ _, fun h => (disjoint_left.mp he) hv h⟩
    exact mem_image.mpr ⟨⟨v,hp⟩,by simpa [nonPortEdge] using hv,rfl⟩

lemma nonPortEdge_card {markers : SimpleHypergraph V} {e : Finset V}
    (he : Disjoint e (originalPorts markers)) : (nonPortEdge markers e).card=e.card := by
  have h := congrArg Finset.card (nonPortEdge_image he)
  rw [card_image_of_injective _ Subtype.val_injective] at h
  exact h

namespace ConnectedCloneCycle
variable {r : ℕ} {markers : SimpleHypergraph V}

@[expose] def junctionRoleProbability (root : ↥markers) (a : ↥root.val)
    (p : Law (ConnectedCloneCycle r markers)) (e : Finset V) (u v : V) : ℝ :=
  p.event (fun C => ∀ w ∈ e, w ∈ (role root a C).1 ↔ w=u ∨ w=v)

lemma junctionRoleProbability_nonPort (root : ↥markers) (a : ↥root.val)
    (p : Law (ConnectedCloneCycle r markers)) {e : Finset V}
    (he : Disjoint e (originalPorts markers)) (u v : NonPortVertex markers) :
    junctionRoleProbability root a p e u.val v.val =
      roleCompatibilityProbability p (junctionBits root a) (nonPortEdge markers e) u v := by
  classical
  rw [roleCompatibilityProbability_eq_event]
  unfold junctionRoleProbability
  apply congrArg p.event
  funext C
  apply propext
  constructor
  · intro h w
    have hw : w.val.val ∈ e := (mem_filter.mp w.property).2
    change decide (_ ∈ _) = decide (_ = _ ∨ _ = _)
    rw [decide_eq_decide]
    simpa only [Subtype.ext_iff] using h _ hw
  · intro h w hw
    have hp : w ∈ (univ : Finset V) \ originalPorts markers :=
      mem_sdiff.mpr ⟨mem_univ _, fun h => (disjoint_left.mp he) hw h⟩
    have hmem : (⟨w,hp⟩ : NonPortVertex markers) ∈ nonPortEdge markers e := by
      simpa [nonPortEdge] using hw
    have hh := h ⟨⟨w,hp⟩,hmem⟩
    change decide (w ∈ (role root a C).1) = decide ((⟨w,hp⟩ : NonPortVertex markers)=u ∨ (⟨w,hp⟩ : NonPortVertex markers)=v) at hh
    simpa only [decide_eq_decide, Subtype.ext_iff] using hh

lemma junctionRole_error_le (root : ↥markers) (a : ↥root.val)
    (p : Law (ConnectedCloneCycle r markers)) {e : Finset V}
    (he : Disjoint e (originalPorts markers)) {u v : V}
    (hu : u ∈ e) (hv : v ∈ e) (hne : u≠v)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |junctionRoleProbability root a p e u v-b^2*(1-b)^(e.card-2)| ≤
      coordinateMarginalError p (junctionBits root a) (fun _ => bernoulliBitLaw b hb0 hb1)
        (nonPortEdge markers e) := by
  have hup : u ∈ (univ : Finset V) \ originalPorts markers :=
    mem_sdiff.mpr ⟨mem_univ _, fun h => (disjoint_left.mp he) hu h⟩
  have hvp : v ∈ (univ : Finset V) \ originalPorts markers :=
    mem_sdiff.mpr ⟨mem_univ _, fun h => (disjoint_left.mp he) hv h⟩
  have hu' : (⟨u,hup⟩ : NonPortVertex markers) ∈ nonPortEdge markers e := by simpa [nonPortEdge] using hu
  have hv' : (⟨v,hvp⟩ : NonPortVertex markers) ∈ nonPortEdge markers e := by simpa [nonPortEdge] using hv
  have hh := roleCompatibility_error_le p (junctionBits root a) (nonPortEdge markers e)
    hu' hv' (fun h => hne (congrArg Subtype.val h)) b hb0 hb1
  rw [nonPortEdge_card he,← junctionRoleProbability_nonPort root a p he] at hh
  exact hh

/-- The actual eligible-host compatibility bias, using only the random nonport
junction coordinates and the degree bound in the original host. -/
theorem junctionRole_host_bias (root : ↥markers) (a : ↥root.val)
    (p : Law (ConnectedCloneCycle r markers)) (G : SimpleHypergraph V)
    (hG : ∀ e ∈ G, e.card=r) (D : ℝ) (hD : 0 ≤ D)
    (hdeg : ∀ v : V, (vertexDegree G v : ℝ) ≤ D)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (∑ e ∈ eligibleRoleEdges markers G, ∑ uv ∈ e.offDiag,
      |junctionRoleProbability root a p e uv.1 uv.2-b^2*(1-b)^(r-2)|) ≤
      (r*(r-1) : ℕ) * Real.sqrt (4*(G.card:ℝ)*D*
        coordinateDeficit p (junctionBits root a)
          (coordinateCrossEntropy p (junctionBits root a)
            (fun _ => bernoulliBitLaw b hb0.le hb1.le)) univ) := by
  classical
  let I := ↥(eligibleRoleEdges markers G)
  let q : NonPortVertex markers → Law Bool := fun _ => bernoulliBitLaw b hb0.le hb1.le
  let X := junctionBits (r:=r) root a
  let A : I → Finset (NonPortVertex markers) := fun e => nonPortEdge markers e.val
  let d : I → ℝ := fun e => coordinateMarginalError p X q (A e)
  let Δ := coordinateDeficit p X (coordinateCrossEntropy p X q) univ
  have hΔ : 0 ≤ Δ := by
    have hm := coordinateDeficit_mono p X (coordinateCrossEntropy p X q)
      (coordinateEntropy_singleton_le_crossEntropy p X q
        (fun _ => bernoulliBitLaw_pos hb0 hb1)) (empty_subset (univ : Finset (NonPortVertex markers)))
    rw [coordinateDeficit_empty] at hm
    exact hm
  have hdeg' (v : NonPortVertex markers) :
      (∑ e : I, if v ∈ A e then (1:ℝ) else 0) ≤ D := by
    change (∑ e : I, if v ∈ nonPortEdge markers e.val then (1:ℝ) else 0) ≤ D
    simp only [nonPortEdge, mem_filter, mem_univ, true_and]
    rw [sum_coe_sort (eligibleRoleEdges markers G) (fun e => if v.val ∈ e then (1:ℝ) else 0)]
    calc
      _ ≤ ∑ e ∈ G, if v.val ∈ e then (1:ℝ) else 0 := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro e _ _
        split_ifs <;> norm_num
      _ = (vertexDegree G v.val : ℝ) := by simp [vertexDegree, sum_boole]
      _ ≤ D := hdeg v.val
  have hs := coordinateMarginalError_sum_sq p X q
    (fun _ => bernoulliBitLaw_pos hb0 hb1) A D hD hdeg'
  have hcard : (Fintype.card I : ℝ) ≤ G.card := by
    exact_mod_cast (show Fintype.card I ≤ G.card by
      change Fintype.card ↥(eligibleRoleEdges markers G) ≤ G.card
      rw [Fintype.card_coe]
      exact card_le_card (filter_subset (fun e => Disjoint e (originalPorts markers)) G))
  have hm : 4*(Fintype.card I:ℝ)*D*Δ ≤ 4*(G.card:ℝ)*D*Δ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hD) hΔ
  have hb : (∑ e : I, d e) ≤ Real.sqrt (4*(G.card:ℝ)*D*Δ) :=
    Real.le_sqrt_of_sq_le (hs.trans hm)
  have hlocal (e : I) : (∑ uv ∈ e.val.offDiag,
      |junctionRoleProbability root a p e.val uv.1 uv.2-b^2*(1-b)^(r-2)|) ≤
      (r*(r-1):ℕ)*d e := by
    have he := mem_filter.mp e.property
    calc
      _ ≤ ∑ uv ∈ e.val.offDiag, d e := by
        apply sum_le_sum
        intro uv huv
        obtain ⟨hu,hv,hne⟩ := mem_offDiag.mp huv
        simpa only [hG e.val he.1] using junctionRole_error_le root a p he.2 hu hv hne b hb0.le hb1.le
      _ = _ := by
        rw [sum_const, nsmul_eq_mul, offDiag_card, hG e.val he.1]
        simp [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [← sum_coe_sort (eligibleRoleEdges markers G)]
  calc
    _ ≤ ∑ e : I, (r*(r-1):ℕ)*d e := sum_le_sum (fun e _ => hlocal e)
    _ = (r*(r-1):ℕ)*(∑ e : I, d e) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

end ConnectedCloneCycle
end LooseHamilton
