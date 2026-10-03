module

public import HittingTimeLooseHamilton.PortContractionRootEdges
public import HittingTimeLooseHamilton.RootEventGoodLinks

public section

/-! Actual original-port source bounds from the registered root event and the
proved contraction partition. The density gate must still be established by
mobility before the common event can supply the root-test nonfailure. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The third registered test and the exact port partition give the claimed
lower bound on the total cycle count, with the degree of the raw host. -/
theorem port_source_bound_of_registered_test {r : ℕ} (hr : 3 ≤ r)
    (h time : ℕ) (M F H : SimpleHypergraph V) (P : Finset V) (y z u : V)
    (hyz : y ≠ z) (hm : {y,z} ∈ M)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hH : H ⊆ completeEdges V r) (hsize : 5*(r-1) < Fintype.card V)
    (c : ℝ) (hc : 0 ≤ c)
    (hn : ¬ RootLinkBad
      ((registerPortRootTest r h time M (originalPorts M) P y z u c).badSet (F,H))
      (vertexDegree H y) (F,H)) :
    (c/3)*(vertexDegree H y:ℝ)*
      (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ) ≤
      unrestrictedCycleCount r M (fixedPortHost H (originalPorts M)) := by
  classical
  let G := fixedPortHost H (originalPorts M)
  let Γ := (registerPortRootTest r h time M (originalPorts M) P y z u c).badSet (F,H)
  let good := rootGoodEdges H Γ y
  have hΓ : Γ ⊆ rootEdgeUniverse r y :=
    (registerPortRootTest r h time M (originalPorts M) P y z u c).bad_subset _
  have hG : G ⊆ allowedEdges r (originalPorts M) := by
    intro e he
    obtain ⟨heH,hp⟩ := mem_filter.mp he
    exact (mem_allowedEdges _ _ _).mpr ⟨(mem_completeEdges _ _).mp (hH heH),hp⟩
  have hgood : ∀ e ∈ good, e ∈ G.filter (y ∈ ·) ∧
      c*(rootFreePortSource r M G y z P u:ℝ) ≤
        (rootFreePortScore r M G y z (e.erase y):ℝ) := by
    intro e he
    obtain ⟨he,hnot⟩ := mem_sdiff.mp he
    obtain ⟨heH,hye⟩ := mem_filter.mp he
    have heroot : e ∈ rootEdgeUniverse r y :=
      (mem_rootEdgeUniverse _ _ _).mpr ⟨(mem_completeEdges _ _).mp (hH heH),hye⟩
    have hnb : e ∉ rootFreePortBadSet r M G (originalPorts M) P y z u c := by
      intro hb
      exact hnot (mem_filter.mpr ⟨heroot,Or.inr hb⟩)
    have hs := rootFreePort_good_score r M G (originalPorts M) P y z u c e heroot hnb
    exact ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨heH,((mem_allowedEdges _ _ _).mp hs.1).2⟩,hye⟩,hs.2.2⟩
  have hd : (vertexDegree H y:ℝ)/3 ≤ (good.card:ℝ) :=
    rootGoodEdges_card_lower r F H Γ y hΓ hn
  have hpart := original_port_partition_rootEdges hr M G y z hyz hm hM hG hsize
  calc
    _ = ((vertexDegree H y:ℝ)/3)*(c*(rootFreePortSource r M G y z P u:ℝ)) := by ring
    _ ≤ (good.card:ℝ)*(c*(rootFreePortSource r M G y z P u:ℝ)) :=
      mul_le_mul_of_nonneg_right hd (mul_nonneg hc (Nat.cast_nonneg _))
    _ = ∑ _e ∈ good, c*(rootFreePortSource r M G y z P u:ℝ) := by simp
    _ ≤ ∑ e ∈ good, (rootFreePortScore r M G y z (e.erase y):ℝ) :=
      sum_le_sum (fun e he => (hgood e he).2)
    _ ≤ ∑ e ∈ G.filter (y ∈ ·), (rootFreePortScore r M G y z (e.erase y):ℝ) :=
      sum_le_sum_of_subset_of_nonneg (fun e he => (hgood e he).1)
        (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by exact_mod_cast hpart.symm

/-- Positive root degree turns the partition lower bound into a source cap. -/
theorem port_source_cap_of_registered_test {r : ℕ} (hr : 3 ≤ r)
    (h time : ℕ) (M F H : SimpleHypergraph V) (P : Finset V) (y z u : V)
    (hyz : y ≠ z) (hm : {y,z} ∈ M)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hH : H ⊆ completeEdges V r) (hsize : 5*(r-1) < Fintype.card V)
    (c : ℝ) (hc : 0 < c) (hd : 0 < vertexDegree H y)
    (hn : ¬ RootLinkBad
      ((registerPortRootTest r h time M (originalPorts M) P y z u c).badSet (F,H))
      (vertexDegree H y) (F,H)) :
    (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ) ≤
      3*(unrestrictedCycleCount r M (fixedPortHost H (originalPorts M)):ℝ)/
        (c*(vertexDegree H y:ℝ)) := by
  have hb := port_source_bound_of_registered_test hr h time M F H P y z u hyz hm hM
    hH hsize c hc.le hn
  apply (le_div_iff₀ (mul_pos hc (Nat.cast_pos.mpr hd))).mpr
  nlinarith

end LooseHamilton
