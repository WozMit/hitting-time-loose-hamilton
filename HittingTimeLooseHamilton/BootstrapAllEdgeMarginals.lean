module

public import HittingTimeLooseHamilton.PortMarginalCap
public import HittingTimeLooseHamilton.OriginalPortPartner

public section

/-! Finite assembly of the ordinary and original-port completion caps. All
edge sets are covered, including absent edges, forbidden edges and an empty
cycle family. -/
noncomputable section
namespace LooseHamilton.BootstrapAllEdgeMarginals
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The extension by zero for an empty family is also the actual marginal. -/
theorem marginal_zero_of_count_zero (r : ℕ) (M H : Finset (Finset V))
    (hX : cycleCount r M H (originalPorts M) = 0) (e : Finset V) :
    cycleMarginal r M H (originalPorts M) e = 0 := by
  unfold cycleMarginal FiniteFamily.marginal
  change _ / (cycleCount r M H (originalPorts M) : ℝ) = 0
  simp [hX]

omit [Fintype V] in
/-- A legal endpoint cut at an original marker gives exactly a legal port
source of the kind bounded by the port maximum theorem. -/
theorem port_label_legal {r : ℕ} {M G : Finset (Finset V)}
    (hM : IsPairMatching M) {y z : V} (hyz : y ≠ z) (hm : {y,z} ∈ M)
    {l : EndpointCutLabelI V} (hl : EndpointCutLegalI r (M.erase {y,z}) G ∅ y z l) :
    LegalPrivateCompletion r (M.erase {y,z}) l.2 {l.1,z} ∧
      y ∉ l.2 ∪ {l.1,z} := by
  have hf := hl.endpoint_fresh
  simp only [empty_union,mem_union,mem_insert,mem_singleton,not_or] at hf
  have hd := hl.private_disjoint
  simp only [empty_union] at hd
  have hz : z ∉ originalPorts (M.erase {y,z}) := by
    exact fun hz => disjoint_left.mp (port_pair_disjoint_remainder M y z hM.2 hm)
      (by simp) hz
  constructor
  · refine ⟨hl.private_card,by simp [hf.2.2],?_,?_⟩
    · apply disjoint_left.mpr
      intro v hv hpair
      exact disjoint_left.mp hd hv (mem_union_right _ (by simpa [pair_comm] using (mem_insert_of_mem hpair : v ∈ insert y {l.1,z})))
    · apply disjoint_left.mpr
      intro v hv hp
      rcases mem_union.mp hv with hv | hv
      · exact disjoint_left.mp hd hv (mem_union_left _ hp)
      · simp only [mem_insert,mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hf.1 hp
        · exact hz hp
  · simp only [mem_union,mem_insert,mem_singleton,not_or]
    refine ⟨?_,Ne.symm hf.2.1,hyz⟩
    exact fun hy => disjoint_left.mp hd hy (by simp)

/-- Uniform completion bounds imply the cap for every actual true-edge
marginal. The two-port-or-more case is forbidden by definition. -/
theorem all_edges_le {r : ℕ} {M H : Finset (Finset V)}
    (hr : 3 ≤ r) (hM : IsPairMatching M)
    (hsize : 5*(r-1) < Fintype.card V)
    (Do Dp μ : ℝ) (hDo : 0 ≤ Do) (hDp : 0 ≤ Dp) (hμ : 0 < μ)
    (hordinary : 0 < cycleCount r M H (originalPorts M) →
      ∀ (P : Finset V) (y z : V), LegalPrivateCompletion r M P {y,z} →
      (completionCount r M (H ∩ allowedEdges r (originalPorts M)) P {y,z}:ℝ) ≤
        Do*(cycleCount r M H (originalPorts M):ℝ)/μ)
    (hport : 0 < cycleCount r M H (originalPorts M) →
      ∀ (P : Finset V) (y z u : V),
      LegalPrivateCompletion r (M.erase {y,z}) P {u,z} →
      y ∉ P ∪ {u,z} → {y,z} ∈ M → y ≠ z →
      (rootFreePortSource r M (H ∩ allowedEdges r (originalPorts M)) y z P u:ℝ) ≤
        Dp*(cycleCount r M H (originalPorts M):ℝ)/μ) :
    ∀ e : Finset V, cycleMarginal r M H (originalPorts M) e ≤
      (r.choose 2:ℝ)*max Do Dp/μ := by
  classical
  intro e
  have hbound : 0 ≤ (r.choose 2:ℝ)*max Do Dp/μ :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hDp.trans (le_max_right _ _))) hμ.le
  by_cases hX : 0 < cycleCount r M H (originalPorts M)
  swap
  · rw [marginal_zero_of_count_zero r M H (by omega) e]
    exact hbound
  by_cases heH : e ∈ H
  swap
  · rw [cycleMarginal_absent r M H (originalPorts M) e heH]
    exact hbound
  by_cases heA : e ∈ allowedEdges r (originalPorts M)
  swap
  · rw [cycleMarginal_forbidden r M H (originalPorts M) e heA]
    exact hbound
  have he := ((mem_allowedEdges _ _ _).mp heA).1
  have hscaleO : Do*(cycleCount r M H (originalPorts M):ℝ)/μ ≤
      max Do Dp*(cycleCount r M H (originalPorts M):ℝ)/μ :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hμ.le
  have hscaleP : Dp*(cycleCount r M H (originalPorts M):ℝ)/μ ≤
      max Do Dp*(cycleCount r M H (originalPorts M):ℝ)/μ :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)) hμ.le
  by_cases hd : Disjoint e (originalPorts M)
  · apply cycleMarginal_avoiding_ports_le hr he heH hd (max Do Dp) μ hX
    intro q hq
    obtain ⟨hqsub,hqcard⟩ := mem_powersetCard.mp hq
    obtain ⟨y,z,hyz,rfl⟩ := card_eq_two.mp hqcard
    apply (hordinary hX (e \ {y,z}) y z ?_).trans hscaleO
    refine ⟨?_,by simp [hyz],sdiff_disjoint,?_⟩
    · rw [card_sdiff_of_subset hqsub,he]
      simp [hyz]
    · rw [sdiff_union_of_subset hqsub]
      exact hd
  · obtain ⟨y,hye,hyM⟩ := not_disjoint_iff.mp hd
    obtain ⟨z,hzy,hm⟩ := OriginalPortPartner.exists_partner hM ⟨y,hyM⟩
    unfold cycleMarginal
    rw [cycleFamily_eq_unrestricted_inter r M H (originalPorts M) hr]
    apply port_edge_marginal_le hr M (H ∩ allowedEdges r (originalPorts M))
      y z hzy.symm hm hM.2 inter_subset_right hsize e he hye (max Do Dp) μ
      (hDo.trans (le_max_left _ _)) hμ
    · rwa [←cycleCount_eq_unrestricted_inter r M H (originalPorts M) hr]
    · intro l hl _
      obtain ⟨hs,hy⟩ := port_label_legal hM hzy.symm hm hl
      simpa only [rootFreePortSource, ←cycleCount_eq_unrestricted_inter r M H (originalPorts M) hr] using
        (hport hX l.2 y z l.1 hs hy hm hzy.symm).trans hscaleP

end LooseHamilton.BootstrapAllEdgeMarginals
