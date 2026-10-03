module

public import HittingTimeLooseHamilton.PortContractionLinkLabels

public section

/-! The exact original-port identity in its unordered-link form. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reindex a sum over cut labels by its link set and other junction. -/
theorem portCut_sum_links {r : ℕ} (hr : 2 ≤ r) (M G : Finset (Finset V))
    (y z : V) (hG : G ⊆ completeEdges V r) (f : EndpointCutLabelI V → ℕ) :
    ∑ l ∈ endpointCutLabelsI r M G ∅ y z, f l =
      ∑ A ∈ portLinkSets G (originalPorts (insert {y,z} M)) y,
        ∑ v ∈ A, f (v,A.erase v) := by
  classical
  rw [sum_sigma']
  apply sum_bij (fun l _ => ⟨insert l.1 l.2,l.1⟩)
  · intro l hl
    have h := portCutLabel_to_link ((mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hl)
    exact mem_sigma.mpr ⟨h.1, mem_insert_self _ _⟩
  · intro l hl k hk heq
    have hL := (portCutLabel_to_link ((mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hl)).2
    have hK := (portCutLabel_to_link ((mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hk)).2
    have h1 : l.1 = k.1 := congrArg Sigma.snd heq
    have h2 : insert l.1 l.2 = insert k.1 k.2 := congrArg Sigma.fst heq
    apply Prod.ext h1
    have he := congrArg (fun A : Finset V => A.erase l.1) h2
    have hK' : l.1 ∉ k.2 := h1 ▸ hK
    simpa only [← h1, erase_insert hL, erase_insert hK'] using he
  · intro a ha
    obtain ⟨hA,hv⟩ := mem_sigma.mp ha
    refine ⟨(a.2,a.1.erase a.2), ?_, ?_⟩
    · exact (mem_endpointCutLabelsI _ _ _ _ _ _ _).mpr (portLink_to_cutLabel hr hG _ hA _ hv)
    · simp only [insert_erase hv]
  · intro l hl
    have hn := (portCutLabel_to_link ((mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hl)).2
    simp only [erase_insert hn]

/-- Equation (portidentity): every actual original cycle has exactly one root
link and one other junction on its root-incident ordinary edge. -/
theorem original_port_partition {r : ℕ} (hr : 3 ≤ r)
    (M₀ G : Finset (Finset V)) (y z : V) (hyz : y ≠ z)
    (hm : {y,z} ∈ M₀) (hM : (M₀ : Set (Finset V)).PairwiseDisjoint id)
    (hG : G ⊆ allowedEdges r (originalPorts M₀))
    (hsize : 5 * (r-1) < Fintype.card V) :
    unrestrictedCycleCount r M₀ G =
      ∑ A ∈ portLinkSets G (originalPorts M₀) y,
        ∑ v ∈ A, rootFreePortCompletion r M₀ G y z (A.erase v) {v,z} := by
  rw [original_port_cut_partition hr M₀ G y z hyz hm hM hG hsize]
  have hG' : G ⊆ completeEdges V r := by
    intro e he
    exact (mem_completeEdges r e).mpr ((mem_allowedEdges r _ e).mp (hG he)).1
  rw [portCut_sum_links (by omega) _ _ y z hG']
  simp only [insert_erase hm]

end LooseHamilton
