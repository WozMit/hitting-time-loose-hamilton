module

public import HittingTimeLooseHamilton.BootstrapNestedDirectedRestriction
public import HittingTimeLooseHamilton.BootstrapBaseSourceDictionary
public import HittingTimeLooseHamilton.BootstrapEndpointFrameCounts

public section

/-! Exact base-subtype dictionaries for endpoint cores and directed candidates. -/
noncomputable section
namespace LooseHamilton.BootstrapBaseSourceDictionary
open Finset BootstrapBases AuxiliaryFrame
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

theorem frame_core_count_base (b : Base M) (F : Frame r M)
    (H : SimpleHypergraph V) (P : Finset V)
    (hd : F.val.deleted = deleted b ∪ P) (hrel : F.val.relative = none) :
    F.cycleCount H = cycleOnCount r (univ \ restrictEdge (active b) P)
      (restrictEdges (active b) F.markers) (host r H b) := by
  have hSA : F.active ⊆ active b := by
    intro v hv
    have hv' : v ∉ deleted b ∪ P := by
      simpa only [Frame.active, Code.active, hd, mem_sdiff, mem_univ, true_and] using hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun h => hv' (mem_union_left _ h)⟩
  rw [F.cycleCount_no_relative hrel H]
  have hc := cycleOnCount_restrictWithin r F.active (active b) hSA F.markers
    (H ∩ allowedEdges r (originalPorts M))
    (fun e he => (F.property.retained e he).trans hSA)
  simpa only [Frame.active,Code.active,hd,restrict_base_active,host] using hc

/-- Both directed starts and the entire original-port filter survive restriction
to the original base. This is equality of actual counts, with no factor two. -/
theorem frame_relative_count_base (b : Base M) (F : Frame r M)
    (H : SimpleHypergraph V) (P : Finset V) (q : V × V)
    (hd : F.val.deleted = deleted b ∪ P) (hrel : F.val.relative = some q)
    (ha : F.val.root.1 ∈ active b) (hy : q.1 ∈ active b) :
    F.cycleCount H = directedCycleOnCount r (univ \ restrictEdge (active b) P)
      (restrictEdges (active b) F.markers) (host r H b)
      (activeRestrictedMarker (active b)
        ⟨{F.val.root.1,F.val.root.2},F.property.root_mem⟩)
      (activeRestrictedMarker (active b)
        ⟨{q.1,q.2},F.property.relative_mem q (by simp [hrel])⟩)
      ⟨F.val.root.1,ha⟩ ⟨q.1,hy⟩ := by
  have hSA : F.active ⊆ active b := by
    intro v hv
    have hv' : v ∉ deleted b ∪ P := by
      simpa only [Frame.active,Code.active,hd,mem_sdiff,mem_univ,true_and] using hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun h => hv' (mem_union_left _ h)⟩
  rw [F.cycleCount_relative_some q hrel H]
  have hc := directedCycleOnCount_restrictWithin (r := r) (active b) F.active hSA F.markers
    (H ∩ allowedEdges r (originalPorts M)) F.property.retained
    ⟨{F.val.root.1,F.val.root.2},F.property.root_mem⟩
    ⟨{q.1,q.2},F.property.relative_mem q (by simp [hrel])⟩
    ⟨F.val.root.1,ha⟩ ⟨q.1,hy⟩
  simpa only [Frame.active,Code.active,hd,restrict_base_active,host] using hc

end LooseHamilton.BootstrapBaseSourceDictionary
