module

public import HittingTimeLooseHamilton.RootTestRegistrations

public section

/-! The fixed validity gate vanishes for actual original-port sources. -/
noncomputable section
namespace LooseHamilton.BootstrapPortRegisteredDensity
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem badSet_eq (r h time : ℕ) (M J H : SimpleHypergraph V)
    (P : Finset V) (y z u : V) (c : ℝ)
    (hs : LegalPrivateCompletion r (M.erase {y,z}) P {u,z})
    (hy : y ∉ P ∪ {u,z}) (hm : {y,z} ∈ M) (hyz : y ≠ z) :
    (registerPortRootTest r h time M (originalPorts M) P y z u c).badSet (J,H) =
      rootFreePortBadSet r M (fixedPortHost H (originalPorts M))
        (originalPorts M) P y z u c := by
  classical
  ext e
  have hsubset := filter_subset (fun e =>
    e ∉ allowedEdges r (originalPorts M) ∨
      (¬ ∀ v ∈ e.erase y, LegalPrivateCompletion r (M.erase {y,z}) ((e.erase y).erase v) {v,z}) ∨
      (rootFreePortScore r M (fixedPortHost H (originalPorts M)) y z (e.erase y):ℝ) <
        c*rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u)
    (rootEdgeUniverse r y)
  have hvalid : LegalPrivateCompletion r (M.erase {y,z}) P {u,z} ∧
      y ∉ P ∪ {u,z} ∧ {y,z} ∈ M ∧ y ≠ z := ⟨hs,hy,hm,hyz⟩
  change e ∈ (rootEdgeUniverse r y).filter _ ↔ _
  constructor
  · intro he
    obtain ⟨_,hb⟩ := mem_filter.mp he
    exact hb.resolve_left (not_not.mpr hvalid)
  · intro he
    exact mem_filter.mpr ⟨hsubset he,Or.inr he⟩

theorem observed_badSet_eq (r h time : ℕ) (M J H : SimpleHypergraph V)
    (P : Finset V) (y z u : V) (c : ℝ)
    (hs : LegalPrivateCompletion r (M.erase {y,z}) P {u,z})
    (hy : y ∉ P ∪ {u,z}) (hm : {y,z} ∈ M) (hyz : y ≠ z) :
    (registerPortRootTest r h time M (originalPorts M) P y z u c).badSet
        (rootFreeEdges y J,rootFreeEdges y H) =
      rootFreePortBadSet r M (fixedPortHost H (originalPorts M))
        (originalPorts M) P y z u c := by
  rw [registerPortRootTest_observation]
  exact badSet_eq r h time M J H P y z u c hs hy hm hyz

end LooseHamilton.BootstrapPortRegisteredDensity
