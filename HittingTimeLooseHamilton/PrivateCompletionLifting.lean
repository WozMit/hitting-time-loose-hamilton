module

public import HittingTimeLooseHamilton.CompletionModels

public section

/-! Structural transport from a surviving vertex subtype. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lifting a legal private completion preserves all cardinality and
separation requirements against the ambient markers. -/
theorem LegalPrivateCompletion.lift {r : ℕ} {B : Finset V}
    {markers : Finset (Finset V)} {P q : Finset ↥B}
    (h : LegalPrivateCompletion r (restrictEdges B markers) P q) :
    LegalPrivateCompletion r markers (liftEdge B P) (liftEdge B q) := by
  refine ⟨by simpa using h.private_card, by simpa using h.pair_card,
    (liftEdge_disjoint B P q).mpr h.private_pair_disjoint, ?_⟩
  rw [← liftEdge_union]
  apply disjoint_left.mpr
  intro w hw hm
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hw
  obtain ⟨m, hm, ham⟩ := mem_biUnion.mp hm
  exact disjoint_left.mp h.ports_disjoint ha
    (mem_biUnion.mpr ⟨restrictEdge B m, mem_image_of_mem _ hm,
      (mem_restrictEdge B m a).mpr ham⟩)

/-- Allowedness transports using the fixed original ports, independently of
which auxiliary markers remain. -/
theorem liftEdge_mem_allowed_iff (r : ℕ) (B ports : Finset V)
    (e : Finset ↥B) :
    liftEdge B e ∈ allowedEdges r ports ↔
      e ∈ allowedEdges r (restrictedPorts B ports) := by
  rw [← inducedHost_allowed]
  simpa only [mem_inducedHost, ambientEdge_eq_liftEdge]

end LooseHamilton
