module

public import HittingTimeLooseHamilton.FrameEntropyBiasedInstance
public import HittingTimeLooseHamilton.CandidateBalanceSpecification

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ} {original : Finset (Finset V)}

/-- The active raw host is precisely the inherited fixed-original-port host. -/
lemma restrict_rawHost_eq_fixedPortHost (F : Frame r original)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) :
    restrictEdges F.active (F.rawHost H) =
      fixedPortHost (inducedHost F.active H)
        (restrictedPorts F.active (originalPorts original)) := by
  ext e
  have hactive : liftEdge F.active e ⊆ F.active := liftEdge_subset _ _
  have hmem : e ∈ restrictEdges F.active (F.rawHost H) ↔
      liftEdge F.active e ∈ F.rawHost H := by
    constructor
    · intro he
      obtain ⟨a,ha,rfl⟩ := mem_image.mp he
      simpa only [lift_restrictEdge _ _ (mem_filter.mp ha).2] using ha
    · intro he
      exact mem_image.mpr ⟨liftEdge F.active e, he, restrict_liftEdge _ _⟩
  rw [hmem]
  have hi : (e ∩ restrictedPorts F.active (originalPorts original)).card =
      (liftEdge F.active e ∩ originalPorts original).card := by
    rw [← ambientEdge_card F.active (e ∩ _), ambientEdge_inter_ports,
      ambientEdge_eq_liftEdge]
  simp only [rawHost, mem_filter, mem_inter, mem_allowedEdges, fixedPortHost,
    mem_inducedHost, ambientEdge_eq_liftEdge, hi]
  constructor
  · rintro ⟨⟨he,hr,hp⟩,hs⟩
    exact ⟨he,hp⟩
  · rintro ⟨he,hp⟩
    exact ⟨⟨he,(mem_completeEdges _ _).mp (hH he),hp⟩,hactive⟩

/-- The inherited regularity event supplies the actual numbered entropy host's
upper degree, codegree, and partition estimates with the same constants. -/
theorem entropyInstance_inherited_regular (F : Frame r original)
    (j h : ℕ) (c C L : ℝ) (ω : CandidateBalance.Outcome V r M ell)
    (hh : 4*r ≤ h)
    (hreg : CandidateBalance.InheritedRegularity original j h c C L ω)
    (hcycles : (F.cycleFamily (extensionState ω.1 ω.2 j)).Nonempty) :
    PathGraphUpperRegular r C L
      (F.entropyInstance (extensionState ω.1 ω.2 j) hcycles).host := by
  have hs := hreg.2.2.2 F.val.deleted (F.val.deleted_card_le.trans hh)
  change PathGraphUpperRegular r C L
    (fixedPortHost (inducedHost F.active (extensionState ω.1 ω.2 j))
      (restrictedPorts F.active (originalPorts original))) at hs
  rw [← F.restrict_rawHost_eq_fixedPortHost _ (extensionState_subset _ _ _)] at hs
  exact hs.vertexEdges F.vertexNumbering

end LooseHamilton.AuxiliaryFrame.Frame
