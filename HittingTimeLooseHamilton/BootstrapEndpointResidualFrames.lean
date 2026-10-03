module

public import HittingTimeLooseHamilton.BootstrapEndpointFrames
public import HittingTimeLooseHamilton.PrivateCompletionLifting

public section

/-! Actual endpoint core frames in either surviving base, constructed from
legal residual labels. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointResidualFrames
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]

@[expose] def liftLabelI (A : Finset V) (l : EndpointCutLabelI ↥A) : EndpointCutLabelI V :=
  (l.1.val, liftEdge A l.2)
@[expose] def liftLabelII (A : Finset V) (l : EndpointCutLabelII ↥A) : EndpointCutLabelII V :=
  (l.1.val, l.2.1.val, l.2.2.1.val, liftEdge A l.2.2.2.1, liftEdge A l.2.2.2.2)

private theorem mem_ports_restrict (A : Finset V) (M : Finset (Finset V)) (v : ↥A) :
    v ∈ originalPorts (restrictEdges A M) ↔ v.val ∈ originalPorts M := by
  simp only [originalPorts, restrictEdges, mem_biUnion, mem_image]
  constructor
  · rintro ⟨e, ⟨f,hf,rfl⟩, hv⟩
    exact ⟨f,hf,(mem_restrictEdge A f v).mp hv⟩
  · rintro ⟨f,hf,hv⟩
    exact ⟨restrictEdge A f, ⟨f,hf,rfl⟩, (mem_restrictEdge A f v).mpr hv⟩

omit [Fintype V] in
private theorem mem_lift (A : Finset V) (S : Finset ↥A) (v : ↥A) :
    v.val ∈ liftEdge A S ↔ v ∈ S := by
  simp [liftEdge, Subtype.val_injective.eq_iff]

private theorem lift_avoid (A : Finset V) (M : Finset (Finset V))
    (P Q T : Finset ↥A)
    (h : Disjoint Q (P ∪ originalPorts (restrictEdges A M) ∪ T)) :
    Disjoint (liftEdge A Q) (liftEdge A P ∪ originalPorts M ∪ liftEdge A T) := by
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hv
  apply disjoint_left.mp h ha
  simpa only [mem_union, mem_lift, ← mem_ports_restrict A M a] using hw

theorem cut_legalI_lift {r : ℕ} {A : Finset V} {M : Finset (Finset V)}
    {G : Finset (Finset ↥A)} {P : Finset ↥A} {y z : ↥A}
    {l : EndpointCutLabelI ↥A}
    (h : EndpointCutLegalI r (restrictEdges A M) G P y z l) :
    EndpointCutLegalI r M (G.image (liftEdge A)) (liftEdge A P)
      y.val z.val (liftLabelI A l) := by
  refine ⟨?_, by simpa [liftLabelI] using h.private_card, ?_, ?_⟩
  · simpa only [liftLabelI, mem_union, mem_lift, mem_insert, mem_singleton,
      Subtype.val_injective.eq_iff, ← mem_ports_restrict A M l.1] using h.endpoint_fresh
  · simpa [liftLabelI, liftEdge] using lift_avoid A M P l.2 {y,z,l.1} h.private_disjoint
  · have hh := mem_image_of_mem (liftEdge A) h.edge_mem
    simpa [EndpointCutLabelI.edge, liftLabelI, liftEdge, image_union] using hh

theorem cut_legalII_lift {r : ℕ} {A : Finset V} {M : Finset (Finset V)}
    (hM : ∀ m ∈ M, m ⊆ A)
    {G : Finset (Finset ↥A)} {P : Finset ↥A} {y z : ↥A}
    {l : EndpointCutLabelII ↥A}
    (h : EndpointCutLegalII r (restrictEdges A M) G P y z l) :
    EndpointCutLegalII r M (G.image (liftEdge A)) (liftEdge A P)
      y.val z.val (liftLabelII A l) := by
  refine ⟨?_, ?_, ?_, by simpa [liftLabelII] using h.first_private_card,
    by simpa [liftLabelII] using h.second_private_card, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := mem_image_of_mem (liftEdge A) h.oldMarker_mem
    rw [liftEdges_restrictEdges A M hM] at hh
    simpa [EndpointCutLabelII.oldMarker, liftLabelII] using hh
  · exact fun hh => h.ports_ne (Subtype.ext hh)
  · simpa only [liftLabelII, mem_union, mem_lift, mem_insert, mem_singleton,
      Subtype.val_injective.eq_iff, ← mem_ports_restrict A M l.2.2.1] using h.endpoint_fresh
  · exact (liftEdge_disjoint A _ _).mpr h.private_disjoint
  · simpa [liftLabelII, liftEdge] using
      lift_avoid A M P l.2.2.2.1 {y,z,l.2.2.1} h.first_private_disjoint
  · simpa [liftLabelII, liftEdge] using
      lift_avoid A M P l.2.2.2.2 {y,z,l.2.2.1} h.second_private_disjoint
  · have hh := mem_image_of_mem (liftEdge A) h.firstEdge_mem
    simpa [EndpointCutLabelII.firstEdge, liftLabelII, liftEdge, image_union] using hh
  · have hh := mem_image_of_mem (liftEdge A) h.secondEdge_mem
    simpa [EndpointCutLabelII.secondEdge, liftLabelII, liftEdge, image_union] using hh

theorem endpointI_core_exists {r : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    {G : Finset (Finset ↥(active b))} {P : Finset ↥(active b)}
    {y z : ↥(active b)} {l : EndpointCutLabelI ↥(active b)}
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z})
    (hl : EndpointCutLegalI r (restrictEdges (active b) (markers hM b)) G P y z l) :
    ∃ F : AuxiliaryFrame.Frame r M,
      F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y) ∧
      F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
        (liftEdge (active b)) ∧
      F.val.root = (l.1.val,z.val) ∧ F.val.relative = none := by
  have hs' := hs.lift
  rw [liftEdge_pair] at hs'
  have hl' := cut_legalI_lift hl
  have hp : ({l.1.val,z.val} : Finset V) ⊆ active b := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact l.1.property
    · exact (mem_singleton.mp hv) ▸ z.property
  obtain ⟨F,hd,hm,hroot,hrel⟩ := BootstrapEndpointFrames.endpointI_core_exists
    hM b hr hs' hl' hp
  refine ⟨F, ?_, ?_, hroot, hrel⟩
  · simpa [EndpointCutLabelI.deleted, liftLabelI, liftEdge_union, liftEdge, image_union] using hd
  · simpa [AuxiliaryFrame.Frame.markers, EndpointCutLabelI.markers, liftLabelI,
      liftEdges_restrictEdges (active b) (markers hM b) (fun _ h => markers_retained hM b h)]
      using hm

theorem endpointII_core_exists {r : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    {G : Finset (Finset ↥(active b))} {P : Finset ↥(active b)}
    {y z : ↥(active b)} {l : EndpointCutLabelII ↥(active b)}
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z})
    (hl : EndpointCutLegalII r (restrictEdges (active b) (markers hM b)) G P y z l) :
    ∃ F : AuxiliaryFrame.Frame r M,
      F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y) ∧
      F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
        (liftEdge (active b)) ∧
      F.val.root = (l.2.2.1.val,z.val) ∧ F.val.relative = none := by
  have hs' := hs.lift
  rw [liftEdge_pair] at hs'
  have hret : ∀ m ∈ markers hM b, m ⊆ active b := fun _ h => markers_retained hM b h
  have hl' := cut_legalII_lift hret hl
  have hp : ({l.2.2.1.val,z.val} : Finset V) ⊆ active b := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact l.2.2.1.property
    · exact (mem_singleton.mp hv) ▸ z.property
  obtain ⟨F,hd,hm,hroot,hrel⟩ := BootstrapEndpointFrames.endpointII_core_exists
    hM b hr hs' hl' hp
  refine ⟨F, ?_, ?_, hroot, hrel⟩
  · simpa [EndpointCutLabelII.deleted, liftLabelII, liftEdge, image_union] using hd
  · have he := Finset.image_erase (liftEdge_injective (active b))
      (restrictEdges (active b) (markers hM b)) l.oldMarker
    simp only [EndpointCutLabelII.markers, image_insert, he,
      liftEdges_restrictEdges (active b) (markers hM b) hret, liftEdge_pair]
    simpa [AuxiliaryFrame.Frame.markers, EndpointCutLabelII.markers, EndpointCutLabelII.oldMarker, liftLabelII] using hm

end LooseHamilton.BootstrapEndpointResidualFrames
