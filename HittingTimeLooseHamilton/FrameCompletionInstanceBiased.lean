module

public import HittingTimeLooseHamilton.FrameCompletionInstance

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

@[expose] def completionRoot (F : Frame r original) (c : Finset V × V × V) :
    ↥(F.completionMarkers c) := ⟨{c.2.1,c.2.2},mem_insert_self _ _⟩

@[expose] def completionNumberedRoot (F : Frame r original) (c : Finset V × V × V) :
    ↥(F.completionNumberedEdges c (F.completionMarkers c)) :=
  vertexEdgeEquiv (F.completionNumbering c) (restrictEdges (F.completionActive c) (F.completionMarkers c))
    (activeRestrictedMarker (F.completionActive c) (F.completionRoot c))

@[expose] def completionNumberedInitial (F : Frame r original) (c : Finset V × V × V)
    (hc : F.LegalCandidate c) : ↥(F.completionNumberedRoot c).val :=
  ⟨F.completionNumbering c ⟨c.2.1,F.completion_markers_supported hc _ (mem_insert_self _ _) (by simp)⟩,
    mem_image_of_mem _ ((mem_restrictEdge _ _ _).mpr (by simp [completionRoot]))⟩

/-- The law is the image of the uniform actual completion family. Every original
prescribed direction is retained in the underlying family; no retention estimate
or unrestricted-family substitution occurs. -/
@[expose] def completionEntropyInstance (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (hc : F.LegalCandidate c)
    (hY : (F.completionFamily H c).Nonempty) : BiasedRoleInstance r where
  N := (F.completionActive c).card
  host := F.completionNumberedEdges c (F.completionRawHost H c)
  markers := F.completionNumberedEdges c (F.completionMarkers c)
  host_uniform := F.completionNumberedEdges_uniform H c
  marked_matching := ((hc.1.augmented_matching F.property.matching).restrict _
    (F.completion_markers_supported hc)).vertexEdges (F.completionNumbering c)
  root := F.completionNumberedRoot c
  initial := F.completionNumberedInitial c hc
  cycleLaw := F.completionCycleLaw H c hY

@[simp] theorem completionEntropyInstance_N (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (hc : F.LegalCandidate c) (hY : (F.completionFamily H c).Nonempty) :
    (F.completionEntropyInstance H c hc hY).N=(F.completionActive c).card := rfl

@[simp] theorem completionEntropyInstance_s (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (hc : F.LegalCandidate c) (hY : (F.completionFamily H c).Nonempty) :
    (F.completionEntropyInstance H c hc hY).s=F.s+1 := by
  change (F.completionNumberedEdges c (F.completionMarkers c)).card=_
  rw [F.completionNumberedEdges_card _ _ (F.completion_markers_supported hc)]
  exact hc.1.augmented_card

@[simp] theorem completionEntropyInstance_mu (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (hc : F.LegalCandidate c) (hY : (F.completionFamily H c).Nonempty) :
    (F.completionEntropyInstance H c hc hY).μ =
      (r:ℝ)*(F.completionRawHost H c).card/(F.completionActive c).card := by
  unfold BiasedRoleInstance.μ
  change meanDegree (V:=Fin (F.completionActive c).card) r
    (F.completionNumberedEdges c (F.completionRawHost H c)).card=_
  rw [F.completionNumberedEdges_card c (F.completionRawHost H c) (fun _ he => (mem_filter.mp he).2)]
  simp [meanDegree]

@[simp] theorem completionEntropyInstance_entropy (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (hc : F.LegalCandidate c) (hY : (F.completionFamily H c).Nonempty) :
    FiniteEntropy.entropy (F.completionEntropyInstance H c hc hY).cycleLaw.mass =
      Real.log (F.completionCount H c) := F.completionCycleLaw_entropy H c hY

@[simp] theorem completionEntropyInstance_k (F : Frame r original) (hr : 3≤r)
    (H : SimpleHypergraph V) (hX : (F.cycleFamily H).Nonempty)
    (c : Finset V × V × V) (hc : F.LegalCandidate c) (hY : (F.completionFamily H c).Nonempty) :
    (F.completionEntropyInstance H c hc hY).k=F.k-1 := by
  obtain ⟨E,hE⟩ := hY
  obtain ⟨_,C,_⟩ := (F.mem_completionFamily H c E).mp hE
  have he := F.completion_edge_card hr hX hc hE
  have hv := C.vertex_card hr
  rw [he,hc.1.augmented_card] at hv
  change (F.active \ c.1).card=(r-1)*(F.k-1)+(F.s+1) at hv
  unfold BiasedRoleInstance.k ordinaryEdgeCount
  simp only [Fintype.card_fin]
  change ((F.completionActive c).card-
    (F.completionNumberedEdges c (F.completionMarkers c)).card)/(r-1)=_
  rw [F.completionNumberedEdges_card _ _ (F.completion_markers_supported hc)]
  change ((F.active \ c.1).card-(insert {c.2.1,c.2.2} F.markers).card)/(r-1)=_
  rw [hc.1.augmented_card,hv]
  change ((r-1)*(F.k-1)+(F.s+1)-(F.s+1))/(r-1)=_
  rw [Nat.add_sub_cancel,Nat.mul_div_right _ (by omega : 0<r-1)]
end LooseHamilton.AuxiliaryFrame.Frame
