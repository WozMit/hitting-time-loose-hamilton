module

public import HittingTimeLooseHamilton.EndpointSpliceModels

public section

/-! # Recovering the input ordinary edge set by deleting the inserted edges -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z t : V}

@[expose] def endpointSpliceNewEdge (y : V) (b : EndpointSpliceInnerLabel V) : Finset V :=
  {y,b.2} ∪ b.1

@[expose] def endpointSpliceOutputI (y : V) (l : EndpointCutLabelI V)
    (b : EndpointSpliceInnerLabel V) (F : Finset (Finset V)) : Finset (Finset V) :=
  insert (endpointSpliceNewEdge y b) (insert (l.edge y) F)
@[expose] def endpointSpliceOutputII (y : V) (l : EndpointCutLabelII V)
    (b : EndpointSpliceInnerLabel V) (F : Finset (Finset V)) : Finset (Finset V) :=
  insert (endpointSpliceNewEdge y b) (insert (l.firstEdge y) (insert l.secondEdge F))

theorem endpointSpliceInputI_avoids_y {l : EndpointCutLabelI V}
    {b : EndpointSpliceInnerLabel V} {F : Finset (Finset V)}
    (hF : F ∈ endpointSpliceInputFamilyI r M G P y z t l b)
    {e : Finset V} (he : e ∈ F) : y ∉ e := by
  obtain ⟨hcycle,_⟩ := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp hF
  obtain ⟨⟨C⟩,_⟩ := (mem_cycleOnFamily _ _ _ _ _).mp hcycle
  intro hy
  have h := C.edge_subset_active he hy
  simpa [EndpointCutLabelI.deleted] using h

theorem endpointSpliceInputII_avoids_deleted {l : EndpointCutLabelII V}
    {b : EndpointSpliceInnerLabel V} {F : Finset (Finset V)}
    (hF : F ∈ endpointSpliceInputFamilyII r M G P y z t l b)
    {e : Finset V} (he : e ∈ F) {v : V} (hv : v ∈ l.deleted y) : v ∉ e := by
  obtain ⟨hcycle,_⟩ := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp hF
  obtain ⟨⟨C⟩,_⟩ := (mem_cycleOnFamily _ _ _ _ _).mp hcycle
  intro hve
  exact (mem_sdiff.mp (C.edge_subset_active he hve)).2
    (mem_union_left _ (mem_union_right _ hv))

private theorem union_sdiff_of_disjoint {α : Type*} [DecidableEq α]
    (K F : Finset α) (h : Disjoint K F) : (K ∪ F) \ K = F := by
  ext a
  simp only [mem_sdiff, mem_union]
  constructor
  · rintro ⟨hk | hf, hn⟩
    · exact False.elim (hn hk)
    · exact hf
  · intro hf
    exact ⟨Or.inr hf, fun hk => disjoint_left.mp h hk hf⟩

theorem endpointSpliceOutputI_recover {l : EndpointCutLabelI V}
    {b : EndpointSpliceInnerLabel V} {F : Finset (Finset V)}
    (hF : F ∈ endpointSpliceInputFamilyI r M G P y z t l b) :
    endpointSpliceOutputI y l b F \ {endpointSpliceNewEdge y b,l.edge y} = F := by
  have hn : endpointSpliceNewEdge y b ∉ F := fun he =>
    endpointSpliceInputI_avoids_y hF he (by simp [endpointSpliceNewEdge])
  have hc : l.edge y ∉ F := fun he =>
    endpointSpliceInputI_avoids_y hF he (by simp [EndpointCutLabelI.edge])
  have hdis : Disjoint ({endpointSpliceNewEdge y b,l.edge y} : Finset (Finset V)) F := by
    simp [disjoint_insert_left, disjoint_singleton_left, hn, hc]
  have h := union_sdiff_of_disjoint _ _ hdis
  simpa [endpointSpliceOutputI] using h

theorem endpointSpliceOutputII_recover {l : EndpointCutLabelII V}
    {b : EndpointSpliceInnerLabel V} {F : Finset (Finset V)}
    (hF : F ∈ endpointSpliceInputFamilyII r M G P y z t l b) :
    endpointSpliceOutputII y l b F \
      {endpointSpliceNewEdge y b,l.firstEdge y,l.secondEdge} = F := by
  have hn : endpointSpliceNewEdge y b ∉ F := fun he =>
    endpointSpliceInputII_avoids_deleted hF he (v := y) (by simp [EndpointCutLabelII.deleted])
      (by simp [endpointSpliceNewEdge])
  have hc : l.firstEdge y ∉ F := fun he =>
    endpointSpliceInputII_avoids_deleted hF he (v := y) (by simp [EndpointCutLabelII.deleted])
      (by simp [EndpointCutLabelII.firstEdge])
  have hd : l.secondEdge ∉ F := fun he =>
    endpointSpliceInputII_avoids_deleted hF he (v := l.2.1)
      (by simp [EndpointCutLabelII.deleted]) (by simp [EndpointCutLabelII.secondEdge])
  have hdis : Disjoint ({endpointSpliceNewEdge y b,l.firstEdge y,l.secondEdge} :
      Finset (Finset V)) F := by
    simp [disjoint_insert_left, disjoint_singleton_left, hn, hc, hd]
  have h := union_sdiff_of_disjoint _ _ hdis
  simpa [endpointSpliceOutputII] using h

end LooseHamilton
