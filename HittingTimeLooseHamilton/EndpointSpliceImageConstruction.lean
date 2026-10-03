module

public import HittingTimeLooseHamilton.EndpointSpliceImages
public import HittingTimeLooseHamilton.EndpointSpliceExchangeLegal
public import HittingTimeLooseHamilton.EndpointSpliceRestoreI
public import HittingTimeLooseHamilton.EndpointSpliceRestoreII

public section
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G F : Finset (Finset V)} {P : Finset V} {y z t : V}

/-- Construct the Type I splice image from every legal actual directed input. -/
theorem endpointSplice_image_I (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelI V} {b : EndpointSpliceInnerLabel V}
    (hl : EndpointCutLegalI r M G P y z l)
    (hb : EndpointSpliceLegalI r M G P y z t l b)
    (hF : F ∈ endpointSpliceInputFamilyI r M G P y z t l b) :
    Nonempty (EndpointSpliceImageI r M G P y z t l b F) := by
  obtain ⟨hcycle,hd⟩ := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp hF
  have hFG := ((mem_cycleOnFamily _ _ _ _ _).mp hcycle).2
  obtain ⟨C,hzero,hv,ha,ht⟩ := endpointSplice_exchange hr hs hM (Subset.refl M)
    hl.endpoint_fresh hb hd
  have hout := endpointSplice_restore_I hs hM hl hb C hzero hv ha ht
  rw [pair_comm b.2 y] at hout
  obtain ⟨D,hroot,hin,hout,hcut,hend⟩ := hout
  have hhost : endpointSpliceOutputI y l b F ⊆ G := by
    intro e he
    rcases mem_insert.mp he with rfl | he
    · exact hb.edge_mem
    · rcases mem_insert.mp he with rfl | he
      · exact hl.edge_mem
      · exact hFG he
  refine ⟨⟨D,hhost,hroot,hin,hout,hcut,?_⟩⟩
  apply (D.edgeEndpointPair_eq hr ⟨l.edge y,mem_insert_of_mem (mem_insert_self _ _)⟩).trans
  change {D.junction _, D.junction _} = {y,l.1}
  rw [hcut,hend]

/-- Construct the Type II splice image, restoring its original marked edge. -/
theorem endpointSplice_image_II (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    {l : EndpointCutLabelII V} {b : EndpointSpliceInnerLabel V}
    (hl : EndpointCutLegalII r M G P y z l)
    (hb : EndpointSpliceLegalII r M G P y z t l b)
    (hF : F ∈ endpointSpliceInputFamilyII r M G P y z t l b) :
    Nonempty (EndpointSpliceImageII r M G P y z t l b F) := by
  obtain ⟨hcycle,hd⟩ := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp hF
  have hFG := ((mem_cycleOnFamily _ _ _ _ _).mp hcycle).2
  obtain ⟨C,hzero,hv,ha,ht⟩ := endpointSplice_exchange hr hs hM (erase_subset _ _)
    hl.endpoint_fresh hb hd
  have hout := endpointSplice_restore_II hs hM hl hb C hzero hv ha ht
  rw [pair_comm b.2 y] at hout
  obtain ⟨D,hroot,hin,hout,hcut,hend,hsecond,hsecondend⟩ := hout
  have hhost : endpointSpliceOutputII y l b F ⊆ G := by
    intro e he
    rcases mem_insert.mp he with rfl | he
    · exact hb.edge_mem
    · rcases mem_insert.mp he with rfl | he
      · exact hl.firstEdge_mem
      · rcases mem_insert.mp he with rfl | he
        · exact hl.secondEdge_mem
        · exact hFG he
  refine ⟨⟨D,hhost,hroot,hin,hout,hcut,?_,?_⟩⟩
  · apply (D.edgeEndpointPair_eq hr ⟨l.firstEdge y,mem_insert_of_mem (mem_insert_self _ _)⟩).trans
    change {D.junction _, D.junction _} = {y,l.1}
    rw [hcut,hend]
  · apply (D.edgeEndpointPair_eq hr ⟨l.secondEdge,mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))⟩).trans
    change {D.junction _, D.junction _} = {l.2.1,l.2.2.1}
    rw [hsecond,hsecondend]
end LooseHamilton
