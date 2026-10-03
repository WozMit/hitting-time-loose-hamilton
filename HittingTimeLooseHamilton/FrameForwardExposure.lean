module

public import HittingTimeLooseHamilton.CandidateRestrictedResampling
public import HittingTimeLooseHamilton.RestrictedHostBatchLaw
public import HittingTimeLooseHamilton.FrameRemainderParameters

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V→ℕ} {original : Finset (Finset V)}

/-- Each complement record fixes the residual population and the batch size. -/
@[expose] def recordBatchSize (f : Frame r original) (j : ℕ) (B0 : SimpleHypergraph V) : ℕ :=
  ⌊FrameScales.nu (Fintype.card V)*(j-B0.card:ℕ)/f.k⌋₊

theorem record_unexposed_card (f : Frame r original) (D : Finset V)
    (j : ℕ) (hMj : M≤j) (hj : j≤(completeEdges V r).card)
    (A0 B0 : SimpleHypergraph V) (ω : Outcome V r M ell)
    (he : EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω) :
    (unexposed f D (extensionState ω.1 ω.2 j)).card=j-B0.card := by
  change (extensionState ω.1 ω.2 j ∩ samplingUniverse f D).card=_
  rw [edgeComplement_card,extensionState_card _ _ _ hMj hj,he.2]

theorem record_batchSize (f : Frame r original) (D : Finset V)
    (j : ℕ) (hMj : M≤j) (hj : j≤(completeEdges V r).card)
    (A0 B0 : SimpleHypergraph V) (ω : Outcome V r M ell)
    (he : EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω) :
    batchSize f D (extensionState ω.1 ω.2 j)=recordBatchSize f j B0 := by
  unfold batchSize recordBatchSize
  rw [record_unexposed_card f D j hMj hj A0 B0 ω he]

theorem record_fixedAllowed (f : Frame r original) (D : Finset V)
    (j : ℕ) (A0 B0 : SimpleHypergraph V) (ω : Outcome V r M ell)
    (he : EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω) :
    fixedAllowed f D (extensionState ω.1 ω.2 j)=B0∩allowedUniverse f := by
  change (extensionState ω.1 ω.2 j \ samplingUniverse f D)∩allowedUniverse f=_
  rw [he.2]

theorem record_rawRemainder (f : Frame r original) (D : Finset V)
    (j : ℕ) (A0 B0 T : SimpleHypergraph V) (ω : Outcome V r M ell)
    (he : EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω) :
    rawRemainder f D (extensionState ω.1 ω.2 j) T=
      (unexposed f D (extensionState ω.1 ω.2 j)\T)∪(B0∩allowedUniverse f) := by
  rw [rawRemainder,record_fixedAllowed f D j A0 B0 ω he]

/-- The restricted no-deficit event is exactly feasibility of the original
terminal remainder, with all fixed terminal edges restored. -/
theorem record_terminal_remainder (f : Frame r original) (D : Finset V)
    (j : ℕ) (A0 B0 T : SimpleHypergraph V) (ω : Outcome V r M ell)
    (he : EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω)
    (hT : T⊆samplingUniverse f D) :
    A0∪(unexposed f D ω.1.val\T)=ω.1.val\T := by
  rw [←he.1]
  ext e
  simp only [unexposed,mem_union,mem_sdiff,mem_inter]
  constructor
  · rintro (⟨he,hn⟩ | ⟨⟨he,hu⟩,ht⟩)
    · exact ⟨he,fun ht=>hn (hT ht)⟩
    · exact ⟨he,ht⟩
  · rintro ⟨he,ht⟩
    by_cases hu : e∈samplingUniverse f D
    · exact Or.inr ⟨⟨he,hu⟩,ht⟩
    · exact Or.inl ⟨he,hu⟩

/-- A batch removed from J0 is contained in precisely the later reverse
universe U minus the unexposed current remainder. -/
theorem removed_subset_record_reverse (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T⊆unexposed f D H) :
    T⊆samplingUniverse f D\(unexposed f D H\T) := by
  intro e he
  exact mem_sdiff.mpr ⟨(mem_inter.mp (hT he)).2,fun hh=>(mem_sdiff.mp hh).2 he⟩
end LooseHamilton.CandidateBalance
