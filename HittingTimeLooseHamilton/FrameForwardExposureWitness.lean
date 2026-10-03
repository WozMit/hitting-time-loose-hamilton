module

public import HittingTimeLooseHamilton.FrameForwardExposureLaw
public import HittingTimeLooseHamilton.FrameForwardWitnessDefinitions

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameScales
variable {N r M : ℕ} {ell : Fin N→ℕ} {original : Finset (Finset (Fin N))}

/-- In a fixed complement record, this predicate depends only on the two
unexposed remainders and the removed batch. It retains the fixed allowed edges. -/
@[expose] def RecordForwardWitnessSuccess (f : Frame r original) (D : Finset (Fin N))
    (A0 B0 : SimpleHypergraph (Fin N)) (ell : Fin N→ℕ) (τ : ℕ)
    (F F0 T : SimpleHypergraph (Fin N)) : Prop :=
  let G := F∪(B0∩allowedUniverse f)
  let A := missingAbnormalEdges f D G
  (∀v,ell v≤vertexDegree (A0∪F0) v) ∧
  A⊆samplingUniverse f D\F ∧
  0<(samplingUniverse f D\F).card ∧
  alpha N/8*((samplingUniverse f D\F).card:ℝ)≤A.card ∧
  ((T∩A).card:ℝ)≤(alpha N)^2*τ

/-- Exact forward/reverse witness dictionary on every source in the record.
There is no further conditioning on regularity or on entropy. -/
theorem record_forward_witness_iff (f : Frame r original) (D : Finset (Fin N))
    (j : ℕ) (hMj : M≤j) (hj : j≤(completeEdges (Fin N) r).card)
    (A0 B0 T : SimpleHypergraph (Fin N)) (ω : Outcome (Fin N) r M ell)
    (he : EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω)
    (hT : T⊆unexposed f D (extensionState ω.1 ω.2 j)) :
    ForwardWitnessSuccess f D ω.1.val ell (extensionState ω.1 ω.2 j) T ↔
    RecordForwardWitnessSuccess f D A0 B0 ell (recordBatchSize f j B0)
      (unexposed f D (extensionState ω.1 ω.2 j)\T)
      (unexposed f D ω.1.val\T) T := by
  have hTU : T⊆samplingUniverse f D := hT.trans inter_subset_right
  unfold ForwardWitnessSuccess RecordForwardWitnessSuccess
  dsimp only
  rw [record_rawRemainder f D j A0 B0 T ω he,
    record_batchSize f D j hMj hj A0 B0 ω he,
    record_terminal_remainder f D j A0 B0 T ω he hTU]
  rfl
end LooseHamilton.CandidateBalance
