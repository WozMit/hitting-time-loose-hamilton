module

public import HittingTimeLooseHamilton.EndpointCuts
public import HittingTimeLooseHamilton.EndpointSplicing

public section

/-! Actual source cuts and actual directed splice counts, with both geometric
cut types combined into one finite index type. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev EndpointMigrationCut (r : ℕ) (M G : Finset (Finset V)) (P : Finset V) (y z : V) :=
  {l // l ∈ endpointCutLabelsI r M G P y z} ⊕
    {l // l ∈ endpointCutLabelsII r M G P y z}

@[expose] def endpointMigrationWeight {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z : V} :
    EndpointMigrationCut r M G P y z → ℝ
  | .inl l => (endpointCutCoreFamilyI r M G P y z l.val).card
  | .inr l => (endpointCutCoreFamilyII r M G P y z l.val).card

@[expose] def endpointMigrationLabels {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z : V}
    (t : V) : EndpointMigrationCut r M G P y z → Finset (EndpointSpliceInnerLabel V)
  | .inl l => endpointSpliceLabelsI r M G P y z t l.val
  | .inr l => endpointSpliceLabelsII r M G P y z t l.val

@[expose] def endpointMigrationY {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z : V}
    (t : V) : EndpointMigrationCut r M G P y z → EndpointSpliceInnerLabel V → ℝ
  | .inl l => fun b => endpointSpliceYI r M G P y z t l.val b
  | .inr l => fun b => endpointSpliceYII r M G P y z t l.val b

theorem endpointMigrationWeight_nonneg {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z : V} (b : EndpointMigrationCut r M G P y z) :
    0 ≤ endpointMigrationWeight b := by
  cases b <;> exact Nat.cast_nonneg _

theorem endpointMigrationY_nonneg {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z : V} (t : V) (b : EndpointMigrationCut r M G P y z)
    (q : EndpointSpliceInnerLabel V) : 0 ≤ endpointMigrationY t b q := by
  cases b <;> exact Nat.cast_nonneg _

variable {r : ℕ} {M G : Finset (Finset V)} {P U : Finset V} {y z : V}

theorem endpointMigrationWeight_sum (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U)
    (hsize : 5 * (r - 1) < (univ \ P).card) :
    ∑ b : EndpointMigrationCut r M G P y z, endpointMigrationWeight b =
      (completionCount r M G P {y,z} : ℝ) := by
  rw [endpoint_cut_partition_families hr hs hM hports hG hsize]
  simp only [Fintype.sum_sum_type, endpointMigrationWeight, Nat.cast_add, Nat.cast_sum]
  congr 1
  · exact (Finset.sum_subtype (endpointCutLabelsI r M G P y z) (fun _ => Iff.rfl)
      (fun l => ((endpointCutCoreFamilyI r M G P y z l).card : ℝ))).symm
  · exact (Finset.sum_subtype (endpointCutLabelsII r M G P y z) (fun _ => Iff.rfl)
      (fun l => ((endpointCutCoreFamilyII r M G P y z l).card : ℝ))).symm

theorem endpointMigrationY_sum_le (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (t : V) :
    (∑ b : EndpointMigrationCut r M G P y z,
      ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q) ≤
      (completionCount r M G P {t,z} : ℝ) := by
  have h := endpoint_directed_splicing (G := G) (t := t) hr hs hM
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  simp only [Fintype.sum_sum_type, endpointMigrationLabels, endpointMigrationY]
  simp only [Nat.cast_add, Nat.cast_sum] at h'
  rw [Finset.sum_subtype (endpointCutLabelsI r M G P y z) (fun _ => Iff.rfl),
    Finset.sum_subtype (endpointCutLabelsII r M G P y z) (fun _ => Iff.rfl)] at h'
  exact h'

theorem endpointMigrationCut_card :
    Fintype.card (EndpointMigrationCut r M G P y z) =
      endpointCutLabelCount r M G P y z := by
  simp [EndpointMigrationCut, endpointCutLabelCount]

end LooseHamilton
