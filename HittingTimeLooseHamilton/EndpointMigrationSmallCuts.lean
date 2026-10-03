module

public import HittingTimeLooseHamilton.EndpointMigrationFamilies
public import HittingTimeLooseHamilton.MigrationWeightedTargets
public import HittingTimeLooseHamilton.MigrationCutScales

public section

/-! Small-cut removal for the actual endpoint partition, with a fixed
polynomial cutoff and an explicit vanishing relative loss. -/
noncomputable section
namespace LooseHamilton
open Finset Migration
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P U : Finset V} {y z : V}

@[expose] def endpointRetainedCuts (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) : Finset (EndpointMigrationCut r M G P y z) :=
  univ.filter (fun b =>
    (completionCount r M G P {y,z} : ℝ) / (Fintype.card V : ℝ)^(2*r+2) ≤
      endpointMigrationWeight b)

/-- Discarding all actual cut cores below `W/N^(2r+2)` loses at most
`((r-1)+(r-1)^2)*W/N^4`. No entropy or randomness hypothesis is needed. -/
theorem endpoint_small_cut_mass_le (hr : 3 ≤ r)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U) :
    (∑ b ∈ (univ : Finset (EndpointMigrationCut r M G P y z)).filter
      (fun b => endpointMigrationWeight b <
        (completionCount r M G P {y,z} : ℝ) / (Fintype.card V : ℝ)^(2*r+2)),
      endpointMigrationWeight b) ≤
      cutLoss r (Fintype.card V) * (completionCount r M G P {y,z} : ℝ) := by
  classical
  have hN : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  have hW : 0 ≤ (completionCount r M G P {y,z} : ℝ) := Nat.cast_nonneg _
  have hq : 0 ≤ (completionCount r M G P {y,z} : ℝ) /
      (Fintype.card V : ℝ)^(2*r+2) := div_nonneg hW (by positivity)
  have hsmall := small_cut_mass_le (univ : Finset (EndpointMigrationCut r M G P y z))
    endpointMigrationWeight _ hq
  have hy : y ∉ originalPorts M := fun hy => hports.root_ordinary (hports.old_ports hy)
  have hcount := endpoint_cut_count_polynomial (H := G) (P := P) (z := z) hr (Subset.refl _) 
    (hG.trans (by intro e he; exact (mem_filter.mp he).1)) hM hy
  have hcount' : (Fintype.card (EndpointMigrationCut r M G P y z) : ℝ) ≤
      cutLossCoefficient r * (Fintype.card V : ℝ)^(2*r-2) := by
    rw [endpointMigrationCut_card]
    unfold cutLossCoefficient
    exact_mod_cast hcount
  calc
    _ ≤ (Fintype.card (EndpointMigrationCut r M G P y z) : ℝ) *
        ((completionCount r M G P {y,z} : ℝ) / (Fintype.card V : ℝ)^(2*r+2)) := by
      simpa only [card_univ] using hsmall
    _ ≤ (cutLossCoefficient r * (Fintype.card V : ℝ)^(2*r-2)) *
        ((completionCount r M G P {y,z} : ℝ) / (Fintype.card V : ℝ)^(2*r+2)) :=
      mul_le_mul_of_nonneg_right hcount' hq
    _ = (cutLossCoefficient r * (Fintype.card V : ℝ)^(2*r-2) /
        (Fintype.card V : ℝ)^(2*r+2)) * (completionCount r M G P {y,z} : ℝ) := by ring
    _ = _ := by rw [polynomial_cut_loss_eq (by omega) hN]

/-- The retained actual cut cores carry a `1-cutLoss` fraction of the source. -/
theorem endpoint_retained_cut_mass_ge (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U)
    (hsize : 5 * (r - 1) < (univ \ P).card) :
    (1-cutLoss r (Fintype.card V)) * (completionCount r M G P {y,z} : ℝ) ≤
      ∑ b ∈ endpointRetainedCuts r M G P y z, endpointMigrationWeight b := by
  have hsmall := endpoint_small_cut_mass_le (P := P) hr hM hports hG
  have hsum := endpointMigrationWeight_sum hr hs hM hports hG hsize
  have hsplit := sum_filter_add_sum_filter_not
    (univ : Finset (EndpointMigrationCut r M G P y z))
    (fun b => endpointMigrationWeight b <
      (completionCount r M G P {y,z} : ℝ) / (Fintype.card V : ℝ)^(2*r+2))
    endpointMigrationWeight
  simp only [not_lt] at hsplit
  rw [hsum] at hsplit
  change _ ≤ ∑ b ∈ univ.filter _, endpointMigrationWeight b
  nlinarith

end LooseHamilton
