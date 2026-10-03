module

public import HittingTimeLooseHamilton.EndpointMigrationSmallCuts
public import HittingTimeLooseHamilton.BootstrapMobilityConstants

public section

noncomputable section
namespace LooseHamilton.BootstrapEndpointWeightedAveraging
open Finset Migration
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P U : Finset V} {y z : V}

/-- The cutoff uses the ambient order even when `V` is a residual base. -/
@[expose] def ambientRetainedCuts (N r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) : Finset (EndpointMigrationCut r M G P y z) :=
  univ.filter (fun b => (completionCount r M G P {y,z} : ℝ) /
    (N : ℝ)^(2*r+2) ≤ endpointMigrationWeight b)

theorem ambient_small_cut_mass_le (N : ℕ) (hVN : Fintype.card V ≤ N)
    (hr : 3 ≤ r) (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U) :
    (∑ b ∈ (univ : Finset (EndpointMigrationCut r M G P y z)).filter
      (fun b => endpointMigrationWeight b <
        (completionCount r M G P {y,z} : ℝ) / (N : ℝ)^(2*r+2)),
      endpointMigrationWeight b) ≤
      cutLoss r N * (completionCount r M G P {y,z} : ℝ) := by
  classical
  have hN : 0 < N := (Fintype.card_pos_iff.mpr ⟨y⟩).trans_le hVN
  have hq : 0 ≤ (completionCount r M G P {y,z} : ℝ) / (N : ℝ)^(2*r+2) := by positivity
  have hsmall := small_cut_mass_le (univ : Finset (EndpointMigrationCut r M G P y z))
    endpointMigrationWeight _ hq
  have hy : y ∉ originalPorts M := fun hy => hports.root_ordinary (hports.old_ports hy)
  have hcount := endpoint_cut_count_polynomial (H := G) (P := P) (z := z) hr
    (Subset.refl _) (hG.trans (by intro e he; exact (mem_filter.mp he).1)) hM hy
  have hcount' : (Fintype.card (EndpointMigrationCut r M G P y z) : ℝ) ≤
      cutLossCoefficient r * (N : ℝ)^(2*r-2) := by
    rw [endpointMigrationCut_card]
    have hh : endpointCutLabelCount r M G P y z ≤
        ((r-1)+(r-1)^2)*N^(2*r-2) :=
      hcount.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hVN _))
    unfold cutLossCoefficient
    exact_mod_cast hh
  calc
    _ ≤ (Fintype.card (EndpointMigrationCut r M G P y z) : ℝ) *
        ((completionCount r M G P {y,z} : ℝ) / (N : ℝ)^(2*r+2)) := by
      simpa only [card_univ] using hsmall
    _ ≤ (cutLossCoefficient r * (N : ℝ)^(2*r-2)) *
        ((completionCount r M G P {y,z} : ℝ) / (N : ℝ)^(2*r+2)) :=
      mul_le_mul_of_nonneg_right hcount' hq
    _ = (cutLossCoefficient r * (N : ℝ)^(2*r-2) / (N : ℝ)^(2*r+2)) *
        (completionCount r M G P {y,z} : ℝ) := by ring
    _ = _ := by rw [polynomial_cut_loss_eq (by omega) hN]

theorem ambient_retained_cut_mass_ge (N : ℕ) (hVN : Fintype.card V ≤ N)
    (hr : 3 ≤ r) (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U)
    (hsize : 5*(r-1) < (univ \ P).card) :
    (1-cutLoss r N)*(completionCount r M G P {y,z} : ℝ) ≤
      ∑ b ∈ ambientRetainedCuts N r M G P y z, endpointMigrationWeight b := by
  have hsmall := ambient_small_cut_mass_le (P := P) N hVN hr hM hports hG
  have hsum := endpointMigrationWeight_sum hr hs hM hports hG hsize
  have hsplit := sum_filter_add_sum_filter_not
    (univ : Finset (EndpointMigrationCut r M G P y z))
    (fun b => endpointMigrationWeight b <
      (completionCount r M G P {y,z} : ℝ)/(N:ℝ)^(2*r+2)) endpointMigrationWeight
  simp only [not_lt] at hsplit
  rw [hsum] at hsplit
  change _ ≤ ∑ b ∈ univ.filter _, endpointMigrationWeight b
  nlinarith

/-- Actual directed summands are averaged with cut weights, not by taking a
union of cut exceptional sets. The host and target type may be residual. -/
theorem endpoint_from_cut_contributions (N : ℕ) (hVN : Fintype.card V ≤ N)
    (hr : 3 ≤ r) (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U)
    (hsize : 5*(r-1) < (univ \ P).card)
    (targets : Finset V) (bad : EndpointMigrationCut r M G P y z → V → Prop)
    [DecidableRel bad] (ε a : ℝ) (hε : 0 < ε) (ha : 0 ≤ a)
    (hbad : ∀ b ∈ ambientRetainedCuts N r M G P y z,
      ((targets.filter (bad b)).card : ℝ) ≤ ε^2*N)
    (hcontrib : ∀ b ∈ ambientRetainedCuts N r M G P y z,
      ∀ t ∈ targets, ¬bad b t → a*endpointMigrationWeight b ≤
        ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q) :
    ∃ exceptional : Finset V, exceptional ⊆ targets ∧
      (exceptional.card : ℝ) ≤ ε*N ∧
      ∀ t ∈ targets, t ∉ exceptional →
        a*(1-cutLoss r N-ε)*(completionCount r M G P {y,z} : ℝ) ≤
          (completionCount r M G P {t,z} : ℝ) := by
  classical
  let W : ℝ := completionCount r M G P {y,z}
  let cuts := ambientRetainedCuts N r M G P y z
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hW : 0 ≤ W := Nat.cast_nonneg _
  by_cases hz : W = 0
  · refine ⟨∅, empty_subset _, ?_, ?_⟩
    · simpa using mul_nonneg hε.le hN
    · intro t ht he
      change a*(1-cutLoss r N-ε)*W ≤ _
      rw [hz, mul_zero]
      exact Nat.cast_nonneg _
  have hp : 0 < W := lt_of_le_of_ne hW (Ne.symm hz)
  have hret := ambient_retained_cut_mass_ge N hVN hr hs hM hports hG hsize
  have hpartition := endpointMigrationWeight_sum hr hs hM hports hG hsize
  have hmass : ∑ b ∈ cuts, endpointMigrationWeight b ≤ W := by
    change _ ≤ (completionCount r M G P {y,z} : ℝ)
    rw [← hpartition]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun b _ _ => endpointMigrationWeight_nonneg b)
  let exceptional := targets.filter (fun t => ε*W <
    ∑ b ∈ cuts.filter (fun b => bad b t), endpointMigrationWeight b)
  refine ⟨exceptional, filter_subset _ _, ?_, ?_⟩
  · exact weighted_exceptional_targets cuts targets endpointMigrationWeight bad ε N W
      (fun b _ => endpointMigrationWeight_nonneg b) hε hN hp hbad hmass
  intro t ht hte
  have hsmall : (∑ b ∈ cuts.filter (fun b => bad b t), endpointMigrationWeight b) ≤ ε*W := by
    simpa only [exceptional, mem_filter, ht, true_and, not_lt] using hte
  have hgood := good_retained_mass_ge cuts endpointMigrationWeight (fun b => bad b t)
    (cutLoss r N) ε W hret hsmall
  calc
    _ = a*((1-cutLoss r N-ε)*W) := by ring
    _ ≤ a*∑ b ∈ cuts.filter (fun b => ¬bad b t), endpointMigrationWeight b :=
      mul_le_mul_of_nonneg_left hgood ha
    _ = ∑ b ∈ cuts.filter (fun b => ¬bad b t), a*endpointMigrationWeight b := by rw [mul_sum]
    _ ≤ ∑ b ∈ cuts.filter (fun b => ¬bad b t),
        ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q := by
      apply sum_le_sum
      intro b hb
      exact hcontrib b (mem_filter.mp hb).1 t ht (mem_filter.mp hb).2
    _ ≤ ∑ b : EndpointMigrationCut r M G P y z,
        ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun b _ _ => sum_nonneg (fun q _ => endpointMigrationY_nonneg t b q))
    _ ≤ _ := endpointMigrationY_sum_le hr hs hM t

/-- A fixed endpoint factor follows after the two independent mass losses
are bounded by one quarter. -/
theorem endpoint_fixed_factor (N : ℕ) (hVN : Fintype.card V ≤ N)
    (hr : 3 ≤ r) (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U)
    (hsize : 5*(r-1) < (univ \ P).card)
    (targets : Finset V) (bad : EndpointMigrationCut r M G P y z → V → Prop)
    [DecidableRel bad] (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (hδ : cutLoss r N ≤ 1/4) (he : ε ≤ 1/4)
    (hbad : ∀ b ∈ ambientRetainedCuts N r M G P y z,
      ((targets.filter (bad b)).card : ℝ) ≤ ε^2*N)
    (hcontrib : ∀ b ∈ ambientRetainedCuts N r M G P y z,
      ∀ t ∈ targets, ¬bad b t → BootstrapConstants.privateFactor r c*endpointMigrationWeight b ≤
        ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q) :
    ∃ exceptional : Finset V, exceptional ⊆ targets ∧
      (exceptional.card : ℝ) ≤ ε*N ∧
      ∀ t ∈ targets, t ∉ exceptional →
        BootstrapConstants.endpointFactor r c*(completionCount r M G P {y,z} : ℝ) ≤
          (completionCount r M G P {t,z} : ℝ) := by
  have ha := BootstrapConstants.privateFactor_pos hr hc
  obtain ⟨E, hE, hcard, htarget⟩ := endpoint_from_cut_contributions N hVN hr hs hM
    hports hG hsize targets bad ε (BootstrapConstants.privateFactor r c) hε ha.le hbad hcontrib
  refine ⟨E, hE, hcard, ?_⟩
  intro t ht hte
  apply le_trans _ (htarget t ht hte)
  have hh : (1/4:ℝ) ≤ 1-cutLoss r N-ε := by linarith
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh ha.le)
    (show 0 ≤ (completionCount r M G P {y,z} : ℝ) from Nat.cast_nonneg _)
  simpa only [BootstrapConstants.endpointFactor, div_eq_mul_inv, one_mul] using hm

/-- The useful application form accepts source-dependent exceptional sets
for each retained cut, and constructs the weighted exceptional set itself. -/
theorem endpoint_fixed_factor_of_cut_exceptions (N : ℕ) (hVN : Fintype.card V ≤ N)
    (hr : 3 ≤ r) (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U)
    (hsize : 5*(r-1) < (univ \ P).card)
    (targets : Finset V) (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (hδ : cutLoss r N ≤ 1/4) (he : ε ≤ 1/4)
    (hcuts : ∀ b ∈ ambientRetainedCuts N r M G P y z, ∃ E : Finset V,
      (E.card : ℝ) ≤ ε^2*N ∧ ∀ t ∈ targets, t ∉ E →
        BootstrapConstants.privateFactor r c*endpointMigrationWeight b ≤
          ∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q) :
    ∃ exceptional : Finset V, exceptional ⊆ targets ∧
      (exceptional.card : ℝ) ≤ ε*N ∧
      ∀ t ∈ targets, t ∉ exceptional →
        BootstrapConstants.endpointFactor r c*(completionCount r M G P {y,z} : ℝ) ≤
          (completionCount r M G P {t,z} : ℝ) := by
  classical
  let bad : EndpointMigrationCut r M G P y z → V → Prop := fun b t =>
    (∑ q ∈ endpointMigrationLabels t b, endpointMigrationY t b q) <
      BootstrapConstants.privateFactor r c*endpointMigrationWeight b
  apply endpoint_fixed_factor N hVN hr hs hM hports hG hsize targets bad ε c hε hc hδ he
  · intro b hb
    obtain ⟨E, hcard, hgood⟩ := hcuts b hb
    apply le_trans _ hcard
    apply Nat.cast_le.mpr
    apply card_le_card
    intro t ht
    obtain ⟨ht, hbad⟩ := mem_filter.mp ht
    by_contra hte
    exact (not_lt_of_ge (hgood t ht hte)) hbad
  · intro b hb t ht hgood
    exact not_lt.mp hgood

end LooseHamilton.BootstrapEndpointWeightedAveraging
