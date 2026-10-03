module

public import HittingTimeLooseHamilton.PrivateCoordinateMigration

public section

/-! # Deterministic private-coordinate mobility (Section 9)

All summands count actual mixed-cycle edge sets in the fixed host.  Labels use
unordered junction pairs; therefore the cached migration injection counts each
summand once.  The link-sampling hypothesis below is an explicit lower bound
on the number of legal good labels, not a hypothesis about the output count.
-/
noncomputable section
set_option maxHeartbeats 800000
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary root degree in the fixed allowed host. -/
@[expose] def migrationRootDegree (host : Finset (Finset V)) (x : V) : ℕ :=
  (host.filter fun e => x ∈ e).card

/-- The actual `X` summand in the private-coordinate injection. -/
@[expose] def privateMigrationSummand (r : ℕ) (markers host : Finset (Finset V))
    (D q : Finset V) (x : V) (a : Finset V × Finset V) : ℕ :=
  unrestrictedCycleCount r
    (restrictEdges (univ \ (D ∪ insert x a.1)) (insert a.2 (insert q markers)))
    (inducedHost (univ \ (D ∪ insert x a.1)) host)

/-- Sum any subfamily of actual legal private-migration summands. -/
theorem privateMigration_good_sum_le {r : ℕ} {markers host : Finset (Finset V)}
    {D q : Finset V} {x : V} (hr : 3 ≤ r)
    (hD : LegalPrivateCompletion r markers D q)
    (good : Finset (Finset V × Finset V))
    (hgood : good ⊆ privateMigrationLabels r markers host D q x) :
    ∑ a ∈ good, (privateMigrationSummand r markers host D q x a : ℝ) ≤
      completionCount r markers host D q := by
  have hsum : (∑ a ∈ good, privateMigrationSummand r markers host D q x a) ≤
      completionCount r markers host D q :=
    (Finset.sum_le_sum_of_subset hgood).trans (privateMigration_X_le hr hD)
  exact_mod_cast hsum

/-- A positive fraction of good root-link labels, each with its candidate
lower bound, yields the claimed degree-over-mean mobility factor.  The source
count is exactly `W_G(S ∪ {x};q)` and the target count is `W_G(S ∪ {t};q)`. -/
theorem private_coordinate_mobility {r : ℕ} {markers host : Finset (Finset V)}
    (S q : Finset V) (x t : V) (hr : 3 ≤ r)
    (hD : LegalPrivateCompletion r markers (insert t S) q)
    (good : Finset (Finset V × Finset V))
    (hgood : good ⊆ privateMigrationLabels r markers host (insert t S) q x)
    (κ lam μ : ℝ) (hlam : 0 ≤ lam) (hμ : 0 < μ)
    (hlink : κ * migrationRootDegree host x ≤ (good.card : ℝ))
    (hbalance : ∀ a ∈ good,
      lam * (completionCount r markers host (insert x S) q : ℝ) / μ ≤
        privateMigrationSummand r markers host (insert t S) q x a) :
    κ * lam * (migrationRootDegree host x : ℝ) / μ *
        (completionCount r markers host (insert x S) q : ℝ) ≤
      completionCount r markers host (insert t S) q := by
  have hb : 0 ≤ lam * (completionCount r markers host (insert x S) q : ℝ) / μ :=
    div_nonneg (mul_nonneg hlam (Nat.cast_nonneg _)) hμ.le
  calc
    _ = (κ * migrationRootDegree host x) *
        (lam * (completionCount r markers host (insert x S) q : ℝ) / μ) := by ring
    _ ≤ (good.card : ℝ) *
        (lam * (completionCount r markers host (insert x S) q : ℝ) / μ) :=
      mul_le_mul_of_nonneg_right hlink hb
    _ = ∑ _a ∈ good,
        lam * (completionCount r markers host (insert x S) q : ℝ) / μ := by simp
    _ ≤ ∑ a ∈ good,
        (privateMigrationSummand r markers host (insert t S) q x a : ℝ) :=
      Finset.sum_le_sum hbalance
    _ ≤ _ := privateMigration_good_sum_le hr hD good hgood

end LooseHamilton
