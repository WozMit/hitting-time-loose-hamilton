module

public import HittingTimeLooseHamilton.SequentialCompletionLabels

public section

/-! Quantitative bounds for the concrete completion-label decoders. -/
noncomputable section
namespace LooseHamilton.Migration.SequentialLabels
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Only successful prefixes require an estimate; choices and exception sets
may depend on the whole earlier history. -/
theorem failed_subset_bound {K : ℕ} {L : Type*} [DecidableEq L]
    (labels : Finset L) (forget : ChoicePath V K → L)
    (hsurj : ∀ l ∈ labels, ∃ p, forget p = l)
    (step : (k : ℕ) → ChoicePath V k → V → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ k < K, ∀ p, Successful step k p →
      ((univ.filter (fun v => ¬step k p v)).card:ℝ) ≤ ε*(Fintype.card V:ℝ))
    (good : L → Prop)
    (hgood : ∀ p, Successful step K p → good (forget p)) :
    ((labels.filter (fun l => ¬good l)).card:ℝ) ≤
      (K:ℝ)*ε*(Fintype.card V:ℝ)^K := by
  have hf := failed_labels_card_le labels forget good hsurj
  have hs : (univ.filter (fun p => ¬good (forget p))).card ≤
      (univ.filter (fun p => ¬Successful step K p)).card := by
    apply card_le_card
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact fun h => hp (hgood p h)
  exact (Nat.cast_le.mpr (hf.trans hs)).trans
    (sequential_failure_card_le_upto step ε hε K hstep)

/-- The ordinary schedule has exactly `d+2` moves.  The representation
hypothesis is merely the actual private-set cardinality, not an abstract map. -/
theorem ordinary_failed_subset_bound (d : ℕ) (labels : Finset (Finset V × V × V))
    (hlabels : ∀ l ∈ labels, l.1.card = d)
    (step : (k : ℕ) → ChoicePath V k → V → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ k < d+2, ∀ p, Successful step k p →
      ((univ.filter (fun v => ¬step k p v)).card:ℝ) ≤ ε*(Fintype.card V:ℝ))
    (weight : Finset V × V × V → ℝ) (cp ce B : ℝ)
    (hweight : ∀ p, Successful step (d+2) p →
      cp^d*ce^2*B ≤ weight (ordinaryForget d p)) :
    ((labels.filter (fun l => weight l < cp^d*ce^2*B)).card:ℝ) ≤
      ((d+2:ℕ):ℝ)*ε*(Fintype.card V:ℝ)^(d+2) := by
  have hsurj : ∀ l ∈ labels, ∃ p, ordinaryForget d p = l := by
    rintro ⟨P,y,z⟩ hl
    exact ordinaryForget_surjective P (hlabels _ hl) y z
  simpa only [not_le] using failed_subset_bound labels (ordinaryForget d) hsurj
    step ε hε hstep (fun l => cp^d*ce^2*B ≤ weight l) hweight

/-- The original-port schedule has `d+1` moves and retains the fixed endpoint. -/
theorem port_failed_subset_bound (d : ℕ) (z : V)
    (labels : Finset (Finset V × V × V))
    (hlabels : ∀ l ∈ labels, l.1.card = d ∧ l.2.2 = z)
    (step : (k : ℕ) → ChoicePath V k → V → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ k < d+1, ∀ p, Successful step k p →
      ((univ.filter (fun v => ¬step k p v)).card:ℝ) ≤ ε*(Fintype.card V:ℝ))
    (weight : Finset V × V × V → ℝ) (cp ce B : ℝ)
    (hweight : ∀ p, Successful step (d+1) p →
      cp^d*ce*B ≤ weight (portForget d z p)) :
    ((labels.filter (fun l => weight l < cp^d*ce*B)).card:ℝ) ≤
      ((d+1:ℕ):ℝ)*ε*(Fintype.card V:ℝ)^(d+1) := by
  have hsurj : ∀ l ∈ labels, ∃ p, portForget d z p = l := by
    rintro ⟨P,y,t⟩ hl
    obtain ⟨hP,rfl⟩ := hlabels _ hl
    exact portForget_surjective P hP y t
  simpa only [not_le] using failed_subset_bound labels (portForget d z) hsurj
    step ε hε hstep (fun l => cp^d*ce*B ≤ weight l) hweight

/-- Forbidden vertices and all repetitions cost only the proved lower-order
collision term, even after passing to the actual final-label family. -/
theorem collision_failed_subset_bound {K : ℕ} {L : Type*} [DecidableEq L]
    (labels : Finset L) (forget : ChoicePath V K → L)
    (hsurj : ∀ l ∈ labels, ∃ p, forget p = l)
    (forbidden : Finset V) (hN : 0 < Fintype.card V) (hK : 1 ≤ K)
    (good : L → Prop)
    (hgood : ∀ p, Successful
      (fun k p v => v ∉ forbidden ∪ pathVertices k p) K p → good (forget p)) :
    ((labels.filter (fun l => ¬good l)).card:ℝ) ≤
      (K:ℝ)*((forbidden.card:ℝ)+K)*(Fintype.card V:ℝ)^(K-1) := by
  have hf := failed_labels_card_le labels forget good hsurj
  have hs : (univ.filter (fun p => ¬good (forget p))).card ≤
      (univ.filter (fun p => ¬Successful
        (fun k p v => v ∉ forbidden ∪ pathVertices k p) K p)).card := by
    apply card_le_card
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact fun h => hp (hgood p h)
  exact (Nat.cast_le.mpr (hf.trans hs)).trans
    (collision_path_card_le forbidden K hN hK)

/-- Absolute per-step losses on a residual alphabet, measured against the
ambient order. This avoids confusing `N` with `N-1` in the deleted base. -/
theorem failed_subset_absolute_bound {K N : ℕ} {L : Type*} [DecidableEq L]
    (labels : Finset L) (forget : ChoicePath V K → L)
    (hsurj : ∀ l ∈ labels, ∃ p, forget p = l)
    (step : (k : ℕ) → ChoicePath V k → V → Prop)
    (B : ℝ) (hB : 0 ≤ B) (hV : 0 < Fintype.card V)
    (hN : Fintype.card V ≤ N) (hK : 1 ≤ K)
    (hstep : ∀ k < K, ∀ p, Successful step k p →
      ((univ.filter (fun v => ¬step k p v)).card:ℝ) ≤ B)
    (good : L → Prop)
    (hgood : ∀ p, Successful step K p → good (forget p)) :
    ((labels.filter (fun l => ¬good l)).card:ℝ) ≤
      (K:ℝ)*B*(N:ℝ)^(K-1) := by
  have hn : (0:ℝ) < Fintype.card V := Nat.cast_pos.mpr hV
  have hh := failed_subset_bound labels forget hsurj step
    (B / (Fintype.card V:ℝ)) (div_nonneg hB hn.le)
    (by simpa only [div_mul_cancel₀ _ hn.ne'] using hstep) good hgood
  have hp : (Fintype.card V:ℝ)^K =
      (Fintype.card V:ℝ)^(K-1)*(Fintype.card V:ℝ) := by
    rw [←pow_succ, Nat.sub_add_cancel hK]
  rw [hp] at hh
  have he : (K:ℝ)*(B/(Fintype.card V:ℝ))*
      ((Fintype.card V:ℝ)^(K-1)*(Fintype.card V:ℝ)) =
      (K:ℝ)*B*(Fintype.card V:ℝ)^(K-1) := by
    field_simp
    <;> ring
  rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) hB)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hN) _

end LooseHamilton.Migration.SequentialLabels
