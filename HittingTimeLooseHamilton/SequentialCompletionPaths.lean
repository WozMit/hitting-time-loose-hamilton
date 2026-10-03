module

public import HittingTimeLooseHamilton.SequentialCompletionMoves

public section

noncomputable section
namespace LooseHamilton.SequentialCompletion
open Finset Migration BootstrapBases
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def factor (r : ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  if k<r-2 then BootstrapConstants.privateFactor r c else BootstrapConstants.endpointFactor r c

@[expose] def Step {r : ℕ} (s : State V (r-2)) (M H : SimpleHypergraph V) (U : Finset V)
    (c : ℝ) (k : ℕ) (p : ChoicePath V k) (v : V) : Prop :=
  let a := stateAt s k p
  let t := advance k a v
  t.Valid (r := r) M ∧ EndpointSourcePorts U M t.first t.second ∧
    factor r c k * (a.weight r M H:ℝ) ≤ t.weight r M H

theorem successful_valid {r : ℕ} (s : State V (r-2)) (M H : SimpleHypergraph V)
    (U : Finset V) (c : ℝ) (hs : s.Valid (r := r) M)
    (hp : EndpointSourcePorts U M s.first s.second) :
    ∀ k (p : ChoicePath V k), Successful (Step s M H U c) k p →
      (stateAt s k p).Valid (r := r) M ∧
      EndpointSourcePorts U M (stateAt s k p).first (stateAt s k p).second := by
  intro k
  cases k with
  | zero => intro p _; exact ⟨hs,hp⟩
  | succ k => intro p h; exact ⟨h.2.1,h.2.2.1⟩

theorem successful_floor {r : ℕ} (hr : 3 ≤ r) (s : State V (r-2))
    (M H : SimpleHypergraph V) (U : Finset V) (c : ℝ) (hc : 0<c) :
    ∀ k (p : ChoicePath V k), Successful (Step s M H U c) k p →
      BootstrapConstants.mobilityFloor r c ^ k * (s.weight r M H:ℝ) ≤
        (stateAt s k p).weight r M H := by
  intro k
  induction k with
  | zero => intro p _; simp
  | succ k ih =>
    intro p hp
    have hi := ih p.1 hp.1
    have hf : BootstrapConstants.mobilityFloor r c ≤ factor r c k := by
      dsimp [factor]; split_ifs
      · exact (BootstrapConstants.mobilityFloor_bounds r c).2.1
      · exact (BootstrapConstants.mobilityFloor_bounds r c).2.2
    have hh := mul_le_mul_of_nonneg_left hi (BootstrapConstants.mobilityFloor_pos hr hc).le
    have hh' := mul_le_mul_of_nonneg_right hf
      (Nat.cast_nonneg ((stateAt s k p.1).weight r M H): (0:ℝ) ≤ _)
    have hm := hp.2.2.2
    change _ ≤ ((advance k (stateAt s k p.1) p.2).weight r M H:ℝ)
    rw [pow_succ]
    nlinarith

/-- The value condition in the step relation is the exact literal-count
condition required by the cached multiplicative path lemma. -/
theorem step_weight {r : ℕ} (s : State V (r-2)) (M H : SimpleHypergraph V)
    (U : Finset V) (c : ℝ) (k : ℕ) (p : ChoicePath V k) (v : V)
    (hp : Step s M H U c k p v) :
    factor r c k * ((stateAt s k p).weight r M H:ℝ) ≤
      (stateAt s (k+1) (p,v)).weight r M H := hp.2.2

theorem factor_nonneg {r : ℕ} (hr : 3 ≤ r) {c : ℝ} (hc : 0<c) (k : ℕ) :
    0 ≤ factor r c k := by
  dsimp [factor]; split_ifs
  · exact (BootstrapConstants.privateFactor_pos hr hc).le
  · exact (BootstrapConstants.endpointFactor_pos hr hc).le

end LooseHamilton.SequentialCompletion
