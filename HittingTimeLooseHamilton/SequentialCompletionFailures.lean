module

public import HittingTimeLooseHamilton.SequentialCompletionDecoding
public import HittingTimeLooseHamilton.SequentialCompletionPaths

public section

/-! Quantitative failed-label counts for the genuine completion-state schedule. -/
noncomputable section
namespace LooseHamilton.SequentialCompletion
open Finset Migration Migration.SequentialLabels
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem successful_product_lower {r : ℕ} (hr : 3 ≤ r) (s : State V (r-2))
    (M H : SimpleHypergraph V) (U : Finset V) (c : ℝ) (hc : 0<c)
    (k : ℕ) (p : ChoicePath V k) (hp : Successful (Step s M H U c) k p) :
    (∏ i ∈ range k, factor r c i) * (s.weight r M H:ℝ) ≤
      (stateAt s k p).weight r M H := by
  exact successful_value_lower (Step s M H U c)
    (fun k p => ((stateAt s k p).weight r M H:ℝ)) (factor r c)
    (s.weight r M H:ℝ) (factor_nonneg hr hc) (by intro p; rfl)
    (by intro k p v hp hv; exact step_weight s M H U c k p v hv) k p hp

theorem successful_ordinary_lower {r : ℕ} (hr : 3 ≤ r) (s : State V (r-2))
    (M H : SimpleHypergraph V) (U : Finset V) (c : ℝ) (hc : 0<c)
    (p : ChoicePath V (r-2+2)) (hp : Successful (Step s M H U c) (r-2+2) p) :
    BootstrapConstants.privateFactor r c ^ (r-2) *
      BootstrapConstants.endpointFactor r c ^ 2 * (s.weight r M H:ℝ) ≤
      completionCount r M H (ordinaryForget (r-2) p).1
        {(ordinaryForget (r-2) p).2.1,(ordinaryForget (r-2) p).2.2} := by
  have hh := successful_product_lower hr s M H U c hc _ p hp
  rw [ordinary_terminal_weight] at hh
  simpa only [factor, mobility_schedule_product] using hh

theorem successful_port_lower {r : ℕ} (hr : 3 ≤ r) (s : State V (r-2))
    (M H : SimpleHypergraph V) (U : Finset V) (c : ℝ) (hc : 0<c)
    (p : ChoicePath V (r-2+1)) (hp : Successful (Step s M H U c) (r-2+1) p) :
    BootstrapConstants.privateFactor r c ^ (r-2) *
      BootstrapConstants.endpointFactor r c * (s.weight r M H:ℝ) ≤
      completionCount r M H (portForget (r-2) s.second p).1
        {(portForget (r-2) s.second p).2.1,(portForget (r-2) s.second p).2.2} := by
  have hh := successful_product_lower hr s M H U c hc _ p hp
  rw [port_terminal_weight] at hh
  simpa only [factor, mobility_schedule_product, pow_one] using hh

/-- The ordinary branch counts actual private sets and ordered endpoints.
The step loss is absolute and can be measured in an ambient space larger
than the residual alphabet. -/
theorem ordinary_failed_labels {r N : ℕ} (hr : 3 ≤ r) (s : State V (r-2))
    (M H : SimpleHypergraph V) (U : Finset V) (c : ℝ) (hc : 0<c)
    (labels : Finset (Finset V × V × V))
    (hlabels : ∀ l ∈ labels, l.1.card = r-2)
    (B : ℝ) (hB : 0 ≤ B) (hV : 0 < Fintype.card V) (hN : Fintype.card V ≤ N)
    (hstep : ∀ k < r-2+2, ∀ p, Successful (Step s M H U c) k p →
      ((univ.filter (fun v => ¬Step s M H U c k p v)).card:ℝ) ≤ B) :
    ((labels.filter (fun l => (completionCount r M H l.1 {l.2.1,l.2.2}:ℝ) <
      BootstrapConstants.privateFactor r c ^ (r-2) *
        BootstrapConstants.endpointFactor r c ^ 2 * (s.weight r M H:ℝ))).card:ℝ) ≤
      (r:ℝ)*B*(N:ℝ)^(r-1) := by
  have hsurj : ∀ l ∈ labels, ∃ p, ordinaryForget (r-2) p = l := by
    rintro ⟨P,y,z⟩ hl
    exact ordinaryForget_surjective P (hlabels _ hl) y z
  have hh := failed_subset_absolute_bound labels (ordinaryForget (r-2)) hsurj
    (Step s M H U c) B hB hV hN (by omega : 1 ≤ r-2+2) hstep
    (fun l => BootstrapConstants.privateFactor r c ^ (r-2) *
      BootstrapConstants.endpointFactor r c ^ 2 * (s.weight r M H:ℝ) ≤
        (completionCount r M H l.1 {l.2.1,l.2.2}:ℝ))
    (successful_ordinary_lower hr s M H U c hc)
  have he : r-2+2=r := by omega
  simpa only [not_le,he] using hh

/-- The port branch retains its original endpoint and has one fewer move. -/
theorem port_failed_labels {r N : ℕ} (hr : 3 ≤ r) (s : State V (r-2))
    (M H : SimpleHypergraph V) (U : Finset V) (c : ℝ) (hc : 0<c)
    (labels : Finset (Finset V × V × V))
    (hlabels : ∀ l ∈ labels, l.1.card = r-2 ∧ l.2.2 = s.second)
    (B : ℝ) (hB : 0 ≤ B) (hV : 0 < Fintype.card V) (hN : Fintype.card V ≤ N)
    (hstep : ∀ k < r-2+1, ∀ p, Successful (Step s M H U c) k p →
      ((univ.filter (fun v => ¬Step s M H U c k p v)).card:ℝ) ≤ B) :
    ((labels.filter (fun l => (completionCount r M H l.1 {l.2.1,l.2.2}:ℝ) <
      BootstrapConstants.privateFactor r c ^ (r-2) *
        BootstrapConstants.endpointFactor r c * (s.weight r M H:ℝ))).card:ℝ) ≤
      ((r-1:ℕ):ℝ)*B*(N:ℝ)^(r-2) := by
  have hsurj : ∀ l ∈ labels, ∃ p, portForget (r-2) s.second p = l := by
    rintro ⟨P,y,z⟩ hl
    obtain ⟨hP,he⟩ := hlabels _ hl
    change z = s.second at he
    subst z
    exact portForget_surjective P hP y s.second
  have hh := failed_subset_absolute_bound labels (portForget (r-2) s.second) hsurj
    (Step s M H U c) B hB hV hN (by omega : 1 ≤ r-2+1) hstep
    (fun l => BootstrapConstants.privateFactor r c ^ (r-2) *
      BootstrapConstants.endpointFactor r c * (s.weight r M H:ℝ) ≤
        (completionCount r M H l.1 {l.2.1,l.2.2}:ℝ))
    (successful_port_lower hr s M H U c hc)
  have he : r-2+1=r-1 := by omega
  have he' : r-1-1=r-2 := by omega
  simpa only [not_le,he,he'] using hh

end LooseHamilton.SequentialCompletion
