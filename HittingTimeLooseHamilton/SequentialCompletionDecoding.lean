module

public import HittingTimeLooseHamilton.SequentialCompletionStates
public import HittingTimeLooseHamilton.SequentialCompletionCounting

public section

/-! The literal sequential state has the advertised completion label. -/
noncomputable section
namespace LooseHamilton.SequentialCompletion
open Finset Migration Migration.SequentialLabels
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem stateAt_chosen_coordinate {d : ℕ} (s : State V d) :
    ∀ k (hk : k ≤ d) (p : ChoicePath V k) (i : Fin k),
    (stateAt s k p).coords ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ = coordinates k p i := by
  intro k
  induction k with
  | zero => intro hk p i; exact Fin.elim0 i
  | succ k ih =>
    intro hk p i
    rcases p with ⟨p,v⟩
    have hkd : k < d := by omega
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [stateAt, advance, hkd, State.replacePrivate, coordinates]
    · have hn : (⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_succ_le hk)⟩ : Fin d) ≠
          ⟨k,hkd⟩ := by intro he; have := congrArg Fin.val he; simp only at this; omega
      simpa [stateAt, advance, hkd, State.replacePrivate, coordinates,
        Function.update_of_ne hn] using ih (Nat.le_of_succ_le hk) p j

theorem stateAt_private_coordinates {d : ℕ} (s : State V d) (p : ChoicePath V d) :
    (stateAt s d p).coords = coordinates d p := by
  funext i
  exact stateAt_chosen_coordinate s d le_rfl p i

theorem stateAt_private_endpoints {d : ℕ} (s : State V d) :
    ∀ k ≤ d, ∀ p : ChoicePath V k,
      (stateAt s k p).first = s.first ∧ (stateAt s k p).second = s.second := by
  intro k
  induction k with
  | zero => intro hk p; exact ⟨rfl,rfl⟩
  | succ k ih =>
    intro hk p
    have hkd : k < d := by omega
    simpa [stateAt, advance, hkd, State.replacePrivate] using
      ih (Nat.le_of_succ_le hk) p.1

/-- Actual set and ordered endpoints after all ordinary moves. -/
theorem ordinary_terminal_label {d : ℕ} (s : State V d) (p : ChoicePath V (d+2)) :
    ((stateAt s (d+2) p).block, (stateAt s (d+2) p).first,
      (stateAt s (d+2) p).second) = ordinaryForget d p := by
  rcases p with ⟨⟨p,y⟩,z⟩
  simp [stateAt, advance, State.replaceFirst, State.replaceSecond,
    State.block, ordinaryForget, stateAt_private_coordinates, pathVertices_eq_image]

/-- The original-port endpoint is retained after the shorter schedule. -/
theorem port_terminal_label {d : ℕ} (s : State V d) (p : ChoicePath V (d+1)) :
    ((stateAt s (d+1) p).block, (stateAt s (d+1) p).first,
      (stateAt s (d+1) p).second) = portForget d s.second p := by
  rcases p with ⟨p,y⟩
  have hs := (stateAt_private_endpoints s d le_rfl p).2
  simp [stateAt, advance, State.replaceFirst, State.block, portForget,
    stateAt_private_coordinates, pathVertices_eq_image, hs]

/-- No abstract weight representation is assumed: these are the literal
completion counts of the terminal state. -/
theorem ordinary_terminal_weight {d : ℕ} (s : State V d) (p : ChoicePath V (d+2))
    (r : ℕ) (M H : SimpleHypergraph V) :
    (stateAt s (d+2) p).weight r M H =
      completionCount r M H (ordinaryForget d p).1
        {(ordinaryForget d p).2.1,(ordinaryForget d p).2.2} := by
  have h := ordinary_terminal_label s p
  have hP := congrArg Prod.fst h
  have hy := congrArg (fun x : Finset V × V × V => x.2.1) h
  have hz := congrArg (fun x : Finset V × V × V => x.2.2) h
  simp only at hP hy hz
  simp only [State.weight,hP,hy,hz]

theorem port_terminal_weight {d : ℕ} (s : State V d) (p : ChoicePath V (d+1))
    (r : ℕ) (M H : SimpleHypergraph V) :
    (stateAt s (d+1) p).weight r M H =
      completionCount r M H (portForget d s.second p).1
        {(portForget d s.second p).2.1,(portForget d s.second p).2.2} := by
  have h := port_terminal_label s p
  have hP := congrArg Prod.fst h
  have hy := congrArg (fun x : Finset V × V × V => x.2.1) h
  have hz := congrArg (fun x : Finset V × V × V => x.2.2) h
  simp only at hP hy hz
  simp only [State.weight,hP,hy,hz]

/-- Every literal legal completion has an injectively ordered source state. -/
theorem exists_state_of_legal {d r : ℕ} (M : SimpleHypergraph V)
    (P : Finset V) (y z : V) (hP : P.card = d)
    (hs : LegalPrivateCompletion r M P {y,z}) :
    ∃ s : State V d, s.block = P ∧ s.first = y ∧ s.second = z ∧
      s.Valid (r := r) M := by
  let e := P.equivFinOfCardEq hP
  let f : Fin d → V := fun i => (e.symm i).val
  have hi : Function.Injective f := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hb : univ.image f = P := by
    ext v
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact (e.symm i).property
    · intro hv
      exact ⟨e ⟨v,hv⟩, by simp [f]⟩
  refine ⟨⟨f,y,z⟩, hb, rfl, rfl, hi, ?_⟩
  simpa only [State.block, hb] using hs

end LooseHamilton.SequentialCompletion
