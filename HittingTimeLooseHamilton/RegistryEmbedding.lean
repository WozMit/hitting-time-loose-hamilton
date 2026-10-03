module

public import HittingTimeLooseHamilton.RootTestRegistry

public section

/-! Extending a fixed registry along an embedding preserves every registered
root test literally, including its outcome-dependent bad-set function. -/
noncomputable section
namespace LooseHamilton

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {I J : Type*} {r h : ℕ}

/-- Fill unused labels with fixed fallback tests. The choice of a preimage
uses only the embedding and label, never a random outcome. -/
@[expose] def extendRootRegistry (f : I ↪ J) (tests : I → RegisteredRootTest V r h)
    (fallback : J → RegisteredRootTest V r h) (j : J) : RegisteredRootTest V r h := by
  classical
  exact if hj : ∃ i, f i = j then tests (Classical.choose hj) else fallback j

@[simp] theorem extendRootRegistry_apply (f : I ↪ J)
    (tests : I → RegisteredRootTest V r h)
    (fallback : J → RegisteredRootTest V r h) (i : I) :
    extendRootRegistry f tests fallback (f i) = tests i := by
  classical
  unfold extendRootRegistry
  have hi : ∃ k, f k = f i := ⟨i, rfl⟩
  rw [dif_pos hi]
  exact congrArg tests (f.injective (Classical.choose_spec hi))

 theorem extendRootRegistry_unused (f : I ↪ J)
    (tests : I → RegisteredRootTest V r h)
    (fallback : J → RegisteredRootTest V r h) {j : J}
    (hj : ¬ ∃ i, f i = j) : extendRootRegistry f tests fallback j = fallback j := by
  classical
  exact dif_neg hj

/-- The common event for the larger fixed registry controls the original one. -/
theorem CommonRootTests.of_extension (f : I ↪ J)
    {tests : I → RegisteredRootTest V r h}
    {fallback : J → RegisteredRootTest V r h} {M : ℕ} {ell : V → ℕ} {c : ℝ}
    {ω : TerminalState V r M ell × MissingOrder V r M}
    (hω : CommonRootTests (extendRootRegistry f tests fallback) M ell c ω) :
    CommonRootTests tests M ell c ω := by
  intro i
  simpa only [extendRootRegistry_apply] using hω (f i)

/-- An adaptively chosen original label can be read through the extension. -/
theorem CommonRootTests.extension_selected (f : I ↪ J)
    {tests : I → RegisteredRootTest V r h}
    {fallback : J → RegisteredRootTest V r h} {M : ℕ} {ell : V → ℕ} {c : ℝ}
    (select : (TerminalState V r M ell × MissingOrder V r M) → I)
    {ω : TerminalState V r M ell × MissingOrder V r M}
    (hω : CommonRootTests (extendRootRegistry f tests fallback) M ell c ω) :
    ¬ (tests (select ω)).failure M ell c ω :=
  (hω.of_extension f).selected select

end LooseHamilton
