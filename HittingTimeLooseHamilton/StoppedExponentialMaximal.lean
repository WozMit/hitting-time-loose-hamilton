module

public import HittingTimeLooseHamilton.StoppedExponentialMGF

public section

noncomputable section
namespace LooseHamilton.StoppedExponential
open Finset
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

@[expose] def partialSum (d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := ∑ i ∈ range t, d i ω

@[expose] def running (d : ℕ → Ω → ℝ) (A : ℝ) (t : ℕ) (ω : Ω) : Prop :=
  ∀ i ≤ t, partialSum d i ω ≤ A

@[expose] def stopped (d : ℕ → Ω → ℝ) (A : ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | t+1, ω => stopped d A t ω + if running d A t ω then d t ω else 0

lemma partialSum_succ (d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    partialSum d (t+1) ω = partialSum d t ω + d t ω := by simp [partialSum, sum_range_succ]

lemma running_congr (d : ℕ → Ω → ℝ) (A : ℝ) (t : ℕ) (ω ω' : Ω)
    (h : ∀ i < t, d i ω = d i ω') :
    running d A t ω ↔ running d A t ω' := by
  have he : ∀ j ≤ t, partialSum d j ω = partialSum d j ω' := by
    intro j hj
    apply sum_congr rfl
    intro i hi
    exact h i (lt_of_lt_of_le (mem_range.mp hi) hj)
  constructor
  · intro hr j hj
    rw [← he j hj]
    exact hr j hj
  · intro hr j hj
    rw [he j hj]
    exact hr j hj

lemma stopped_congr (d : ℕ → Ω → ℝ) (A : ℝ) (t : ℕ) (ω ω' : Ω)
    (h : ∀ i < t, d i ω = d i ω') : stopped d A t ω = stopped d A t ω' := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp : ∀ i < t, d i ω = d i ω' := fun i hi => h i (by omega)
    simp only [stopped, ih hp, running_congr d A t ω ω' hp, h t (by omega)]

lemma stopped_eq_of_running (d : ℕ → Ω → ℝ) (A : ℝ) (t : ℕ) (ω : Ω)
    (h : running d A t ω) : stopped d A t ω = partialSum d t ω := by
  induction t with
  | zero => simp [stopped, partialSum]
  | succ t ih =>
    have hp : running d A t ω := fun i hi => h i (by omega)
    simp [stopped, hp, ih hp, partialSum_succ]

lemma stopped_gt_of_crossing (d : ℕ → Ω → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (t : ℕ) (ω : Ω) (h : ¬ running d A t ω) : A < stopped d A t ω := by
  classical
  induction t with
  | zero =>
    apply False.elim
    apply h
    intro i hi
    have hi0 : i = 0 := by omega
    simpa [hi0, partialSum] using hA
  | succ t ih =>
    by_cases hp : running d A t ω
    · have hx : A < partialSum d (t+1) ω := by
        by_contra hn
        apply h
        intro i hi
        by_cases hi' : i ≤ t
        · exact hp i hi'
        · have : i=t+1 := by omega
          simpa [this] using le_of_not_gt hn
      simpa [stopped, hp, stopped_eq_of_running d A t ω hp, partialSum_succ] using hx
    · simpa [stopped, hp] using ih hp

/-- Finite-history martingale differences. The two conditions say that previous increments
are observed, and that every nonnegative history-measurable multiplier has zero weighted drift. -/
structure Differences (p : FiniteEntropy.Law Ω) (d : ℕ → Ω → ℝ)
    (R : ℕ → Ω → Ω → Prop) (n : ℕ) : Prop where
  past : ∀ t < n, ∀ ω ω', R t ω ω' → ∀ i < t, d i ω = d i ω'
  cancel : ∀ t < n, ∀ f : Ω → ℝ, (∀ ω, 0 ≤ f ω) →
    (∀ ω ω', R t ω ω' → f ω = f ω') → ∑ ω, p.mass ω * f ω * d t ω = 0

lemma stopped_mgf (p : FiniteEntropy.Law Ω) (d : ℕ → Ω → ℝ)
    (R : ℕ → Ω → Ω → Prop) (n : ℕ) (hD : Differences p d R n)
    (b : ℕ → ℝ) (hb : ∀ i < n, 0 ≤ b i) (hd : ∀ i < n, ∀ ω, |d i ω| ≤ b i)
    (A lam : ℝ) :
    ∑ ω, p.mass ω * Real.exp (lam * stopped d A n ω) ≤
      Real.exp (lam^2 * (∑ i ∈ range n, (b i)^2) / 2) := by
  have hind : ∀ t ≤ n, ∑ ω, p.mass ω * Real.exp (lam * stopped d A t ω) ≤
      Real.exp (lam^2 * (∑ i ∈ range t, (b i)^2) / 2) := by
    intro t ht
    induction t with
    | zero => simpa [stopped] using le_of_eq p.total
    | succ t ih =>
      have htn : t<n := by omega
      have hip := ih (by omega)
      let f : Ω → ℝ := fun ω => Real.exp (lam * stopped d A t ω)
      let e : Ω → ℝ := fun ω => if running d A t ω then d t ω else 0
      have hz : ∑ ω, p.mass ω * f ω * e ω = 0 := by
        have hh := hD.cancel t htn (fun ω => if running d A t ω then f ω else 0)
          (fun ω => by split_ifs <;> positivity)
          (by
            intro ω ω' he
            have hp := hD.past t htn ω ω' he
            simp only [running_congr d A t ω ω' hp]
            simp [f, stopped_congr d A t ω ω' hp])
        convert hh using 1
        apply sum_congr rfl
        intro ω _
        dsimp [e]
        split_ifs <;> ring
      have hm := weighted_mgf p e f (b t) lam (hb t htn)
        (fun ω => (Real.exp_pos _).le)
        (fun ω => by dsimp [e]; split_ifs; exact hd t htn ω; simpa using hb t htn) hz
      calc
        _ = ∑ ω, p.mass ω * f ω * Real.exp (lam * e ω) := by
          apply sum_congr rfl
          intro ω _
          simp only [stopped, mul_add, Real.exp_add, f, e]
          ring
        _ ≤ (∑ ω, p.mass ω*f ω) * Real.exp (lam^2 * (b t)^2 / 2) := hm
        _ ≤ Real.exp (lam^2 * (∑ i ∈ range t, (b i)^2) / 2) *
            Real.exp (lam^2 * (b t)^2 / 2) :=
          mul_le_mul_of_nonneg_right hip (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add, sum_range_succ]; congr 1; ring
  exact hind n le_rfl

/-- Maximal Azuma bound under finite conditional mean-zero identities. -/
theorem maximal (p : FiniteEntropy.Law Ω) (d : ℕ → Ω → ℝ)
    (R : ℕ → Ω → Ω → Prop) (n : ℕ) (hD : Differences p d R n)
    (b : ℕ → ℝ) (hb : ∀ i < n, 0 ≤ b i) (hd : ∀ i < n, ∀ ω, |d i ω| ≤ b i)
    (A : ℝ) (hA : 0 < A) (hV : 0 < ∑ i ∈ range n, (b i)^2) :
    p.event (fun ω => ∃ t ≤ n, A < partialSum d t ω) ≤
      Real.exp (-A^2 / (2 * ∑ i ∈ range n, (b i)^2)) := by
  let V : ℝ := ∑ i ∈ range n, (b i)^2
  let lam : ℝ := A/V
  have hlam : 0 < lam := div_pos hA hV
  have hm := stopped_mgf p d R n hD b hb hd A lam
  have hmark : p.event (fun ω => ∃ t ≤ n, A < partialSum d t ω) * Real.exp (lam*A) ≤
      ∑ ω, p.mass ω * Real.exp (lam * stopped d A n ω) := by
    rw [FiniteEntropy.Law.event, sum_mul]
    apply sum_le_sum
    intro ω _
    split_ifs with h
    · have hn : ¬ running d A n ω := by obtain ⟨t,ht,hx⟩ := h; intro hr; exact not_lt_of_ge (hr t ht) hx
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (stopped_gt_of_crossing d A hA.le n ω hn).le hlam.le)) (p.nonneg ω)
    · exact le_of_eq_of_le (zero_mul _) (mul_nonneg (p.nonneg ω) (Real.exp_pos _).le)
  have hh := (le_div_iff₀ (Real.exp_pos (lam*A))).mpr (hmark.trans hm)
  convert hh using 1
  rw [← Real.exp_sub]
  congr 1
  dsimp [lam, V]
  field_simp
  <;> ring

end LooseHamilton.StoppedExponential
