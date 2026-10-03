module

public import HittingTimeLooseHamilton.UniformFiberBound
public import HittingTimeLooseHamilton.AssociationModels

public section
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma sum_vertexDegree_eq {r : ℕ} {F : SimpleHypergraph V}
    (hF : F ⊆ completeEdges V r) : ∑ v, vertexDegree F v = F.card*r := by
  calc
    _ = ∑ v, ∑ e ∈ F, if v ∈ e then 1 else 0 := by simp [vertexDegree, sum_boole]
    _ = ∑ e ∈ F, ∑ v, if v ∈ e then 1 else 0 := sum_comm
    _ = ∑ e ∈ F, e.card := by simp
    _ = _ := by
      have hh : ∀ e ∈ F, e.card = r := fun e he => (mem_filter.mp (hF he)).2
      simp_rw [sum_congr rfl (fun e he => hh e he)]
      simp

/-- Prescribing all degrees inside the terminal family gives exactly the
unrestricted fixed-degree family; the edge count follows from the degree sum. -/
@[expose] def terminalDegreeFiberEquiv (r M : ℕ) (hr : 0 < r) (ell : V → ℕ)
    (d : V → ℕ) (F₀ : TerminalState V r M ell)
    (hd : (fun v => vertexDegree F₀.val v) = d) :
    {F : TerminalState V r M ell // (fun v => vertexDegree F.val v) = d} ≃
      FixedDegreeState V r d where
  toFun F := ⟨F.val.val,F.val.property.1,fun v => congrFun F.property v⟩
  invFun F := by
    have hcard : F.val.card = M := by
      have he : F.val.card*r = F₀.val.card*r := by
        rw [← sum_vertexDegree_eq F.property.1,← sum_vertexDegree_eq F₀.property.1]
        apply sum_congr rfl
        intro v _
        exact (F.property.2 v).trans (congrFun hd v).symm
      exact (Nat.eq_of_mul_eq_mul_right hr he).trans F₀.property.2.1
    exact ⟨⟨F.val,F.property.1,hcard,fun v =>
      (F₀.property.2.2 v).trans_eq ((congrFun hd v).trans (F.property.2 v).symm)⟩,
      funext F.property.2⟩
  left_inv F := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv F := by apply Subtype.ext; rfl

/-- Mixture over exact degree sequences. A uniform bound on the good sequences
bounds the joint bad-event probability under the terminal law. -/
theorem terminal_event_le_of_fixedDegrees (r M : ℕ) (hr : 0 < r) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (G : (V → ℕ) → Prop)
    (P : SimpleHypergraph V → Prop) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ d, G d → ∀ [Nonempty (FixedDegreeState V r d)],
      (fixedDegreeLaw r d).event (fun F => P F.val) ≤ b) :
    (terminalLaw r M ell).event (fun F => G (fun v => vertexDegree F.val v) ∧ P F.val) ≤ b := by
  classical
  let ds := (univ : Finset (TerminalState V r M ell)).image (fun F v => vertexDegree F.val v)
  let f : TerminalState V r M ell → ↥ds := fun F =>
    ⟨fun v => vertexDegree F.val v,mem_image.mpr ⟨F,mem_univ _,rfl⟩⟩
  apply uniform_event_le_of_fibers f
  intro d hne
  letI := hne
  obtain ⟨F₀⟩ := hne
  have hd : (fun v => vertexDegree F₀.val.val v) = d.val := congrArg Subtype.val F₀.property
  let e₁ : {F : TerminalState V r M ell // f F = d} ≃
      {F : TerminalState V r M ell // (fun v => vertexDegree F.val v) = d.val} :=
    Equiv.subtypeEquivRight (fun F => Subtype.ext_iff)
  let e := e₁.trans (terminalDegreeFiberEquiv r M hr ell d.val F₀.val hd)
  letI : Nonempty (FixedDegreeState V r d.val) := ⟨e F₀⟩
  by_cases hg : G d.val
  · have ht := FiniteEntropy.Law.uniform_event_equiv e (fun F => P F.val)
    have he : (fun F : {F : TerminalState V r M ell // f F = d} =>
        G (fun v => vertexDegree F.val.val v) ∧ P F.val.val) =
        (fun F => P (e F).val) := by
      funext F
      have hf : (fun v => vertexDegree F.val.val v) = d.val := congrArg Subtype.val F.property
      simp only [hf,hg,true_and]
      rfl
    rw [he,ht]
    exact h d.val hg
  · have he : (fun F : {F : TerminalState V r M ell // f F = d} =>
        G (fun v => vertexDegree F.val.val v) ∧ P F.val.val) = (fun _ => False) := by
      funext F
      have hf : (fun v => vertexDegree F.val.val v) = d.val := congrArg Subtype.val F.property
      simp [hf,hg]
    rw [he]
    simpa [FiniteEntropy.Law.event] using hb
end LooseHamilton
