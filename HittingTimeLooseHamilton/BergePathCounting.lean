module

public import HittingTimeLooseHamilton.BergePairStar
public import HittingTimeLooseHamilton.ExceptionalSetModels
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

/-! Finite encodings and a union bound for short Berge paths.

The template type records every path vertex and edge. Only an upper bound on
its cardinality is used, so forgetting edge injectivity cannot lose any path.
-/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable (V : Type*) [Fintype V] [DecidableEq V]

/-- A complete-host Berge path with its ordered endpoints included. -/
@[expose] def BergeTemplate (r t : ℕ) :=
  { a : (Fin (t+1) → V) × (Fin t → Finset V) //
    Function.Injective a.1 ∧ Function.Injective a.2 ∧
      ∀ i, (a.2 i).card = r ∧ a.1 i.castSucc ∈ a.2 i ∧ a.1 i.succ ∈ a.2 i }

@[expose] instance (r t : ℕ) : Fintype (BergeTemplate V r t) := by
  classical
  unfold BergeTemplate
  infer_instance

variable {V}
namespace BergeTemplate
variable {r t : ℕ}

@[expose] def vertices (p : BergeTemplate V r t) : Fin (t+1) → V := p.val.1
@[expose] def edges (p : BergeTemplate V r t) : Fin t → Finset V := p.val.2

theorem vertices_injective (p : BergeTemplate V r t) : Function.Injective p.vertices := p.property.1
theorem edges_injective (p : BergeTemplate V r t) : Function.Injective p.edges := p.property.2.1

@[expose] def initial (p : BergeTemplate V r t) : V := p.vertices 0
@[expose] def terminal (p : BergeTemplate V r t) : V := p.vertices (Fin.last t)

theorem endpoints_ne (p : BergeTemplate V r t) (ht : 1 ≤ t) : p.initial ≠ p.terminal := by
  intro he
  have h := congrArg Fin.val (p.vertices_injective he)
  simp only [Fin.val_zero, Fin.val_last] at h
  omega

@[expose] def edgeSet (p : BergeTemplate V r t) : SimpleHypergraph V := univ.image p.edges

@[simp] theorem edgeSet_card (p : BergeTemplate V r t) : p.edgeSet.card = t := by
  rw [edgeSet, card_image_of_injective _ p.edges_injective, card_univ, Fintype.card_fin]

theorem edgeSet_subset_complete (p : BergeTemplate V r t) : p.edgeSet ⊆ completeEdges V r := by
  intro e he
  obtain ⟨i, _, rfl⟩ := mem_image.mp he
  exact (mem_completeEdges r _).mpr (p.property.2.2 i).1

@[simp] theorem edgeSet_subset_iff (p : BergeTemplate V r t) (H : SimpleHypergraph V) :
    p.edgeSet ⊆ H ↔ ∀ i, p.edges i ∈ H := by
  simp [edgeSet, image_subset_iff]

end BergeTemplate

/-- Convert an existing Berge path in any uniform host to its counted template. -/
@[expose] def BergePath.toTemplate {F : SimpleHypergraph V} {r t : ℕ} {u v : V}
    (p : BergePath F t u v) (hF : F ⊆ completeEdges V r) : BergeTemplate V r t :=
  ⟨(p.vertices,p.edges),p.vertices_injective,p.edges_injective,fun i =>
    ⟨(mem_completeEdges r _).mp (hF (p.edge_mem i)),p.left_mem i,p.right_mem i⟩⟩

@[simp] theorem BergePath.toTemplate_initial {F : SimpleHypergraph V} {r t : ℕ} {u v : V}
    (p : BergePath F t u v) (hF : F ⊆ completeEdges V r) :
    (p.toTemplate hF).initial = u := p.initial

@[simp] theorem BergePath.toTemplate_terminal {F : SimpleHypergraph V} {r t : ℕ} {u v : V}
    (p : BergePath F t u v) (hF : F ⊆ completeEdges V r) :
    (p.toTemplate hF).terminal = v := p.terminal

theorem BergePath.toTemplate_edgeSet {F : SimpleHypergraph V} {r t : ℕ} {u v : V}
    (p : BergePath F t u v) (hF : F ⊆ completeEdges V r) :
    (p.toTemplate hF).edgeSet ⊆ F :=
  (BergeTemplate.edgeSet_subset_iff _ F).mpr p.edge_mem

private def BergeSlotChoices (r t : ℕ) :=
  Σ a : {a : Fin (t+1) → V // Function.Injective a},
    ∀ i : Fin t, ↥(pairStar r (a.val i.castSucc) (a.val i.succ))

private instance (r t : ℕ) : Fintype (BergeSlotChoices (V:=V) r t) := by
  classical
  unfold BergeSlotChoices
  infer_instance

private def templateSlotChoices {r t : ℕ} (p : BergeTemplate V r t) :
    BergeSlotChoices (V:=V) r t :=
  ⟨⟨p.vertices,p.vertices_injective⟩,fun i =>
    ⟨p.edges i,(mem_pairStar r _ _ _).mpr (p.property.2.2 i)⟩⟩

private theorem templateSlotChoices_injective {r t : ℕ} :
    Function.Injective (templateSlotChoices (V:=V) (r:=r) (t:=t)) := by
  intro p q hpq
  have hv : p.vertices = q.vertices := congrArg (fun a => a.1.val) hpq
  have he : p.edges = q.edges := by
    funext i
    exact congrArg (fun a : BergeSlotChoices (V:=V) r t => (a.2 i).val) hpq
  apply Subtype.ext
  exact Prod.ext hv he

/-- A fixed length has at most `n^(t+1) choose(n-2,r-2)^t` templates. -/
theorem bergeTemplate_card_le {r t : ℕ} (hr : 2 ≤ r) :
    Fintype.card (BergeTemplate V r t) ≤
      (Fintype.card V)^(t+1) * ((Fintype.card V-2).choose (r-2))^t := by
  let d := (Fintype.card V-2).choose (r-2)
  have hslots : Fintype.card (BergeSlotChoices (V:=V) r t) =
      Fintype.card {a : Fin (t+1) → V // Function.Injective a} * d^t := by
    unfold BergeSlotChoices
    rw [Fintype.card_sigma]
    have he (a : {a : Fin (t+1) → V // Function.Injective a}) :
        Fintype.card (∀ i : Fin t, ↥(pairStar r (a.val i.castSucc) (a.val i.succ))) = d^t := by
      rw [Fintype.card_pi]
      have hpair (i : Fin t) :
          Fintype.card ↥(pairStar r (a.val i.castSucc) (a.val i.succ)) = d := by
        rw [Fintype.card_coe, pairStar_card hr]
        intro h
        have hh := congrArg Fin.val (a.property h)
        change i.val = i.val+1 at hh
        omega
      simp_rw [hpair]
      simp
    simp_rw [he]
    simp
  calc
    Fintype.card (BergeTemplate V r t) ≤ Fintype.card (BergeSlotChoices (V:=V) r t) :=
      Fintype.card_le_of_injective _ templateSlotChoices_injective
    _ = Fintype.card {a : Fin (t+1) → V // Function.Injective a} * d^t := hslots
    _ ≤ (Fintype.card V)^(t+1) * d^t := by
      apply Nat.mul_le_mul_right
      simpa using Fintype.card_subtype_le (fun a : Fin (t+1) → V => Function.Injective a)

/-- Summing a common bound over all complete-host path templates. -/
theorem bergeTemplate_event_union_bound {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) {r t : ℕ} (hr : 2 ≤ r)
    (E : BergeTemplate V r t → Ω → Prop) {b : ℝ} (hb : 0 ≤ b)
    (hE : ∀ a, p.event (E a) ≤ b) :
    p.event (fun ω => ∃ a, E a ω) ≤
      ((Fintype.card V : ℝ)^(t+1) * (((Fintype.card V-2).choose (r-2) : ℕ) : ℝ)^t) * b := by
  apply (p.finite_union_bound E).trans
  calc
    (∑ a, p.event (E a)) ≤ ∑ _a : BergeTemplate V r t, b :=
      sum_le_sum (fun a _ => hE a)
    _ = (Fintype.card (BergeTemplate V r t) : ℝ) * b := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hb
      exact_mod_cast bergeTemplate_card_le (V:=V) (t:=t) hr
end LooseHamilton
