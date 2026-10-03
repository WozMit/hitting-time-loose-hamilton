module

public import HittingTimeLooseHamilton.PrivateMigrationExpansion

public section

/-! Joint recovery of every summation label and the original actual edge set. -/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Inserting an edge through `x` determines that edge whenever all old edges
avoid `x`. This is the label-recovery step of the migration. -/
theorem inserted_edge_recovery {x : V} {e e' : Finset V}
    {F F' : Finset (Finset V)} (hx : x ∈ e) (hx' : x ∈ e')
    (hF : ∀ f ∈ F, x ∉ f) (hF' : ∀ f ∈ F', x ∉ f)
    (heq : insert e F = insert e' F') : e = e' := by
  have he : e ∈ insert e' F' := heq ▸ mem_insert_self e F
  rcases mem_insert.mp he with he | he
  · exact he
  · exact False.elim (hF' e he hx)

/-- The distinguished vertex and the unordered endpoint pair determine the
remaining private vertices. -/
theorem privateMigration_rest_recovery {x : V} {R uv : Finset V}
    (hx : x ∉ R) (hd : Disjoint (insert x R) uv) :
    ((uv ∪ insert x R) \ uv).erase x = R := by
  have he : (uv ∪ insert x R) \ uv = insert x R := by
    ext v
    have hdis := disjoint_left.mp hd
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hv, hn⟩
      exact hv.resolve_left hn
    · intro hv
      exact ⟨Or.inr hv, fun h => hdis hv h⟩
  rw [he, erase_insert hx]

variable {r : ℕ} {markers host : Finset (Finset V)} {D q : Finset V}
  {x : V} {R uv R' uv' : Finset V} {F F' : Finset (Finset V)}

/-- Recovery is joint in both unordered labels and the input edge set. -/
theorem privateMigration_joint_injective (hr : 3 ≤ r)
    (h : PrivateMigrationLegal r markers host D q x R uv)
    (h' : PrivateMigrationLegal r markers host D q x R' uv')
    (hF : F ∈ privateMigrationInputFamily r markers host D q x R uv)
    (hF' : F' ∈ privateMigrationInputFamily r markers host D q x R' uv')
    (heq : insert (uv ∪ insert x R) F = insert (uv' ∪ insert x R') F') :
    R = R' ∧ uv = uv' ∧ F = F' := by
  have he : uv ∪ insert x R = uv' ∪ insert x R' :=
    inserted_edge_recovery (mem_union_right _ (mem_insert_self _ _))
      (mem_union_right _ (mem_insert_self _ _))
      (fun _ hf => privateMigration_input_x_absent hF hf)
      (fun _ hf => privateMigration_input_x_absent hF' hf) heq
  have hp := privateMigration_expand_role hr h hF
  rw [heq, he] at hp
  have huv : uv = uv' := hp.symm.trans (privateMigration_expand_role hr h' hF')
  have hR := privateMigration_rest_recovery h.x_not_mem_rest h.private_pair_disjoint
  rw [he, huv] at hR
  have hRR : R = R' := hR.symm.trans
    (privateMigration_rest_recovery h'.x_not_mem_rest h'.private_pair_disjoint)
  have hFF := congrArg (fun E => E.erase (uv ∪ insert x R)) heq
  rw [privateMigration_erase_expand hF, he, privateMigration_erase_expand hF'] at hFF
  exact ⟨hRR, huv, hFF⟩

end LooseHamilton
