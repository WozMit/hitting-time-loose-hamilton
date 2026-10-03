module

public import HittingTimeLooseHamilton.UniformSubtypeProbability
public import HittingTimeLooseHamilton.CoreConditionalCounting

public section
noncomputable section
namespace LooseHamilton
attribute [local instance] Classical.propDecidable

/-- A positive finite event contains an outcome. -/
lemma exists_of_event_pos {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (E : Ω → Prop) (h : 0 < p.event E) : ∃ ω, E ω := by
  by_contra hn
  have he := p.event_eq_zero_of_false (not_exists.mp hn)
  linarith

/-- Conditioning a uniform finite family and changing coordinates by an exact
fiber equivalence gives the uniform law on the new family. -/
theorem uniform_conditioned_equiv {Ω A : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype A] [Nonempty A] (E P : Ω → Prop)
    [Nonempty {ω // E ω}] (e : {ω // E ω} ≃ A) (Q : A → Prop)
    (h : ∀ ω : {ω // E ω}, P ω.val ↔ Q (e ω))
    (hE : 0 < (FiniteEntropy.uniform : FiniteEntropy.Law Ω).event E) :
    ((FiniteEntropy.uniform : FiniteEntropy.Law Ω).condition E hE).event P =
      (FiniteEntropy.uniform : FiniteEntropy.Law A).event Q := by
  rw [condition_event_eq_joint,uniform_event_and_eq_mul_subtype]
  have he : (fun ω : {ω // E ω} => P ω.val) = (fun ω => Q (e ω)) :=
    funext (fun ω => propext (h ω))
  rw [he,FiniteEntropy.Law.uniform_event_equiv e Q]
  exact mul_div_cancel_left₀ _ hE.ne'

/-- The same exact conditioning rule after any sampling procedure whose
pushforward is uniform; the original sample space need not be uniform. -/
theorem uniform_pushforward_conditioned_equiv {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (p : FiniteEntropy.Law Ω) (f : Ω → A)
    (hf : p.map f = (FiniteEntropy.uniform : FiniteEntropy.Law A))
    (E P : A → Prop) [Nonempty {a // E a}]
    (e : {a // E a} ≃ B) (Q : B → Prop)
    (h : ∀ a : {a // E a}, P a.val ↔ Q (e a))
    (hE : 0 < p.event (fun ω => E (f ω))) :
    (p.condition (fun ω => E (f ω)) hE).event (fun ω => P (f ω)) =
      (FiniteEntropy.uniform : FiniteEntropy.Law B).event Q := by
  have hm (R : A → Prop) : p.event (fun ω => R (f ω)) =
      (FiniteEntropy.uniform : FiniteEntropy.Law A).event R := by
    rw [← FiniteEntropy.Law.event_map,hf]
  have he : 0 < (FiniteEntropy.uniform : FiniteEntropy.Law A).event E := by
    rwa [hm] at hE
  rw [condition_event_eq_joint,hm (fun a => E a ∧ P a),hm E]
  rw [← condition_event_eq_joint _ E P he]
  exact uniform_conditioned_equiv E P e Q h he
end LooseHamilton
