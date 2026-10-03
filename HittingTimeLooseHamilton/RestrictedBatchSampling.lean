module

public import HittingTimeLooseHamilton.BatchSelectionUniform

public section

/-! A fresh independent uniform batch from any fixed-size observed host.
The source distribution need not be uniform; only its observed-state law is used. -/
noncomputable section
namespace LooseHamilton.RestrictedSampling
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A Ω : Type*} [Fintype V] [DecidableEq V] [Fintype A] [Fintype Ω]

@[expose] def BatchState (host : A → SimpleHypergraph V) (τ : ℕ) :=
  {b : A × SimpleHypergraph V // b.2 ⊆ host b.1 ∧ b.2.card = τ}

@[expose] instance (host : A → SimpleHypergraph V) (τ : ℕ) : Fintype (BatchState host τ) := by
  classical
  unfold BatchState
  infer_instance

@[expose] instance (host : A → SimpleHypergraph V) (τ : ℕ) : DecidableEq (BatchState host τ) :=
  Classical.decEq _

@[expose] def select (host : A → SimpleHypergraph V) (m τ : ℕ)
    (hc : ∀ a, (host a).card = m) (hτ : τ ≤ m)
    (a : A) (σ : BatchOrder m) : BatchState host τ :=
  ⟨(a, batchSelection (host a) m (hc a) τ σ),
    batchSelection_subset _ _ _ _ _, batchSelection_card _ _ _ _ hτ _⟩

lemma select_probability (host : A → SimpleHypergraph V) (m τ : ℕ)
    (hc : ∀ a, (host a).card = m) (hτ : τ ≤ m)
    (a : A) (b : BatchState host τ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event
      (fun σ => select host m τ hc hτ a σ = b) =
        if a = b.val.1 then 1 / (m.choose τ : ℝ) else 0 := by
  classical
  have he (σ : BatchOrder m) : select host m τ hc hτ a σ = b ↔
      a = b.val.1 ∧ batchSelection (host a) m (hc a) τ σ = b.val.2 := by
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      exact ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
    · rintro ⟨ha, hS⟩
      apply Subtype.ext
      exact Prod.ext ha hS
  simp_rw [he]
  rw [FiniteEntropy.Law.event_const_and]
  split_ifs with ha
  · subst a
    exact batchSelection_probability _ _ _ _ hτ _ b.property.1 b.property.2
  · rfl

lemma state_nonempty [Nonempty A] (host : A → SimpleHypergraph V) (m τ : ℕ)
    (hc : ∀ a, (host a).card = m) (hτ : τ ≤ m) : Nonempty (BatchState host τ) := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨select host m τ hc hτ a (Equiv.refl _)⟩

/-- The actual independent-batch experiment, expressed without surrogate measures. -/
@[expose] def observe (host : A → SimpleHypergraph V) (m τ : ℕ)
    (hc : ∀ a, (host a).card = m) (hτ : τ ≤ m) (f : Ω → A)
    (ω : Ω × BatchOrder m) : BatchState host τ :=
  select host m τ hc hτ (f ω.1) ω.2

lemma observed_mass [Nonempty A] (p : FiniteEntropy.Law Ω) (f : Ω → A)
    (hf : p.map f = FiniteEntropy.uniform)
    (host : A → SimpleHypergraph V) (m τ : ℕ)
    (hc : ∀ a, (host a).card = m) (hτ : τ ≤ m) (b : BatchState host τ) :
    ((p.prod FiniteEntropy.uniform).map (observe host m τ hc hτ f)).mass b =
      1 / ((Fintype.card A : ℝ) * (m.choose τ : ℝ)) := by
  classical
  change (p.prod FiniteEntropy.uniform).event
    (fun ω => observe host m τ hc hτ f ω = b) = _
  rw [FiniteEntropy.Law.event_prod_sum]
  simp only [observe]
  simp_rw [select_probability]
  have hs : (∑ ω, p.mass ω * (if f ω = b.val.1 then 1/(m.choose τ:ℝ) else 0)) =
      p.event (fun ω => f ω = b.val.1) * (1/(m.choose τ:ℝ)) := by
    unfold FiniteEntropy.Law.event
    rw [sum_mul]
    apply sum_congr rfl
    intro ω _
    split_ifs <;> simp
  rw [hs]
  have hmass := congrArg (fun q : FiniteEntropy.Law A => q.mass b.val.1) hf
  change p.event (fun ω => f ω = b.val.1) = _ at hmass
  rw [hmass]
  simp only [FiniteEntropy.uniform]
  ring

lemma state_card [Nonempty A] (host : A → SimpleHypergraph V) (m τ : ℕ)
    (hc : ∀ a, (host a).card = m) (hτ : τ ≤ m) :
    Fintype.card (BatchState host τ) = Fintype.card A * m.choose τ := by
  let p : FiniteEntropy.Law A := FiniteEntropy.uniform
  have hid : p.map id = p := p.map_id
  let q := (p.prod FiniteEntropy.uniform).map (observe host m τ hc hτ id)
  have ht := q.total
  dsimp only [q] at ht
  simp_rw [observed_mass p id hid] at ht
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one_div] at ht
  have hA : (0:ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hC : (0:ℝ) < m.choose τ := by exact_mod_cast Nat.choose_pos hτ
  have hh := (div_eq_iff (mul_pos hA hC).ne').mp ht
  have he : (Fintype.card (BatchState host τ):ℝ) =
      (Fintype.card A:ℝ)*(m.choose τ:ℝ) := by simpa using hh
  exact_mod_cast he

/-- Uniform observed pairs followed by independent uniform fixed-size batches
produce exactly the uniform law on valid triples. No feasibility is discarded. -/
theorem observed_law_uniform [Nonempty A] (p : FiniteEntropy.Law Ω) (f : Ω → A)
    (hf : p.map f = FiniteEntropy.uniform)
    (host : A → SimpleHypergraph V) (m τ : ℕ)
    (hc : ∀ a, (host a).card = m) (hτ : τ ≤ m) :
    (p.prod FiniteEntropy.uniform).map (observe host m τ hc hτ f) =
      @FiniteEntropy.uniform (BatchState host τ) inferInstance (state_nonempty host m τ hc hτ) := by
  apply FiniteEntropy.Law.ext_mass
  intro b
  rw [observed_mass p f hf]
  simp only [FiniteEntropy.uniform, ← one_div]
  rw [state_card host m τ hc hτ, Nat.cast_mul]

end LooseHamilton.RestrictedSampling
