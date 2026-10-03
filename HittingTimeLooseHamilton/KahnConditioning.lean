module

public import HittingTimeLooseHamilton.KahnLaw

public section

open scoped BigOperators
noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteEntropy
namespace Law
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- Integration against a pushforward finite law. -/
lemma sum_map_mul (p : Law A) (f : A → B) (g : B → ℝ) :
    (∑ b, (p.map f).mass b * g b) = ∑ a, p.mass a * g (f a) := by
  classical
  simp only [map, event, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

@[ext] lemma ext_mass (p q : Law A) (h : ∀ a, p.mass a = q.mass a) : p = q := by
  cases p
  cases q
  congr
  exact funext h

lemma map_map (p : Law A) (f : A → B) (g : B → C) :
    (p.map f).map g = p.map (g ∘ f) := by
  classical
  apply ext_mass
  intro c
  have h := p.sum_map_mul f (fun b => if g b = c then 1 else 0)
  simpa [map, event, mul_ite] using h

lemma map_id (p : Law A) : p.map id = p := by
  classical
  apply ext_mass
  intro a
  simp [map, event]

lemma mass_le_map (p : Law A) (f : A → B) (a : A) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  change p.mass a ≤ ∑ c, if f c = f a then p.mass c else 0
  calc
    p.mass a = if f a = f a then p.mass a else 0 := by simp
    _ ≤ ∑ c, if f c = f a then p.mass c else 0 :=
      Finset.single_le_sum (f := fun c => if f c = f a then p.mass c else 0)
        (fun c _ => ite_nonneg (p.nonneg c) (le_refl 0)) (Finset.mem_univ a)

lemma map_mass_of_injective (p : Law A) (f : A → B) (hf : Function.Injective f)
    (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  change (∑ c, if f c = f a then p.mass c else 0) = p.mass a
  simp [hf.eq_iff]

/-- Relabeling a variable injectively preserves its entropy, including zero atoms. -/
lemma entropy_map_of_injective (p : Law A) (f : A → B) (hf : Function.Injective f) :
    entropy (p.map f).mass = entropy p.mass := by
  unfold entropy
  rw [p.sum_map_mul f (fun b => Real.log ((p.map f).mass b))]
  simp_rw [p.map_mass_of_injective f hf]

/-- Conditional entropy of the underlying outcome given a deterministic observation.
The zero-probability convention is harmless because every summand is multiplied by its mass. -/
@[expose] noncomputable def conditionalEntropy (p : Law A) (f : A → B) : ℝ :=
  -∑ a, p.mass a * Real.log (p.mass a / (p.map f).mass (f a))

/-- Chain rule for an outcome and a deterministic observation of it. -/
lemma entropy_chain (p : Law A) (f : A → B) :
    entropy p.mass = entropy (p.map f).mass + p.conditionalEntropy f := by
  have hpoint (a : A) :
      p.mass a * Real.log (p.mass a / (p.map f).mass (f a)) =
      p.mass a * Real.log (p.mass a) -
        p.mass a * Real.log ((p.map f).mass (f a)) := by
    by_cases hp : p.mass a = 0
    · simp [hp]
    · have hm : 0 < (p.map f).mass (f a) :=
        lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)) (p.mass_le_map f a)
      rw [Real.log_div hp hm.ne', mul_sub]
  unfold entropy conditionalEntropy
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, p.sum_map_mul f (fun b => Real.log ((p.map f).mass b))]
  ring

lemma conditionalEntropy_nonneg (p : Law A) (f : A → B) :
    0 ≤ p.conditionalEntropy f := by
  unfold conditionalEntropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro a _
  apply mul_nonpos_of_nonneg_of_nonpos (p.nonneg a)
  apply Real.log_nonpos
  · exact div_nonneg (p.nonneg a) ((p.map f).nonneg _)
  · by_cases hm : (p.map f).mass (f a) = 0
    · simp [hm]
    · exact (div_le_one (lt_of_le_of_ne ((p.map f).nonneg _) (Ne.symm hm))).mpr
        (p.mass_le_map f a)

/-- Taking a deterministic observation cannot increase Shannon entropy. -/
lemma entropy_map_le (p : Law A) (f : A → B) :
    entropy (p.map f).mass ≤ entropy p.mass := by
  have h := p.conditionalEntropy_nonneg f
  rw [p.entropy_chain f]
  linarith

/-- More informative observations decrease conditional entropy of the full outcome. -/
lemma conditionalEntropy_comp_le (p : Law A) (f : A → B) (g : B → C) :
    p.conditionalEntropy f ≤ p.conditionalEntropy (g ∘ f) := by
  have h := (p.map f).entropy_map_le g
  rw [p.map_map f g] at h
  have hf := p.entropy_chain f
  have hg := p.entropy_chain (g ∘ f)
  linarith

/-- Entropy of one finite random variable conditional on another. -/
@[expose] noncomputable def conditionalMapEntropy (p : Law A) (X : A → B) (Y : A → C) : ℝ :=
  (p.map (fun a => (X a, Y a))).conditionalEntropy Prod.snd

/-- The two-variable chain rule. -/
lemma entropy_map_pair (p : Law A) (X : A → B) (Y : A → C) :
    entropy (p.map (fun a => (X a,Y a))).mass =
      entropy (p.map Y).mass + p.conditionalMapEntropy X Y := by
  unfold conditionalMapEntropy
  have h := (p.map (fun a => (X a,Y a))).entropy_chain Prod.snd
  rw [p.map_map] at h
  exact h

lemma conditionalMapEntropy_nonneg (p : Law A) (X : A → B) (Y : A → C) :
    0 ≤ p.conditionalMapEntropy X Y :=
  (p.map (fun a => (X a,Y a))).conditionalEntropy_nonneg Prod.snd

/-- Conditional law on an event of positive probability. -/
@[expose] noncomputable def condition (p : Law A) (E : A → Prop) (hE : 0 < p.event E) : Law A := by
  classical
  exact {
    mass := fun a => if E a then p.mass a / p.event E else 0
    nonneg := fun a => ite_nonneg (div_nonneg (p.nonneg a) hE.le) (le_refl 0)
    total := by
      calc
        (∑ a, if E a then p.mass a / p.event E else 0) =
            (∑ a, if E a then p.mass a else 0) / p.event E := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp
        _ = 1 := div_self hE.ne'
  }

/-- Conditional law, with the original law as a harmless value on null events. -/
@[expose] noncomputable def conditionOr (p : Law A) (E : A → Prop) : Law A :=
  if h : 0 < p.event E then p.condition E h else p

lemma event_pos_of_mass_pos (p : Law A) (E : A → Prop) (a : A)
    (ha : E a) (hp : 0 < p.mass a) : 0 < p.event E := by
  classical
  apply lt_of_lt_of_le hp
  change p.mass a ≤ ∑ c, if E c then p.mass c else 0
  calc
    p.mass a = if E a then p.mass a else 0 := by simp [ha]
    _ ≤ _ := Finset.single_le_sum
      (fun c _ => ite_nonneg (p.nonneg c) (le_refl 0)) (Finset.mem_univ a)

lemma event_mul_conditionOr (p : Law A) (E : A → Prop) (a : A) :
    p.event E * (p.conditionOr E).mass a = if E a then p.mass a else 0 := by
  classical
  by_cases he : 0 < p.event E
  · simp only [conditionOr, dif_pos he, condition]
    split_ifs with ha
    · exact mul_div_cancel₀ (p.mass a) he.ne'
    · exact mul_zero _
  · have hz : p.event E = 0 := le_antisymm (le_of_not_gt he) (p.event_nonneg E)
    rw [hz, zero_mul]
    by_cases ha : E a
    · have hp : p.mass a = 0 := by
        apply le_antisymm _ (p.nonneg a)
        exact le_of_not_gt (fun hp => he (p.event_pos_of_mass_pos E a ha hp))
      simp [ha, hp]
    · simp [ha]

/-- The joint law with given first marginal and conditional kernels. -/
@[expose] def kernel (p : Law A) (q : A → Law B) : Law (A × B) where
  mass := fun ab => p.mass ab.1 * (q ab.1).mass ab.2
  nonneg := fun ab => mul_nonneg (p.nonneg _) ((q _).nonneg _)
  total := by
    simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum]
    simp only [Law.total, mul_one]

lemma conditional_kernel_eq_map (p : Law A) (f : A → B) :
    (p.map f).kernel (fun b => p.conditionOr (fun a => f a = b)) =
      p.map (fun a => (f a,a)) := by
  classical
  apply ext_mass
  intro ⟨b,a⟩
  change p.event (fun c => f c = b) * (p.conditionOr (fun c => f c = b)).mass a = _
  rw [p.event_mul_conditionOr]
  simp [map, event, Prod.mk.injEq, and_comm, ite_and]

lemma event_map (p : Law A) (f : A → B) (E : B → Prop) :
    (p.map f).event E = p.event (fun a => E (f a)) := by
  classical
  have h := p.sum_map_mul f (fun b => if E b then 1 else 0)
  simpa [event, mul_ite] using h

lemma map_eq_of_mass_zero_or_eq (p : Law A) (f g : A → B)
    (h : ∀ a, p.mass a = 0 ∨ f a = g a) : p.map f = p.map g := by
  classical
  apply ext_mass
  intro b
  apply Finset.sum_congr rfl
  intro a _
  rcases h a with ha | ha
  · simp [ha]
  · simp [ha]

lemma conditionOr_map (p : Law A) (f : A → B) (E : B → Prop) :
    (p.map f).conditionOr E = (p.conditionOr (fun a => E (f a))).map f := by
  classical
  by_cases he : 0 < p.event (fun a => E (f a))
  · have he' : 0 < (p.map f).event E := by simpa [p.event_map] using he
    simp only [conditionOr, dif_pos he, dif_pos he']
    apply ext_mass
    intro b
    simp only [condition, map, event]
    have hd : (∑ b, if E b then ∑ a, if f a = b then p.mass a else 0 else 0) =
        p.event (fun a => E (f a)) := p.event_map f E
    rw [hd]
    by_cases hb : E b
    · simp only [hb, ↓reduceIte]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : f a = b
      · simp [ha, hb, event]
      · simp [ha]
    · simp only [hb, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : f a = b
      · simp [ha, hb, event]
      · simp [ha]
  · have he' : ¬ 0 < (p.map f).event E := by simpa [p.event_map] using he
    simp only [conditionOr, dif_neg he, dif_neg he']

/-- Conditional entropy is the probability-weighted average of fiber-law entropies. -/
lemma conditionalEntropy_eq_sum (p : Law A) (f : A → B) :
    p.conditionalEntropy f =
      ∑ b, (p.map f).mass b * entropy (p.conditionOr (fun a => f a = b)).mass := by
  have hk := entropy_kernel (p.map f) (fun b => p.conditionOr (fun a => f a = b))
  change entropy ((p.map f).kernel (fun b => p.conditionOr (fun a => f a = b))).mass = _ at hk
  rw [p.conditional_kernel_eq_map f,
    p.entropy_map_of_injective (fun a => (f a,a)) (fun a c h => (Prod.mk.inj h).2)] at hk
  have hc := p.entropy_chain f
  linarith

/-- Average-of-conditionals formula for an arbitrary observable. -/
lemma conditionalMapEntropy_eq_sum (p : Law A) (X : A → B) (Y : A → C) :
    p.conditionalMapEntropy X Y =
      ∑ c, (p.map Y).mass c * entropy ((p.conditionOr (fun a => Y a = c)).map X).mass := by
  unfold conditionalMapEntropy
  rw [conditionalEntropy_eq_sum, p.map_map]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hz : (p.map Y).mass c = 0
  · simp only [Function.comp_def, hz, zero_mul]
  · have hc : 0 < p.event (fun a => Y a = c) :=
      lt_of_le_of_ne ((p.map Y).nonneg c) (Ne.symm hz)
    rw [p.conditionOr_map]
    have heq :
        (p.conditionOr (fun a => Y a = c)).map (fun a => (X a,Y a)) =
        ((p.conditionOr (fun a => Y a = c)).map X).map (fun x => (x,c)) := by
      rw [map_map]
      apply map_eq_of_mass_zero_or_eq
      intro a
      by_cases ha : Y a = c
      · exact Or.inr (by simp [ha])
      · exact Or.inl (by simp [conditionOr, dif_pos hc, condition, ha])
    change (p.map Y).mass c * entropy
      ((p.conditionOr (fun a => Y a = c)).map (fun a => (X a,Y a))).mass = _
    rw [heq, entropy_map_of_injective _ _ (fun a b h => (Prod.mk.inj h).1)]

lemma fst_eq_map (p : Law (A × B)) : p.fst = p.map Prod.fst := by
  classical
  apply ext_mass
  intro a
  simp only [fst, map, event, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

lemma snd_eq_map (p : Law (A × B)) : p.snd = p.map Prod.snd := by
  classical
  apply ext_mass
  intro b
  simp [snd, map, event, Fintype.sum_prod_type]

lemma entropy_map_pair_le (p : Law A) (X : A → B) (Y : A → C) :
    entropy (p.map (fun a => (X a,Y a))).mass ≤
      entropy (p.map X).mass + entropy (p.map Y).mass := by
  have h := entropy_subadditive (p.map (fun a => (X a,Y a)))
  rw [fst_eq_map, snd_eq_map, p.map_map, p.map_map] at h
  exact h

/-- Subadditivity remains valid after conditioning on any finite observation. -/
lemma conditionalMapEntropy_pair_le {D : Type*} [Fintype D]
    (p : Law A) (X : A → B) (Y : A → C) (Z : A → D) :
    p.conditionalMapEntropy (fun a => (X a,Y a)) Z ≤
      p.conditionalMapEntropy X Z + p.conditionalMapEntropy Y Z := by
  simp only [conditionalMapEntropy_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d _
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    ((p.conditionOr (fun a => Z a = d)).entropy_map_pair_le X Y) ((p.map Z).nonneg d)

/-- Conditioning an observable on a finer deterministic observation decreases its entropy. -/
lemma conditionalMapEntropy_comp_le (p : Law A) (X : A → B) (Y : A → C)
    {D : Type*} [Fintype D] (g : C → D) :
    p.conditionalMapEntropy X Y ≤ p.conditionalMapEntropy X (g ∘ Y) := by
  have hsub := p.conditionalMapEntropy_pair_le X Y (g ∘ Y)
  have hXY := p.entropy_map_pair X Y
  have hYg := p.entropy_map_pair Y (g ∘ Y)
  have hXYg := p.entropy_map_pair (fun a => (X a,Y a)) (g ∘ Y)
  have hYeq : entropy (p.map (fun a => (Y a,(g ∘ Y) a))).mass =
      entropy (p.map Y).mass := by
    have h := (p.map Y).entropy_map_of_injective (fun c => (c,g c))
      (fun a b h => (Prod.mk.inj h).1)
    rw [p.map_map] at h
    exact h
  have hXYeq : entropy (p.map (fun a => ((X a,Y a),(g ∘ Y) a))).mass =
      entropy (p.map (fun a => (X a,Y a))).mass := by
    have h := (p.map (fun a => (X a,Y a))).entropy_map_of_injective
      (fun bc => (bc,g bc.2)) (fun a b h => (Prod.mk.inj h).1)
    rw [p.map_map] at h
    exact h
  rw [hYeq] at hYg
  rw [hXYeq] at hXYg
  linarith

end Law
end FiniteEntropy
