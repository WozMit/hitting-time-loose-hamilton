module

public import HittingTimeLooseHamilton.MigrationWeightedTargets

public section

/-! Finite sequential mobility: exceptions may depend on every earlier choice.
Counting takes place before forgetting the order of private coordinates. -/
noncomputable section
namespace LooseHamilton.Migration
open Finset
universe u
attribute [local instance] Classical.propDecidable

/-- An ordered history of target choices, represented as iterated products. -/
@[expose] def ChoicePath (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | k+1 => ChoicePath V k × V

@[expose] instance choicePathFintype (V : Type*) [Fintype V] : (k : ℕ) → Fintype (ChoicePath V k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k+1 => @instFintypeProd _ _ (choicePathFintype V k) inferInstance

@[simp] theorem choicePath_card (V : Type*) [Fintype V] (k : ℕ) :
    Fintype.card (ChoicePath V k) = (Fintype.card V)^k := by
  induction k with
  | zero => exact Fintype.card_punit
  | succ k ih =>
    change Fintype.card (ChoicePath V k × V) = _
    rw [Fintype.card_prod, ih, pow_succ]

/-- Successful histories satisfy each step predicate along their actual prefix. -/
@[expose] def Successful {V : Type*} (step : (k : ℕ) → ChoicePath V k → V → Prop) :
    (k : ℕ) → ChoicePath V k → Prop
  | 0, _ => True
  | k+1, p => Successful step k p.1 ∧ step k p.1 p.2

/-- One more adaptive choice: old exceptional prefixes contribute their whole
fibres; only successful prefixes require the new step estimate. -/
theorem product_failure_card_le {A V : Type*} [Fintype A] [Fintype V]
    (good : A → Prop) (step : A → V → Prop) (b : ℝ)
    (hb : 0 ≤ b)
    (hstep : ∀ a, good a → ((univ.filter (fun v => ¬step a v)).card:ℝ) ≤ b) :
    ((univ.filter (fun p : A×V => ¬(good p.1 ∧ step p.1 p.2))).card:ℝ) ≤
      ((univ.filter (fun a => ¬good a)).card:ℝ)*(Fintype.card V:ℝ) +
      (Fintype.card A:ℝ)*b := by
  classical
  have he : ((univ.filter (fun p : A×V => ¬(good p.1 ∧ step p.1 p.2))).card:ℝ) =
      ∑ a : A, ((univ.filter (fun v : V => ¬(good a ∧ step a v))).card:ℝ) := by
    simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
    exact Fintype.sum_prod_type _
  rw [he]
  calc
    _ ≤ ∑ a : A, ((if good a then 0 else (Fintype.card V:ℝ)) + b) := by
      apply sum_le_sum
      intro a ha
      by_cases hg : good a
      · simpa [hg] using hstep a hg
      · simpa [hg] using hb
    _ = _ := by
      rw [sum_add_distrib]
      simp only [sum_const, card_univ, nsmul_eq_mul]
      congr 1
      rw [show (fun a => if good a then (0:ℝ) else (Fintype.card V:ℝ)) =
          (fun a => if ¬good a then (Fintype.card V:ℝ) else 0) by funext a; split_ifs <;> simp_all]
      rw [←sum_filter]
      simp

/-- With at most `ε N` failed targets at each successful prefix, at most
`k ε N^k` ordered histories fail after `k` choices. -/
theorem sequential_failure_card_le {V : Type*} [Fintype V]
    (step : (k : ℕ) → ChoicePath V k → V → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ k p, Successful step k p →
      ((univ.filter (fun v => ¬step k p v)).card:ℝ) ≤ ε*(Fintype.card V:ℝ)) :
    ∀ k : ℕ, ((univ.filter (fun p : ChoicePath V k => ¬Successful step k p)).card:ℝ) ≤
      (k:ℝ)*ε*(Fintype.card V:ℝ)^k := by
  classical
  intro k
  induction k with
  | zero => simp [Successful]
  | succ k ih =>
    have hp := product_failure_card_le (Successful step k) (step k)
      (ε*(Fintype.card V:ℝ)) (mul_nonneg hε (Nat.cast_nonneg _)) (hstep k)
    have hb : ((univ.filter (fun p : ChoicePath V k × V =>
        ¬(Successful step k p.1 ∧ step k p.1 p.2))).card:ℝ) ≤
        ((k+1:ℕ):ℝ)*ε*(Fintype.card V:ℝ)^(k+1) := by
      apply hp.trans
      rw [choicePath_card, Nat.cast_pow]
      have hm := mul_le_mul_of_nonneg_right ih (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
      push_cast
      rw [pow_succ]
      nlinarith
    convert hb using 1
    congr 2
    ext p
    constructor <;> intro hp
    · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩
    · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩

theorem sequential_failure_card_le_upto {V : Type*} [Fintype V]
    (step : (k : ℕ) → ChoicePath V k → V → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (K : ℕ) (hstep : ∀ k < K, ∀ p, Successful step k p →
      ((univ.filter (fun v => ¬step k p v)).card:ℝ) ≤ ε*(Fintype.card V:ℝ)) :
    ((univ.filter (fun p : ChoicePath V K => ¬Successful step K p)).card:ℝ) ≤
      (K:ℝ)*ε*(Fintype.card V:ℝ)^K := by
  classical
  induction K with
  | zero => simp [Successful]
  | succ k ih =>
    have hp := product_failure_card_le (Successful step k) (step k)
      (ε*(Fintype.card V:ℝ)) (mul_nonneg hε (Nat.cast_nonneg _)) (hstep k (Nat.lt_succ_self k))
    have hb : ((univ.filter (fun p : ChoicePath V k × V =>
        ¬(Successful step k p.1 ∧ step k p.1 p.2))).card:ℝ) ≤
        ((k+1:ℕ):ℝ)*ε*(Fintype.card V:ℝ)^(k+1) := by
      apply hp.trans
      rw [choicePath_card, Nat.cast_pow]
      have hi := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      have hm := mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
      push_cast
      rw [pow_succ]
      nlinarith
    convert hb using 1
    congr 2
    ext p
    constructor <;> intro hp
    · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩
    · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩

/-- A multiplicative lower bound is transported along every successful path. -/
theorem successful_value_lower {V : Type*}
    (step : (k : ℕ) → ChoicePath V k → V → Prop)
    (value : (k : ℕ) → ChoicePath V k → ℝ) (factor : ℕ → ℝ) (base : ℝ)
    (hfactor : ∀ k, 0 ≤ factor k) (hbase : ∀ p, base ≤ value 0 p)
    (hmove : ∀ k p v, Successful step k p → step k p v →
      factor k * value k p ≤ value (k+1) (p,v)) :
    ∀ k p, Successful step k p → (∏ i ∈ range k, factor i)*base ≤ value k p := by
  intro k
  induction k with
  | zero => intro p hp; simpa using hbase p
  | succ k ih =>
    intro p hp
    rcases p with ⟨p,v⟩
    have hl := mul_le_mul_of_nonneg_left (ih p hp.1) (hfactor k)
    have hm := hmove k p v hp.1 hp.2
    rw [prod_range_succ]
    nlinarith

/-- Combining finite sequential counting with the multiplicative invariant. -/
theorem sequential_low_value_card_le {V : Type*} [Fintype V]
    (step : (k : ℕ) → ChoicePath V k → V → Prop)
    (value : (k : ℕ) → ChoicePath V k → ℝ) (factor : ℕ → ℝ) (base ε : ℝ)
    (hε : 0 ≤ ε) (hfactor : ∀ k, 0 ≤ factor k)
    (hbase : ∀ p, base ≤ value 0 p)
    (hmove : ∀ k p v, Successful step k p → step k p v →
      factor k * value k p ≤ value (k+1) (p,v))
    (hstep : ∀ k p, Successful step k p →
      ((univ.filter (fun v => ¬step k p v)).card:ℝ) ≤ ε*(Fintype.card V:ℝ))
    (k : ℕ) :
    ((univ.filter (fun p => value k p < (∏ i ∈ range k, factor i)*base)).card:ℝ) ≤
      (k:ℝ)*ε*(Fintype.card V:ℝ)^k := by
  apply le_trans _ (sequential_failure_card_le step ε hε hstep k)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  simp only [mem_filter, mem_univ, true_and] at hp ⊢
  intro hs
  exact (not_lt_of_ge (successful_value_lower step value factor base hfactor hbase hmove k p hs)) hp

/-- Forgetting ordering cannot increase the number of exceptional labels.
Every label must have at least one ordered representative, and its value is
independent of that representative. -/
theorem failed_labels_card_le {P L : Type*} [Fintype P] [DecidableEq L]
    (labels : Finset L) (forget : P → L) (good : L → Prop)
    (hsurj : ∀ l ∈ labels, ∃ p, forget p=l) :
    (labels.filter (fun l => ¬good l)).card ≤
      (univ.filter (fun p => ¬good (forget p))).card := by
  have hsub : labels.filter (fun l => ¬good l) ⊆
      (univ.filter (fun p => ¬good (forget p))).image forget := by
    intro l hl
    obtain ⟨p,hp⟩ := hsurj l (mem_filter.mp hl).1
    apply mem_image.mpr
    refine ⟨p,?_,hp⟩
    simpa [hp] using (mem_filter.mp hl).2
  exact (card_le_card hsub).trans (card_image_le)

/-- If a bad link has a failed marked representative, reconstructing the link
from the representative bounds bad links by failed representatives. -/
theorem bad_links_card_le_failed_labels {L K : Type*} [DecidableEq L] [DecidableEq K]
    (badLinks : Finset K) (failed : Finset L) (decode : L → K)
    (hwitness : ∀ A ∈ badLinks, ∃ l ∈ failed, decode l=A) :
    badLinks.card ≤ failed.card := by
  apply le_trans (card_le_card (show badLinks ⊆ failed.image decode from ?_)) card_image_le
  intro A hA
  obtain ⟨l,hl,he⟩ := hwitness A hA
  exact mem_image.mpr ⟨l,hl,he⟩

/-- A nonnegative sum below the comparison threshold has every summand below
it. This turns the port test's bad sums into failed marked completions. -/
theorem summand_lt_of_sum_lt {A : Type*} [DecidableEq A]
    (s : Finset A) (w : A → ℝ) (a : A) (ha : a∈s) (threshold : ℝ)
    (hw : ∀ b ∈ s, 0 ≤ w b) (hs : ∑ b ∈ s, w b < threshold) :
    w a < threshold := (single_le_sum hw ha).trans_lt hs

/-- The vertices already chosen along a path. -/
@[expose] def pathVertices {V : Type*} [DecidableEq V] : (k : ℕ) → ChoicePath V k → Finset V
  | 0, _ => ∅
  | k+1, p => insert p.2 (pathVertices k p.1)

theorem pathVertices_card_le {V : Type*} [DecidableEq V] :
    ∀ k (p : ChoicePath V k), (pathVertices k p).card ≤ k := by
  intro k
  induction k with
  | zero => intro p; simp [pathVertices]
  | succ k ih =>
    intro p
    exact (card_insert_le _ _).trans (Nat.add_le_add_right (ih p.1) 1)

/-- Forbidden labels and collisions together cost at most
`K (|forbidden|+K) N^(K-1)` ordered paths. -/
theorem collision_path_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (forbidden : Finset V) (K : ℕ) (hN : 0 < Fintype.card V) (hK : 1 ≤ K) :
    ((univ.filter (fun p : ChoicePath V K => ¬Successful
      (fun k p v => v ∉ forbidden ∪ pathVertices k p) K p)).card:ℝ) ≤
      (K:ℝ)*((forbidden.card:ℝ)+K)*(Fintype.card V:ℝ)^(K-1) := by
  let ε : ℝ := ((forbidden.card:ℝ)+K)/(Fintype.card V:ℝ)
  have hn : (0:ℝ) < Fintype.card V := Nat.cast_pos.mpr hN
  have hε : 0 ≤ ε := div_nonneg (by positivity) hn.le
  have hb := sequential_failure_card_le_upto
    (fun k p v => v ∉ forbidden ∪ pathVertices k p) ε hε K (by
      intro k hk p hp
      have he : univ.filter (fun v => ¬ (v ∉ (forbidden ∪ pathVertices k p))) =
          forbidden ∪ pathVertices k p := by ext v; simp only [mem_filter, mem_univ, true_and, not_not]
      have hc := (card_union_le forbidden (pathVertices k p)).trans
        (Nat.add_le_add_left (pathVertices_card_le k p) forbidden.card)
      have hc' : (↑(forbidden ∪ pathVertices k p).card:ℝ) ≤ (forbidden.card:ℝ)+K := by
        exact_mod_cast hc.trans (Nat.add_le_add_left hk.le forbidden.card)
      have hc'' : (↑(forbidden ∪ pathVertices k p).card:ℝ) ≤ ε*(Fintype.card V:ℝ) := by
        simpa [ε, div_mul_cancel₀ _ hn.ne'] using hc'
      convert hc'' using 1
      congr 2
      ext v
      simp only [mem_filter, mem_univ, true_and, not_not])
  have hpow : (Fintype.card V:ℝ)^K = (Fintype.card V:ℝ)^(K-1)*(Fintype.card V:ℝ) := by
    rw [←pow_succ, Nat.sub_add_cancel hK]
  rw [hpow] at hb
  have he : (K:ℝ)*ε*((Fintype.card V:ℝ)^(K-1)*(Fintype.card V:ℝ)) =
      (K:ℝ)*((forbidden.card:ℝ)+K)*(Fintype.card V:ℝ)^(K-1) := by
    dsimp [ε]
    field_simp
    <;> ring
  exact hb.trans_eq he
end LooseHamilton.Migration


