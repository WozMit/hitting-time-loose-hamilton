module

public import HittingTimeLooseHamilton.AuxiliaryFrameLabels

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame
open Finset
variable {V : Type*} [DecidableEq V]

/-- Every bounded deletion set can be encoded, with empty label slots as padding. -/
theorem exists_labelledSet (S : Finset V) (a : ℕ) (h : S.card ≤ a) :
    ∃ f : Fin a → Option V, labelledSet f = S := by
  induction a generalizing S with
  | zero =>
      have hs : S = ∅ := card_eq_zero.mp (by omega)
      subst S
      exact ⟨fun _ => none, by ext y; simp [labelledSet]⟩
  | succ a ih =>
      by_cases hs : S.Nonempty
      · obtain ⟨x,hx⟩ := hs
        have hc : (S.erase x).card ≤ a := by
          have := card_erase_of_mem hx
          omega
        obtain ⟨f,hf⟩ := ih (S.erase x) hc
        refine ⟨Fin.cases (some x) f, ?_⟩
        have he : labelledSet (Fin.cases (some x) f) = insert x (labelledSet f) := by
          ext y
          simp [labelledSet, Fin.exists_fin_succ, eq_comm]
        rw [he,hf,insert_erase hx]
      · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hs
        subst S
        exact ⟨fun _ => none, by ext y; simp [labelledSet]⟩

/-- Every bounded family of pairs can be represented by bounded ordered endpoint labels. -/
theorem exists_pairSet (M : Finset (Finset V)) (a : ℕ)
    (hm : ∀ e ∈ M, e.card = 2) (hc : M.card ≤ a) :
    ∃ f : Fin a → Option (V × V), pairSet f = M := by
  classical
  have hex : ∀ e : ↥M, ∃ p : V × V, ({p.1,p.2} : Finset V) = e.val := by
    intro e
    obtain ⟨x,y,_,he⟩ := card_eq_two.mp (hm e.val e.property)
    exact ⟨(x,y),he.symm⟩
  choose f hf using hex
  let T : Finset (V × V) := univ.image f
  have ht : T.card ≤ a := (card_image_le).trans (by simpa using hc)
  obtain ⟨g,hg⟩ := exists_labelledSet T a ht
  refine ⟨g, ?_⟩
  unfold pairSet
  rw [hg]
  ext e
  simp only [T, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨p,⟨q,rfl⟩,he⟩
    rw [hf q] at he
    exact he ▸ q.property
  · intro he
    exact ⟨f ⟨e,he⟩,⟨⟨e,he⟩,rfl⟩,hf ⟨e,he⟩⟩


/-- Any frame satisfying the manuscript's finite budgets has a label representation. -/
theorem exists_frame [Fintype V] (r : ℕ) (original current : Finset (Finset V))
    (D : Finset V) (p : V × V) (q : Option (V × V))
    (ho : IsPairMatching original) (hm : IsPairMatching current)
    (hd : D.card ≤ 4*r) (hb : MarkerBudget original current)
    (hret : ∀ e ∈ current, e ⊆ univ \ D)
    (hp : {p.1,p.2} ∈ current) (hq : ∀ t ∈ q, {t.1,t.2} ∈ current) :
    ∃ F : Frame r original, F.val.deleted = D ∧ F.val.markers original = current ∧
      F.val.root = p ∧ F.val.relative = q := by
  classical
  obtain ⟨d,hd'⟩ := exists_labelledSet D (4*r) hd
  obtain ⟨a,ha⟩ := exists_pairSet (original \ current) 2
    (fun e he => ho.1 e (mem_sdiff.mp he).1) hb.removed_le
  obtain ⟨b,hb'⟩ := exists_pairSet (current \ original) 2
    (fun e he => hm.1 e (mem_sdiff.mp he).1) hb.introduced_le
  let c : Code r V := (d,a,b,p,q)
  have hc : c.markers original = current := by
    change (original \ pairSet a) ∪ pairSet b = current
    rw [ha,hb']
    ext e
    simp only [mem_union,mem_sdiff]
    tauto
  have hdel : c.deleted = D := hd'
  have hactive : c.active = univ \ D := by simp only [Code.active,hdel]
  have hl : Legal original c := by
    constructor
    · rwa [hc]
    · rwa [hc,hactive]
    · simpa only [hc, c, Code.root, Code.relative] using hp
    · simpa only [hc, c, Code.root, Code.relative] using hq
  exact ⟨⟨c,hl⟩,hdel,hc,rfl,rfl⟩

end LooseHamilton.AuxiliaryFrame
