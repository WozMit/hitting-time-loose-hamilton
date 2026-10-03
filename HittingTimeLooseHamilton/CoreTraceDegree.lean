module

public import HittingTimeLooseHamilton.CoreTrace
public import HittingTimeLooseHamilton.CoreSeparation

public section

/-! A surviving vertex sees deleted vertices in one block only. Summing pair
codegrees within that block bounds its degree in the exposed trace. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

/-- Generic incidence summation over a uniquely contacted deleted block. -/
theorem trace_degree_le_of_unique_contact (F : SimpleHypergraph V) (block : A → Finset V)
    {w : V} {c d : ℕ} (hw : w ∉ univ.biUnion block)
    (hcard : ∀ a, (block a).card ≤ d)
    (hpair : ∀ x : V, w ≠ x → pairDegree F w x ≤ c)
    (hunique : ∀ a b : A, ∀ x ∈ block a, ∀ y ∈ block b,
      ∀ e ∈ F, ∀ f ∈ F, w ∈ e → x ∈ e → w ∈ f → y ∈ f → a=b) :
    vertexDegree (traceOn (univ.biUnion block) F) w ≤ c*d := by
  classical
  by_cases hcontact : ∃ a : A, ∃ x ∈ block a, ∃ e ∈ F, w ∈ e ∧ x ∈ e
  · obtain ⟨a,x,hxa,e,he,hwe,hxe⟩ := hcontact
    have hsub : (traceOn (univ.biUnion block) F).filter (fun f => w ∈ f) ⊆
        (block a).biUnion (fun y => F.filter (fun f => w ∈ f ∧ y ∈ f)) := by
      intro f hf
      obtain ⟨hf, hwf⟩ := mem_filter.mp hf
      obtain ⟨hfF, hmeet⟩ := (mem_traceOn _ _ _).mp hf
      obtain ⟨y, hyf, hyD⟩ := not_disjoint_iff.mp hmeet
      obtain ⟨b, _, hyb⟩ := mem_biUnion.mp hyD
      have hba := hunique b a y hyb x hxa f hfF e he hwf hyf hwe hxe
      subst b
      exact mem_biUnion.mpr ⟨y,hyb,mem_filter.mpr ⟨hfF,hwf,hyf⟩⟩
    calc
      vertexDegree (traceOn (univ.biUnion block) F) w ≤
          ((block a).biUnion (fun y => F.filter (fun f => w ∈ f ∧ y ∈ f))).card :=
        card_le_card hsub
      _ ≤ ∑ y ∈ block a, (F.filter (fun f => w ∈ f ∧ y ∈ f)).card := card_biUnion_le
      _ ≤ ∑ _y ∈ block a, c := by
        apply sum_le_sum
        intro y hy
        apply hpair
        intro hwy
        exact hw (mem_biUnion.mpr ⟨a,mem_univ _,by simpa only [hwy] using hy⟩)
      _ = c * (block a).card := by simp [Nat.mul_comm]
      _ ≤ c*d := Nat.mul_le_mul_left c (hcard a)
  · have hempty : (traceOn (univ.biUnion block) F).filter (fun e => w ∈ e) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,hwe⟩ := mem_filter.mp he
      obtain ⟨heF,hmeet⟩ := (mem_traceOn _ _ _).mp he
      obtain ⟨x,hxe,hxD⟩ := not_disjoint_iff.mp hmeet
      obtain ⟨a,_,hxa⟩ := mem_biUnion.mp hxD
      exact hcontact ⟨a,x,hxa,e,heF,hwe,hxe⟩
    simp only [vertexDegree,hempty,card_empty]
    omega

/-- The exposed trace loses at most `2d` edges at a surviving vertex under the
manuscript's Berge separation and pair-degree hypotheses. -/
theorem trace_degree_le_two_private_size {F : SimpleHypergraph V} {B : Finset V}
    (edge block : ↥B → Finset V) (hedge : ∀ v, edge v ∈ F)
    (hanchor : ∀ v, v.val ∈ block v) (hblock : ∀ v, block v ⊆ edge v)
    (hsep : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → ¬ shortBergeConnected F u v)
    {d : ℕ} (hcard : ∀ v, (block v).card ≤ d)
    (hpair : ∀ u v : V, u ≠ v → pairDegree F u v ≤ 2)
    {w : V} (hw : w ∉ univ.biUnion block) :
    vertexDegree (traceOn (univ.biUnion block) F) w ≤ 2*d := by
  apply trace_degree_le_of_unique_contact F block hw hcard (hpair w)
  intro a b x hxa y hyb e he f hf hwe hxe hwf hyf
  exact contacted_block_unique edge block hedge hanchor hblock hsep hw
    hxa hyb he hf hxe hwe hyf hwf
end LooseHamilton
