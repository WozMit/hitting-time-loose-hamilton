module

public import HittingTimeLooseHamilton.UniformPrefixProbability
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

@[expose] instance rootFiniteOrderNonempty (B : Type*) [Fintype B] : Nonempty (FiniteOrder B) :=
  ⟨Fintype.equivFin B⟩

/-- Prefix in a selected part, viewed in the original universe. -/
@[expose] def rootPartPrefix (S : Finset A) (σ : FiniteOrder ↥S) (j : ℕ) : Finset A :=
  (orderPrefix σ j).image Subtype.val

lemma rootPartPrefix_subset (S : Finset A) (σ : FiniteOrder ↥S) (j : ℕ) :
    rootPartPrefix S σ j⊆S := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
  exact y.property

lemma rootPartPrefix_card (S : Finset A) (σ : FiniteOrder ↥S) (j : ℕ) (hj : j≤S.card) :
    (rootPartPrefix S σ j).card=j := by
  rw [rootPartPrefix,card_image_of_injective _ Subtype.val_injective,orderPrefix_card]
  simpa only [Fintype.card_coe] using hj

lemma rootPartPrefix_mono (S : Finset A) (σ : FiniteOrder ↥S) {j k : ℕ} (hjk : j≤k) :
    rootPartPrefix S σ j⊆rootPartPrefix S σ k := by
  apply image_subset_image
  intro x hx
  exact (mem_orderPrefix σ k x).mpr (lt_of_lt_of_le ((mem_orderPrefix σ j x).mp hx) hjk)

/-- Independent orders of the hit-set and its complement reconstruct a set with a specified hit count. -/
@[expose] def rootCountSet (S : Finset A) (b j : ℕ)
    (σ : FiniteOrder ↥S × FiniteOrder ↥((univ:Finset A)\S)) : Finset A :=
  rootPartPrefix S σ.1 j ∪ rootPartPrefix (univ\S) σ.2 (b-j)

lemma rootCountSet_disjoint (S : Finset A) (b j : ℕ)
    (σ : FiniteOrder ↥S × FiniteOrder ↥((univ:Finset A)\S)) :
    Disjoint (rootPartPrefix S σ.1 j) (rootPartPrefix (univ\S) σ.2 (b-j)) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact (mem_sdiff.mp (rootPartPrefix_subset _ _ _ hy)).2 (rootPartPrefix_subset _ _ _ hx)

lemma rootCountSet_card (S : Finset A) (b j : ℕ)
    (σ : FiniteOrder ↥S × FiniteOrder ↥((univ:Finset A)\S))
    (hjb : j≤b) (hjS : j≤S.card) (hjC : b-j≤(univ\S).card) :
    (rootCountSet S b j σ).card=b := by
  rw [rootCountSet,card_union_of_disjoint (rootCountSet_disjoint S b j σ),
    rootPartPrefix_card _ _ _ hjS,rootPartPrefix_card _ _ _ hjC]
  omega

lemma rootCountSet_inter (S : Finset A) (b j : ℕ)
    (σ : FiniteOrder ↥S × FiniteOrder ↥((univ:Finset A)\S)) :
    rootCountSet S b j σ ∩ S=rootPartPrefix S σ.1 j := by
  ext x
  simp only [rootCountSet,mem_inter,mem_union]
  constructor
  · rintro ⟨hx,hs⟩
    rcases hx with hx|hx
    · exact hx
    · exact False.elim ((mem_sdiff.mp (rootPartPrefix_subset _ _ _ hx)).2 hs)
  · intro hx
    exact ⟨Or.inl hx,rootPartPrefix_subset _ _ _ hx⟩

lemma rootCountSet_hit_card (S : Finset A) (b j : ℕ)
    (σ : FiniteOrder ↥S × FiniteOrder ↥((univ:Finset A)\S)) (hjS : j≤S.card) :
    (rootCountSet S b j σ ∩ S).card=j := by
  rw [rootCountSet_inter,rootPartPrefix_card _ _ _ hjS]

lemma rootPartPrefix_eq_iff (S T : Finset A) (σ : FiniteOrder ↥S) (j : ℕ) :
    rootPartPrefix S σ j=T∩S ↔ orderPrefix σ j=T.subtype (fun x=>x∈S) := by
  constructor
  · intro h
    ext x
    have hx := congrArg (fun W : Finset A=>x.val∈W) h
    have hh : x.val∈rootPartPrefix S σ j ↔ x∈orderPrefix σ j := by
      simp only [rootPartPrefix,mem_image]
      constructor
      · rintro ⟨y,hy,he⟩
        have : y=x := Subtype.ext he
        simpa [this] using hy
      · intro hx
        exact ⟨x,hx,rfl⟩
    simpa only [hh,mem_inter,x.property,and_true,mem_subtype] using Iff.of_eq hx
  · intro h
    ext x
    simp only [rootPartPrefix,h,mem_image,mem_subtype,mem_inter]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy,y.property⟩
    · rintro ⟨ht,hs⟩
      exact ⟨⟨x,hs⟩,ht,rfl⟩

lemma rootCountSet_eq_iff (S T : Finset A) (b j : ℕ)
    (σ : FiniteOrder ↥S × FiniteOrder ↥((univ:Finset A)\S)) :
    rootCountSet S b j σ=T ↔
      orderPrefix σ.1 j=T.subtype (fun x=>x∈S) ∧
      orderPrefix σ.2 (b-j)=T.subtype (fun x=>x∈(univ\S)) := by
  rw [←rootPartPrefix_eq_iff,←rootPartPrefix_eq_iff]
  constructor
  · intro h
    constructor
    · rw [←h,rootCountSet_inter]
    · rw [←h]
      ext x
      simp only [rootCountSet,mem_inter,mem_union,mem_sdiff,mem_univ,true_and]
      have hp := rootPartPrefix_subset S σ.1 j (x:=x)
      have hc := rootPartPrefix_subset (univ\S) σ.2 (b-j) (x:=x)
      simp only [mem_sdiff,mem_univ,true_and] at hc
      tauto
  · rintro ⟨h1,h2⟩
    unfold rootCountSet
    rw [h1,h2]
    ext x
    simp
    tauto

lemma rootCountSet_probability (S T : Finset A) (b j : ℕ)
    (hjb : j≤b) (hjS : j≤S.card) (hjC : b-j≤(univ\S).card)
    (hT : T.card=b) (hTS : (T∩S).card=j) :
    ((FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder ↥S)).prod
      (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder ↥((univ:Finset A)\S)))).event
      (fun σ=>rootCountSet S b j σ=T) =
        1/((S.card.choose j:ℝ)*((univ\S).card.choose (b-j):ℝ)) := by
  classical
  have htc : (T.subtype (fun x=>x∈(univ\S))).card=b-j := by
    rw [card_subtype]
    have he : T.filter (fun x=>x∈(univ\S))=T\S := by ext x; simp
    rw [he]
    have hh := card_sdiff_add_card_inter T S
    omega
  have hts : (T.subtype (fun x=>x∈S)).card=j := by
    rw [card_subtype]
    have he : T.filter (fun x=>x∈S)=T∩S := by ext x; simp
    rw [he,hTS]
  simp_rw [rootCountSet_eq_iff]
  have hev := FiniteEntropy.Law.event_prod_and
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder ↥S))
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder ↥((univ:Finset A)\S)))
    (fun σ=>orderPrefix σ j=T.subtype (fun x=>x∈S))
    (fun σ=>orderPrefix σ (b-j)=T.subtype (fun x=>x∈(univ\S)))
  rw [hev,FiniteEntropy.Law.uniform_event,FiniteEntropy.Law.uniform_event]
  rw [uniform_order_prefix_probability j (by simpa only [Fintype.card_coe] using hjS) _ hts,
      uniform_order_prefix_probability (b-j) (by simpa only [Fintype.card_coe] using hjC) _ htc]
  simp only [Fintype.card_coe]
  ring
end LooseHamilton
