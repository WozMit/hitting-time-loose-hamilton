module

public import HittingTimeLooseHamilton.BiasedRoleCloneBias

public section

noncomputable section
open Finset FiniteEntropy
open scoped BigOperators
namespace LooseHamilton

lemma projected_event_le_sum {S A B : Type*} [Fintype S] [DecidableEq A]
    [DecidableEq B] (p : Law S) (H : Finset A) (F : S → Finset A)
    (f : A → B) (hF : ∀ s, F s ⊆ H) (b : B) :
    p.event (fun s => b ∈ (F s).image f) ≤
      ∑ a ∈ H.filter (fun a => f a=b), p.event (fun s => a∈F s) := by
  classical
  unfold Law.event
  rw [sum_comm]
  apply sum_le_sum
  intro s _
  by_cases hb : b ∈ (F s).image f
  · obtain ⟨a,ha,he⟩ := mem_image.mp hb
    have hmem : a ∈ H.filter (fun a => f a=b) := mem_filter.mpr ⟨hF s ha,he⟩
    rw [if_pos (mem_image.mpr ⟨a,ha,he⟩)]
    calc
      p.mass s = (if (fun s => a∈F s) s then p.mass s else 0) := by simp [ha]
      _ ≤ _ := single_le_sum (fun x _ => ite_nonneg (p.nonneg s) (le_refl 0)) hmem
    apply sum_le_sum
    intro x hx
    split_ifs <;> rfl
  · simp only [if_neg hb]
    apply sum_nonneg
    intro x hx
    split_ifs
    · exact p.nonneg s
    · exact le_refl _

lemma projected_collision_le {S A B : Type*} [Fintype S] [Fintype B]
    [DecidableEq A] [DecidableEq B] (p : Law S) (H : Finset A)
    (F : S → Finset A) (f : A → B) (hF : ∀ s, F s ⊆ H)
    (M : ℕ) (hM : ∀ b, (H.filter (fun a => f a=b)).card ≤ M) :
    (∑ b, (p.event (fun s => b∈(F s).image f))^2) ≤
      (M : ℝ) * ∑ a∈H, (p.event (fun s => a∈F s))^2 := by
  classical
  have hp (b : B) := projected_event_le_sum p H F f hF b
  have hb (b : B) : (p.event (fun s => b∈(F s).image f))^2 ≤
      (M : ℝ) * ∑ a∈H.filter (fun a => f a=b),
        (p.event (fun s => a∈F s))^2 := by
    have he := sum_mul_sq_le_sq_mul_sq (H.filter (fun a => f a=b))
      (fun _ => (1:ℝ)) (fun a => p.event (fun s => a∈F s))
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at he
    have hc : ((H.filter (fun a => f a=b)).card:ℝ) ≤ M := by exact_mod_cast hM b
    have hz : 0 ≤ p.event (fun s => b∈(F s).image f) := p.event_nonneg _
    have hs : 0 ≤ ∑ a∈H.filter (fun a => f a=b),
        (p.event (fun s => a∈F s))^2 := sum_nonneg (fun _ _ => sq_nonneg _)
    exact (sq_le_sq₀ hz (le_trans hz (hp b))).mpr (hp b) |>.trans
      (he.trans (mul_le_mul_of_nonneg_right hc hs))
  calc
    _ ≤ ∑ b, (M:ℝ) * ∑ a∈H.filter (fun a => f a=b),
        (p.event (fun s => a∈F s))^2 := sum_le_sum (fun b _ => hb b)
    _ = _ := by
      rw [← mul_sum]
      congr 1
      simp only [sum_filter]
      rw [sum_comm]
      simp

end LooseHamilton

namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers G : SimpleHypergraph V}

lemma cloneHost_projection_fibre_card (U : Finset (V × Fin 3))
    (hG : ∀ e∈G,e.card=r) (e : Finset V) :
    ((cloneHost G U).filter (fun B => B.image Prod.fst=e)).card ≤ r*r := by
  by_cases he : e∈G
  · calc
      _ ≤ (directedCloneEdges e).card := by
        apply card_le_card
        intro B hB
        obtain ⟨hB,hp⟩ := mem_filter.mp hB
        obtain ⟨hB,_⟩ := mem_filter.mp hB
        obtain ⟨e',he',hBe⟩ := mem_biUnion.mp hB
        have hh := (directedCloneEdges_project hBe).symm.trans hp
        exact hh ▸ hBe
      _ ≤ _ := by simpa [hG e he] using directedCloneEdges_card_le e
  · have hh : ((cloneHost G U).filter (fun B => B.image Prod.fst=e))=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hB,hp⟩ := mem_filter.mp hB
      obtain ⟨hB,_⟩ := mem_filter.mp hB
      obtain ⟨e',he',hBe⟩ := mem_biUnion.mp hB
      exact he (((directedCloneEdges_project hBe).symm.trans hp) ▸ he')
    rw [hh,card_empty]
    exact Nat.zero_le _

lemma biasedCloneLift_project (root : ↥markers) (a : ↥root.val)
    (C : BiasedCycleState r markers G) :
    (biasedCloneLift root a C).image (fun B => B.image Prod.fst)=C.val := by
  exact ((biasedConnectedCycle C).directedWitness root a).cloneMatching_project

lemma fibre_original_collision_le (hr : 3≤r) (hG : ∀ e∈G,e.card=r)
    (root : ↥markers) (a : ↥root.val) (C₀ : BiasedCycleState r markers G)
    (p : Law (BiasedCloneFibre root a C₀))
    (labels : ↥(biasedCloneUniverse root a C₀) ≃ Fin (r*ordinaryEdgeCount r markers)) :
    (∑ e : Finset V, (p.event (fun C => e∈C.val.val))^2) ≤
      (r:ℝ)^2 * ∑ f∈(biasedCloneKahnHost hG root a C₀ labels).edges,
        ((p.map (biasedCloneKahnMatching hr hG root a C₀ labels)).event
          (fun M => f∈M.val.val))^2 := by
  have h := projected_collision_le p (cloneHost G (biasedCloneUniverse root a C₀))
    (fun C => biasedCloneLift root a C.val) (fun B => B.image Prod.fst)
    (biasedCloneFibre_host root a C₀) (r*r)
    (cloneHost_projection_fibre_card _ hG)
  simp_rw [biasedCloneLift_project] at h
  have hs : (∑ f∈(biasedCloneKahnHost hG root a C₀ labels).edges,
        ((p.map (biasedCloneKahnMatching hr hG root a C₀ labels)).event
          (fun M => f∈M.val.val))^2) =
      ∑ B∈cloneHost G (biasedCloneUniverse root a C₀),
        (p.event (fun C => B∈biasedCloneLift root a C.val))^2 := by
    change (∑ f∈(cloneHost G (biasedCloneUniverse root a C₀)).image
      (CloneRelabel.edge _ labels), _) = _
    rw [sum_image]
    · apply sum_congr rfl
      intro B hB
      rw [biasedCloneKahn_edge_event hr hG root a C₀ labels p B
        (cloneHost_subset_slots _ _ B hB)]
    · intro B hB D hD he
      exact CloneRelabel.edge_injective_on _ labels
        (cloneHost_subset_slots _ _ B hB) (cloneHost_subset_slots _ _ D hD) he
  rw [hs]
  simpa only [Nat.cast_mul, pow_two] using h

end LooseHamilton

namespace LooseHamilton.BiasedEnsemble
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers G : SimpleHypergraph V}

/-- Convexity followed by the finite clone projection. This applies to the
actual conditional laws of connected cycles, with no role regularity assumed. -/
theorem original_collision_le (hr : 3≤r) (hG : ∀ e∈G,e.card=r)
    (root : ↥markers) (a : ↥root.val) (p : Law (BiasedCycleState r markers G)) :
    (∑ e : Finset V, (p.event (fun C => e∈C.val))^2) ≤
      (r:ℝ)^2 * ∑ z, (law root a p).mass z *
        ∑ f∈(host hr hG root a p z).edges,
          ((matchingLaw hr hG root a p z).event (fun M => f∈M.val.val))^2 := by
  have hj (e : Finset V) : (p.event (fun C => e∈C.val))^2 ≤
      ∑ z, (law root a p).mass z *
        ((fibreLaw root a p z).event (fun C => e∈C.val.val))^2 := by
    rw [event_average root a p (fun C => e∈C.val)]
    simpa only [(law root a p).total,one_mul] using
      weighted_sum_sq_le (law root a p).mass
        (fun z => (fibreLaw root a p z).event (fun C => e∈C.val.val))
        (law root a p).nonneg
  calc
    _ ≤ ∑ e : Finset V, ∑ z, (law root a p).mass z *
        ((fibreLaw root a p z).event (fun C => e∈C.val.val))^2 :=
      sum_le_sum (fun e _ => hj e)
    _ = ∑ z, (law root a p).mass z * ∑ e : Finset V,
        ((fibreLaw root a p z).event (fun C => e∈C.val.val))^2 := by
      rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ z, (law root a p).mass z * ((r:ℝ)^2 *
        ∑ f∈(host hr hG root a p z).edges,
          ((matchingLaw hr hG root a p z).event (fun M => f∈M.val.val))^2) := by
      apply sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ ((law root a p).nonneg z)
      exact fibre_original_collision_le hr hG root a (reference root a p z)
        (fibreLaw root a p z) (labels hr root a p z)
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intros; ring

end LooseHamilton.BiasedEnsemble
