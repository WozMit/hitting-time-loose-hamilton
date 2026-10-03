module

public import HittingTimeLooseHamilton.PrivateRootDensityAveraging
public import HittingTimeLooseHamilton.FrameCandidateCountsBounds

public section

/-! Structurally invalid private links are genuine collision errors. The
bound uses a fixed forbidden vertex set, not an assumed small bad-link set. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every link avoiding the source labels, target, and original ports admits
an unordered legal split. The root itself may be an original port. -/
theorem private_split_of_disjoint {r : ℕ} (hr : 3 ≤ r)
    (markers : SimpleHypergraph V) (U S q A : Finset V) (x t : V)
    (hS : S.card = r-3) (hA : A.card = r-1) (hxA : x ∉ A) (hxt : x ≠ t)
    (hsource : LegalPrivateCompletion r markers (insert x S) q)
    (htarget : LegalPrivateCompletion r markers (insert t S) q)
    (hdis : Disjoint A ((insert t S ∪ originalPorts (insert q markers)) ∪ U)) :
    ∃ R uv, PrivateRootSplitLegal r markers (allowedEdges r U) S q x t A R uv := by
  classical
  obtain ⟨uv,huv,hcard⟩ := exists_subset_card_eq (show 2 ≤ A.card by omega)
  let R := A \ uv
  have hxR : x ∉ R := fun hx => hxA (mem_sdiff.mp hx).1
  have hxuv : x ∉ uv := fun hx => hxA (huv hx)
  have hxS : x ∉ S := by
    intro hx
    have hc := hsource.private_card
    rw [insert_eq_of_mem hx,hS] at hc
    omega
  have hxports : x ∉ originalPorts (insert q markers) := by
    intro hx
    obtain ⟨m,hm,hxm⟩ := mem_biUnion.mp hx
    exact (mem_sdiff.mp (hsource.augmented_subset_active m hm hxm)).2 (mem_insert_self _ _)
  have hdecomp : uv ∪ insert x R = insert x A := by
    ext v
    simp only [R,mem_union,mem_insert,mem_sdiff]
    constructor
    · rintro (hv | rfl | ⟨hv,_⟩)
      · exact Or.inr (huv hv)
      · exact Or.inl rfl
      · exact Or.inr hv
    · rintro (rfl | hv)
      · exact Or.inr (Or.inl rfl)
      · by_cases hh : v ∈ uv
        · exact Or.inl hh
        · exact Or.inr (Or.inr ⟨hv,hh⟩)
  have hallowed : insert x A ∈ allowedEdges r U := by
    apply (mem_allowedEdges _ _ _).mpr
    constructor
    · rw [card_insert_of_notMem hxA,hA]; omega
    · have hs : insert x A ∩ U ⊆ {x} := by
        intro v hv
        obtain ⟨hv,hvU⟩ := mem_inter.mp hv
        rcases mem_insert.mp hv with rfl | hv
        · simp
        · exact False.elim (disjoint_left.mp hdis hv (mem_union_right _ hvU))
      exact (card_le_card hs).trans (by simp)
  refine ⟨R,uv,⟨hS,hA,hxA,hallowed,hsource,htarget,?_⟩⟩
  refine ⟨?_,hxR,hcard,?_,?_,?_⟩
  · dsimp [R]
    rw [card_sdiff_of_subset huv,hA,hcard]
    omega
  · exact disjoint_insert_left.mpr ⟨hxuv,sdiff_disjoint⟩
  · rw [hdecomp]
    apply disjoint_insert_left.mpr
    constructor
    · simp only [mem_union,mem_insert]
      tauto
    · exact hdis.mono_right subset_union_left
  · simp [hdecomp]

/-- Erasing the root injects structurally invalid edges into the links that
meet the displayed forbidden set. -/
theorem private_invalid_card_le {r : ℕ} (hr : 3 ≤ r)
    (markers : SimpleHypergraph V) (U S q : Finset V) (x t : V)
    (hS : S.card = r-3) (hxt : x ≠ t)
    (hsource : LegalPrivateCompletion r markers (insert x S) q)
    (htarget : LegalPrivateCompletion r markers (insert t S) q) :
    ((privateRootInvalidEdges r markers (allowedEdges r U) S q x t).card:ℝ) ≤
      (((insert t S ∪ originalPorts (insert q markers)) ∪ U).card:ℝ)*
        ((Fintype.card V - 1).choose (r-2):ℝ) := by
  classical
  let D := (insert t S ∪ originalPorts (insert q markers)) ∪ U
  let invalid := privateRootInvalidEdges r markers (allowedEdges r U) S q x t
  let bad := (univ.powersetCard (r-1)).filter fun A : Finset V => ¬ Disjoint A D
  have hinj : Set.InjOn (fun e : Finset V => e.erase x) (↑invalid : Set (Finset V)) := by
    intro e he f hf hh
    have heX := ((mem_rootEdgeUniverse _ _ _).mp (mem_filter.mp he).1).2
    have hfX := ((mem_rootEdgeUniverse _ _ _).mp (mem_filter.mp hf).1).2
    have hi := congrArg (insert x) hh
    simpa only [insert_erase heX,insert_erase hfX] using hi
  have hsub : invalid.image (fun e => e.erase x) ⊆ bad := by
    intro A hA
    obtain ⟨e,he,rfl⟩ := mem_image.mp hA
    obtain ⟨heroot,hbad⟩ := mem_filter.mp he
    obtain ⟨hecard,hxe⟩ := (mem_rootEdgeUniverse _ _ _).mp heroot
    have hcard : (e.erase x).card = r-1 := by rw [card_erase_of_mem hxe,hecard]
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,hcard⟩,?_⟩
    intro hd
    exact hbad (private_split_of_disjoint hr markers U S q (e.erase x) x t hS hcard
      (notMem_erase _ _) hxt hsource htarget hd)
  have hc : invalid.card ≤ bad.card := by
    rw [← card_image_of_injOn hinj]
    exact card_le_card hsub
  have hb := AuxiliaryFrame.Frame.powersetCard_meeting_le (r := r-1) (univ : Finset V) D
    (by omega)
  have hrr : r-1-1 = r-2 := by omega
  simpa only [bad,card_univ,hrr] using (Nat.cast_le.mpr hc).trans hb

end LooseHamilton
