module

public import HittingTimeLooseHamilton.RootEventGoodLinks
public import HittingTimeLooseHamilton.PrivateMigrationMobility

public section

/-! Select one split from each good sampled root edge. The selected labels
are jointly distinct because each label reconstructs its root edge. This turns
registered root-test nonfailure into the actual private-migration inequality. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual private mobility from the actual root-link occupancy event. The
candidate argument is used separately to establish the observable density gate;
this theorem discharges the formerly abstract good-link sampling hypothesis. -/
theorem private_mobility_of_root_test (r h time : ℕ)
    (markers F H : SimpleHypergraph V) (S q U : Finset V) (x t : V)
    (c : ℝ) (hr : 3 ≤ r) (hc : 0 ≤ c)
    (hH : H ⊆ completeEdges V r)
    (htarget : LegalPrivateCompletion r markers (insert t S) q)
    (hμ : 0 < privateRootSourceMean r H S x)
    (hn : ¬ RootLinkBad
      ((registerPrivateRootTest r h time markers S q U x t c).badSet (F,H))
      (vertexDegree H x) (F,H)) :
    (c/3) * (vertexDegree H x : ℝ) / privateRootSourceMean r H S x *
        (completionCount r markers (fixedPortHost H U) (insert x S) q : ℝ) ≤
      completionCount r markers (fixedPortHost H U) (insert t S) q := by
  classical
  let G := fixedPortHost H U
  let Γ := (registerPrivateRootTest r h time markers S q U x t c).badSet (F,H)
  let E := rootGoodEdges H Γ x
  have hΓ : Γ ⊆ rootEdgeUniverse r x :=
    (registerPrivateRootTest r h time markers S q U x t c).bad_subset _
  have hex : ∀ e : ↥E, ∃ a : Finset V × Finset V,
      PrivateMigrationLegal r markers G (insert t S) q x a.1 a.2 ∧
      c * (completionCount r markers G (insert x S) q : ℝ) /
          privateRootSourceMean r H S x ≤
        (privateMigrationSummand r markers G (insert t S) q x a : ℝ) ∧
      a.2 ∪ insert x a.1 = e.val := by
    intro e
    obtain ⟨he,hnot⟩ := mem_sdiff.mp e.property
    obtain ⟨heH,hxe⟩ := mem_filter.mp he
    have heU : e.val ∈ rootEdgeUniverse r x :=
      (mem_rootEdgeUniverse _ _ _).mpr ⟨(mem_completeEdges _ _).mp (hH heH), hxe⟩
    have hnotbad : ¬ PrivateRootBad r markers (allowedEdges r U) G H S q x t c (e.val.erase x) := by
      intro hb
      apply hnot
      exact mem_filter.mpr ⟨heU,hb⟩
    obtain ⟨R,uv,hlegal,hbound⟩ := privateRoot_not_bad_witness r markers
      (allowedEdges r U) G H S q x t c (e.val.erase x) hnotbad
    have hedge : insert x (e.val.erase x) = e.val := insert_erase hxe
    have heallowed : e.val ∈ allowedEdges r U := hedge ▸ hlegal.edge_allowed
    have heG : e.val ∈ G := mem_filter.mpr ⟨heH,(mem_allowedEdges _ _ _).mp heallowed |>.2⟩
    refine ⟨(R,uv), hlegal.actual_label (hedge.symm ▸ heG), hbound, ?_⟩
    exact (mem_singleton.mp hlegal.split_legal.edge_mem).trans hedge
  choose chooseLabel hchoose using hex
  have hinj : Function.Injective chooseLabel := by
    intro e f hef
    apply Subtype.ext
    exact (hchoose e).2.2.symm.trans ((congrArg (fun a : Finset V × Finset V =>
      a.2 ∪ insert x a.1) hef).trans (hchoose f).2.2)
  let good := univ.image chooseLabel
  have hcard : good.card = E.card := by
    rw [show good = univ.image chooseLabel from rfl, card_image_of_injective _ hinj, card_univ,
      Fintype.card_coe]
  have hlegal : good ⊆ privateMigrationLabels r markers G (insert t S) q x := by
    intro a ha
    obtain ⟨e,_,rfl⟩ := mem_image.mp ha
    exact (mem_privateMigrationLabels _ _ _ _ _ _ _).mpr (hchoose e).1
  have hbound : ∀ a ∈ good,
      c * (completionCount r markers G (insert x S) q : ℝ) / privateRootSourceMean r H S x ≤
        (privateMigrationSummand r markers G (insert t S) q x a : ℝ) := by
    intro a ha
    obtain ⟨e,_,rfl⟩ := mem_image.mp ha
    exact (hchoose e).2.1
  have hdegree : (vertexDegree H x : ℝ)/3 ≤ (good.card : ℝ) := by
    rw [hcard]
    exact rootGoodEdges_card_lower r F H Γ x hΓ hn
  have hscale : 0 ≤ c * (completionCount r markers G (insert x S) q : ℝ) /
      privateRootSourceMean r H S x := div_nonneg (mul_nonneg hc (Nat.cast_nonneg _)) hμ.le
  calc
    _ = ((vertexDegree H x : ℝ)/3) *
        (c * (completionCount r markers G (insert x S) q : ℝ) / privateRootSourceMean r H S x) := by ring
    _ ≤ (good.card : ℝ) *
        (c * (completionCount r markers G (insert x S) q : ℝ) / privateRootSourceMean r H S x) :=
      mul_le_mul_of_nonneg_right hdegree hscale
    _ = ∑ _a ∈ good, c * (completionCount r markers G (insert x S) q : ℝ) /
        privateRootSourceMean r H S x := by simp
    _ ≤ ∑ a ∈ good, (privateMigrationSummand r markers G (insert t S) q x a : ℝ) :=
      sum_le_sum hbound
    _ ≤ _ := privateMigration_good_sum_le hr htarget good hlegal

end LooseHamilton
