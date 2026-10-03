module

public import HittingTimeLooseHamilton.RootTestRegistrations
public import HittingTimeLooseHamilton.RootSamplingInterpretation

public section

/-! The registered common event supplies actual good root edges, before a
split is chosen. No link-count hypothesis is postulated here. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def rootGoodEdges (H Γ : SimpleHypergraph V) (x : V) : SimpleHypergraph V :=
  (H.filter fun e => x ∈ e) \ Γ

/-- Outside the occupancy failure, more than one third of the current root
edges pass the actual test; the weak bound is convenient for migration. -/
theorem rootGoodEdges_card_lower (r : ℕ) (F H Γ : SimpleHypergraph V) (x : V)
    (hΓ : Γ ⊆ rootEdgeUniverse r x)
    (hgood : ¬ RootLinkBad Γ (vertexDegree H x) (F,H)) :
    (vertexDegree H x : ℝ) / 3 ≤ (rootGoodEdges H Γ x).card := by
  have hi : (H.filter fun e => x ∈ e) ∩ Γ = H ∩ Γ := by
    ext e
    simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨he,_⟩,hΓe⟩; exact ⟨he,hΓe⟩
    · rintro ⟨he,hΓe⟩
      exact ⟨⟨he, ((mem_rootEdgeUniverse _ _ _).mp (hΓ hΓe)).2⟩,hΓe⟩
  have hc := card_sdiff_add_card_inter (H.filter fun e => x ∈ e) Γ
  rw [hi] at hc
  change (rootGoodEdges H Γ x).card + (H ∩ Γ).card = vertexDegree H x at hc
  have hstrict : 3 * (H ∩ Γ).card < 2 * vertexDegree H x := by
    simpa only [RootLinkBad, not_le] using hgood
  have hcR : ((rootGoodEdges H Γ x).card : ℝ) + (H ∩ Γ).card = vertexDegree H x := by
    exact_mod_cast hc
  have hsR : (3 : ℝ) * (H ∩ Γ).card < 2 * vertexDegree H x := by
    exact_mod_cast hstrict
  linarith

/-- Unpack the actual registered nonfailure on its observable regularity and
density gates. This works for a label selected after observing the outcome. -/
theorem RegisteredRootTest.not_bad_on_gates {r h M : ℕ} {ell : V → ℕ}
    (test : RegisteredRootTest V r h) (c : ℝ)
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (hn : ¬ test.failure M ell c ω)
    (htime : M ≤ test.time ∧ test.time ≤ (completeEdges V r).card)
    (hpresent : test.prescribed ⊆ (rootSamplingPair r M ell test.time ω).2)
    (hdef : (∑ v, rootAdjustedDeficit test.root ell
      (rootFreePairObservation r M ell test.time test.root ω).1 v) ≤ 1)
    (hdegree : c * FrameScales.L1 (Fintype.card V) ≤
      ((test.time - (rootFreePairObservation r M ell test.time test.root ω).2.card : ℕ) : ℝ))
    (hdensity : rootLinkDensity r test.root
      (test.badSet (rootFreePairObservation r M ell test.time test.root ω)) ≤
        FrameScales.rho (Fintype.card V)) :
    ¬ RootLinkBad (test.badSet (rootFreePairObservation r M ell test.time test.root ω))
      (test.time - (rootFreePairObservation r M ell test.time test.root ω).2.card)
      (rootSamplingPair r M ell test.time ω) := by
  intro hb
  exact hn ⟨htime.1,htime.2,hpresent,hdef,hdegree,hdensity,hb⟩

end LooseHamilton
