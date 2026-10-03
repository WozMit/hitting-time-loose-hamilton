module

public import HittingTimeLooseHamilton.CoreFiniteBounds
public import HittingTimeLooseHamilton.CoreCompletionEquiv
public import HittingTimeLooseHamilton.CoreParameterBounds
public import HittingTimeLooseHamilton.CompletionMatching

public section

/-! Uniform eventual verification of every conditioned-core parameter. -/
noncomputable section
namespace LooseHamilton
open Finset Filter

/-- The finite parameter statement holds uniformly for every good host and every
permitted private-block choice, once n is sufficiently large for the fixed r. -/
theorem core_admissible_eventually {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ (F : SimpleHypergraph (Fin n)),
      F ⊆ completeEdges (Fin n) r → NoIsolated F →
      exceptionalSetGood r 20 F →
      ∀ C : CoreBlockFamily r F (lowDegreeVertices F),
      |(r : ℝ) * F.card / n - Real.log n| ≤ 2 * Real.log (Real.log n) + 1 →
      r-1 ∣ n →
      CoreAdmissible (V := ↥C.coreVertices) r (F.card-(traceOn C.deleted F).card)
        (fun w => coreLowerBound C.deleted (traceOn C.deleted F) w.val)
        (restrictEdges C.coreVertices C.markers) ((2*(r-2) : ℕ)+2) := by
  filter_upwards [core_parameter_bounds_eventually r] with n hn
  intro F hF hNI hg C hdensity hdiv
  have hs : ((lowDegreeVertices F).card : ℝ) ≤ (n : ℝ) ^ (1/12 : ℝ) := by
    convert hg.low_card_bound using 1 <;> simp [Fintype.card_fin]
  have hT : ((traceOn C.deleted F).card : ℝ) ≤
      20*(r-2 : ℕ)*(lowDegreeVertices F).card*Real.log n := by
    simpa only [Fintype.card_fin] using C.trace_card_bound hg
  obtain ⟨hN,hd,hm,hell⟩ := hn (lowDegreeVertices F).card F.card
    (traceOn C.deleted F).card hs (card_le_card (filter_subset _ _)) hT hdensity
  have hsupport : ∀ e ∈ C.markers, e ⊆ C.coreVertices := by
    intro e he
    obtain ⟨v,_,rfl⟩ := mem_image.mp he
    exact C.ports_core v
  have hc : (restrictEdges C.coreVertices C.markers).card = (lowDegreeVertices F).card := by
    rw [restrictEdges_card_of_supported _ _ hsupport,C.markers_card]
  have hnv : Fintype.card ↥C.coreVertices = n-(r-2)*(lowDegreeVertices F).card := by
    rw [Fintype.card_coe,C.coreVertices_card,Fintype.card_fin]
  refine ⟨hr,C.markers_matching.restrict _ hsupport,?_,?_,?_,?_,by positivity,?_,?_⟩
  · rw [hc]; exact hg.low_nonempty
  · rw [hc,hnv]; exact hm
  · rw [Fintype.card_coe,hc,← C.markers_card]
    exact C.core_divisibility (by omega) (by simpa only [Fintype.card_fin] using hdiv)
  · simpa only [meanDegree,hnv] using hd
  · intro w
    have hj := C.trace_degree_bound hg w.val w.property
    have hh := hell (vertexDegree (traceOn C.deleted F) w.val) hj
    simpa only [coreLowerBound,lowerDegreeBase,Fintype.card_fin,hnv] using hh
  · exact ⟨coreCompletionEquiv r F.card C.deleted (traceOn C.deleted F)
      ⟨coreOutside C.deleted F,C.actual_core_mem hF hNI⟩⟩
end LooseHamilton
