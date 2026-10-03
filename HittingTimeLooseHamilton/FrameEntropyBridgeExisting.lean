module

public import HittingTimeLooseHamilton.FrameCandidateCounts
public import HittingTimeLooseHamilton.FrameEntropyBridgeProbability
public import HittingTimeLooseHamilton.FrameEntropyBiasedInstance
public import HittingTimeLooseHamilton.EntropyExceptionalRoles

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
open scoped BigOperators
local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

@[expose] def existingCandidateEdges (F : Frame r original) (H : Finset (Finset V)) :=
  (F.rawHost H).filter (fun e => Disjoint e (originalPorts F.markers))

@[expose] def existingCandidates (F : Frame r original) (H : Finset (Finset V)) :=
  F.candidates.filter (fun c => c.1 ∪ {c.2.1,c.2.2} ∈ F.rawHost H)

lemma existingCandidateEdges_subset (F : Frame r original) (H : Finset (Finset V)) :
    F.existingCandidateEdges H ⊆ F.candidateEdges := by
  intro e he
  obtain ⟨hH,hd⟩ := mem_filter.mp he
  obtain ⟨hsub,ha⟩ := mem_filter.mp hH
  obtain ⟨hc,hp⟩ := (mem_allowedEdges _ _ _).mp (mem_inter.mp hsub).2
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨ha,hc⟩,hd,hp⟩

lemma existingCandidates_eq (F : Frame r original) (hr : 2 ≤ r)
    (H : Finset (Finset V)) :
    F.existingCandidates H = (F.existingCandidateEdges H).biUnion edgeCandidates := by
  ext c
  simp only [existingCandidates,candidates,mem_filter,mem_univ,true_and,mem_biUnion]
  constructor
  · rintro ⟨hc,he⟩
    obtain ⟨e,hec,hce⟩ := (F.legalCandidate_iff hr c).mp hc
    obtain ⟨p,hp,hpc⟩ := mem_image.mp hce
    have hsame : c.1 ∪ {c.2.1,c.2.2}=e := by
      rw [← hpc]; exact candidate_union_of_role hp
    refine ⟨e,mem_filter.mpr ⟨hsame ▸ he,?_⟩,mem_image.mpr ⟨p,hp,hpc⟩⟩
    exact (mem_filter.mp hec).2.1
  · rintro ⟨e,he,hc⟩
    refine ⟨(F.legalCandidate_iff hr c).mpr ⟨e,F.existingCandidateEdges_subset H he,hc⟩,?_⟩
    obtain ⟨p,hp,hpc⟩ := mem_image.mp hc
    rw [← hpc,candidate_union_of_role hp]
    exact (mem_filter.mp he).1

lemma edgeCandidates_disjoint {e f : Finset V} (hef : e ≠ f) :
    Disjoint (edgeCandidates e) (edgeCandidates f) := by
  apply disjoint_left.mpr
  intro c hc hd
  obtain ⟨p,hp,hpc⟩ := mem_image.mp hc
  obtain ⟨q,hq,hqc⟩ := mem_image.mp hd
  apply hef
  calc
    e = c.1 ∪ {c.2.1,c.2.2} := by rw [← hpc]; exact (candidate_union_of_role hp).symm
    _ = f := by rw [← hqc]; exact candidate_union_of_role hq

/-- Exact dictionary between candidate triples and ordered roles on existing edges,
valid for every predicate, hence in particular for strict exceptional tests. -/
theorem existingCandidates_filter_card (F : Frame r original) (hr : 2 ≤ r)
    (H : Finset (Finset V)) (P : Finset V × V × V → Prop) :
    ((F.existingCandidates H).filter P).card =
      ∑ e ∈ F.existingCandidateEdges H,
        (e.offDiag.filter (fun uv => P (e \ {uv.1,uv.2},uv))).card := by
  rw [F.existingCandidates_eq hr H,filter_biUnion,card_biUnion]
  · apply sum_congr rfl
    intro e he
    unfold edgeCandidates
    rw [filter_image,card_image_of_injective]
    intro a b h
    exact congrArg Prod.snd h
  · intro e he f hf hne
    exact (edgeCandidates_disjoint hne).mono (filter_subset _ _) (filter_subset _ _)

theorem existingCandidates_card (F : Frame r original) (hr : 2 ≤ r)
    (H : Finset (Finset V)) :
    (F.existingCandidates H).card = (F.existingCandidateEdges H).card*(r*(r-1)) := by
  rw [F.existingCandidates_eq hr H]
  exact edgeCandidates_biUnion_card _ (fun e he =>
    (mem_powersetCard.mp (mem_filter.mp (F.existingCandidateEdges_subset H he)).1).2)

/-- The printed strict relative test, using actual completion and cycle counts. -/
@[expose] def existingExceptional (F : Frame r original) (H : Finset (Finset V)) (t : ℝ) :=
  (F.existingCandidates H).filter (fun c =>
    t < |(F.completionCount H c:ℝ) /
      ((F.cycleCount H:ℝ)/(((r:ℝ)-1)^2*F.mu H))-1|)

@[expose] def existingExceptionalProportion (F : Frame r original) (H : Finset (Finset V)) (t : ℝ) : ℝ :=
  ((F.existingExceptional H t).card:ℝ)/(F.existingCandidates H).card

end LooseHamilton.AuxiliaryFrame.Frame
