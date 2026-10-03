module

public import HittingTimeLooseHamilton.StoppedCountingFamily
public import HittingTimeLooseHamilton.ProcessOrderCoordinates
public import HittingTimeLooseHamilton.Setup

public section
noncomputable section
namespace LooseHamilton.FirstFailure
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

@[expose] def host (H : Finset (Edge V r)) : SimpleHypergraph V := H.image Subtype.val

lemma mem_host (H : Finset (Edge V r)) (e : Edge V r) : e.val ∈ host H ↔ e ∈ H := by
  simp only [host,mem_image]
  constructor
  · rintro ⟨f,hf,he⟩; exact (Subtype.ext he : f=e) ▸ hf
  · intro he; exact ⟨e,he,rfl⟩

lemma host_injective : Function.Injective (host (V:=V) (r:=r)) := by
  intro H K h
  ext e
  rw [← mem_host,← mem_host,h]

lemma host_subset (H K : Finset (Edge V r)) : host H ⊆ host K ↔ H ⊆ K := by
  constructor
  · intro h e he; exact (mem_host K e).mp (h ((mem_host H e).mpr he))
  · intro h e he; obtain ⟨f,hf,rfl⟩ := mem_image.mp he; exact mem_image.mpr ⟨f,h hf,rfl⟩

lemma host_complete_subset (H : Finset (Edge V r)) : host H ⊆ completeEdges V r := by
  intro e he; obtain ⟨f,hf,rfl⟩ := mem_image.mp he; exact f.property

@[simp] lemma host_card (H : Finset (Edge V r)) : (host H).card = H.card :=
  card_image_of_injective H Subtype.val_injective

@[simp] lemma host_univ : host (univ : Finset (Edge V r)) = completeEdges V r := by
  ext e; simp [host]

lemma host_lift {H : SimpleHypergraph V} (hH : H ⊆ completeEdges V r) :
    host (liftEdges r H) = H := liftEdges_image hH

lemma lift_host (H : Finset (Edge V r)) : liftEdges r (host H) = H := by
  ext e; rw [mem_liftEdges,mem_host]

@[expose] def family (r : ℕ) (markers : SimpleHypergraph V) (ports : Finset V) :
    Finset (Finset (Edge V r)) := by
  classical
  exact univ.filter (fun C => IsMixedCycle r markers (host C) ∧ host C ⊆ allowedEdges r ports)

@[simp] lemma mem_family (markers : SimpleHypergraph V) (ports : Finset V)
    (C : Finset (Edge V r)) : C ∈ family r markers ports ↔
    IsMixedCycle r markers (host C) ∧ host C ⊆ allowedEdges r ports := by
  classical
  simp [family]

lemma surviving_image (markers : SimpleHypergraph V) (ports : Finset V)
    (H : Finset (Edge V r)) :
    (StoppedCounting.survivingFamily (family r markers ports) H).image host =
      cycleFamily r markers (host H) ports := by
  classical
  ext C
  simp only [mem_image,StoppedCounting.survivingFamily,mem_filter,mem_family,mem_cycleFamily]
  constructor
  · rintro ⟨D,⟨⟨hm,ha⟩,hd⟩,rfl⟩
    exact ⟨hm,(host_subset D H).mpr hd,ha⟩
  · rintro ⟨hm,hs,ha⟩
    have hc := hs.trans (host_complete_subset H)
    refine ⟨liftEdges r C,?_,host_lift hc⟩
    rw [host_lift hc]
    exact ⟨⟨hm,ha⟩,(host_subset _ _).mp (by rw [host_lift hc]; exact hs)⟩

lemma familyCount_eq (markers : SimpleHypergraph V) (ports : Finset V)
    (H : Finset (Edge V r)) :
    StoppedCounting.familyCount (family r markers ports) H = cycleCount r markers (host H) ports := by
  unfold StoppedCounting.familyCount cycleCount FiniteFamily.count
  rw [← surviving_image,card_image_of_injective _ host_injective]

lemma incidenceCount_eq (markers : SimpleHypergraph V) (ports : Finset V)
    (H : Finset (Edge V r)) (e : Edge V r) :
    FiniteFamily.incidenceCount (StoppedCounting.survivingFamily (family r markers ports) H) e =
      FiniteFamily.incidenceCount (cycleFamily r markers (host H) ports) e.val := by
  classical
  unfold FiniteFamily.incidenceCount
  rw [← surviving_image]
  have he : ((StoppedCounting.survivingFamily (family r markers ports) H).image host).filter
      (fun C => e.val ∈ C) =
      ((StoppedCounting.survivingFamily (family r markers ports) H).filter (fun C => e ∈ C)).image host := by
    ext C
    simp only [mem_filter,mem_image]
    constructor
    · rintro ⟨⟨D,hD,rfl⟩,he⟩; exact ⟨D,⟨hD,(mem_host D e).mp he⟩,rfl⟩
    · rintro ⟨D,⟨hD,he⟩,rfl⟩; exact ⟨⟨D,hD,rfl⟩,(mem_host D e).mpr he⟩
  rw [he,card_image_of_injective _ host_injective]

lemma marginal_eq (markers : SimpleHypergraph V) (ports : Finset V)
    (H : Finset (Edge V r)) (e : Edge V r) :
    StoppedCounting.marginal (family r markers ports) H e =
      cycleMarginal r markers (host H) ports e.val := by
  unfold StoppedCounting.marginal cycleMarginal FiniteFamily.marginal
  rw [incidenceCount_eq]
  change _ / (StoppedCounting.familyCount _ H : ℝ) = _
  rw [familyCount_eq]
  rfl

lemma uniformFamily (markers : SimpleHypergraph V) (ports : Finset V) (hr : 3 ≤ r) :
    StoppedCounting.UniformFamily (family r markers ports) (ordinaryEdgeCount r markers) := by
  intro C hC
  have hh := ((mem_family markers ports C).mp hC).1.edge_card hr
  rw [host_card] at hh
  exact hh

lemma full_count_pos (markers : SimpleHypergraph V) (ports : Finset V)
    (h : 0 < cycleCount r markers (completeEdges V r) ports) :
    0 < StoppedCounting.familyCount (family r markers ports) univ := by
  rw [familyCount_eq,host_univ]
  exact h
end LooseHamilton.FirstFailure
