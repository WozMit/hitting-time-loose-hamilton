module

public import HittingTimeLooseHamilton.VertexRelabel

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem relabelEdges_swap_involutive (y z : V) :
    Function.Involutive (relabelEdges (Equiv.swap y z)) := by
  intro E
  simp only [relabelEdges, image_image]
  have h : (fun e : Finset V => image (⇑(Equiv.swap y z)) (image (⇑(Equiv.swap y z)) e)) = id := by
    funext e
    simp [image_image, Function.comp_def]
  change E.image (fun e => image (⇑(Equiv.swap y z)) (image (⇑(Equiv.swap y z)) e)) = E
  rw [h, image_id]

theorem relabelCycle_mem_complete {r : ℕ} {markers E : Finset (Finset V)}
    (σ : Equiv.Perm V) (hM : ∀ m ∈ markers, m.image σ = m)
    (ports : Finset V) (hP : ports.image σ = ports)
    (hE : E ∈ cycleFamily r markers (completeEdges V r) ports) :
    relabelEdges σ E ∈ cycleFamily r markers (completeEdges V r) ports := by
  obtain ⟨⟨C⟩, hhost, hallowed⟩ := (mem_cycleFamily _ _ _ _ _).mp hE
  apply (mem_cycleFamily _ _ _ _ _).mpr
  refine ⟨⟨C.relabel σ hM⟩, ?_, ?_⟩
  · intro e he
    change e ∈ E.image (Finset.image σ) at he
    obtain ⟨e0,he0,rfl⟩ := mem_image.mp he
    simpa [card_image_of_injective _ σ.injective] using hhost he0
  · intro e he
    change e ∈ E.image (Finset.image σ) at he
    obtain ⟨e0,he0,rfl⟩ := mem_image.mp he
    have ha := hallowed he0
    simp only [allowedEdges, mem_filter, mem_completeEdges] at ha ⊢
    constructor
    · simpa [card_image_of_injective _ σ.injective] using ha.1
    · rw [← hP, ← image_inter _ _ σ.injective, card_image_of_injective _ σ.injective]
      exact ha.2

/-- Swapping the endpoints of a pair interchanges the two directed families
when every marked pair and the prohibition set are preserved. -/
theorem directedCycleCount_eq_swap {r : ℕ} {markers : Finset (Finset V)}
    (ports : Finset V) (root distinguished : ↥markers) (a : ↥root.val)
    (y z : V) (hM : ∀ m ∈ markers, m.image (Equiv.swap y z) = m)
    (hP : ports.image (Equiv.swap y z) = ports)
    (ha : Equiv.swap y z a.val = a.val) :
    directedCycleCount r markers (completeEdges V r) ports root distinguished a y =
      directedCycleCount r markers (completeEdges V r) ports root distinguished a z := by
  let σ := Equiv.swap y z
  have transport {E : Finset (Finset V)} {u : V}
      (h : E ∈ directedCycleFamily r markers (completeEdges V r) ports root distinguished a u) :
      relabelEdges σ E ∈ directedCycleFamily r markers (completeEdges V r) ports
        root distinguished a (σ u) := by
    obtain ⟨hE, C,hroot,hd⟩ := (mem_directedCycleFamily _ _ _ _ _ _ _ _ _).mp h
    apply (mem_directedCycleFamily _ _ _ _ _ _ _ _ _).mpr
    refine ⟨relabelCycle_mem_complete σ hM ports hP hE, C.relabel σ hM, ?_, ?_⟩
    · apply Subtype.ext
      rw [C.relabel_markerStart σ hM root, hroot]
      exact ha
    · rw [C.relabel_markerStart σ hM distinguished, hd]
  apply Finset.card_bij (fun E _ => relabelEdges σ E)
  · intro E hE
    simpa [σ] using transport hE
  · intro E hE F hF h
    exact (relabelEdges_swap_involutive y z).injective h
  · intro E hE
    refine ⟨relabelEdges σ E, ?_, (relabelEdges_swap_involutive y z) E⟩
    simpa [σ] using transport hE

theorem IsPairMatching.swap_marker_image {markers : Finset (Finset V)}
    (hM : IsPairMatching markers) (distinguished : ↥markers) {y z : V}
    (hp : distinguished.val = {y,z}) :
    ∀ m ∈ markers, m.image (Equiv.swap y z) = m := by
  intro m hm
  by_cases he : m = distinguished.val
  · subst m
    simp [hp, pair_comm]
  · have hd := hM.2 hm distinguished.property he
    calc
      m.image (Equiv.swap y z) = m.image id := by
        apply image_congr
        intro x hx
        have hxy : x ≠ y := by
          intro hh
          subst x
          exact disjoint_left.mp hd hx (by simp [hp])
        have hxz : x ≠ z := by
          intro hh
          subst x
          exact disjoint_left.mp hd hx (by simp [hp])
        exact Equiv.swap_apply_of_ne_of_ne hxy hxz
      _ = m := image_id

theorem IsPairMatching.swap_root_fixed {markers : Finset (Finset V)}
    (hM : IsPairMatching markers) (root distinguished : ↥markers)
    (hne : root ≠ distinguished) (a : ↥root.val) {y z : V}
    (hp : distinguished.val = {y,z}) : Equiv.swap y z a.val = a.val := by
  have hd := hM.2 root.property distinguished.property
    (fun h => hne (Subtype.ext h))
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact disjoint_left.mp hd a.property (by simp [hp, h])
  · intro h
    exact disjoint_left.mp hd a.property (by simp [hp, h])

/-- The two relative directions are equipotent in the complete host. The
prohibition set may be retained if the endpoint swap preserves it. -/
theorem directedCycleCount_eq_reverse_complete {r : ℕ}
    {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (ports : Finset V) (root distinguished : ↥markers) (hne : root ≠ distinguished)
    (a : ↥root.val) {y z : V} (hp : distinguished.val = {y,z})
    (hP : ports.image (Equiv.swap y z) = ports) :
    directedCycleCount r markers (completeEdges V r) ports root distinguished a y =
      directedCycleCount r markers (completeEdges V r) ports root distinguished a z :=
  directedCycleCount_eq_swap ports root distinguished a y z
    (hM.swap_marker_image distinguished hp) hP (hM.swap_root_fixed root distinguished hne a hp)
end LooseHamilton
