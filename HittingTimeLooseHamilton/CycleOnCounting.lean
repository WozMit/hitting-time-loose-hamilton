module

public import HittingTimeLooseHamilton.VertexRestriction
public import HittingTimeLooseHamilton.Operations
public import HittingTimeLooseHamilton.Counting

public section

/-! # Counting cycles on active vertices

Ambient edge sets and subtype edge sets give equivalent finite families.
-/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def cycleOnFamily (r : ℕ) (S : Finset V) (markers host : Finset (Finset V)) :
    Finset (Finset (Finset V)) := by
  classical
  exact univ.filter (fun E => IsMixedCycleOn r S markers E ∧ E ⊆ host)

@[simp] theorem mem_cycleOnFamily (r : ℕ) (S : Finset V)
    (markers host E : Finset (Finset V)) :
    E ∈ cycleOnFamily r S markers host ↔ IsMixedCycleOn r S markers E ∧ E ⊆ host := by
  classical
  simp [cycleOnFamily]

@[expose] def cycleOnCount (r : ℕ) (S : Finset V) (markers host : Finset (Finset V)) : ℕ :=
  (cycleOnFamily r S markers host).card

omit [Fintype V] in
@[simp] theorem ambientEdge_eq_liftEdge (S : Finset V) (e : Finset ↥S) :
    ambientEdge S e = liftEdge S e := by
  ext x
  simp [ambientEdge, liftEdge]

@[simp] theorem liftEdges_restrictEdges (S : Finset V) (E : Finset (Finset V))
    (hE : ∀ e ∈ E, e ⊆ S) :
    (restrictEdges S E).image (liftEdge S) = E := by
  ext e
  simp only [restrictEdges, mem_image]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    simpa only [lift_restrictEdge S b (hE b hb)] using hb
  · intro he
    exact ⟨restrictEdge S e, ⟨e, he, rfl⟩, lift_restrictEdge S e (hE e he)⟩

@[simp] theorem restrictEdges_liftEdges (S : Finset V) (E : Finset (Finset ↥S)) :
    restrictEdges S (E.image (liftEdge S)) = E := by
  simp [restrictEdges, image_image, Function.comp_def]

omit [Fintype V] in
theorem liftEdge_subset (S : Finset V) (e : Finset ↥S) : liftEdge S e ⊆ S := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := mem_image.mp hx
  exact a.property

theorem restrictEdges_subset_inducedHost (S : Finset V)
    (E H : Finset (Finset V)) (hE : ∀ e ∈ E, e ⊆ S) (hEH : E ⊆ H) :
    restrictEdges S E ⊆ inducedHost S H := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := mem_image.mp he
  rw [mem_inducedHost, ambientEdge_eq_liftEdge, lift_restrictEdge S a (hE a ha)]
  exact hEH ha

theorem liftEdges_subset_host (S : Finset V) (E : Finset (Finset ↥S))
    (H : Finset (Finset V)) (hEH : E ⊆ inducedHost S H) :
    E.image (liftEdge S) ⊆ H := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := mem_image.mp he
  simpa using (mem_inducedHost S H a).mp (hEH ha)

/-- Edges outside the active vertex set cannot affect the completion family. -/
theorem cycleOnFamily_eq_filter_active (r : ℕ) (S : Finset V)
    (markers host : Finset (Finset V)) :
    cycleOnFamily r S markers host =
      cycleOnFamily r S markers (host.filter (fun e => e ⊆ S)) := by
  classical
  ext E
  simp only [mem_cycleOnFamily]
  constructor
  · rintro ⟨⟨C⟩, hH⟩
    exact ⟨⟨C⟩, fun e he => mem_filter.mpr ⟨hH he, C.edge_subset_active he⟩⟩
  · rintro ⟨hC, hH⟩
    exact ⟨hC, fun e he => (mem_filter.mp (hH he)).1⟩

/-- Equal induced hosts give identical ambient completion families. -/
theorem cycleOnFamily_congr_inducedHost (r : ℕ) (S : Finset V)
    (markers H G : Finset (Finset V)) (hHG : inducedHost S H = inducedHost S G) :
    cycleOnFamily r S markers H = cycleOnFamily r S markers G := by
  classical
  have edge_mem (e : Finset V) (he : e ⊆ S) : e ∈ H ↔ e ∈ G := by
    have hh := congrArg (fun T => restrictEdge S e ∈ T) hHG
    simpa only [mem_inducedHost, ambientEdge_eq_liftEdge, lift_restrictEdge S e he]
      using Iff.of_eq hh
  ext E
  simp only [mem_cycleOnFamily]
  constructor
  · rintro ⟨⟨C⟩, hH⟩
    exact ⟨⟨C⟩, fun e he => (edge_mem e (C.edge_subset_active he)).mp (hH he)⟩
  · rintro ⟨⟨C⟩, hG⟩
    exact ⟨⟨C⟩, fun e he => (edge_mem e (C.edge_subset_active he)).mpr (hG he)⟩

/-- A cycle family restricted to its active vertices, in the ambient-to-subtype direction. -/
@[expose] noncomputable def cycleOnToRestricted {r : ℕ} (hr : 3 ≤ r) (S : Finset V)
    (markers host : Finset (Finset V)) :
    ↥(cycleOnFamily r S markers host) →
      ↥(unrestrictedCycleFamily r (restrictEdges S markers) (inducedHost S host)) :=
  fun E => ⟨restrictEdges S E.val, by
    obtain ⟨hC, hH⟩ := (mem_cycleOnFamily _ _ _ _ _).mp E.property
    obtain ⟨C⟩ := hC
    apply (mem_unrestrictedCycleFamily _ _ _ _ hr).mpr
    exact ⟨⟨C.restrict⟩,
      restrictEdges_subset_inducedHost S _ _ (fun _ h => C.edge_subset_active h) hH⟩⟩

theorem cycleOnToRestricted_injective {r : ℕ} (hr : 3 ≤ r) (S : Finset V)
    (markers host : Finset (Finset V)) :
    Function.Injective (cycleOnToRestricted hr S markers host) := by
  intro A B h
  apply Subtype.ext
  obtain ⟨CA⟩ := ((mem_cycleOnFamily _ _ _ _ _).mp A.property).1
  obtain ⟨CB⟩ := ((mem_cycleOnFamily _ _ _ _ _).mp B.property).1
  have he : restrictEdges S A.val = restrictEdges S B.val := congrArg Subtype.val h
  have hl := congrArg (fun E => E.image (liftEdge S)) he
  simpa only [liftEdges_restrictEdges S A.val (fun _ h => CA.edge_subset_active h),
    liftEdges_restrictEdges S B.val (fun _ h => CB.edge_subset_active h)] using hl

/-- Exact equivalence between ambient and induced-vertex completion families. -/
@[expose] noncomputable def cycleOnFamilyEquiv {r : ℕ} (hr : 3 ≤ r) (S : Finset V)
    (markers host : Finset (Finset V)) (hM : ∀ e ∈ markers, e ⊆ S) :
    ↥(cycleOnFamily r S markers host) ≃
      ↥(unrestrictedCycleFamily r (restrictEdges S markers) (inducedHost S host)) :=
  Equiv.ofBijective (cycleOnToRestricted hr S markers host) ⟨
    cycleOnToRestricted_injective hr S markers host, by
      intro E
      obtain ⟨hC, hH⟩ := (mem_unrestrictedCycleFamily _ _ _ _ hr).mp E.property
      obtain ⟨C⟩ := hC
      have hc : IsMixedCycleOn r S markers (E.val.image (liftEdge S)) := by
        have h := C.lift
        rw [liftEdges_restrictEdges S markers hM] at h
        exact ⟨h⟩
      refine ⟨⟨E.val.image (liftEdge S), (mem_cycleOnFamily _ _ _ _ _).mpr
        ⟨hc, liftEdges_subset_host S E.val host hH⟩⟩, ?_⟩
      apply Subtype.ext
      exact restrictEdges_liftEdges S E.val⟩

/-- Ambient completion counts are the manuscript's spanning-cycle counts on the
induced host. -/
theorem cycleOnCount_eq_unrestricted {r : ℕ} (hr : 3 ≤ r) (S : Finset V)
    (markers host : Finset (Finset V)) (hM : ∀ e ∈ markers, e ⊆ S) :
    cycleOnCount r S markers host =
      unrestrictedCycleCount r (restrictEdges S markers) (inducedHost S host) := by
  have hc := Fintype.card_congr (cycleOnFamilyEquiv hr S markers host hM)
  simpa only [Fintype.card_coe, cycleOnCount, unrestrictedCycleCount, FiniteFamily.count] using hc

end LooseHamilton
