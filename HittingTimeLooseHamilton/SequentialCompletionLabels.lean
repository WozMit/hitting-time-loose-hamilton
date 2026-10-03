module

public import HittingTimeLooseHamilton.SequentialMobilityLabels

public section

/-! Concrete ordered histories and the actual set-valued completion labels. -/
noncomputable section
namespace LooseHamilton.Migration.SequentialLabels
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*}

@[expose] def coordinates : (k : ℕ) → ChoicePath V k → Fin k → V
  | 0, _ => Fin.elim0
  | k+1, p => Fin.lastCases p.2 (coordinates k p.1)

@[expose] def pathOfCoordinates : (k : ℕ) → (Fin k → V) → ChoicePath V k
  | 0, _ => PUnit.unit
  | k+1, f => (pathOfCoordinates k (fun i => f i.castSucc), f (Fin.last k))

@[simp] theorem coordinates_pathOfCoordinates (k : ℕ) (f : Fin k → V) :
    coordinates k (pathOfCoordinates k f) = f := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinates, pathOfCoordinates]
    · simp [coordinates, pathOfCoordinates, ih]

@[simp] theorem pathOfCoordinates_coordinates (k : ℕ) (p : ChoicePath V k) :
    pathOfCoordinates k (coordinates k p) = p := by
  induction k with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ k ih =>
    rcases p with ⟨p,v⟩
    simp [coordinates, pathOfCoordinates, ih]
    rfl

@[expose] def coordinatesEquiv (k : ℕ) : ChoicePath V k ≃ (Fin k → V) where
  toFun := coordinates k
  invFun := pathOfCoordinates k
  left_inv := pathOfCoordinates_coordinates k
  right_inv := coordinates_pathOfCoordinates k

variable [DecidableEq V]

theorem pathVertices_eq_image (k : ℕ) (p : ChoicePath V k) :
    pathVertices k p = univ.image (coordinates k p) := by
  induction k with
  | zero => simp [pathVertices]
  | succ k ih =>
    rcases p with ⟨p,v⟩
    change insert v (pathVertices k p) = _
    rw [ih]
    ext a
    simp only [mem_insert, mem_image, mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨i,hi⟩)
      · exact ⟨Fin.last k, by simp [coordinates]⟩
      · exact ⟨i.castSucc, by simpa [coordinates] using hi⟩
    · rintro ⟨i,hi⟩
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hi; exact Or.inl (by simpa [coordinates] using hi.symm)
      · intro hi
        exact Or.inr ⟨j, by simpa [coordinates] using hi⟩

theorem exists_path_vertices {d : ℕ} (P : Finset V) (hP : P.card = d) :
    ∃ p : ChoicePath V d, pathVertices d p = P := by
  let e := P.equivFinOfCardEq hP
  let f : Fin d → V := fun i => (e.symm i).val
  refine ⟨pathOfCoordinates d f, ?_⟩
  rw [pathVertices_eq_image, coordinates_pathOfCoordinates]
  ext v
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact (e.symm i).property
  · intro hv
    exact ⟨e ⟨v,hv⟩, by simp [f]⟩

/-- Endpoint order is retained; only the private-coordinate order is forgotten. -/
@[expose] def ordinaryForget (d : ℕ) (p : ChoicePath V (d+2)) : Finset V × V × V :=
  (pathVertices d p.1.1, p.1.2, p.2)

/-- The original-port endpoint remains fixed throughout the one-endpoint branch. -/
@[expose] def portForget (d : ℕ) (z : V) (p : ChoicePath V (d+1)) : Finset V × V × V :=
  (pathVertices d p.1, p.2, z)

theorem ordinaryForget_surjective {d : ℕ} (P : Finset V) (hP : P.card = d)
    (y z : V) : ∃ p, ordinaryForget d p = (P,y,z) := by
  obtain ⟨p,hp⟩ := exists_path_vertices P hP
  exact ⟨((p,y),z), by simp [ordinaryForget, hp]⟩

theorem portForget_surjective {d : ℕ} (P : Finset V) (hP : P.card = d)
    (y z : V) : ∃ p, portForget d z p = (P,y,z) := by
  obtain ⟨p,hp⟩ := exists_path_vertices P hP
  exact ⟨(p,y), by simp [portForget, hp]⟩

variable [Fintype V]

@[expose] def ordinaryLabels (d : ℕ) : Finset (Finset V × V × V) :=
  (univ.powersetCard d).product (univ.product univ)

@[expose] def portLabels (d : ℕ) (z : V) : Finset (Finset V × V × V) :=
  (univ.powersetCard d).product (univ.product {z})

@[simp] theorem mem_ordinaryLabels (d : ℕ) (l : Finset V × V × V) :
    l ∈ ordinaryLabels d ↔ l.1.card = d := by simp [ordinaryLabels]

@[simp] theorem mem_portLabels (d : ℕ) (z : V) (l : Finset V × V × V) :
    l ∈ portLabels d z ↔ l.1.card = d ∧ l.2.2 = z := by
  rcases l with ⟨P,y,t⟩
  simp [portLabels, eq_comm]

/-- Actual ordinary labels have ordered-history representatives, without an
assumed abstract surjection. -/
theorem ordinaryLabels_represented (d : ℕ) :
    ∀ l ∈ ordinaryLabels (V:=V) d, ∃ p, ordinaryForget d p = l := by
  rintro ⟨P,y,z⟩ hl
  exact ordinaryForget_surjective P ((mem_ordinaryLabels d _).mp hl) y z

theorem portLabels_represented (d : ℕ) (z : V) :
    ∀ l ∈ portLabels (V:=V) d z, ∃ p, portForget d z p = l := by
  rintro ⟨P,y,t⟩ hl
  obtain ⟨hP,rfl⟩ := (mem_portLabels d z _).mp hl
  exact portForget_surjective P hP y t

/-- Quantitative forgetting for any property of the literal final label. -/
theorem ordinary_failed_labels_card_le (d : ℕ)
    (good : Finset V × V × V → Prop) :
    ((ordinaryLabels (V:=V) d).filter (fun l => ¬ good l)).card ≤
      (univ.filter (fun p => ¬good (ordinaryForget d p))).card :=
  failed_labels_card_le _ _ _ (ordinaryLabels_represented d)

theorem port_failed_labels_card_le (d : ℕ) (z : V)
    (good : Finset V × V × V → Prop) :
    ((portLabels (V:=V) d z).filter (fun l => ¬ good l)).card ≤
      (univ.filter (fun p => ¬good (portForget d z p))).card :=
  failed_labels_card_le _ _ _ (portLabels_represented d z)

end LooseHamilton.Migration.SequentialLabels
