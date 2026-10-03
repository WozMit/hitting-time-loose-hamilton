module

public import HittingTimeLooseHamilton.KahnConditioning

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy
variable {Ω V B : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype B]

/-- Record precisely the coordinates belonging to a finite set. -/
@[expose] def coordinateMask (s : Finset V) (x : V → B) : V → Option B :=
  fun v => if v ∈ s then some (x v) else none

/-- Joint entropy of the indicated coordinates. -/
@[expose] def coordinateEntropy (p : Law Ω) (X : Ω → V → B) (s : Finset V) : ℝ :=
  entropy (p.map (fun ω => coordinateMask s (X ω))).mass

lemma entropy_eq_of_mutual_determination {A C : Type*} [Fintype A] [Fintype C]
    (p : Law Ω) (f : Ω → A) (g : Ω → C)
    (F : A → C) (G : C → A) (hF : ∀ ω, F (f ω) = g ω)
    (hG : ∀ ω, G (g ω) = f ω) :
    entropy (p.map f).mass = entropy (p.map g).mass := by
  apply le_antisymm
  · have h := (p.map g).entropy_map_le G
    rw [Law.map_map] at h
    simpa only [Function.comp_def, show (fun a => G (g a)) = f from funext hG] using h
  · have h := (p.map f).entropy_map_le F
    rw [Law.map_map] at h
    simpa only [Function.comp_def, show (fun a => F (f a)) = g from funext hF] using h

lemma coordinateEntropy_insert (p : Law Ω) (X : Ω → V → B)
    (s : Finset V) (v : V) (hv : v ∉ s) :
    coordinateEntropy p X (insert v s) = coordinateEntropy p X s +
      p.conditionalMapEntropy (fun ω => some (X ω v))
        (fun ω => coordinateMask s (X ω)) := by
  have he := entropy_eq_of_mutual_determination p
    (fun ω => coordinateMask (insert v s) (X ω))
    (fun ω => (some (X ω v), coordinateMask s (X ω)))
    (fun y => (y v, fun w => if w ∈ s then y w else none))
    (fun y w => if w = v then y.1 else y.2 w) ?_ ?_
  · rw [coordinateEntropy, he, p.entropy_map_pair]
    rfl
  · intro ω
    apply Prod.ext
    · simp [coordinateMask]
    · funext w
      by_cases hw : w ∈ s <;> simp [coordinateMask, hw]
  · intro ω
    funext w
    by_cases hw : w = v
    · subst w; simp [coordinateMask]
    · simp [coordinateMask, hw]

lemma coordinateEntropy_diminishing (p : Law Ω) (X : Ω → V → B)
    (s t : Finset V) (hst : s ⊆ t) (v : V) (hv : v ∉ t) :
    coordinateEntropy p X (insert v t) - coordinateEntropy p X t ≤
      coordinateEntropy p X (insert v s) - coordinateEntropy p X s := by
  rw [coordinateEntropy_insert p X t v hv,
    coordinateEntropy_insert p X s v (fun h => hv (hst h))]
  simp only [add_sub_cancel_left]
  have h := p.conditionalMapEntropy_comp_le (fun ω => some (X ω v))
    (fun ω => coordinateMask t (X ω))
    (fun y w => if w ∈ s then y w else none)
  convert h using 1
  congr 1
  funext ω w
  by_cases hw : w ∈ s
  · simp [Function.comp_def, coordinateMask, hw, hst hw]
  · simp [Function.comp_def, coordinateMask, hw]

end LooseHamilton
