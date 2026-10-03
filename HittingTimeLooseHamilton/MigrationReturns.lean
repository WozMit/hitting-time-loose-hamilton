module

public import HittingTimeLooseHamilton.EndpointSpliceImageConstruction
public import HittingTimeLooseHamilton.PrivateMigrationExpansion

public section

/-! Actual outputs restore the base completion space after every migration. -/
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Certificates for actual outputs, recording their final deleted block,
root pair and edge family. No restoration property is assumed here. -/
inductive MigrationReturn (r : ℕ) (M G : Finset (Finset V)) :
    Finset V → Finset V → Finset (Finset V) → Prop
  | privateMove {D q R uv : Finset V} {x : V} {F : Finset (Finset V)}
      (card : D.card = r - 2)
      (legal : PrivateMigrationLegal r M G D q x R uv)
      (input : F ∈ privateMigrationInputFamily r M G D q x R uv) :
      MigrationReturn r M G D q (insert (uv ∪ insert x R) F)
  | endpointI {P : Finset V} {y z t : V} {F : Finset (Finset V)}
      {l : EndpointCutLabelI V} {b : EndpointSpliceInnerLabel V}
      (source : LegalPrivateCompletion r M P {y,z})
      (matching : (M : Set (Finset V)).PairwiseDisjoint id)
      (cut : EndpointCutLegalI r M G P y z l)
      (splice : EndpointSpliceLegalI r M G P y z t l b)
      (input : F ∈ endpointSpliceInputFamilyI r M G P y z t l b) :
      MigrationReturn r M G P {t,z} (endpointSpliceOutputI y l b F)
  | endpointII {P : Finset V} {y z t : V} {F : Finset (Finset V)}
      {l : EndpointCutLabelII V} {b : EndpointSpliceInnerLabel V}
      (source : LegalPrivateCompletion r M P {y,z})
      (matching : (M : Set (Finset V)).PairwiseDisjoint id)
      (cut : EndpointCutLegalII r M G P y z l)
      (splice : EndpointSpliceLegalII r M G P y z t l b)
      (input : F ∈ endpointSpliceInputFamilyII r M G P y z t l b) :
      MigrationReturn r M G P {t,z} (endpointSpliceOutputII y l b F)

/-- All auxiliary deletions and auxiliary markers are restored. -/
theorem MigrationReturn.restored {r : ℕ} {M G F : Finset (Finset V)}
    {P q : Finset V} (h : MigrationReturn r M G P q F) (hr : 3 ≤ r) :
    F ∈ completionFamily r M G P q ∧ P.card = r - 2 := by
  cases h with
  | privateMove hc hl hi => exact ⟨privateMigration_expand_mem hr hl hi, hc⟩
  | endpointI hs hm hl hb hi =>
    obtain ⟨image⟩ := endpointSplice_image_I hr hs hm hl hb hi
    exact ⟨(mem_completionFamily _ _ _ _ _ _).mpr ⟨⟨image.cycle⟩, image.host_subset⟩,
      hs.private_card⟩
  | endpointII hs hm hl hb hi =>
    obtain ⟨image⟩ := endpointSplice_image_II hr hs hm hl hb hi
    exact ⟨(mem_completionFamily _ _ _ _ _ _).mpr ⟨⟨image.cycle⟩, image.host_subset⟩,
      hs.private_card⟩

/-- In any finite history of completed migrations, every returned cycle has
only its current base block deleted, independently of the history length.
Earlier temporary deleted sets do not occur in these output families. -/
theorem migration_returns_do_not_accumulate {r n : ℕ} {M G : Finset (Finset V)}
    (hr : 3 ≤ r) (P q : Fin n → Finset V) (F : Fin n → Finset (Finset V))
    (moves : ∀ i, MigrationReturn r M G (P i) (q i) (F i)) :
    ∀ i, F i ∈ completionFamily r M G (P i) (q i) ∧
      (univ \ (univ \ P i)).card = r - 2 := by
  intro i
  obtain ⟨hf, hc⟩ := (moves i).restored hr
  exact ⟨hf, by simpa using hc⟩

/-- Adjoining the original port adds at most one permanent deletion. -/
theorem migration_returns_port_bound {r n : ℕ} {M G : Finset (Finset V)}
    (hr : 3 ≤ r) (x : V) (P q : Fin n → Finset V)
    (F : Fin n → Finset (Finset V))
    (moves : ∀ i, MigrationReturn r M G (P i) (q i) (F i)) :
    ∀ i, (insert x (P i)).card ≤ r - 1 := by
  intro i
  have hc := ((moves i).restored hr).2
  have := card_insert_le x (P i)
  omega
end LooseHamilton
