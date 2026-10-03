module

public import HittingTimeLooseHamilton.EndpointSpliceMap
public import HittingTimeLooseHamilton.EndpointSpliceImageConstruction
public import HittingTimeLooseHamilton.EndpointSpliceCounts

public section

/-! # Section 9: directed endpoint-splicing injection (endpointmap)

All summands count actual edge sets with the relative direction `a→z, v→t`.
The old host is only restricted to surviving vertices. The proof constructs the
arc reversal, restores the cut path, expands the new edge, and then uses joint
recovery of every label and the input cycle. No injection or surgery is assumed.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Y_{G_b}(Q;v→t)` for a Type I cut, rooted at `a→z`. Its equality with the
previous directed-count definition is `endpointSpliceCountI_eq_Y`. -/
@[expose] def endpointSpliceYI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelI V) (b : EndpointSpliceInnerLabel V) : ℕ :=
  (endpointSpliceInputFamilyI r M G P y z t l b).card

/-- `Y_{G_b}(Q;v→t)` for a Type II cut, with the traversed old marker removed.
The exact restricted-host comparison is `endpointSpliceCountII_eq_Y`. -/
@[expose] def endpointSpliceYII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelII V) (b : EndpointSpliceInnerLabel V) : ℕ :=
  (endpointSpliceInputFamilyII r M G P y z t l b).card

variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z t : V}

/-- The concrete surgeries discharge all local output and orientation obligations. -/
theorem endpointSplice_image_properties (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) :
    EndpointSpliceImageProperties r M G P y z t := by
  constructor
  · intro l hl b hb F hF
    exact endpointSplice_image_I hr hs hM hl hb hF
  · intro l hl b hb F hF
    exact endpointSplice_image_II hr hs hM hl hb hF

/-- The actual endpoint-splicing map is injective jointly in both types of cut,
all cut labels, the new private block and endpoint, and the input cycle. -/
theorem endpoint_directed_splicing_injective (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) :
    Function.Injective (endpointSpliceMap
      (endpointSplice_image_properties (G := G) (t := t) hr hs hM)) := by
  apply endpointSpliceMap_injective hr hM
  intro hy
  exact disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp)) hy

/-- Equation (endpointmap). Splitting the outer sum into Type I and Type II
counts every legal cut exactly once. Every inner sum runs over all legal `(Q,v)`
with `|Q|=r-2` and `{y,v} ∪ Q ∈ G`, as specified by `EndpointSpliceLegal`.
The constructed cyclic order is `t→z A₁ v→y P_b a A₂⁻¹ t`. -/
theorem endpoint_directed_splicing (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) :
    completionCount r M G P {t,z} ≥
      (∑ l ∈ endpointCutLabelsI r M G P y z,
        ∑ b ∈ endpointSpliceLabelsI r M G P y z t l,
          endpointSpliceYI r M G P y z t l b) +
      ∑ l ∈ endpointCutLabelsII r M G P y z,
        ∑ b ∈ endpointSpliceLabelsII r M G P y z t l,
          endpointSpliceYII r M G P y z t l b := by
  have hy : y ∉ originalPorts M := fun hy =>
    disjoint_left.mp hs.ports_disjoint (mem_union_right _ (by simp)) hy
  exact endpointSplice_count_le_of_images hr hM hy
    (endpointSplice_image_properties hr hs hM)

end LooseHamilton
