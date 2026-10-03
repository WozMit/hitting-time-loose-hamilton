module

public import HittingTimeLooseHamilton.EndpointCutCounting
public import HittingTimeLooseHamilton.EndpointCutJointInjection

public section

/-! # Assembling the concrete cut maps into a disjoint-sum bijection -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Verified local expansion properties used in the finite-family assembly.
The geometric expansion constructs these properties from cut legality. -/
structure EndpointCutExpansionProperties (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z : V) : Prop where
  typeI : ∀ (l : EndpointCutLabelI V), EndpointCutLegalI r M G P y z l →
    ∀ F ∈ endpointCutCoreFamilyI r M G P y z l,
      insert (l.edge y) F ∈ completionFamily r M G P {y,z} ∧
      edgeEndpointPair (insert {y,z} M) (insert (l.edge y) F) (l.edge y) = {y,l.1}
  typeII : ∀ (l : EndpointCutLabelII V), EndpointCutLegalII r M G P y z l →
    ∀ F ∈ endpointCutCoreFamilyII r M G P y z l,
      insert (l.firstEdge y) (insert l.secondEdge F) ∈ completionFamily r M G P {y,z} ∧
      edgeEndpointPair (insert {y,z} M) (insert (l.firstEdge y) (insert l.secondEdge F))
        (l.firstEdge y) = {y,l.1} ∧
      edgeEndpointPair (insert {y,z} M) (insert (l.firstEdge y) (insert l.secondEdge F))
        l.secondEdge = {l.2.1,l.2.2.1}

variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z : V}

@[expose] def endpointCutExpansionMap (h : EndpointCutExpansionProperties r M G P y z) :
    EndpointCutDomain r M G P y z → ↥(completionFamily r M G P {y,z})
  | .inl ⟨l,F⟩ => ⟨insert (l.val.edge y) F.val,
      (h.typeI _ ((mem_endpointCutLabelsI _ _ _ _ _ _ _).mp l.property) _ F.property).1⟩
  | .inr ⟨l,F⟩ => ⟨insert (l.val.firstEdge y) (insert l.val.secondEdge F.val),
      (h.typeII _ ((mem_endpointCutLabelsII _ _ _ _ _ _ _).mp l.property) _ F.property).1⟩

theorem endpointCutExpansionMap_injective
    (h : EndpointCutExpansionProperties r M G P y z)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M) :
    Function.Injective (endpointCutExpansionMap h) := by
  intro a b hab
  have heq := congrArg Subtype.val hab
  cases a with
  | inl a =>
    obtain ⟨⟨l,hl⟩,⟨F,hF⟩⟩ := a
    have hl := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hl
    have hleft := h.typeI l hl F hF
    obtain ⟨⟨C⟩,_⟩ := (mem_completionFamily _ _ _ _ _ _).mp hleft.1
    cases b with
    | inl b =>
      obtain ⟨⟨k,hk⟩,⟨F',hF'⟩⟩ := b
      have hk := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hk
      have hright := h.typeI k hk F' hF'
      change insert (l.edge y) F = insert (k.edge y) F' at heq
      have hek : k.edge y ∈ insert (l.edge y) F := by rw [heq]; simp
      have hrk := hright.2
      rw [← heq] at hrk
      have hlk := endpointCutLabelI_joint_recovery C hl hk (by simp) hek hleft.2 hrk
      have hFF := endpointCutCoreI_output_recovery hF hF' hlk heq
      subst k; subst F'; rfl
    | inr b =>
      obtain ⟨⟨k,hk⟩,⟨F',hF'⟩⟩ := b
      have hk := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hk
      have hright := h.typeII k hk F' hF'
      change insert (l.edge y) F = insert (k.firstEdge y) (insert k.secondEdge F') at heq
      have hek : k.firstEdge y ∈ insert (l.edge y) F := by rw [heq]; simp
      have hrk := hright.2.1
      rw [← heq] at hrk
      exact False.elim (endpointCutLabel_types_disjoint C hl hk (by simp) hek hleft.2 hrk)
  | inr a =>
    obtain ⟨⟨l,hl⟩,⟨F,hF⟩⟩ := a
    have hl := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hl
    have hleft := h.typeII l hl F hF
    obtain ⟨⟨C⟩,_⟩ := (mem_completionFamily _ _ _ _ _ _).mp hleft.1
    cases b with
    | inl b =>
      obtain ⟨⟨k,hk⟩,⟨F',hF'⟩⟩ := b
      have hk := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hk
      have hright := h.typeI k hk F' hF'
      change insert (l.firstEdge y) (insert l.secondEdge F) = insert (k.edge y) F' at heq
      have hek : k.edge y ∈ insert (l.firstEdge y) (insert l.secondEdge F) := by rw [heq]; simp
      have hrk := hright.2
      rw [← heq] at hrk
      exact False.elim (endpointCutLabel_types_disjoint C hk hl hek (by simp) hrk hleft.2.1)
    | inr b =>
      obtain ⟨⟨k,hk⟩,⟨F',hF'⟩⟩ := b
      have hk := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hk
      have hright := h.typeII k hk F' hF'
      change insert (l.firstEdge y) (insert l.secondEdge F) =
        insert (k.firstEdge y) (insert k.secondEdge F') at heq
      have hek₁ : k.firstEdge y ∈ insert (l.firstEdge y) (insert l.secondEdge F) := by rw [heq]; simp
      have hek₂ : k.secondEdge ∈ insert (l.firstEdge y) (insert l.secondEdge F) := by rw [heq]; simp
      have hrk₁ := hright.2.1
      have hrk₂ := hright.2.2
      rw [← heq] at hrk₁ hrk₂
      have hlk := endpointCutLabelII_joint_recovery C hM hy hl hk
        (by simp) hek₁ (by simp) hek₂ hleft.2.1 hrk₁ hleft.2.2 hrk₂
      have hFF := endpointCutCoreII_output_recovery hF hF' hlk heq
      subst k; subst F'; rfl

/-- Exhaustiveness furnished by selecting and contracting the initial path. -/
@[expose] def EndpointCutContractionProperty (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z : V) : Prop :=
  ∀ F ∈ completionFamily r M G P {y,z},
    (∃ (l : EndpointCutLabelI V), EndpointCutLegalI r M G P y z l ∧
      ∃ F' ∈ endpointCutCoreFamilyI r M G P y z l, insert (l.edge y) F' = F) ∨
    (∃ (l : EndpointCutLabelII V), EndpointCutLegalII r M G P y z l ∧
      ∃ F' ∈ endpointCutCoreFamilyII r M G P y z l,
        insert (l.firstEdge y) (insert l.secondEdge F') = F)

theorem endpointCutExpansionMap_surjective
    (h : EndpointCutExpansionProperties r M G P y z)
    (hc : EndpointCutContractionProperty r M G P y z) :
    Function.Surjective (endpointCutExpansionMap h) := by
  intro F
  rcases hc F.val F.property with ⟨l,hl,F',hF',heq⟩ | ⟨l,hl,F',hF',heq⟩
  · refine ⟨.inl ⟨⟨l, (mem_endpointCutLabelsI _ _ _ _ _ _ _).mpr hl⟩,
      ⟨F',hF'⟩⟩, ?_⟩
    exact Subtype.ext heq
  · refine ⟨.inr ⟨⟨l, (mem_endpointCutLabelsII _ _ _ _ _ _ _).mpr hl⟩,
      ⟨F',hF'⟩⟩, ?_⟩
    exact Subtype.ext heq

theorem endpointCut_partition_of_surgeries
    (h : EndpointCutExpansionProperties r M G P y z)
    (hc : EndpointCutContractionProperty r M G P y z)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M) :
    completionCount r M G P {y,z} =
      (∑ l ∈ endpointCutLabelsI r M G P y z,
        (endpointCutCoreFamilyI r M G P y z l).card) +
      ∑ l ∈ endpointCutLabelsII r M G P y z,
        (endpointCutCoreFamilyII r M G P y z l).card :=
  endpointCut_partition_of_bijective (endpointCutExpansionMap h)
    ⟨endpointCutExpansionMap_injective h hM hy, endpointCutExpansionMap_surjective h hc⟩

end LooseHamilton
