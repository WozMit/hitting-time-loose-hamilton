module

public import HittingTimeLooseHamilton.FrameEntropyBridgeExisting

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
open scoped BigOperators
local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- A total extension of the active vertex numbering; used only on active vertices. -/
@[expose] def numberVertex (F : Frame r original) (v : V) : Fin F.n :=
  if h : v ∈ F.active then F.vertexNumbering ⟨v,h⟩ else F.numberedInitial.val

@[simp] lemma numberVertex_of_mem (F : Frame r original) {v : V} (hv : v ∈ F.active) :
    F.numberVertex v = F.vertexNumbering ⟨v,hv⟩ := by simp [numberVertex,hv]

lemma numberVertex_inj (F : Frame r original) {u v : V}
    (hu : u ∈ F.active) (hv : v ∈ F.active)
    (h : F.numberVertex u = F.numberVertex v) : u=v := by
  rw [F.numberVertex_of_mem hu,F.numberVertex_of_mem hv] at h
  exact congrArg Subtype.val (F.vertexNumbering.injective h)

lemma numberedEdge_eq_image (F : Frame r original) (e : Finset V) (he : e ⊆ F.active) :
    F.numberedEdge e = e.image F.numberVertex := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨u.val,(mem_restrictEdge _ _ _).mp hu,F.numberVertex_of_mem u.property⟩
  · rintro hv
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨⟨u,he hu⟩,(mem_restrictEdge _ _ _).mpr hu,(F.numberVertex_of_mem (he hu)).symm⟩

lemma numberedEdges_eq_image (F : Frame r original) (E : Finset (Finset V)) :
    F.numberedEdges E = E.image F.numberedEdge := by
  simp only [numberedEdges,vertexEdges,restrictEdges,image_image]
  rfl

/-- Numbering is a bijection on all ordered endpoint pairs of an active edge,
including after an arbitrary filter. -/
theorem numberedEdge_offDiag_filter_card (F : Frame r original)
    (e : Finset V) (he : e ⊆ F.active) (P : Fin F.n × Fin F.n → Prop) :
    ((F.numberedEdge e).offDiag.filter P).card =
      (e.offDiag.filter (fun uv => P (F.numberVertex uv.1,F.numberVertex uv.2))).card := by
  symm
  apply card_bij (fun uv _ => (F.numberVertex uv.1,F.numberVertex uv.2))
  · intro uv huv
    obtain ⟨hp,hP⟩ := mem_filter.mp huv
    obtain ⟨hu,hv,hne⟩ := mem_offDiag.mp hp
    apply mem_filter.mpr
    refine ⟨mem_offDiag.mpr ⟨?_,?_,?_⟩,hP⟩
    · rw [F.numberedEdge_eq_image e he]; exact mem_image_of_mem _ hu
    · rw [F.numberedEdge_eq_image e he]; exact mem_image_of_mem _ hv
    · intro h
      exact hne (F.numberVertex_inj (he hu) (he hv) h)
  · intro uv huv xy hxy hh
    obtain ⟨hu,hv,_⟩ := mem_offDiag.mp (mem_filter.mp huv).1
    obtain ⟨hx,hy,_⟩ := mem_offDiag.mp (mem_filter.mp hxy).1
    exact Prod.ext (F.numberVertex_inj (he hu) (he hx) (congrArg Prod.fst hh))
      (F.numberVertex_inj (he hv) (he hy) (congrArg Prod.snd hh))
  · intro uv huv
    obtain ⟨hp,hP⟩ := mem_filter.mp huv
    obtain ⟨hu,hv,hne⟩ := mem_offDiag.mp hp
    rw [F.numberedEdge_eq_image e he] at hu hv
    obtain ⟨u,hu,huv'⟩ := mem_image.mp hu
    obtain ⟨v,hv,hvv⟩ := mem_image.mp hv
    have heq : (F.numberVertex u,F.numberVertex v)=uv := Prod.ext huv' hvv
    refine ⟨(u,v),mem_filter.mpr ⟨mem_offDiag.mpr ⟨hu,hv,?_⟩,?_⟩,heq⟩
    · intro h
      exact hne (huv'.symm.trans ((congrArg F.numberVertex h).trans hvv))
    · simpa only [heq] using hP

lemma sum_numberedEdges (F : Frame r original) (E : Finset (Finset V))
    (hE : ∀e∈E,e⊆F.active) (g : Finset (Fin F.n) → ℕ) :
    ∑ e ∈ F.numberedEdges E, g e = ∑ e ∈ E, g (F.numberedEdge e) := by
  rw [F.numberedEdges_eq_image E]
  apply sum_image
  intro e he f hf h
  exact F.numberedEdge_inj (hE e he) (hE f hf) h

end LooseHamilton.AuxiliaryFrame.Frame
