module

public import HittingTimeLooseHamilton.BootstrapTagFrames
public import HittingTimeLooseHamilton.BootstrapCatalogueGeometry

public section

/-! A fixed injective placement of the raw catalogue in the existing polynomial
root-test index. Tags encode bases, not cycle-family semantics. -/
noncomputable section
namespace LooseHamilton.BootstrapCatalogueEmbedding
open BootstrapBases BootstrapCatalogue RootFreeTestIndexing
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {M : Finset (Finset V)} {r : ℕ}

@[expose] def label : BaseLabel r V → RootTestLabel r V
  | .inl l => .inl l
  | .inr (.inl l) => .inr (.inl l)
  | .inr (.inr l) => .inr (.inr (.inl l))

@[expose] def unlabel : RootTestLabel r V → Option (BaseLabel r V)
  | .inl l => some (.inl l)
  | .inr (.inl l) => some (.inr (.inl l))
  | .inr (.inr (.inl l)) => some (.inr (.inr l))
  | .inr (.inr (.inr _)) => none

@[simp] theorem unlabel_label (l : BaseLabel r V) : unlabel (label l) = some l := by
  rcases l with l | (l | l) <;> rfl

theorem label_injective : Function.Injective (@label V _ _ r) := by
  intro l k h
  simpa using congrArg unlabel h

theorem label_ne_port (l : BaseLabel r V) (p : PortLabel r V) :
    label l ≠ Sum.inr (Sum.inr (Sum.inr p)) := by
  intro h
  have := congrArg unlabel h
  rw [unlabel_label] at this
  change some l = none at this
  cases this

@[expose] def geometry (tag : Base M → AuxiliaryFrame.Frame r M) :
    Geometry r M → AuxiliaryFrame.Frame r M × RootTestLabel r V
  | .inl (b,l) => (tag b,label l)
  | .inr l => (tag none,.inr (.inr (.inr l)))

theorem geometry_injective (tag : Base M → AuxiliaryFrame.Frame r M)
    (ht : Function.Injective tag) : Function.Injective (geometry tag) := by
  intro g h he
  cases g with
  | inl g =>
    cases h with
    | inl h =>
      have hb := ht (congrArg Prod.fst he)
      have hl := label_injective (congrArg Prod.snd he)
      exact congrArg Sum.inl (Prod.ext hb hl)
    | inr h => exact False.elim (label_ne_port g.2 h (congrArg Prod.snd he))
  | inr g =>
    cases h with
    | inl h => exact False.elim (label_ne_port h.2 g (congrArg Prod.snd he.symm))
    | inr h => simpa [geometry] using he

@[expose] def index (tag : Base M → AuxiliaryFrame.Frame r M) (i : Index r M) :
    RootTestIndex r M := ((geometry tag i.1).1,(geometry tag i.1).2,i.2)

theorem index_injective (tag : Base M → AuxiliaryFrame.Frame r M)
    (ht : Function.Injective tag) : Function.Injective (index tag) := by
  intro i j h
  apply Prod.ext
  · apply geometry_injective tag ht
    exact Prod.ext (congrArg (fun x : RootTestIndex r M => x.1) h)
      (congrArg (fun x : RootTestIndex r M => x.2.1) h)
  · exact congrArg (fun x => x.2.2) h

/-- The actual registration embedding, fixed by the original matching and a
single ordered pair outside its ports. -/
@[expose] def embed (hM : IsPairMatching M) (hr : 3 ≤ r) (p q : V)
    (hp : p ∉ originalPorts M) (hq : q ∉ originalPorts M) (hpq : p ≠ q) :
    Index r M ↪ RootTestIndex r M :=
  ⟨index (BootstrapTagFrames.tag hM hr p q hp hq hpq),
    index_injective _ (BootstrapTagFrames.tag_injective hM hr p q hp hq hpq)⟩

@[simp] theorem index_time (tag : Base M → AuxiliaryFrame.Frame r M) (i : Index r M) :
    (index tag i).2.2 = i.2 := rfl

@[simp] theorem index_root (tag : Base M → AuxiliaryFrame.Frame r M) (i : Index r M) :
    labelRoot (index tag i).2.1 = root i.1 := by
  rcases i with ⟨⟨b,l⟩ | l,j⟩
  · rcases l with l | (l | l) <;> rfl
  · rfl

@[simp] theorem index_base (tag : Base M → AuxiliaryFrame.Frame r M)
    (b : Base M) (l : BaseLabel r V) (j) :
    index tag (baseIndex b l j) = (tag b,label l,j) := rfl

@[simp] theorem index_port (tag : Base M → AuxiliaryFrame.Frame r M)
    (l : PortLabel r V) (j) :
    index tag (portIndex l j) = (tag none,Sum.inr (Sum.inr (Sum.inr l)),j) := rfl
end LooseHamilton.BootstrapCatalogueEmbedding
