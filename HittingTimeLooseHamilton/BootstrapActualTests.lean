module

public import HittingTimeLooseHamilton.BootstrapCatalogueDummy
public import HittingTimeLooseHamilton.RootTestRegistrations

public section

/-! Actual tests for the fixed geometric catalogue. Only the original matching,
fixed thresholds and static labels enter these constructors; synthetic frame
markers never enter their counts. -/
noncomputable section
namespace LooseHamilton.BootstrapCatalogue
open Finset RootFreeTestIndexing
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The marker family on the actual surviving vertex space. -/
@[expose] def residualMarkers {M : Finset (Finset V)} (hM : IsPairMatching M)
    (b : BootstrapBases.Base M) : SimpleHypergraph ↥(BootstrapBases.active b) :=
  restrictEdges (BootstrapBases.active b) (BootstrapBases.markers hM b)

/-- Actual private or endpoint test on the residual vertex space. -/
@[expose] def residualTest {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cPrivate cEndpoint : ℝ) (time : ℕ) (b : BootstrapBases.Base M)
    (l : BaseLabel r V) (hs : support l ⊆ BootstrapBases.active b) :
    RegisteredRootTest ↥(BootstrapBases.active b) r h := by
  let A := BootstrapBases.active b
  let U := BootstrapBases.fixedPorts b
  let markers := residualMarkers hM b
  rcases l with ⟨S,x,y,z,t⟩ | (⟨P,y,z,t,a,R⟩ | ⟨P,y,z,t,u,v,a,R,Q⟩)
  · let x' : ↥A := ⟨x, hs (by simp [support])⟩
    let y' : ↥A := ⟨y, hs (by simp [support])⟩
    let z' : ↥A := ⟨z, hs (by simp [support])⟩
    let t' : ↥A := ⟨t, hs (by simp [support])⟩
    exact registerPrivateRootTest r h time markers (restrictEdge A S.val) {y',z'} U x' t' cPrivate
  · let y' : ↥A := ⟨y, hs (by simp [support])⟩
    let z' : ↥A := ⟨z, hs (by simp [support])⟩
    let t' : ↥A := ⟨t, hs (by simp [support])⟩
    let a' : ↥A := ⟨a, hs (by simp [support])⟩
    exact registerEndpointRootTest r h time markers (restrictEdge A P.val) U y' z' t'
      (.inl (a',restrictEdge A R.val)) cEndpoint ∅ (empty_subset _) (by simp)
  · let y' : ↥A := ⟨y, hs (by simp [support])⟩
    let z' : ↥A := ⟨z, hs (by simp [support])⟩
    let t' : ↥A := ⟨t, hs (by simp [support])⟩
    let u' : ↥A := ⟨u, hs (by simp [support])⟩
    let v' : ↥A := ⟨v, hs (by simp [support])⟩
    let a' : ↥A := ⟨a, hs (by simp [support])⟩
    exact registerEndpointRootTest r h time markers (restrictEdge A P.val) U y' z' t'
      (.inr (u',v',a',restrictEdge A R.val,restrictEdge A Q.val)) cEndpoint
      ∅ (empty_subset _) (by simp)

@[simp] theorem residualTest_time {r h : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (cP cE : ℝ) (time) (b) (l : BaseLabel r V) (hs) :
    (residualTest (h := h) hM cP cE time b l hs).time = time := by
  rcases l with l | (l | l) <;> rfl

@[simp] theorem residualTest_root {r h : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (cP cE : ℝ) (time) (b) (l : BaseLabel r V) (hs) :
    (residualTest (h := h) hM cP cE time b l hs).root.val = root (.inl (b,l)) := by
  rcases l with l | (l | l) <;> rfl

@[simp] theorem residualTest_prescribed {r h : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (cP cE : ℝ) (time) (b) (l : BaseLabel r V) (hs) :
    (residualTest (h := h) hM cP cE time b l hs).prescribed = ∅ := by
  rcases l with l | (l | l) <;> rfl

/-- The original-port test is on all ambient vertices and original markers. -/
@[expose] def portTest {r h : ℕ} (M : Finset (Finset V)) (cPort : ℝ) (time : ℕ)
    (l : PortLabel r V) : RegisteredRootTest V r h :=
  registerPortRootTest r h time M (originalPorts M) l.1.val
    l.2.1 l.2.2.1 l.2.2.2 cPort

/-- Valid entries are actual residual tests lifted into ambient sampling, or
actual full-space port tests. -/
@[expose] def genuineTest {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cPrivate cEndpoint cPort : ℝ) (i : Index r M) (hi : admissible i.1) :
    RegisteredRootTest V r h := by
  rcases i with ⟨⟨b,l⟩ | l,j⟩
  · exact (residualTest hM cPrivate cEndpoint j.val b l hi.1).liftDeleted
      (BootstrapBases.deleted b)
  · exact portTest M cPort j.val l

/-- The single fixed registry, with all raw indices retained. -/
@[expose] def tests {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cPrivate cEndpoint cPort : ℝ) : Index r M → RegisteredRootTest V r h :=
  withDummy (genuineTest hM cPrivate cEndpoint cPort)

theorem tests_valid {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cP cE cPort : ℝ) (i : Index r M) (hi : admissible i.1) :
    tests (h := h) hM cP cE cPort i = genuineTest hM cP cE cPort i hi :=
  withDummy_valid _ _ hi

theorem tests_invalid {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cP cE cPort : ℝ) (i : Index r M) (hi : ¬ admissible i.1) :
    tests (h := h) hM cP cE cPort i = dummy i := withDummy_invalid _ _ hi

@[simp] theorem tests_time {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cP cE cPort : ℝ) (i : Index r M) :
    (tests (h := h) hM cP cE cPort i).time = i.2.val := by
  by_cases hi : admissible i.1
  · rw [tests_valid _ _ _ _ _ hi]
    rcases i with ⟨⟨b,l⟩ | l,j⟩
    · exact residualTest_time _ _ _ _ _ _ _
    · rfl
  · rw [tests_invalid _ _ _ _ _ hi]; rfl

@[simp] theorem tests_root {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cP cE cPort : ℝ) (i : Index r M) :
    (tests (h := h) hM cP cE cPort i).root = root i.1 := by
  by_cases hi : admissible i.1
  · rw [tests_valid _ _ _ _ _ hi]
    rcases i with ⟨⟨b,l⟩ | l,j⟩
    · exact residualTest_root _ _ _ _ _ _ _
    · rfl
  · rw [tests_invalid _ _ _ _ _ hi]; rfl

@[simp] theorem tests_prescribed {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cP cE cPort : ℝ) (i : Index r M) :
    (tests (h := h) hM cP cE cPort i).prescribed = ∅ := by
  by_cases hi : admissible i.1
  · rw [tests_valid _ _ _ _ _ hi]
    rcases i with ⟨⟨b,l⟩ | l,j⟩
    · change (residualTest hM cP cE j.val b l hi.1).prescribed.image _ = ∅
      rw [residualTest_prescribed]
      exact image_empty _
    · rfl
  · rw [tests_invalid _ _ _ _ _ hi]; rfl

end LooseHamilton.BootstrapCatalogue
