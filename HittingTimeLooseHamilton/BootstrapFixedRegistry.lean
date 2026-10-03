module

public import HittingTimeLooseHamilton.BootstrapActualTests
public import HittingTimeLooseHamilton.BootstrapCatalogueEmbedding
public import HittingTimeLooseHamilton.BootstrapTagRoom
public import HittingTimeLooseHamilton.RegistryEmbedding

public section

/-! # One fixed registry on the original root-test index
Synthetic tag markers are used solely by the embedding. Embedded entries are
literally the actual catalogue tests, including their bad-set functions.
-/
noncomputable section
namespace LooseHamilton.BootstrapCatalogue
open Finset RootFreeTestIndexing
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A deterministic choice from the original matching alone. -/
@[expose] def tagPair {original : Finset (Finset V)} (hM : IsPairMatching original)
    (hroom : 2*original.card+2 ≤ Fintype.card V) :
    {pq : V × V // pq.1 ∉ originalPorts original ∧
      pq.2 ∉ originalPorts original ∧ pq.1 ≠ pq.2} := by
  have hh := BootstrapTagFrames.exists_unused_pair hM hroom
  let p := Classical.choose hh
  have hp := Classical.choose_spec hh
  exact ⟨(p,Classical.choose hp),Classical.choose_spec hp⟩

@[expose] def catalogueEmbedding {r : ℕ} {original : Finset (Finset V)}
    (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card V) :
    Index r original ↪ RootTestIndex r original :=
  BootstrapCatalogueEmbedding.embed hM hr (tagPair hM hroom).val.1
    (tagPair hM hroom).val.2 (tagPair hM hroom).property.1
    (tagPair hM hroom).property.2.1 (tagPair hM hroom).property.2.2

/-- Unused old-index labels receive a fixed all-bad test. -/
@[expose] def unusedTest {r h : ℕ} {original : Finset (Finset V)}
    (i : RootTestIndex r original) : RegisteredRootTest V r h where
  time := i.2.2.val
  root := labelRoot i.2.1
  prescribed := ∅
  prescribed_subset := empty_subset _
  prescribed_card := by simp
  badSet := fun _ => rootEdgeUniverse r (labelRoot i.2.1)
  bad_subset := fun _ => Subset.rfl

/-- Fixed before sampling: the only inputs are original data and constants. -/
@[expose] def fixedRegistry {r h : ℕ} {original : Finset (Finset V)}
    (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card V) (cP cE cPort : ℝ) :
    RootTestIndex r original → RegisteredRootTest V r h :=
  extendRootRegistry (catalogueEmbedding hM hr hroom) (tests hM cP cE cPort) unusedTest

/-- Exact equality of tests, not just a comparison of failure probabilities. -/
@[simp] theorem fixedRegistry_entry {r h : ℕ} {original : Finset (Finset V)}
    (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card V) (cP cE cPort : ℝ)
    (i : Index r original) :
    fixedRegistry (h := h) hM hr hroom cP cE cPort (catalogueEmbedding hM hr hroom i) =
      tests hM cP cE cPort i := extendRootRegistry_apply _ _ _ _

/-- The full-index common event controls all actual catalogue entries. -/
theorem common_of_fixedRegistry {r h M : ℕ} {ell : V → ℕ}
    {original : Finset (Finset V)} (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card V) (cP cE cPort cRoot : ℝ)
    {ω : TerminalState V r M ell × MissingOrder V r M}
    (hω : CommonRootTests (fixedRegistry (h := h) hM hr hroom cP cE cPort) M ell cRoot ω) :
    CommonRootTests (tests (h := h) hM cP cE cPort) M ell cRoot ω :=
  hω.of_extension (catalogueEmbedding hM hr hroom)

/-- Reading an embedded bad set eliminates every synthetic tag marker. -/
theorem fixedRegistry_badSet {r h : ℕ} {original : Finset (Finset V)}
    (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card V) (cP cE cPort : ℝ)
    (i : Index r original) (data : SimpleHypergraph V × SimpleHypergraph V) :
    (fixedRegistry (h := h) hM hr hroom cP cE cPort
      (catalogueEmbedding hM hr hroom i)).badSet data =
      (tests (h := h) hM cP cE cPort i).badSet data := by
  rw [fixedRegistry_entry]

end LooseHamilton.BootstrapCatalogue
