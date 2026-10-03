module

public import HittingTimeLooseHamilton.KahnLaw
public import HittingTimeLooseHamilton.Cycles
public import HittingTimeLooseHamilton.Models
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Basic

public section

/-!
Finite-family counting and edge marginals. A cycle is counted as an edge set,
not as a choice of cyclic orientation, root, or parametrisation.
-/
noncomputable section
open scoped BigOperators
namespace LooseHamilton
namespace FiniteFamily
variable {E : Type*} [DecidableEq E]

/-- Number of objects (each object is a finite edge set). -/
@[expose] def count (family : Finset (Finset E)) : ℕ := family.card

/-- Number of objects containing a particular edge. -/
@[expose] def incidenceCount (family : Finset (Finset E)) (e : E) : ℕ :=
  (family.filter fun C => e ∈ C).card

/-- Uniform inclusion marginal; by convention it is zero for an empty family. -/
@[expose] def marginal (family : Finset (Finset E)) (e : E) : ℝ :=
  (incidenceCount family e : ℝ) / count family

lemma marginal_nonneg (family : Finset (Finset E)) (e : E) :
    0 ≤ marginal family e := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma marginal_le_one (family : Finset (Finset E)) (e : E) :
    marginal family e ≤ 1 := by
  unfold marginal count incidenceCount
  by_cases h : family.card = 0
  · simp [h]
  · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
    exact_mod_cast Finset.card_filter_le family (fun C => e ∈ C)

@[simp] lemma marginal_empty (e : E) : marginal ∅ e = 0 := by
  simp [marginal, incidenceCount, count]

lemma marginal_eq_zero (family : Finset (Finset E)) (e : E)
    (h : ∀ C ∈ family, e ∉ C) : marginal family e = 0 := by
  have hf : family.filter (fun C => e ∈ C) = ∅ := by
    ext C
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    exact h C
  simp [marginal, incidenceCount, hf]

lemma marginal_eq_zero_of_not_mem_host (family : Finset (Finset E))
    (host : Finset E) (hsub : ∀ C ∈ family, C ⊆ host) {e : E} (he : e ∉ host) :
    marginal family e = 0 :=
  marginal_eq_zero family e fun C hC hCe => he (hsub C hC hCe)

lemma sum_incidenceCount (family : Finset (Finset E)) (host : Finset E)
    (hsub : ∀ C ∈ family, C ⊆ host) :
    ∑ e ∈ host, incidenceCount family e = ∑ C ∈ family, C.card := by
  simp only [incidenceCount, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C hC
  rw [← Finset.card_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hsub C hC h, h⟩⟩

/-- Double-count incidences between the host edges and the objects. -/
theorem sum_marginal (family : Finset (Finset E)) (host : Finset E) (k : ℕ)
    (hpos : 0 < count family) (hsub : ∀ C ∈ family, C ⊆ host)
    (hcard : ∀ C ∈ family, C.card = k) :
    ∑ e ∈ host, marginal family e = (k : ℝ) := by
  have hc : (count family : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)
  have hs : ∑ e ∈ host, incidenceCount family e = count family * k := by
    rw [sum_incidenceCount family host hsub]
    calc
      ∑ C ∈ family, C.card = ∑ _C ∈ family, k := Finset.sum_congr rfl hcard
      _ = count family * k := by simp [count]
  simp only [marginal, ← Finset.sum_div]
  rw [← Nat.cast_sum, hs, Nat.cast_mul]
  exact mul_div_cancel_left₀ (k : ℝ) hc

/-- The finite uniform law on the counted objects. -/
@[expose] def uniformLaw (family : Finset (Finset E)) (hpos : 0 < count family) :
    FiniteEntropy.Law {C // C ∈ family} := by
  have : Nonempty {C // C ∈ family} := by
    obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
    exact ⟨⟨C, hC⟩⟩
  exact FiniteEntropy.uniform

/-- The counting marginal is precisely the probability of inclusion under the
uniform law on the family. -/
theorem uniformLaw_event (family : Finset (Finset E))
    (hpos : 0 < count family) (e : E) :
    (uniformLaw family hpos).event (fun C => e ∈ C.val) = marginal family e := by
  classical
  simp only [FiniteEntropy.Law.event, uniformLaw, FiniteEntropy.uniform,
    Fintype.card_coe]
  rw [Finset.sum_coe_sort family (fun C => if e ∈ C then (family.card : ℝ)⁻¹ else 0)]
  rw [← Finset.sum_filter]
  simp [marginal, incidenceCount, count, div_eq_mul_inv]

end FiniteFamily

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All unoriented connected spanning mixed cycles in the host whose ordinary
edges obey the prohibition from the fixed original port set. The marker set may
change independently of `ports`. -/
@[expose] def cycleFamily (r : ℕ) (markers host : Finset (Finset V)) (ports : Finset V) :
    Finset (Finset (Finset V)) := by
  classical
  exact Finset.univ.filter fun C =>
    IsMixedCycle r markers C ∧ C ⊆ host ∧ C ⊆ allowedEdges r ports

@[simp] theorem mem_cycleFamily (r : ℕ) (markers host : Finset (Finset V))
    (ports : Finset V) (C : Finset (Finset V)) :
    C ∈ cycleFamily r markers host ports ↔
      IsMixedCycle r markers C ∧ C ⊆ host ∧ C ⊆ allowedEdges r ports := by
  classical
  simp [cycleFamily]

/-- The manuscript's `X°(H)`, with its fixed parameters explicit. -/
@[expose] def cycleCount (r : ℕ) (markers host : Finset (Finset V)) (ports : Finset V) : ℕ :=
  FiniteFamily.count (cycleFamily r markers host ports)

/-- The manuscript's `q°_e(H)`. The empty-family value is extended by zero. -/
@[expose] def cycleMarginal (r : ℕ) (markers host : Finset (Finset V)) (ports e : Finset V) : ℝ :=
  FiniteFamily.marginal (cycleFamily r markers host ports) e

theorem cycleMarginal_nonneg (r : ℕ) (markers host : Finset (Finset V))
    (ports e : Finset V) : 0 ≤ cycleMarginal r markers host ports e :=
  FiniteFamily.marginal_nonneg _ _

theorem cycleMarginal_le_one (r : ℕ) (markers host : Finset (Finset V))
    (ports e : Finset V) : cycleMarginal r markers host ports e ≤ 1 :=
  FiniteFamily.marginal_le_one _ _

theorem cycleMarginal_forbidden (r : ℕ) (markers host : Finset (Finset V))
    (ports e : Finset V) (he : e ∉ allowedEdges r ports) :
    cycleMarginal r markers host ports e = 0 := by
  apply FiniteFamily.marginal_eq_zero
  intro C hC heC
  exact he ((mem_cycleFamily _ _ _ _ _).mp hC |>.2.2 heC)

theorem cycleMarginal_absent (r : ℕ) (markers host : Finset (Finset V))
    (ports e : Finset V) (he : e ∉ host) :
    cycleMarginal r markers host ports e = 0 := by
  apply FiniteFamily.marginal_eq_zero
  intro C hC heC
  exact he ((mem_cycleFamily _ _ _ _ _).mp hC |>.2.1 heC)

/-- Uniform sampling of the actual connected cycles counted by `cycleCount`. -/
@[expose] def uniformCycleLaw (r : ℕ) (markers host : Finset (Finset V)) (ports : Finset V)
    (hpos : 0 < cycleCount r markers host ports) :
    FiniteEntropy.Law {C // C ∈ cycleFamily r markers host ports} :=
  FiniteFamily.uniformLaw _ hpos

theorem uniformCycleLaw_event (r : ℕ) (markers host : Finset (Finset V))
    (ports e : Finset V) (hpos : 0 < cycleCount r markers host ports) :
    (uniformCycleLaw r markers host ports hpos).event (fun C => e ∈ C.val) =
      cycleMarginal r markers host ports e :=
  FiniteFamily.uniformLaw_event _ hpos e

/-- The exact incidence identity from Section 1. In particular the common number
of ordinary edges is derived from the spanning-cycle model, not postulated. -/
theorem sum_cycleMarginal (r : ℕ) (markers host : Finset (Finset V))
    (ports : Finset V) (hr : 3 ≤ r) (hpos : 0 < cycleCount r markers host ports) :
    ∑ e ∈ host, cycleMarginal r markers host ports e =
      ((Fintype.card V - markers.card) / (r - 1) : ℕ) := by
  apply FiniteFamily.sum_marginal _ _ _ hpos
  · intro C hC
    exact ((mem_cycleFamily _ _ _ _ _).mp hC).2.1
  · intro C hC
    exact ((mem_cycleFamily _ _ _ _ _).mp hC).1.edge_card hr

/-- Positivity of the count is equivalent to existence of an admissible cycle. -/
theorem cycleCount_pos_iff (r : ℕ) (markers host : Finset (Finset V))
    (ports : Finset V) :
    0 < cycleCount r markers host ports ↔
      ∃ C, IsMixedCycle r markers C ∧ C ⊆ host ∧ C ⊆ allowedEdges r ports := by
  simp only [cycleCount, FiniteFamily.count, Finset.card_pos, Finset.Nonempty,
    mem_cycleFamily]

theorem cycleFamily_mono (r : ℕ) (markers : Finset (Finset V))
    (ports : Finset V) {host host' : Finset (Finset V)} (hh : host ⊆ host') :
    cycleFamily r markers host ports ⊆ cycleFamily r markers host' ports := by
  intro C hC
  obtain ⟨hm, hs, ha⟩ := mem_cycleFamily r markers host ports C |>.mp hC
  exact (mem_cycleFamily _ _ _ _ _).mpr ⟨hm, hs.trans hh, ha⟩

theorem cycleCount_mono (r : ℕ) (markers : Finset (Finset V))
    (ports : Finset V) {host host' : Finset (Finset V)} (hh : host ⊆ host') :
    cycleCount r markers host ports ≤ cycleCount r markers host' ports :=
  Finset.card_le_card (cycleFamily_mono r markers ports hh)

@[simp] theorem allowedEdges_empty (r : ℕ) :
    allowedEdges r (∅ : Finset V) = completeEdges V r := by
  ext e
  simp

/-- The unrestricted host count `X(G, M)` of Section 2. -/
@[expose] def unrestrictedCycleFamily (r : ℕ) (markers host : Finset (Finset V)) :
    Finset (Finset (Finset V)) := cycleFamily r markers host ∅

@[expose] def unrestrictedCycleCount (r : ℕ) (markers host : Finset (Finset V)) : ℕ :=
  FiniteFamily.count (unrestrictedCycleFamily r markers host)

@[simp] theorem mem_unrestrictedCycleFamily (r : ℕ)
    (markers host C : Finset (Finset V)) (hr : 3 ≤ r) :
    C ∈ unrestrictedCycleFamily r markers host ↔ IsMixedCycle r markers C ∧ C ⊆ host := by
  rw [unrestrictedCycleFamily, mem_cycleFamily]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hm, hs⟩
    refine ⟨hm, hs, ?_⟩
    intro e he
    simp only [allowedEdges_empty, mem_completeEdges]
    exact hm.uniform hr e he

/-- The original-port restriction is equivalent to intersecting the host with
its fixed allowed-edge set; the mixed-cycle predicate itself stays unchanged. -/
theorem cycleFamily_eq_unrestricted_inter (r : ℕ)
    (markers host : Finset (Finset V)) (ports : Finset V) (hr : 3 ≤ r) :
    cycleFamily r markers host ports =
      unrestrictedCycleFamily r markers (host ∩ allowedEdges r ports) := by
  ext C
  rw [mem_cycleFamily, mem_unrestrictedCycleFamily _ _ _ _ hr]
  simp only [Finset.subset_inter_iff]

theorem cycleCount_eq_unrestricted_inter (r : ℕ)
    (markers host : Finset (Finset V)) (ports : Finset V) (hr : 3 ≤ r) :
    cycleCount r markers host ports =
      unrestrictedCycleCount r markers (host ∩ allowedEdges r ports) := by
  unfold cycleCount unrestrictedCycleCount
  rw [cycleFamily_eq_unrestricted_inter r markers host ports hr]

theorem unrestrictedCycleCount_pos_iff (r : ℕ) (markers host : Finset (Finset V))
    (hr : 3 ≤ r) :
    0 < unrestrictedCycleCount r markers host ↔ ∃ C, IsMixedCycle r markers C ∧ C ⊆ host := by
  simp only [unrestrictedCycleCount, FiniteFamily.count, Finset.card_pos,
    Finset.Nonempty, mem_unrestrictedCycleFamily r markers host _ hr]

end LooseHamilton
