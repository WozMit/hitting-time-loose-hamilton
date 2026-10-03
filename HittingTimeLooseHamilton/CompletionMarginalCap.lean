module

public import HittingTimeLooseHamilton.CompletionBijection

public section

/-! Deterministic conversion of bounds on the actual completion families into
bounds on true-edge marginals. The fixed original-port prohibition is retained
by intersecting the host with its allowed-edge set. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact edge-count identity sums at most `choose r 2` completion bounds. -/
theorem avoiding_ports_incidence_le {r : ℕ} {markers host : Finset (Finset V)}
    {e : Finset V} (hr : 3 ≤ r) (he : e.card = r) (heH : e ∈ host)
    (hd : Disjoint e (originalPorts markers)) (T : ℝ)
    (hb : ∀ q ∈ e.powersetCard 2,
      (completionCount r markers host (e \ q) q : ℝ) ≤ T) :
    (FiniteFamily.incidenceCount (unrestrictedCycleFamily r markers host) e : ℝ) ≤
      (r.choose 2 : ℝ)*T := by
  rw [edge_count_identity hr he heH hd, Nat.cast_sum]
  calc
    _ ≤ ∑ _q ∈ e.powersetCard 2, T := sum_le_sum hb
    _ = _ := by simp [he]

/-- A bound on each genuine endpoint-pair completion yields the edge marginal
cap, without any assumed identity between abstract counts. -/
theorem avoiding_ports_marginal_le {r : ℕ} {markers host : Finset (Finset V)}
    {e : Finset V} (hr : 3 ≤ r) (he : e.card = r) (heH : e ∈ host)
    (hd : Disjoint e (originalPorts markers)) (D μ : ℝ)
    (hX : 0 < unrestrictedCycleCount r markers host)
    (hb : ∀ q ∈ e.powersetCard 2,
      (completionCount r markers host (e \ q) q : ℝ) ≤
        D*(unrestrictedCycleCount r markers host : ℝ)/μ) :
    FiniteFamily.marginal (unrestrictedCycleFamily r markers host) e ≤
      (r.choose 2 : ℝ)*D/μ := by
  have hp : (0:ℝ) < unrestrictedCycleCount r markers host := Nat.cast_pos.mpr hX
  change (_:ℝ)/(unrestrictedCycleCount r markers host : ℝ) ≤ _
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ (r.choose 2:ℝ)*(D*(unrestrictedCycleCount r markers host:ℝ)/μ) :=
      avoiding_ports_incidence_le hr he heH hd _ hb
    _ = _ := by ring

/-- The same cap for the manuscript's actual prohibited-edge cycle family. -/
theorem cycleMarginal_avoiding_ports_le {r : ℕ} {markers host : Finset (Finset V)}
    {e : Finset V} (hr : 3 ≤ r) (he : e.card = r) (heH : e ∈ host)
    (hd : Disjoint e (originalPorts markers)) (D μ : ℝ)
    (hX : 0 < cycleCount r markers host (originalPorts markers))
    (hb : ∀ q ∈ e.powersetCard 2,
      (completionCount r markers (host ∩ allowedEdges r (originalPorts markers))
        (e \ q) q : ℝ) ≤ D*(cycleCount r markers host (originalPorts markers):ℝ)/μ) :
    cycleMarginal r markers host (originalPorts markers) e ≤ (r.choose 2:ℝ)*D/μ := by
  have hallowed : e ∈ allowedEdges r (originalPorts markers) := by
    simp only [mem_allowedEdges,he,true_and]
    have hz : e ∩ originalPorts markers = ∅ := disjoint_iff_inter_eq_empty.mp hd
    simp [hz]
  have hcount : cycleCount r markers host (originalPorts markers) =
      unrestrictedCycleCount r markers (host ∩ allowedEdges r (originalPorts markers)) := by
    unfold cycleCount unrestrictedCycleCount
    rw [cycleFamily_eq_unrestricted_inter r markers host (originalPorts markers) hr]
  unfold cycleMarginal
  rw [cycleFamily_eq_unrestricted_inter r markers host (originalPorts markers) hr]
  apply avoiding_ports_marginal_le hr he (mem_inter.mpr ⟨heH,hallowed⟩) hd D μ
  · rwa [←hcount]
  · simpa only [←hcount] using hb

/-- The final scale conversion uses the exact vertex identity and average
degree, with at most half the vertices occupied by marker count. -/
theorem inverse_degree_cap_to_k_over_j {N s k j r : ℕ} {q C μ : ℝ}
    (hN : 0 < N) (hj : 0 < j) (hr : 2 ≤ r)
    (hvertex : N = (r-1)*k+s) (hs : 2*s ≤ N)
    (hμ : μ = (r:ℝ)*j/N) (hC : 0 ≤ C) (hq : q ≤ C/μ) :
    q ≤ (2*C)*(k:ℝ)/j := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hjr : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have hrr : (0:ℝ)<r := Nat.cast_pos.mpr (by omega)
  have hv : (N:ℝ) = ((r:ℝ)-1)*k+s := by
    have hv := congrArg (fun n : ℕ => (n:ℝ)) hvertex
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show 1≤r by omega), Nat.cast_one] using hv
  have hsr : 2*(s:ℝ) ≤ N := by exact_mod_cast hs
  have hnk : (N:ℝ) ≤ 2*r*k := by
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hμp : 0<μ := by rw [hμ]; positivity
  calc
    q ≤ C/μ := hq
    _ = C*(N:ℝ)/((r:ℝ)*j) := by rw [hμ]; field_simp
    _ ≤ C*(2*r*k)/((r:ℝ)*j) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnk hC) (by positivity)
    _ = (2*C)*(k:ℝ)/j := by field_simp <;> ring

end LooseHamilton
