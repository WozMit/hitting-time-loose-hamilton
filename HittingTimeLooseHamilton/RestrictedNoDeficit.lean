module

public import HittingTimeLooseHamilton.RestrictedNoDeficitTerminal

public section

/-! Item 30.5: the restricted-host no-deficit estimate with fixed exposure.
The exposed edges stay in the terminal graph and the original degree lower
bounds, low-degree set and vertex count are used throughout. -/
noncomputable section
namespace LooseHamilton
open Finset Filter

/-- The sampling fraction is controlled before using any host-size estimate. -/
lemma restricted_no_deficit_batch_fraction {m k : ℕ} {ν : ℝ}
    (hm : 0 < m) (hk : 0 < k) (hν : 0 ≤ ν) :
    (noDeficitBatchSize m k ν:ℝ)/(m:ℝ) ≤ ν/k := by
  have hh := noDeficit_batch_ratio (n:=k) (m:=m) (k:=k) (Ck:=1)
    hk hm hk hν (by simp)
  simpa only [one_mul,noDeficitBatchSize] using hh

/-- Uniform pointwise complement-exposure estimate. The only offset bound is
on the original admissible source. In particular, there is no bound on the
possibly large offsets remaining after arbitrary edge-complement exposure. -/
theorem restricted_no_deficit_exposure {C K : ℝ} (hC : 0<C) (hK : 0<K)
    (B : ℝ) :
    ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V], N₀≤Fintype.card V →
      ∀ (r M : ℕ) (ell : V→ℕ) (markers : Finset (Finset V)),
      CoreAdmissible r M ell markers B → ∀ F : TerminalState V r M ell,
      TerminalRegular C F.val → ∀ (U J0 A0 S : SimpleHypergraph V),
      J0⊆U → F.val\U=A0 → F.val∩U=S →
      ∀ (k : ℕ) (ν : ℝ), (Fintype.card V:ℝ)≤K*k → 1≤ν →
      ν≤Real.log (Fintype.card V:ℝ) →
      noDeficitBatchSize J0.card k ν≤J0.card ∧
        1-noDeficitError (C*K) (epsilon/8) (Fintype.card V) ν ≤
          (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder J0.card)).event
            (fun σ => ∀ v, ell v ≤ vertexDegree
              (A0 ∪ (S \ batchSelection J0 J0.card rfl
                (noDeficitBatchSize J0.card k ν) σ)) v) := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (eventually_restricted_terminal_no_deficit hC hK B)
  refine ⟨N₀,?_⟩
  intro V _ _ hn r M ell markers hadm F hF U J0 A0 S hJ hA hS k ν hk hν hνlog
  have he := hN₀ _ hn V rfl r M ell markers hadm F hF J0 k ν hk hν hνlog
  exact ⟨he.1,restricted_no_deficit_complement_feasibility
    F.val U J0 A0 S hJ hA hS ell k ν (C*K) (epsilon/8) he⟩

end LooseHamilton
