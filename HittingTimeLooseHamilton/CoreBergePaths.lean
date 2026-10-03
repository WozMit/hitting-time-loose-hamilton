module

public import HittingTimeLooseHamilton.ExceptionalSetModels
public import Mathlib.Tactic

public section

/-! Explicit short Berge paths used by the deterministic exceptional-set core. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One incident edge joins its distinct vertices by a one-edge Berge path. -/
theorem shortBergeConnected_one {H : SimpleHypergraph V} {u v : V} {e : Finset V}
    (he : e ∈ H) (hu : u ∈ e) (hv : v ∈ e) (huv : u ≠ v) : shortBergeConnected H u v := by
  refine ⟨1, by omega, by omega, ⟨{
    vertices := ![u,v]
    vertices_injective := ?_
    edges := ![e]
    edges_injective := ?_
    edge_mem := ?_
    left_mem := ?_
    right_mem := ?_
    initial := rfl
    terminal := rfl }⟩⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i j _; fin_cases i <;> fin_cases j; rfl
  · intro i; fin_cases i; exact he
  · intro i; fin_cases i; exact hu
  · intro i; fin_cases i; exact hv

theorem shortBergeConnected_two {H : SimpleHypergraph V} {u x v : V} {e f : Finset V}
    (he : e ∈ H) (hf : f ∈ H) (hu : u ∈ e) (hxe : x ∈ e)
    (hxf : x ∈ f) (hv : v ∈ f)
    (huv : u ≠ v) (hux : u ≠ x) (hxv : x ≠ v) (hef : e ≠ f) :
    shortBergeConnected H u v := by
  refine ⟨2, by omega, by omega, ⟨{
    vertices := ![u,x,v]
    vertices_injective := ?_
    edges := ![e,f]
    edges_injective := ?_
    edge_mem := ?_
    left_mem := ?_
    right_mem := ?_
    initial := rfl
    terminal := rfl }⟩⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption

theorem shortBergeConnected_three {H : SimpleHypergraph V} {u x y v : V}
    {e f g : Finset V}
    (he : e ∈ H) (hf : f ∈ H) (hg : g ∈ H)
    (hu : u ∈ e) (hxe : x ∈ e) (hxf : x ∈ f) (hyf : y ∈ f)
    (hyg : y ∈ g) (hv : v ∈ g)
    (hverts : List.Pairwise (· ≠ ·) [u,x,y,v])
    (hedges : List.Pairwise (· ≠ ·) [e,f,g]) : shortBergeConnected H u v := by
  simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton,
    List.pairwise_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_true] at hverts hedges
  refine ⟨3, by omega, by omega, ⟨{
    vertices := ![u,x,y,v]
    vertices_injective := ?_
    edges := ![e,f,g]
    edges_injective := ?_
    edge_mem := ?_
    left_mem := ?_
    right_mem := ?_
    initial := rfl
    terminal := rfl }⟩⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption

theorem shortBergeConnected_four {H : SimpleHypergraph V} {u x w y v : V}
    {e f g k : Finset V}
    (he : e ∈ H) (hf : f ∈ H) (hg : g ∈ H) (hk : k ∈ H)
    (hu : u ∈ e) (hxe : x ∈ e) (hxf : x ∈ f) (hwf : w ∈ f)
    (hwg : w ∈ g) (hyg : y ∈ g) (hyk : y ∈ k) (hv : v ∈ k)
    (hverts : List.Pairwise (· ≠ ·) [u,x,w,y,v])
    (hedges : List.Pairwise (· ≠ ·) [e,f,g,k]) : shortBergeConnected H u v := by
  simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton,
    List.pairwise_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_true] at hverts hedges
  refine ⟨4, by omega, by omega, ⟨{
    vertices := ![u,x,w,y,v]
    vertices_injective := ?_
    edges := ![e,f,g,k]
    edges_injective := ?_
    edge_mem := ?_
    left_mem := ?_
    right_mem := ?_
    initial := rfl
    terminal := rfl }⟩⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
end LooseHamilton
