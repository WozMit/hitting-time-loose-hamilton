module

public import HittingTimeLooseHamilton.BootstrapActualTests

public section

/-! Actual legal sources satisfy the static catalogue gates. No cut-presence,
completion-count, observed-host, or target-distinctness hypothesis is used. -/
noncomputable section
namespace LooseHamilton.BootstrapCatalogue
open Finset RootFreeTestIndexing
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Legality of the actual private source gives the private geometric gate. -/
theorem private_sourceDistinct_of_legal {r : ℕ} (markers : SimpleHypergraph V)
    (S : Block (r-3) V) (x y z t : V)
    (hlegal : LegalPrivateCompletion r markers (insert x S.val) {y,z})
    (hx : x ∉ S.val) : sourceDistinct (Sum.inl (S,x,y,z,t) : BaseLabel r V) := by
  have hxy : x ≠ y := by
    intro heq
    exact disjoint_left.mp hlegal.private_pair_disjoint (mem_insert_self _ _)
      (by simp [heq])
  have hxz : x ≠ z := by
    intro heq
    exact disjoint_left.mp hlegal.private_pair_disjoint (mem_insert_self _ _)
      (by simp [heq])
  have hyz : y ≠ z := by
    intro heq
    have := hlegal.pair_card
    simp [heq] at this
  refine ⟨hxy,hxz,hyz,?_⟩
  apply disjoint_left.mpr
  intro v hv hvs
  rcases (by simpa only [mem_insert, mem_singleton] using hvs : v = x ∨ v = y ∨ v = z) with heq | heq | heq
  · exact hx (heq ▸ hv)
  · exact disjoint_left.mp hlegal.private_pair_disjoint (mem_insert_of_mem hv) (by simp [heq])
  · exact disjoint_left.mp hlegal.private_pair_disjoint (mem_insert_of_mem hv) (by simp [heq])

/-- Every surviving legal private source is registered, for every target. -/
theorem private_admissible_of_legal {r : ℕ} {M : SimpleHypergraph V}
    (b : BootstrapBases.Base M) (markers : SimpleHypergraph V)
    (S : Block (r-3) V) (x y z t : V)
    (hlegal : LegalPrivateCompletion r markers (insert x S.val) {y,z})
    (hx : x ∉ S.val)
    (hs : support (Sum.inl (S,x,y,z,t) : BaseLabel r V) ⊆ BootstrapBases.active b) :
    admissible (.inl (b,.inl (S,x,y,z,t))) :=
  ⟨hs, private_sourceDistinct_of_legal markers S x y z t hlegal hx⟩

/-- Type I cut labels need no cut-edge-presence assumption for registration. -/
theorem endpointI_sourceDistinct_of_legal {r : ℕ} (markers : SimpleHypergraph V)
    (P R : Block (r-2) V) (y z t a : V)
    (hlegal : LegalPrivateCompletion r markers P.val {y,z}) :
    sourceDistinct (Sum.inr (.inl (P,y,z,t,a,R)) : BaseLabel r V) := by
  refine ⟨?_,hlegal.private_pair_disjoint⟩
  intro heq
  have := hlegal.pair_card
  simp [heq] at this

/-- Type II cut labels likewise use only source geometry. -/
theorem endpointII_sourceDistinct_of_legal {r : ℕ} (markers : SimpleHypergraph V)
    (P R Q : Block (r-2) V) (y z t u v a : V)
    (hlegal : LegalPrivateCompletion r markers P.val {y,z}) :
    sourceDistinct (Sum.inr (.inr (P,y,z,t,u,v,a,R,Q)) : BaseLabel r V) := by
  exact endpointI_sourceDistinct_of_legal markers P R y z t a hlegal

theorem endpointI_admissible_of_legal {r : ℕ} {M : SimpleHypergraph V}
    (b : BootstrapBases.Base M) (markers : SimpleHypergraph V)
    (P R : Block (r-2) V) (y z t a : V)
    (hlegal : LegalPrivateCompletion r markers P.val {y,z})
    (hs : support (Sum.inr (.inl (P,y,z,t,a,R)) : BaseLabel r V) ⊆ BootstrapBases.active b) :
    admissible (.inl (b,.inr (.inl (P,y,z,t,a,R)))) :=
  ⟨hs, endpointI_sourceDistinct_of_legal markers P R y z t a hlegal⟩

theorem endpointII_admissible_of_legal {r : ℕ} {M : SimpleHypergraph V}
    (b : BootstrapBases.Base M) (markers : SimpleHypergraph V)
    (P R Q : Block (r-2) V) (y z t u v a : V)
    (hlegal : LegalPrivateCompletion r markers P.val {y,z})
    (hs : support (Sum.inr (.inr (P,y,z,t,u,v,a,R,Q)) : BaseLabel r V) ⊆ BootstrapBases.active b) :
    admissible (.inl (b,.inr (.inr (P,y,z,t,u,v,a,R,Q)))) :=
  ⟨hs, endpointII_sourceDistinct_of_legal markers P R Q y z t u v a hlegal⟩

/-- The actual original-port source conditions imply its raw-label gate. -/
theorem port_sourceDistinct_of_legal {r : ℕ} (M : SimpleHypergraph V)
    (P : Block (r-2) V) (a b u : V)
    (hlegal : LegalPrivateCompletion r (M.erase {a,b}) P.val {u,b})
    (ha : a ∉ P.val ∪ {u,b}) (hab : a ≠ b) : portSourceDistinct (P,a,b,u) := by
  refine ⟨hab,disjoint_left.mpr ?_⟩
  intro v hv hvab
  rcases (by simpa only [mem_insert, mem_singleton] using hvab : v = a ∨ v = b) with heq | heq
  · exact ha (mem_union_left _ (heq ▸ hv))
  · exact disjoint_left.mp hlegal.private_pair_disjoint hv (by simp [heq])

theorem port_admissible_of_legal {r : ℕ} (M : SimpleHypergraph V)
    (P : Block (r-2) V) (a b u : V)
    (hlegal : LegalPrivateCompletion r (M.erase {a,b}) P.val {u,b})
    (ha : a ∉ P.val ∪ {u,b}) (hab : a ≠ b) :
    admissible (M := M) (.inr (P,a,b,u)) :=
  port_sourceDistinct_of_legal M P a b u hlegal ha hab

end LooseHamilton.BootstrapCatalogue
