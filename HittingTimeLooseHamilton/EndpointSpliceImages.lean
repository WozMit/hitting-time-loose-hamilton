module

public import HittingTimeLooseHamilton.EndpointSpliceCoreFacts
public import HittingTimeLooseHamilton.EndpointSpliceInnerRecovery

public section

/-! # Oriented output information constructed by endpoint splicing -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

structure EndpointSpliceImageI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelI V) (b : EndpointSpliceInnerLabel V)
    (F : Finset (Finset V)) where
  cycle : MixedCycleOnWitness r (univ \ P) (insert {t,z} M) (endpointSpliceOutputI y l b F)
  host_subset : endpointSpliceOutputI y l b F ⊆ G
  root_start : cycle.junction (cycle.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) = t
  incoming_start : cycle.junction (cycle.slot.symm (.inr
    ⟨endpointSpliceNewEdge y b,by simp [endpointSpliceOutputI]⟩)) = b.2
  incoming_end : cycle.junction (finRotate cycle.length (cycle.slot.symm (.inr
    ⟨endpointSpliceNewEdge y b,by simp [endpointSpliceOutputI]⟩))) = y
  cut_start : cycle.junction (cycle.slot.symm (.inr
    ⟨l.edge y,by simp [endpointSpliceOutputI]⟩)) = y
  cut_role : edgeEndpointPair (insert {t,z} M) (endpointSpliceOutputI y l b F) (l.edge y) = {y,l.1}

structure EndpointSpliceImageII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelII V) (b : EndpointSpliceInnerLabel V)
    (F : Finset (Finset V)) where
  cycle : MixedCycleOnWitness r (univ \ P) (insert {t,z} M) (endpointSpliceOutputII y l b F)
  host_subset : endpointSpliceOutputII y l b F ⊆ G
  root_start : cycle.junction (cycle.slot.symm (.inl ⟨{t,z},mem_insert_self _ _⟩)) = t
  incoming_start : cycle.junction (cycle.slot.symm (.inr
    ⟨endpointSpliceNewEdge y b,by simp [endpointSpliceOutputII]⟩)) = b.2
  incoming_end : cycle.junction (finRotate cycle.length (cycle.slot.symm (.inr
    ⟨endpointSpliceNewEdge y b,by simp [endpointSpliceOutputII]⟩))) = y
  cut_start : cycle.junction (cycle.slot.symm (.inr
    ⟨l.firstEdge y,by simp [endpointSpliceOutputII]⟩)) = y
  cut_role : edgeEndpointPair (insert {t,z} M) (endpointSpliceOutputII y l b F) (l.firstEdge y) = {y,l.1}
  second_role : edgeEndpointPair (insert {t,z} M) (endpointSpliceOutputII y l b F) l.secondEdge = {l.2.1,l.2.2.1}

end LooseHamilton
