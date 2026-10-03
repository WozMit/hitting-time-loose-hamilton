module

public import HittingTimeLooseHamilton.AuxiliaryFrameLabels
public import HittingTimeLooseHamilton.EndpointCutModels
public import Mathlib.Data.Nat.Choose.Bounds

public section

/-! Polynomial registration of root-free tests. The index stores vertex/block
labels, a bounded-change frame and a time. It never stores an observed graph,
a bad set, or a cut chosen after observing its count. -/
noncomputable section
namespace LooseHamilton.RootFreeTestIndexing
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Block (k : ℕ) (V : Type*) [Fintype V] [DecidableEq V] :=
  ↥((univ : Finset V).powersetCard k)

@[expose] def block (S : Finset V) {k : ℕ} (h : S.card = k) : Block k V :=
  ⟨S, mem_powersetCard.mpr ⟨subset_univ _, h⟩⟩

@[simp] theorem block_val (S : Finset V) {k : ℕ} (h : S.card = k) :
    (block S h).val = S := rfl

/-- The paper's fixed private test labels `S,x,y,z,t`. -/
abbrev PrivateLabel (r : ℕ) (V : Type*) [Fintype V] [DecidableEq V] :=
  Block (r-3) V × V × V × V × V
/-- Source private block, source/target endpoints, and the whole Type I cut. -/
abbrev EndpointLabelI (r : ℕ) (V : Type*) [Fintype V] [DecidableEq V] :=
  Block (r-2) V × V × V × V × V × Block (r-2) V
/-- Source private block, source/target endpoints, and the whole Type II cut. -/
abbrev EndpointLabelII (r : ℕ) (V : Type*) [Fintype V] [DecidableEq V] :=
  Block (r-2) V × V × V × V × V × V × V × Block (r-2) V × Block (r-2) V
/-- Source block and original-port labels `P,y₀,z₀,u`. -/
abbrev PortLabel (r : ℕ) (V : Type*) [Fintype V] [DecidableEq V] :=
  Block (r-2) V × V × V × V

abbrev RootTestLabel (r : ℕ) (V : Type*) [Fintype V] [DecidableEq V] :=
  PrivateLabel r V ⊕ EndpointLabelI r V ⊕ EndpointLabelII r V ⊕ PortLabel r V

/-- All correctly-sized private labels have a registered index. -/
@[expose] def privateLabel (r : ℕ) (S : Finset V) (hS : S.card = r-3) (x y z t : V) :
    PrivateLabel r V := (block S hS,x,y,z,t)

/-- The registration precedes any check of host-edge presence or cut count. -/
@[expose] def endpointLabelI (r : ℕ) (P : Finset V) (hP : P.card = r-2) (y z t : V)
    (l : EndpointCutLabelI V) (hl : l.2.card = r-2) : EndpointLabelI r V :=
  (block P hP,y,z,t,l.1,block l.2 hl)

@[expose] def endpointLabelII (r : ℕ) (P : Finset V) (hP : P.card = r-2) (y z t : V)
    (l : EndpointCutLabelII V) (h₁ : l.2.2.2.1.card = r-2)
    (h₂ : l.2.2.2.2.card = r-2) : EndpointLabelII r V :=
  (block P hP,y,z,t,l.1,l.2.1,l.2.2.1,block l.2.2.2.1 h₁,block l.2.2.2.2 h₂)

@[expose] def portLabel (r : ℕ) (P : Finset V) (hP : P.card = r-2) (y₀ z₀ u : V) :
    PortLabel r V := (block P hP,y₀,z₀,u)

theorem block_card_le (k : ℕ) : Fintype.card (Block k V) ≤ (Fintype.card V)^k := by
  simpa only [Block, Fintype.card_coe, card_powersetCard, card_univ] using
    Nat.choose_le_pow (Fintype.card V) k

theorem block_card_le_large (r k : ℕ) (hk : k ≤ r) :
    Fintype.card (Block k V) ≤ (Fintype.card V+1)^r := by
  exact (block_card_le k).trans ((Nat.pow_le_pow_left (by omega) k).trans
    (pow_le_pow_right' (by omega) hk))

theorem private_label_card_le (r : ℕ) :
    Fintype.card (PrivateLabel r V) ≤ (Fintype.card V+1)^(3*r+6) := by
  simp only [PrivateLabel, Fintype.card_prod]
  have hb := block_card_le_large (V := V) r (r-3) (by omega)
  calc
    _ ≤ (Fintype.card V+1)^r * ((Fintype.card V+1) * ((Fintype.card V+1) *
      ((Fintype.card V+1) * (Fintype.card V+1)))) := by gcongr <;> omega
    _ = (Fintype.card V+1)^(r+4) := by ring
    _ ≤ _ := pow_le_pow_right' (by omega) (by omega)

theorem endpoint_labelI_card_le (r : ℕ) :
    Fintype.card (EndpointLabelI r V) ≤ (Fintype.card V+1)^(3*r+6) := by
  simp only [EndpointLabelI, Fintype.card_prod]
  have hb := block_card_le_large (V := V) r (r-2) (by omega)
  calc
    _ ≤ (Fintype.card V+1)^r * ((Fintype.card V+1) * ((Fintype.card V+1) *
      ((Fintype.card V+1) * ((Fintype.card V+1) * (Fintype.card V+1)^r)))) := by
      gcongr <;> omega
    _ = (Fintype.card V+1)^(2*r+4) := by ring
    _ ≤ _ := pow_le_pow_right' (by omega) (by omega)

theorem endpoint_labelII_card_le (r : ℕ) :
    Fintype.card (EndpointLabelII r V) ≤ (Fintype.card V+1)^(3*r+6) := by
  simp only [EndpointLabelII, Fintype.card_prod]
  have hb := block_card_le_large (V := V) r (r-2) (by omega)
  calc
    _ ≤ (Fintype.card V+1)^r * ((Fintype.card V+1) * ((Fintype.card V+1) *
      ((Fintype.card V+1) * ((Fintype.card V+1) * ((Fintype.card V+1) *
      ((Fintype.card V+1) * ((Fintype.card V+1)^r * (Fintype.card V+1)^r))))))) := by
      gcongr <;> omega
    _ = _ := by ring

theorem port_label_card_le (r : ℕ) :
    Fintype.card (PortLabel r V) ≤ (Fintype.card V+1)^(3*r+6) := by
  simp only [PortLabel, Fintype.card_prod]
  have hb := block_card_le_large (V := V) r (r-2) (by omega)
  calc
    _ ≤ (Fintype.card V+1)^r * ((Fintype.card V+1) * ((Fintype.card V+1) *
      (Fintype.card V+1))) := by gcongr <;> omega
    _ = (Fintype.card V+1)^(r+3) := by ring
    _ ≤ _ := pow_le_pow_right' (by omega) (by omega)

theorem root_test_label_card_le (r : ℕ) (hN : 1 ≤ Fintype.card V) :
    Fintype.card (RootTestLabel r V) ≤ (Fintype.card V+1)^(3*r+8) := by
  have hsum : Fintype.card (RootTestLabel r V) ≤ 4*(Fintype.card V+1)^(3*r+6) := by
    simp only [RootTestLabel, Fintype.card_sum]
    have := private_label_card_le (V := V) r
    have := endpoint_labelI_card_le (V := V) r
    have := endpoint_labelII_card_le (V := V) r
    have := port_label_card_le (V := V) r
    omega
  calc
    _ ≤ _ := hsum
    _ ≤ (Fintype.card V+1)^2*(Fintype.card V+1)^(3*r+6) := by
      gcongr
      nlinarith
    _ = _ := by ring

abbrev FrameTimeIndex (r : ℕ) (original : Finset (Finset V)) :=
  AuxiliaryFrame.Frame r original × Fin ((Fintype.card V)^r+1)

/-- Time indices include every possible edge-count time in a simple uniform host. -/
abbrev RootTestIndex (r : ℕ) (original : Finset (Finset V)) :=
  AuxiliaryFrame.Frame r original × RootTestLabel r V × Fin ((Fintype.card V)^r+1)

/-- Every possible edge-count time is represented, including the complete host. -/
@[expose] def timeIndex (r j : ℕ) (hj : j ≤ (completeEdges V r).card) :
    Fin ((Fintype.card V)^r+1) :=
  ⟨j, Nat.lt_succ_of_le (hj.trans (by
    simpa only [completeEdges_card] using Nat.choose_le_pow (Fintype.card V) r))⟩

@[simp] theorem timeIndex_val (r j : ℕ) (hj : j ≤ (completeEdges V r).card) :
    (timeIndex r j hj).val = j := rfl

/-- The root is an actual vertex label, not selected from the observed graph. -/
@[expose] def labelRoot {r : ℕ} : RootTestLabel r V → V
  | .inl l => l.2.1
  | .inr (.inl l) => l.2.1
  | .inr (.inr (.inl l)) => l.2.1
  | .inr (.inr (.inr l)) => l.2.1

theorem time_card_le (r : ℕ) (hN : 1 ≤ Fintype.card V) :
    Fintype.card (Fin ((Fintype.card V)^r+1)) ≤ (Fintype.card V+1)^(r+1) := by
  simp only [Fintype.card_fin]
  have hp : 1 ≤ (Fintype.card V+1)^r := one_le_pow₀ (by omega)
  calc
    _ ≤ (Fintype.card V+1)^r + (Fintype.card V+1)^r := by
      exact Nat.add_le_add (Nat.pow_le_pow_left (by omega) r) hp
    _ ≤ (Fintype.card V+1)*(Fintype.card V+1)^r := by nlinarith
    _ = _ := by rw [pow_succ]; ring

theorem frame_time_card_le (r : ℕ) (original : Finset (Finset V))
    (hN : 2 ≤ Fintype.card V) :
    Fintype.card (FrameTimeIndex r original) ≤ (Fintype.card V)^(10*r+26) := by
  simp only [FrameTimeIndex, Fintype.card_prod]
  calc
    _ ≤ (Fintype.card V+1)^(4*r+12) * (Fintype.card V+1)^(r+1) :=
      Nat.mul_le_mul (AuxiliaryFrame.frame_card_le r original) (time_card_le r (by omega))
    _ = (Fintype.card V+1)^(5*r+13) := by ring
    _ ≤ ((Fintype.card V)^2)^(5*r+13) := Nat.pow_le_pow_left (by nlinarith) _
    _ = _ := by rw [← pow_mul]; congr 1; ring

theorem root_test_index_card_le (r : ℕ) (original : Finset (Finset V))
    (hN : 2 ≤ Fintype.card V) :
    Fintype.card (RootTestIndex r original) ≤ (Fintype.card V)^(16*r+42) := by
  simp only [RootTestIndex, Fintype.card_prod]
  calc
    _ ≤ (Fintype.card V+1)^(4*r+12) *
      ((Fintype.card V+1)^(3*r+8) * (Fintype.card V+1)^(r+1)) :=
      Nat.mul_le_mul (AuxiliaryFrame.frame_card_le r original)
        (Nat.mul_le_mul (root_test_label_card_le r (by omega)) (time_card_le r (by omega)))
    _ = (Fintype.card V+1)^(8*r+21) := by ring
    _ ≤ ((Fintype.card V)^2)^(8*r+21) := Nat.pow_le_pow_left (by nlinarith) _
    _ = _ := by rw [← pow_mul]; congr 1; ring

end LooseHamilton.RootFreeTestIndexing
