module

public import HittingTimeLooseHamilton.RootFreeTestIndexing
public import HittingTimeLooseHamilton.BootstrapBases

public section

/-! Exact raw geometric label families for the marginal bootstrap. Their index
contains no host graph or outcome-dependent eligibility condition. -/
noncomputable section
namespace LooseHamilton.BootstrapCatalogue
open Finset RootFreeTestIndexing
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev BaseLabel (r : ℕ) (V : Type*) [Fintype V] [DecidableEq V] :=
  PrivateLabel r V ⊕ EndpointLabelI r V ⊕ EndpointLabelII r V

/-- Original-port tests occur once on the full ambient space; the other three
families occur on every ordinary or original-port deletion base. -/
abbrev Geometry (r : ℕ) (M : Finset (Finset V)) :=
  (BootstrapBases.Base M × BaseLabel r V) ⊕ PortLabel r V

abbrev Index (r : ℕ) (M : Finset (Finset V)) :=
  Geometry r M × Fin ((Fintype.card V)^r + 1)

theorem private_card_le {r : ℕ} (hr : 3 ≤ r) :
    Fintype.card (PrivateLabel r V) ≤ (Fintype.card V)^(r+1) := by
  simp only [PrivateLabel, Fintype.card_prod]
  have hb := block_card_le (V := V) (r-3)
  calc
    _ ≤ (Fintype.card V)^(r-3) * (Fintype.card V * (Fintype.card V *
        (Fintype.card V * Fintype.card V))) := Nat.mul_le_mul_right _ hb
    _ = (Fintype.card V)^((r-3)+4) := by ring
    _ = _ := by congr 1; omega

theorem endpointI_card_le {r : ℕ} (hr : 3 ≤ r) :
    Fintype.card (EndpointLabelI r V) ≤ (Fintype.card V)^(2*r) := by
  simp only [EndpointLabelI, Fintype.card_prod]
  have hb := block_card_le (V := V) (r-2)
  calc
    _ ≤ (Fintype.card V)^(r-2) * (Fintype.card V * (Fintype.card V *
        (Fintype.card V * (Fintype.card V * (Fintype.card V)^(r-2))))) := by gcongr
    _ = (Fintype.card V)^(2*(r-2)+4) := by ring
    _ = _ := by congr 1; omega

theorem endpointII_card_le {r : ℕ} (hr : 3 ≤ r) :
    Fintype.card (EndpointLabelII r V) ≤ (Fintype.card V)^(3*r) := by
  simp only [EndpointLabelII, Fintype.card_prod]
  have hb := block_card_le (V := V) (r-2)
  calc
    _ ≤ (Fintype.card V)^(r-2) * (Fintype.card V * (Fintype.card V *
        (Fintype.card V * (Fintype.card V * (Fintype.card V * (Fintype.card V *
        ((Fintype.card V)^(r-2) * (Fintype.card V)^(r-2)))))))) := by gcongr
    _ = (Fintype.card V)^(3*(r-2)+6) := by ring
    _ = _ := by congr 1; omega

theorem port_card_le {r : ℕ} (hr : 3 ≤ r) :
    Fintype.card (PortLabel r V) ≤ (Fintype.card V)^(r+1) := by
  simp only [PortLabel, Fintype.card_prod]
  have hb := block_card_le (V := V) (r-2)
  calc
    _ ≤ (Fintype.card V)^(r-2) * (Fintype.card V * (Fintype.card V *
        Fintype.card V)) := Nat.mul_le_mul_right _ hb
    _ = (Fintype.card V)^((r-2)+3) := by ring
    _ = _ := by congr 1; omega

theorem index_card_le_raw {r : ℕ} (hr : 3 ≤ r) {M : Finset (Finset V)}
    (hM : IsPairMatching M) :
    Fintype.card (Index r M) ≤ ((Fintype.card V)^r+1) *
      ((Fintype.card V+1) * ((Fintype.card V)^(r+1) +
        (Fintype.card V)^(2*r) + (Fintype.card V)^(3*r)) +
        (Fintype.card V)^(r+1)) := by
  have hs : Fintype.card (BaseLabel r V) ≤ (Fintype.card V)^(r+1) +
      (Fintype.card V)^(2*r) + (Fintype.card V)^(3*r) := by
    simp only [BaseLabel, Fintype.card_sum]
    have := private_card_le (V := V) hr
    have := endpointI_card_le (V := V) hr
    have := endpointII_card_le (V := V) hr
    omega
  rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add
    (Nat.mul_le_mul (BootstrapBases.card_bases_le hM) hs) (port_card_le hr))

/-- The explicit polynomial calculation in the registration amendment. -/
theorem raw_bound {N r : ℕ} (hN : 2 ≤ N) (hr : 3 ≤ r) :
    (N^r+1)*((N+1)*(N^(r+1)+N^(2*r)+N^(3*r))+N^(r+1)) ≤
      14*N^(4*r+1) := by
  have h1 : 1 ≤ N^r := one_le_pow₀ (by omega)
  have ha : N^(r+1) ≤ N^(3*r) := pow_le_pow_right' (by omega) (by omega)
  have hb : N^(2*r) ≤ N^(3*r) := pow_le_pow_right' (by omega) (by omega)
  have hc : N^(r+1) ≤ N*N^(3*r) := by
    calc
      _ ≤ N^(3*r) := ha
      _ ≤ N*N^(3*r) := Nat.le_mul_of_pos_left _ (by omega)
  calc
    _ ≤ (2*N^r)*((2*N)*(3*N^(3*r))+N*N^(3*r)) := by
      apply Nat.mul_le_mul
      · omega
      · apply Nat.add_le_add
        · exact Nat.mul_le_mul (by omega) (by omega)
        · exact hc
    _ = 14*N^(4*r+1) := by ring

theorem coefficient_absorbed {N r : ℕ} (hN : 2 ≤ N) :
    14*N^(4*r+1) ≤ N^(4*r+5) := by
  have h4 : 14 ≤ N^4 := by
    have := Nat.pow_le_pow_left hN 4
    norm_num at this
    omega
  calc
    _ ≤ N^4*N^(4*r+1) := Nat.mul_le_mul_right _ h4
    _ = _ := by ring

theorem index_card_le_fourteen {r : ℕ} (hr : 3 ≤ r) {M : Finset (Finset V)}
    (hM : IsPairMatching M) (hN : 2 ≤ Fintype.card V) :
    Fintype.card (Index r M) ≤ 14*(Fintype.card V)^(4*r+1) :=
  (index_card_le_raw hr hM).trans (raw_bound hN hr)

theorem index_card_le {r : ℕ} (hr : 3 ≤ r) {M : Finset (Finset V)}
    (hM : IsPairMatching M) (hN : 2 ≤ Fintype.card V) :
    Fintype.card (Index r M) ≤ (Fintype.card V)^(4*r+5) :=
  (index_card_le_fourteen hr hM hN).trans (coefficient_absorbed hN)

end LooseHamilton.BootstrapCatalogue
