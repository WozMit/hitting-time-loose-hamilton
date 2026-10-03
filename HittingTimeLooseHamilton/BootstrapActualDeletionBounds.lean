module

public import HittingTimeLooseHamilton.BootstrapBases
public import HittingTimeLooseHamilton.EndpointSpliceModels

public section

/-! Actual finite deletion sets, with the original-base deletion retained.
The bounds require only block sizes, so apply to the fixed raw registry before
any graph is observed. Coincident labels only reduce the cardinalities. -/
noncomputable section
namespace LooseHamilton.BootstrapActualDeletionBounds
open Finset BootstrapBases
variable {V : Type*} [DecidableEq V]
variable {M : Finset (Finset V)} {r : ℕ}

theorem private_source (b : Base M) (S : Finset V) (x : V)
    (hr : 3 ≤ r) (hS : S.card = r-3) :
    (deleted b ∪ insert x S).card ≤ (deleted b).card + (r-2) := by
  have h₁ := card_union_le (deleted b) (insert x S)
  have h₂ := card_insert_le x S
  omega

theorem private_candidate (b : Base M) (S Q : Finset V) (x : V)
    (hr : 3 ≤ r) (hS : S.card = r-3) (hQ : Q.card = r-2) :
    (deleted b ∪ insert x S ∪ Q).card ≤ (deleted b).card + 2*(r-2) := by
  have h₁ := private_source b S x hr hS
  have h₂ := card_union_le (deleted b ∪ insert x S) Q
  omega

theorem endpointI_core (b : Base M) (P : Finset V) (y : V)
    (l : EndpointCutLabelI V) (hP : P.card = r-2) (hl : l.2.card = r-2) :
    (deleted b ∪ (P ∪ l.deleted y)).card ≤ (deleted b).card + 2*(r-2)+1 := by
  have h₁ := card_union_le (deleted b) (P ∪ l.deleted y)
  have h₂ := card_union_le P (l.deleted y)
  have h₃ := card_insert_le y l.2
  unfold EndpointCutLabelI.deleted at h₁ h₂ ⊢
  omega

theorem endpointI_candidate (b : Base M) (P : Finset V) (y : V)
    (l : EndpointCutLabelI V) (q : EndpointSpliceInnerLabel V)
    (hP : P.card = r-2) (hl : l.2.card = r-2) (hq : q.1.card = r-2) :
    (deleted b ∪ (P ∪ l.deleted y ∪ q.1)).card ≤
      (deleted b).card + 3*(r-2)+1 := by
  have h₁ := endpointI_core b P y l hP hl
  have h₂ := card_union_le (deleted b ∪ (P ∪ l.deleted y)) q.1
  rw [union_assoc] at h₂
  omega

theorem endpointII_core (b : Base M) (P : Finset V) (y : V)
    (l : EndpointCutLabelII V) (hP : P.card = r-2)
    (hR : l.2.2.2.1.card = r-2) (hQ : l.2.2.2.2.card = r-2) :
    (deleted b ∪ (P ∪ l.deleted y)).card ≤ (deleted b).card + 3*(r-2)+3 := by
  have h₁ := card_union_le (deleted b) (P ∪ l.deleted y)
  have h₂ := card_union_le P (l.deleted y)
  have h₃ := card_union_le ({y,l.1,l.2.1} ∪ l.2.2.2.1) l.2.2.2.2
  have h₄ := card_union_le {y,l.1,l.2.1} l.2.2.2.1
  have h₅ := card_insert_le y {l.1,l.2.1}
  have h₆ := card_insert_le l.1 {l.2.1}
  have h₇ := card_singleton l.2.1
  unfold EndpointCutLabelII.deleted at h₁ h₂ ⊢
  omega

theorem endpointII_candidate (b : Base M) (P : Finset V) (y : V)
    (l : EndpointCutLabelII V) (q : EndpointSpliceInnerLabel V)
    (hP : P.card = r-2) (hR : l.2.2.2.1.card = r-2)
    (hQ : l.2.2.2.2.card = r-2) (hq : q.1.card = r-2) :
    (deleted b ∪ (P ∪ l.deleted y ∪ q.1)).card ≤
      (deleted b).card + 4*(r-2)+3 := by
  have h₁ := endpointII_core b P y l hP hR hQ
  have h₂ := card_union_le (deleted b ∪ (P ∪ l.deleted y)) q.1
  rw [union_assoc] at h₂
  omega

/-- The largest literal deletion bound, including the possible original port,
is exactly the advertised ambient budget. -/
theorem envelope (b : Base M) (hr : 3 ≤ r) :
    (deleted b).card + 4*(r-2)+3 ≤ 4*r-4 := by
  have := deleted_card_le b
  omega

theorem private_source_budget (b : Base M) (S : Finset V) (x : V)
    (hr : 3 ≤ r) (hS : S.card = r-3) :
    (deleted b ∪ insert x S).card ≤ 4*r-4 := by
  have := private_source b S x hr hS
  have := envelope b hr
  omega

theorem private_candidate_budget (b : Base M) (S Q : Finset V) (x : V)
    (hr : 3 ≤ r) (hS : S.card = r-3) (hQ : Q.card = r-2) :
    (deleted b ∪ insert x S ∪ Q).card ≤ 4*r-4 := by
  have := private_candidate b S Q x hr hS hQ
  have := envelope b hr
  omega

theorem endpointI_core_budget (b : Base M) (P : Finset V) (y : V)
    (l : EndpointCutLabelI V) (hr : 3 ≤ r)
    (hP : P.card = r-2) (hl : l.2.card = r-2) :
    (deleted b ∪ (P ∪ l.deleted y)).card ≤ 4*r-4 := by
  have := endpointI_core b P y l hP hl
  have := envelope b hr
  omega

theorem endpointI_candidate_budget (b : Base M) (P : Finset V) (y : V)
    (l : EndpointCutLabelI V) (q : EndpointSpliceInnerLabel V) (hr : 3 ≤ r)
    (hP : P.card = r-2) (hl : l.2.card = r-2) (hq : q.1.card = r-2) :
    (deleted b ∪ (P ∪ l.deleted y ∪ q.1)).card ≤ 4*r-4 := by
  have := endpointI_candidate b P y l q hP hl hq
  have := envelope b hr
  omega

theorem endpointII_core_budget (b : Base M) (P : Finset V) (y : V)
    (l : EndpointCutLabelII V) (hr : 3 ≤ r) (hP : P.card = r-2)
    (hR : l.2.2.2.1.card = r-2) (hQ : l.2.2.2.2.card = r-2) :
    (deleted b ∪ (P ∪ l.deleted y)).card ≤ 4*r-4 := by
  have := endpointII_core b P y l hP hR hQ
  have := envelope b hr
  omega

theorem endpointII_candidate_budget (b : Base M) (P : Finset V) (y : V)
    (l : EndpointCutLabelII V) (q : EndpointSpliceInnerLabel V)
    (hr : 3 ≤ r) (hP : P.card = r-2) (hR : l.2.2.2.1.card = r-2)
    (hQ : l.2.2.2.2.card = r-2) (hq : q.1.card = r-2) :
    (deleted b ∪ (P ∪ l.deleted y ∪ q.1)).card ≤ 4*r-4 :=
  (endpointII_candidate b P y l q hP hR hQ hq).trans (envelope b hr)

end LooseHamilton.BootstrapActualDeletionBounds
