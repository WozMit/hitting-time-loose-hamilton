module

public import HittingTimeLooseHamilton.FrameCandidateCounts
public import HittingTimeLooseHamilton.PathPerturbationBounds
public import HittingTimeLooseHamilton.KahnOrdering

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma powersetCard_vertexDegree_le (S : Finset V) (hr : 1 ≤ r) (v : V) :
    vertexDegree (S.powersetCard r) v ≤ (S.card-1).choose (r-1) := by
  by_cases hv : v ∈ S
  · have h := Kahn.Ordering.card_subsets_containing S {v}
      (singleton_subset_iff.mpr hv) r (by simpa using hr)
    simpa [vertexDegree] using le_of_eq h
  · have he : (S.powersetCard r).filter (fun e => v ∈ e) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,hve⟩ := mem_filter.mp he
      exact hv ((mem_powersetCard.mp he).1 hve)
    simp [vertexDegree,he]

/-- A union bound for size-r sets meeting a fixed vertex set. -/
lemma powersetCard_meeting_le (S D : Finset V) (hr : 1 ≤ r) :
    (((S.powersetCard r).filter (fun e => ¬ Disjoint e D)).card : ℝ) ≤
      D.card * ((S.card-1).choose (r-1):ℝ) := by
  have hh := deleteVertices_edge_loss_real (S.powersetCard r) D
    ((S.card-1).choose (r-1):ℝ)
    (fun v => Nat.cast_le.mpr (powersetCard_vertexDegree_le S hr v))
  rw [deleteVertices_card] at hh
  have hc := card_filter_add_card_filter_not (s := S.powersetCard r) (fun e : Finset V => Disjoint e D)
  change ((S.powersetCard r).card:ℝ) -
    ((S.powersetCard r).filter (fun e => Disjoint e D)).card ≤ _ at hh
  have hc' : (((S.powersetCard r).filter (fun e => Disjoint e D)).card : ℝ) +
    ((S.powersetCard r).filter (fun e => ¬ Disjoint e D)).card =
      (S.powersetCard r).card := by exact_mod_cast hc
  linarith

/-- All edges avoiding both port sets are candidates; the prohibition is not dropped. -/
theorem candidateEdges_deficit (F : Frame r original) (hr : 1 ≤ r) :
    (F.n.choose r : ℝ) - F.candidateEdges.card ≤
      (originalPorts F.markers ∪ originalPorts original).card *
        ((F.n-1).choose (r-1):ℝ) := by
  have hh := deleteVertices_edge_loss_real (F.active.powersetCard r)
    (originalPorts F.markers ∪ originalPorts original)
    ((F.n-1).choose (r-1):ℝ)
    (fun v => Nat.cast_le.mpr (powersetCard_vertexDegree_le F.active hr v))
  rw [deleteVertices_card,card_powersetCard] at hh
  have hsub : survivingHost (F.active.powersetCard r)
      (originalPorts F.markers ∪ originalPorts original) ⊆ F.candidateEdges := by
    intro e he
    obtain ⟨he,hd⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨he,(disjoint_union_right.mp hd).1,?_⟩
    rw [disjoint_iff_inter_eq_empty.mp (disjoint_union_right.mp hd).2]
    simp
  have hh' : ((survivingHost (F.active.powersetCard r)
      (originalPorts F.markers ∪ originalPorts original)).card:ℝ) ≤
      F.candidateEdges.card := Nat.cast_le.mpr (card_le_card hsub)
  change (F.n.choose r:ℝ) - _ ≤ _ at hh
  linarith

/-- Exact finite bound for legal candidates touching any fixed vertex boundary. -/
theorem boundaryCandidates_le (F : Frame r original) (hr : 2 ≤ r) (D : Finset V) :
    ((F.boundaryCandidates D).card:ℝ) ≤
      D.card * ((F.n-1).choose (r-1):ℝ) * (r*(r-1):ℕ) := by
  rw [F.boundaryCandidates_card hr,Nat.cast_mul]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : F.candidateEdges.filter (fun e => ¬ Disjoint e D) ⊆
      (F.active.powersetCard r).filter (fun e => ¬ Disjoint e D) := by
    intro e he
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp he).1).1,(mem_filter.mp he).2⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans
    (powersetCard_meeting_le F.active D (by omega))
/-- The finite half-denominator criterion, before any asymptotic specialisation. -/
theorem candidates_card_half (F : Frame r original) (hr : 2 ≤ r) (hn : r ≤ F.n)
    (hp : 2*r*(originalPorts F.markers ∪ originalPorts original).card ≤ F.n) :
    (F.n.choose r:ℝ) * (r*(r-1):ℕ) / 2 ≤ F.candidates.card := by
  have hident : (F.n.choose r:ℝ)*(r:ℝ) =
      (F.n:ℝ)*((F.n-1).choose (r-1):ℝ) := by
    exact_mod_cast (by simpa only [Nat.choose_one_right] using Nat.choose_mul (n := F.n) (by omega : 1 ≤ r))
  have hp' : 2*(r:ℝ)*(originalPorts F.markers ∪ originalPorts original).card ≤ F.n := by
    exact_mod_cast hp
  have hmul := mul_le_mul_of_nonneg_right hp'
    (Nat.cast_nonneg ((F.n-1).choose (r-1)) : (0:ℝ) ≤ _)
  have hrpos : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
  have hhalf : ((originalPorts F.markers ∪ originalPorts original).card:ℝ)*
      ((F.n-1).choose (r-1):ℝ) ≤ (F.n.choose r:ℝ)/2 := by
    nlinarith
  have hdef := F.candidateEdges_deficit (by omega : 1≤r)
  have hlow : (F.n.choose r:ℝ)/2 ≤ F.candidateEdges.card := by linarith
  have hfinal := mul_le_mul_of_nonneg_right hlow
    (Nat.cast_nonneg (r*(r-1)) : (0:ℝ) ≤ _)
  rw [F.candidates_card hr]
  push_cast
  push_cast at hfinal
  nlinarith

/-- Relative boundary loss after the half-denominator estimate. -/
theorem boundaryCandidates_fraction (F : Frame r original) (hr : 2 ≤ r) (hn : r ≤ F.n)
    (hp : 2*r*(originalPorts F.markers ∪ originalPorts original).card ≤ F.n)
    (D : Finset V) :
    ((F.boundaryCandidates D).card:ℝ) / F.candidates.card ≤
      2*(D.card:ℝ)*r/F.n := by
  have hhalf := F.candidates_card_half hr hn hp
  have hbound := F.boundaryCandidates_le hr D
  have hK : (0:ℝ)<F.n.choose r := by exact_mod_cast Nat.choose_pos hn
  have hR : (0:ℝ)<(r*(r-1):ℕ) := by exact_mod_cast (Nat.mul_pos (by omega : 0<r) (by omega : 0<r-1))
  have hC : (0:ℝ)<F.candidates.card := lt_of_lt_of_le (by positivity) hhalf
  have hnpos : (0:ℝ)<F.n := by exact_mod_cast (by omega : 0<F.n)
  have hident : (F.n.choose r:ℝ)*(r:ℝ) =
      (F.n:ℝ)*((F.n-1).choose (r-1):ℝ) := by
    exact_mod_cast (by simpa only [Nat.choose_one_right] using Nat.choose_mul (n := F.n) (by omega : 1 ≤ r))
  apply (div_le_div_iff₀ hC hnpos).mpr
  calc
    _ ≤ ((D.card:ℝ)*((F.n-1).choose (r-1):ℝ)*(r*(r-1):ℕ))*F.n :=
      mul_le_mul_of_nonneg_right hbound hnpos.le
    _ = (2*(D.card:ℝ)*r)*((F.n.choose r:ℝ)*(r*(r-1):ℕ)/2) := by
      nlinarith [congrArg (fun x : ℝ => x*(D.card:ℝ)*(r*(r-1):ℕ)) hident]
    _ ≤ _ := mul_le_mul_of_nonneg_left hhalf (by positivity)
end LooseHamilton.AuxiliaryFrame.Frame
