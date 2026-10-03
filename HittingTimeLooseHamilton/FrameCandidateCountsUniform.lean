module

public import HittingTimeLooseHamilton.FrameCandidateCountsBounds
public import HittingTimeLooseHamilton.FrameScalarEnvelopes

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset Filter
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma union_ports_card_le (F : Frame r original) (hm : IsPairMatching original) :
    (originalPorts F.markers ∪ originalPorts original).card ≤ 4*original.card+4 := by
  have hm' : F.markers.card ≤ original.card+2 := by
    have hh := F.marker_budget.introduced_le
    have hc := card_le_card_sdiff_add_card (s := F.markers) (t := original)
    omega
  have hc := card_union_le (originalPorts F.markers) (originalPorts original)
  have hfm : (originalPorts F.markers).card = 2*F.markers.card := F.property.matching.ports_card
  rw [hfm,hm.ports_card] at hc
  omega

/-- A single threshold works for every labelled frame and every vertex boundary.
The denominator is the complete legal candidate set, not the host edge set. -/
theorem uniform_candidate_counts (r : ℕ) (hr : 2 ≤ r) :
    ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (original : Finset (Finset V)), N₀ ≤ Fintype.card V →
      IsPairMatching original →
      (original.card:ℝ) ≤ (Fintype.card V:ℝ)^(1/10:ℝ) →
      ∀ (F : Frame r original),
        (F.n.choose r:ℝ)*(r*(r-1):ℕ)/2 ≤ F.candidates.card ∧
        ∀ D : Finset V,
          ((F.boundaryCandidates D).card:ℝ)/F.candidates.card ≤
            4*(D.card:ℝ)*r/Fintype.card V := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (CandidateBalance.eventually_candidate_uniform_envelope r)
  refine ⟨N₀,?_⟩
  intro V _ _ original hN hm hs F
  obtain ⟨hp,hn,hrn⟩ := hN₀ _ hN original.card
    (originalPorts F.markers ∪ originalPorts original).card
    F.val.deleted.card F.n hs (F.union_ports_card_le hm)
    F.val.deleted_card_le F.n_add_deleted
  refine ⟨F.candidates_card_half hr hrn hp,?_⟩
  intro D
  have hbound := F.boundaryCandidates_fraction hr hrn hp D
  have hnpos : (0:ℝ)<F.n := by exact_mod_cast (by omega : 0<F.n)
  have hNpos : (0:ℝ)<Fintype.card V := by
    have hh := F.n_add_deleted
    exact_mod_cast (by omega : 0<Fintype.card V)
  have hn' : (Fintype.card V:ℝ) ≤ 2*F.n := by exact_mod_cast hn
  apply hbound.trans
  apply (div_le_div_iff₀ hnpos hNpos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hn' (show 0 ≤ 2*(D.card:ℝ)*r by positivity)]
end LooseHamilton.AuxiliaryFrame.Frame
