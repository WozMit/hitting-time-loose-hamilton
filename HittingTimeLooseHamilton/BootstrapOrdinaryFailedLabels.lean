module

public import HittingTimeLooseHamilton.BootstrapOrdinaryLabelTransport
public import HittingTimeLooseHamilton.BootstrapSequentialMobility
public import HittingTimeLooseHamilton.SequentialCompletionOrdinaryPorts
public import HittingTimeLooseHamilton.BootstrapMaximumIntersection

public section

noncomputable section
namespace LooseHamilton.BootstrapOrdinaryFailedLabels
open Finset AuxiliaryFrame BootstrapBases BootstrapConstants SequentialCompletion
open BootstrapCompletionMaximum BootstrapOrdinaryLabelTransport

theorem failed_labels {N r : ℕ} {M : Finset (Finset (Fin N))}
    (hr : 3 ≤ r) (hN : 0 < N) (hM : IsPairMatching M)
    (hsmall : (M.card:ℝ) ≤ (N:ℝ)^(1/10:ℝ))
    (F : Frame r M) (hm : F.markers=M)
    (H : SimpleHypergraph (Fin N)) (hH : H ⊆ completeEdges (Fin N) r) (X c : ℝ)
    (hb : BootstrapSequentialMobility.Bounds (r:=r) hM none H X c)
    (a : Finset (Fin N) × Fin N × Fin N) (ha : a ∈ F.candidates)
    (hlarge : X/(N:ℝ)^(2*r) ≤ (weight (r:=r) (M:=M) H a:ℝ)) :
    ((F.candidates.filter (fun b => (weight (r:=r) (M:=M) H b:ℝ) <
      privateFactor r c^(r-2)*endpointFactor r c^2*(weight (r:=r) (M:=M) H a:ℝ))).card:ℝ) ≤
      (r:ℝ)*BootstrapMaximumIntersection.error r N*(N:ℝ)^r := by
  classical
  have hlegal : LegalPrivateCompletion r M a.1 {a.2.1,a.2.2} := by
    have hh := ((mem_filter.mp ha).2 : F.LegalCandidate a).1
    simpa only [hm] using hh
  have hs := legal hM a hlegal
  obtain ⟨s,hP,hy,hz,hvalid⟩ := exists_state_of_legal _ _ _ _ hs.private_card hs
  have hw : s.weight r (restrictEdges (active none) (markers hM none))
      (fixedPortHost (inducedHost (active none) H) (fixedPorts none)) = weight (r:=r) (M:=M) H a := by
    rw [State.weight,hP,hy,hz,←weight_eq hM H hH a]
  have hlabels : ∀ l ∈ F.candidates.image (label (M:=M)), l.1.card=r-2 := by
    rintro l hl
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hl
    rw [block_card]
    exact ((mem_filter.mp hb).2 : F.LegalCandidate b).1.private_card
  have hbnd := hb.ordinary s hvalid (ordinary_source_ports hM s hvalid)
    (by rwa [hw]) (ordinary_fixedPorts hM) (F.candidates.image (label (M:=M))) hlabels
  rw [hw] at hbnd
  have hcard : (F.candidates.filter (fun b => (weight (r:=r) (M:=M) H b:ℝ) <
      privateFactor r c^(r-2)*endpointFactor r c^2*(weight (r:=r) (M:=M) H a:ℝ))).card ≤
    ((F.candidates.image (label (M:=M))).filter (fun l =>
      (completionCount r (restrictEdges (active none) (markers hM none))
        (fixedPortHost (inducedHost (active none) H) (fixedPorts none)) l.1 {l.2.1,l.2.2}:ℝ) <
      privateFactor r c^(r-2)*endpointFactor r c^2*(weight (r:=r) (M:=M) H a:ℝ))).card := by
    apply card_le_card_of_injOn (label (M:=M))
    · intro b hb
      exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hb).1,
        by simpa only [←weight_eq hM H hH b] using (mem_filter.mp hb).2⟩
    · intro b hb d hd he; exact label_injective he
  have hports : (fixedPorts (none : Base M)).card ≤ 2*M.card := by
    rw [←hM.ports_card]
    apply card_le_card_of_injOn Subtype.val
    · intro v hv; exact (mem_fixedPorts none v).mp hv
    · intro a ha b hb he; exact Subtype.ext he
  have he := BootstrapMaximumIntersection.step_bound_le (r:=r) hN hsmall hports
  change exceptionBound r N (fixedPorts (none : Base M)).card ≤ _ at he
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg r : (0:ℝ)≤r))
    (pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) (r-1))
  have hpow : (N:ℝ)*(N:ℝ)^(r-1)=(N:ℝ)^r := by
    rw [←pow_succ']; congr 1; omega
  have hh : (r:ℝ)*(BootstrapMaximumIntersection.error r N*N)*(N:ℝ)^(r-1) =
      (r:ℝ)*BootstrapMaximumIntersection.error r N*(N:ℝ)^r := by rw [←hpow]; ring
  rw [hh] at hm
  exact (Nat.cast_le.mpr hcard).trans (hbnd.trans hm)

end LooseHamilton.BootstrapOrdinaryFailedLabels
