module

public import HittingTimeLooseHamilton.PathRegularity
public import HittingTimeLooseHamilton.TerminalRegularityProbability
public import HittingTimeLooseHamilton.CandidateBalanceSpecification
public import HittingTimeLooseHamilton.FrameForwardProbability
public import HittingTimeLooseHamilton.ExtensionTerminalMarginal

public section

/-! A common terminal and path regularity event with unified constants. -/
noncomputable section
namespace LooseHamilton

lemma event_inter_lower {Ω : Type*} [Fintype Ω] (p : FiniteEntropy.Law Ω)
    (A B : Ω → Prop) (a b : ℝ) (hA : 1-a≤p.event A) (hB : 1-b≤p.event B) :
    1-(a+b)≤p.event (fun x => A x ∧ B x) := by
  have hh := CandidateBalance.event_not_and_le p A B
  rw [p.event_compl,p.event_compl,p.event_compl] at hh
  linarith

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Regularity holds at the terminal state and all eligible times, including
all bounded deletions and the fixed original-port prohibition. -/
@[expose] def CommonRegularity (r M : ℕ) (ell : V → ℕ) (original : Finset (Finset V))
    (h : ℕ) (c C L : ℝ) (ω : CandidateBalance.Outcome V r M ell) : Prop :=
  TerminalRegular C ω.1.val ∧ PathRegularityEvent r M ell c C L ω ∧
    PathDeletionRegularityEvent r M ell h c C L ω ∧
    PathProhibitionRegularityEvent r M ell original h C L ω

lemma CommonRegularity.inherited {r M : ℕ} {ell : V → ℕ}
    {original : Finset (Finset V)} {h j : ℕ} {c C L : ℝ}
    {ω : CandidateBalance.Outcome V r M ell}
    (H : CommonRegularity r M ell original h c C L ω)
    (hj : M≤j) (hK : j≤(completeEdges V r).card) :
    CandidateBalance.InheritedRegularity original j h c C L ω :=
  CandidateBalance.inherited_of_path j h c C L ω hj hK H.1 H.2.1 H.2.2.1 H.2.2.2

lemma TerminalRegular.mono {C D : ℝ} {F : SimpleHypergraph V}
    (H : TerminalRegular C F) (hCD : C≤D) : TerminalRegular D F := by
  refine ⟨?_,H.low_set,H.pair_degree,H.low_stars⟩
  intro v
  exact (H.maximum_degree v).trans (mul_le_mul_of_nonneg_right hCD (Real.log_natCast_nonneg _))

/-- Constants depend only on the uniformity and the deletion budget. The
cutoff is uniform over all original markers, offsets, and terminal sizes. -/
theorem common_regularity_whp (r : ℕ) (hr : 3≤r) (h : ℕ) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧
      ∀ offset L : ℝ, 0≤offset → 0≤L → ∀ η : ℝ, 0<η → ∃ N₀ : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V], N₀≤Fintype.card V →
          ∀ (M : ℕ) (ell : V → ℕ) (original : Finset (Finset V))
            (hadm : CoreAdmissible r M ell original offset),
            letI : Nonempty (TerminalState V r M ell) := hadm.feasible
            1-η≤(extensionLaw r M ell).event (CommonRegularity r M ell original h c C L) := by
  obtain ⟨c,C,hc,hC,hpath⟩ := proposition44 r hr
  obtain ⟨c',C',hc',hC',hpath⟩ := hpath h
  refine ⟨min c c',max terminalRegularityConstant (max C C'),lt_min hc hc',
    terminalRegularityConstant_pos.trans_le (le_max_left _ _),?_⟩
  intro offset L hoff hL η hη
  obtain ⟨Nt,hNt⟩ := terminal_regularity_whp r hr offset hoff (η/2) (by positivity)
  obtain ⟨Np,hNp⟩ := hpath offset L hoff hL (η/2) (by positivity)
  refine ⟨max Nt Np,?_⟩
  intro V _ _ hN M ell original hadm
  letI : Nonempty (TerminalState V r M ell) := hadm.feasible
  have ht := hNt V ((le_max_left _ _).trans hN) M ell original hadm
  have hp := hNp V ((le_max_right _ _).trans hN) M ell original hadm
  rw [←extension_terminal_event r M ell] at ht
  have hh := event_inter_lower (extensionLaw r M ell)
    (fun ω => TerminalRegular terminalRegularityConstant ω.1.val)
    (fun ω => PathRegularityEvent r M ell c C L ω ∧
      PathDeletionRegularityEvent r M ell h c' C' L ω ∧
      PathProhibitionRegularityEvent r M ell original h C' L ω)
    (η/2) (η/2) ht hp
  have hCmax : C ≤ max terminalRegularityConstant (max C C') :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC'max : C' ≤ max terminalRegularityConstant (max C C') :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hm := (extensionLaw r M ell).event_mono (fun ω (H :
      TerminalRegular terminalRegularityConstant ω.1.val ∧
      PathRegularityEvent r M ell c C L ω ∧
      PathDeletionRegularityEvent r M ell h c' C' L ω ∧
      PathProhibitionRegularityEvent r M ell original h C' L ω) => show
        CommonRegularity r M ell original h (min c c')
          (max terminalRegularityConstant (max C C')) L ω from
    ⟨H.1.mono (le_max_left _ _),
      fun j hj hK => (H.2.1 j hj hK).mono (min_le_left _ _) hCmax le_rfl,
      fun j hj hK Z hZ => (H.2.2.1 j hj hK Z hZ).mono (min_le_right _ _) hC'max le_rfl,
      fun j hj hK Z hZ => (H.2.2.2 j hj hK Z hZ).mono hC'max le_rfl⟩)
  linarith

end LooseHamilton
