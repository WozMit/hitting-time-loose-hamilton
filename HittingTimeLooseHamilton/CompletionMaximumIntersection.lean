module

public import HittingTimeLooseHamilton.AuxiliaryFrameCycles
public import HittingTimeLooseHamilton.FrameCandidateCountsBounds

public section

/-! Finite maximum argument on the actual legal directed candidates. The
endpoint reversal accounts for both directions, with the same old root. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- Exchange the endpoints while leaving the unordered private block fixed. -/
@[expose] def reverseCandidate (a : Finset V × V × V) : Finset V × V × V :=
  (a.1,a.2.2,a.2.1)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem reverseCandidate_reverse (a : Finset V × V × V) :
    reverseCandidate (reverseCandidate a) = a := by cases a; rfl

omit [Fintype V] [DecidableEq V] in
theorem reverseCandidate_injective : Function.Injective (@reverseCandidate V) :=
  Function.LeftInverse.injective reverseCandidate_reverse

@[simp] theorem reverseCandidate_mem (f : Frame r original) (a : Finset V × V × V) :
    reverseCandidate a ∈ f.candidates ↔ a ∈ f.candidates := by
  classical
  simp [candidates,LegalCandidate,reverseCandidate,Finset.pair_comm]

/-- Two exceptional direction sets and the mobility exceptions cannot cover
the legal candidates when their total cardinality is smaller. -/
theorem exists_large_two_directions (f : Frame r original)
    (large bad : Finset (Finset V × V × V))
    (hsize : (f.candidates \ large).card + 2*bad.card < f.candidates.card) :
    ∃ a ∈ f.candidates, a ∈ large ∧ a ∉ bad ∧ reverseCandidate a ∉ bad := by
  classical
  let excluded := (f.candidates \ large) ∪ bad ∪ bad.image reverseCandidate
  have he : excluded.card < f.candidates.card := by
    have h₁ := card_union_le (f.candidates \ large) bad
    have h₂ := card_union_le ((f.candidates \ large) ∪ bad) (bad.image reverseCandidate)
    have h₃ : (bad.image reverseCandidate).card ≤ bad.card := card_image_le
    dsimp [excluded]
    omega
  obtain ⟨a,ha,hea⟩ := exists_mem_notMem_of_card_lt_card he
  refine ⟨a,ha,?_,?_,?_⟩
  · by_contra hn
    exact hea (mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨ha,hn⟩)))
  · intro hb
    exact hea (mem_union_left _ (mem_union_right _ hb))
  · intro hb
    exact hea (mem_union_right _ (mem_image.mpr ⟨reverseCandidate a,hb,by simp⟩))

/-- Actual candidate balance plus a sufficiently large mobility family bounds
its source maximum. The count being bounded is the sum of both directed
completion counts, not a new abstract completion statistic. -/
theorem maximum_le_of_candidate_balance (f : Frame r original)
    (host : Finset (Finset V)) (α κ B : ℝ) (hκ : 0 < κ)
    (hscale : 0 < (f.cycleCount host:ℝ)/(((r:ℝ)-1)^2*f.mu host))
    (hbalance : ¬ f.candidateBad host α)
    (large : Finset (Finset V × V × V))
    (hlarge : ∀ a ∈ large, κ*B ≤
      (f.completionCount host a:ℝ) + f.completionCount host (reverseCandidate a))
    (hsize : ((f.candidates \ large).card:ℝ) +
      2*α*(f.candidates.card:ℝ) < f.candidates.card) :
    B ≤ (2*(1+α)/κ) * ((f.cycleCount host:ℝ)/(((r:ℝ)-1)^2*f.mu host)) := by
  classical
  let scale : ℝ := (f.cycleCount host:ℝ)/(((r:ℝ)-1)^2*f.mu host)
  let bad := f.candidates.filter (fun a => |(f.completionCount host a:ℝ)/scale-1| > α)
  have hbad : (bad.card:ℝ) ≤ α*(f.candidates.card:ℝ) := by
    simpa only [candidateBad,not_lt] using hbalance
  have hsize' : (f.candidates \ large).card + 2*bad.card < f.candidates.card := by
    have hb : ((f.candidates \ large).card:ℝ)+2*(bad.card:ℝ) < f.candidates.card := by
      linarith
    exact_mod_cast hb
  obtain ⟨a,ha,hla,hab,hrb⟩ := f.exists_large_two_directions large bad hsize'
  have upper (b : Finset V × V × V) (hb : b ∈ f.candidates) (hn : b ∉ bad) :
      (f.completionCount host b:ℝ) ≤ (1+α)*scale := by
    have habs : |(f.completionCount host b:ℝ)/scale-1| ≤ α := by
      simpa [bad,hb] using hn
    have hu := (abs_le.mp habs).2
    have hd : (f.completionCount host b:ℝ)/scale ≤ 1+α := by linarith
    exact (div_le_iff₀ hscale).mp hd
  have hu₁ := upper a ha hab
  have hu₂ := upper (reverseCandidate a) ((f.reverseCandidate_mem a).mpr ha) hrb
  have hl := hlarge a hla
  calc
    B ≤ (2*(1+α)*scale)/κ := (le_div_iff₀ hκ).mpr (by nlinarith)
    _ = _ := by dsimp [scale]; ring

end LooseHamilton.AuxiliaryFrame.Frame
