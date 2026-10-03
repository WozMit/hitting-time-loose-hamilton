module

public import HittingTimeLooseHamilton.FrameSurvivalConditioned
public import HittingTimeLooseHamilton.FrameEntropyBridgeExisting
public import HittingTimeLooseHamilton.CandidateExperiment

public section

noncomputable section
namespace LooseHamilton.FrameSurvival
open Finset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
local instance sampledRoleCountingPropDecidable : DecidablePred (fun p:Prop => p) := Classical.propDecidable

/-- Inclusion probability for the actual uniform fixed-size host batch. -/
theorem host_inclusion_probability {H : Finset α} {τ : ℕ} {e : α}
    (he : e∈H) (hτ : 1≤τ) (hτH : τ≤H.card) :
    (hostBatchLaw hτH).event (fun T => e∈T.val) = (τ:ℝ)/H.card := by
  classical
  letI := hostBatch_nonempty hτH
  change (FiniteEntropy.uniform : FiniteEntropy.Law (HostBatch H τ)).event _ = _
  rw [FiniteEntropy.Law.uniform_event,← Fintype.card_subtype]
  have hh := Fintype.card_congr (candidateBatchEquiv he hτ)
  change Fintype.card (CandidateBatch H τ e) = _ at hh
  rw [hh]
  simp only [HostBatch,Fintype.card_coe,card_powersetCard,card_erase_of_mem he]
  have hH : (H.card:ℝ) ≠ 0 := by exact_mod_cast (show H.card≠0 by omega)
  have hchoose : (H.card.choose τ:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hτH).ne'
  apply (div_eq_div_iff hchoose hH).mpr
  have h := Nat.add_one_mul_choose_eq (H.card-1) (τ-1)
  rw [show (H.card-1)+1=H.card by omega,show (τ-1)+1=τ by omega] at h
  have h' := congrArg (fun n:ℕ => (n:ℝ)) h
  push_cast at h'
  nlinarith only [h']

/-- Conditional failure probability is multiplied by the candidate inclusion
probability; no independence is claimed. -/
theorem host_inclusion_joint_bound {H : Finset α} {τ : ℕ} {e : α}
    (he : e∈H) (hτ : 1≤τ) (hτH : τ≤H.card)
    (P : Finset α → Prop) (p : ℝ)
    (hP : (hostBatchLaw (show τ-1≤(H.erase e).card by rw [card_erase_of_mem he];omega)).event
      (fun T => P (insert e T.val)) ≤ p) :
    (hostBatchLaw hτH).event (fun T => e∈T.val ∧ P T.val) ≤ (τ:ℝ)/H.card*p := by
  rw [candidate_conditioning he hτ hτH P,host_inclusion_probability he hτ hτH]
  exact mul_le_mul_of_nonneg_left hP (by positivity)

/-- Indexed roles keep multiplicities: different roles may specify one edge. -/
theorem sampled_role_mean {ι : Type*} [DecidableEq ι]
    {H : Finset α} {τ : ℕ} (hτ : 1≤τ) (hτH : τ≤H.card)
    (R : Finset ι) (edge : ι→α) (hR : ∀a∈R,edge a∈H) :
    (∑ T, (hostBatchLaw hτH).mass T*((R.filter (fun a => edge a∈T.val)).card:ℝ)) =
      (τ:ℝ)/H.card*R.card := by
  classical
  have hc (T : HostBatch H τ) : ((R.filter (fun a => edge a∈T.val)).card:ℝ)=
      ∑ a∈R, if edge a∈T.val then (1:ℝ) else 0 := by simp [←sum_filter]
  simp_rw [hc,mul_sum]
  rw [sum_comm]
  have he (a : ι) : (∑ T, (hostBatchLaw hτH).mass T*(if edge a∈T.val then (1:ℝ) else 0))=
      (hostBatchLaw hτH).event (fun T => edge a∈T.val) := by
    unfold FiniteEntropy.Law.event
    apply sum_congr rfl
    intro T _
    split_ifs <;> simp
  simp_rw [he]
  calc
    _ = ∑ _a∈R, (τ:ℝ)/H.card := sum_congr rfl (fun a ha => host_inclusion_probability (hR a ha) hτ hτH)
    _ = _ := by simp [mul_comm]

/-- Integrate rolewise conditional failures without any independence assumption.
Source exceptions are charged their full inclusion probability. -/
theorem sampled_role_failure_mean {ι : Type*} [DecidableEq ι]
    {H : Finset α} {τ : ℕ} (hτ : 1≤τ) (hτH : τ≤H.card)
    (R : Finset ι) (edge : ι→α) (hR : ∀a∈R,edge a∈H)
    (Bad : ι→Prop) (P : Finset α→ι→Prop) (p : ℝ) (hp : 0≤p)
    (hfail : ∀ a, ∀ ha:a∈R, ¬Bad a →
      (hostBatchLaw (show τ-1≤(H.erase (edge a)).card by
        rw [card_erase_of_mem (hR a ha)];omega)).event
        (fun T => P (insert (edge a) T.val) a) ≤ p) :
    (∑ T, (hostBatchLaw hτH).mass T*
      ((R.filter (fun a => edge a∈T.val ∧ P T.val a)).card:ℝ)) ≤
      (τ:ℝ)/H.card*((R.filter Bad).card+p*R.card) := by
  classical
  have hc (T : HostBatch H τ) :
      ((R.filter (fun a => edge a∈T.val ∧ P T.val a)).card:ℝ)=
        ∑ a∈R, if edge a∈T.val ∧ P T.val a then (1:ℝ) else 0 := by simp [←sum_filter]
  simp_rw [hc,mul_sum]
  rw [sum_comm]
  have he (a : ι) :
      (∑ T, (hostBatchLaw hτH).mass T*(if edge a∈T.val ∧ P T.val a then (1:ℝ) else 0))=
      (hostBatchLaw hτH).event (fun T => edge a∈T.val ∧ P T.val a) := by
    unfold FiniteEntropy.Law.event
    apply sum_congr rfl
    intro T _
    split_ifs <;> simp
  simp_rw [he]
  have hpoint (a : ι) (ha : a∈R) :
      (hostBatchLaw hτH).event (fun T => edge a∈T.val ∧ P T.val a) ≤
        (τ:ℝ)/H.card*((if Bad a then (1:ℝ) else 0)+p) := by
    by_cases hb : Bad a
    · have hh := (hostBatchLaw hτH).event_mono (fun T (ht : edge a∈T.val ∧ P T.val a) => ht.1)
      rw [host_inclusion_probability (hR a ha) hτ hτH] at hh
      simp only [if_pos hb]
      exact hh.trans (by nlinarith [mul_nonneg (show 0≤(τ:ℝ)/H.card by positivity) hp])
    · simp only [if_neg hb,zero_add]
      exact host_inclusion_joint_bound (hR a ha) hτ hτH (fun T => P T a) p (hfail a ha hb)
  calc
    _ ≤ ∑ a∈R, (τ:ℝ)/H.card*((if Bad a then (1:ℝ) else 0)+p) := sum_le_sum hpoint
    _ = _ := by simp [mul_add,sum_add_distrib,←mul_sum,←sum_filter]; ring
end LooseHamilton.FrameSurvival
