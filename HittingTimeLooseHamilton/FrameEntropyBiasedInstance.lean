module

public import HittingTimeLooseHamilton.FrameEntropyInstance
public import HittingTimeLooseHamilton.VertexEquivInvariants

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- The actual prescribed-direction cycle law, on the numbered active vertex set. -/
@[expose] def entropyInstance (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty) : BiasedRoleInstance r where
  N := F.n
  host := F.numberedEdges (F.rawHost H)
  markers := F.numberedEdges F.markers
  host_uniform := F.numberedEdges_uniform H
  marked_matching := (F.property.matching.restrictEdges F.active F.property.retained).vertexEdges F.vertexNumbering
  root := F.numberedRoot
  initial := F.numberedInitial
  cycleLaw := F.numberedCycleLaw H h

@[simp] lemma entropyInstance_N (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty) : (F.entropyInstance H h).N=F.n := rfl

@[simp] lemma entropyInstance_s (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty) : (F.entropyInstance H h).s=F.s :=
  F.numberedEdges_card F.markers F.property.retained

@[simp] lemma entropyInstance_k (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty) : (F.entropyInstance H h).k=F.k := by
  simp only [BiasedRoleInstance.k, ordinaryEdgeCount, Fintype.card_fin]
  change (F.n-(F.numberedEdges F.markers).card)/(r-1)=F.k
  rw [F.numberedEdges_card F.markers F.property.retained]
  rfl

@[simp] lemma entropyInstance_mu (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty) : (F.entropyInstance H h).μ=F.mu H := by
  change meanDegree (V:=Fin F.n) r (F.numberedEdges (F.rawHost H)).card=F.mu H
  rw [F.numberedEdges_card (F.rawHost H) (fun e he => (mem_filter.mp he).2)]
  simp [meanDegree, mu, m]

@[simp] lemma entropyInstance_entropy (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty) :
    FiniteEntropy.entropy (F.entropyInstance H h).cycleLaw.mass=Real.log (F.cycleCount H) :=
  F.numberedCycleLaw_entropy H h

/-- Original-N entropy loss converted exactly to the active-size normalization. -/
@[expose] def entropyXi (F : Frame r original) (B : ℝ) : ℝ :=
  (B*(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V)))/F.n

lemma entropyXi_mul_n (F : Frame r original) (B : ℝ) (hn : 0<F.n) :
    F.entropyXi B*F.n=B*(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V)) := by
  unfold entropyXi
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma entropyInstance_entropyBound_iff (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty) (B : ℝ) (hn : 0<F.n) :
    (F.entropyInstance H h).entropyBound (F.entropyXi B) ↔ F.entropyBudget H B := by
  rw [BiasedRoleInstance.entropyBound, entropyInstance_k, entropyInstance_mu,
    entropyInstance_entropy]
  change (F.k:ℝ)*Real.log (((r:ℝ)-1)*F.mu H)-((r:ℝ)-1)*F.k-
    F.entropyXi B*F.n ≤ Real.log (F.cycleCount H) ↔ _
  rw [F.entropyXi_mul_n B hn]
  exact ⟨fun hh => ⟨h,hh⟩, fun hh => hh.2⟩

lemma n_pos (F : Frame r original) : 0<F.n := by
  have hs : 0<F.s := card_pos.mpr F.markers_nonempty
  have hn := F.twice_s_le_n
  omega

lemma imposed_budget_entropyBound (F : Frame r original) (H : Finset (Finset V))
    (B : ℝ) (hB : F.entropyBudget H B) :
    (F.entropyInstance H hB.1).entropyBound (F.entropyXi B) :=
  (F.entropyInstance_entropyBound_iff H hB.1 B F.n_pos).mpr hB

end LooseHamilton.AuxiliaryFrame.Frame
