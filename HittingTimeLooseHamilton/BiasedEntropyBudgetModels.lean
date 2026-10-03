module

public import HittingTimeLooseHamilton.BiasedEntropyEnsemble
public import HittingTimeLooseHamilton.BiasedRoleParameters
public import HittingTimeLooseHamilton.BiasedRoleSupport

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy
variable {r : ℕ}

lemma uniformCard (D : BiasedRoleInstance r) : ∀ e ∈ D.host, e.card=r := by
  intro e he
  exact (mem_completeEdges _ _).mp (D.host_uniform he)

abbrev ensembleIndex (D : BiasedRoleInstance r) :=
  BiasedEnsemble.Index D.root D.initial D.cycleLaw

@[expose] def ensembleLaw (D : BiasedRoleInstance r) : Law D.ensembleIndex :=
  BiasedEnsemble.law D.root D.initial D.cycleLaw

@[expose] def ensembleHost (D : BiasedRoleInstance r) (hr : 3≤r) :
    D.ensembleIndex → Kahn.Hypergraph (r*D.k) r :=
  BiasedEnsemble.host hr D.uniformCard D.root D.initial D.cycleLaw

@[expose] def ensembleMatchingLaw (D : BiasedRoleInstance r) (hr : 3≤r)
    (i : D.ensembleIndex) : Law (Kahn.MatchingIn (D.ensembleHost hr i)) :=
  BiasedEnsemble.matchingLaw hr D.uniformCard D.root D.initial D.cycleLaw i

@[expose] def roleEntropy (D : BiasedRoleInstance r) : ℝ :=
  entropy (D.cycleLaw.map (biasedCloneRole D.root D.initial)).mass

/-- Exact logarithmic role-support size; the root direction is fixed. -/
@[expose] def roleSupport (D : BiasedRoleInstance r) : ℝ :=
  Real.log (((D.N-2*D.s).choose (D.k-D.s):ℝ)*2^(D.s-1))

@[expose] def roleDeficit (D : BiasedRoleInstance r) : ℝ := D.roleSupport-D.roleEntropy

lemma ensemble_entropy_chain (D : BiasedRoleInstance r) (hr : 3≤r) :
    entropy D.cycleLaw.mass = D.roleEntropy +
      ∑ i, D.ensembleLaw.mass i*entropy (D.ensembleMatchingLaw hr i).mass :=
  BiasedEnsemble.entropy_chain hr D.uniformCard D.root D.initial D.cycleLaw

lemma roleEntropy_le_roleSupport (D : BiasedRoleInstance r) (hr : 3≤r) :
    D.roleEntropy ≤ D.roleSupport := by
  have h := ConnectedCloneCycle.role_entropy_le_log_support hr D.marked_matching
    D.root D.initial (D.cycleLaw.map biasedConnectedCycle)
  rw [Law.map_map] at h
  change entropy (D.cycleLaw.map (biasedCloneRole D.root D.initial)).mass ≤ _ at h
  simpa only [roleEntropy, roleSupport, k, s, Fintype.card_fin] using h

lemma roleDeficit_nonneg (D : BiasedRoleInstance r) (hr : 3≤r) :
    0 ≤ D.roleDeficit := sub_nonneg.mpr (D.roleEntropy_le_roleSupport hr)

end LooseHamilton.BiasedRoleInstance
