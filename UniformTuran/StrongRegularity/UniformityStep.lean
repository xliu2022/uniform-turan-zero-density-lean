module

public import UniformTuran.StrongRegularity.NormalizationConstruction
public import UniformTuran.StrongRegularity.InitialGrowthConstruction
public import UniformTuran.StrongRegularity.UniformPumping

/-!
# The proved approximation-to-regularity induction step

Actual initial growth and actual equitable normalization discharge all
construction premises of the finite energy iteration.  The remaining
induction input is precisely the approximation lemma in the previous
uniformity.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.StrongRegularity

theorem regularityLemma_succ_of_approximation {k : ℕ} (hk : 2 ≤ k)
    (hRAL : ApproximationLemma k) : RegularityLemma (k + 1) :=
  regularityLemma_succ_of_normalization (by omega)
    (initialGrowth_of_one_le (by omega))
    (equitableNormalization_of_approximation hk hRAL)

end UniformTuran.StrongRegularity
