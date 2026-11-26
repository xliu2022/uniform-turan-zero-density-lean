module

import UniformTuran
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Every imported declaration in the project namespace is audited transitively.
The only accepted axioms are Lean's standard propositional extensionality,
classical choice, and quotient soundness. The compiler separately checks
the proofs of the main statement and its two explicit corollaries; this
audit checks their complete transitive logical dependencies.

Author and maintainer: Xizhi Liu.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`UniformTuran).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Axiom audit failed: {name} depends on {ax}"
      checked := checked + 1
  logInfo m!"Axiom audit passed for {checked} project declarations."

#print axioms UniformTuran.hasPositionConsistentOrdering_of_density_eq_zero
#print axioms UniformTuran.palette_le_uniformTuranDensity
#print axioms UniformTuran.SpreadableLaw.phi_adjacent_swap
#print axioms UniformTuran.SpreadableLaw.phi_vertex_split
#print axioms UniformTuran.SpreadableLaw.phi_map_of_edgewiseIncreasing
#print axioms UniformTuran.Multipartite.complete_multipartite_bound
#print axioms UniformTuran.Multipartite.completePattern_bound
#print axioms UniformTuran.SpreadableLaw.positionConsistent_bound
#print axioms UniformTuran.exists_spreadable_model_of_approximate_laws
#print axioms UniformTuran.FiniteShadowModels.exists_spreadable_model
#print axioms UniformTuran.main_conclusions_of_finiteModelReduction
#print axioms UniformTuran.uniformDense_to_coordinateDense
#print axioms UniformTuran.admissible_coordinate_models
#print axioms UniformTuran.admissible_iff_mem_Icc_density
#print axioms UniformTuran.uniformDense_induced
#print axioms UniformTuran.admissible_coordinate_models_divisible
#print axioms UniformTuran.Regularity.DenseCounting.dense_counting_lemma
#print axioms UniformTuran.WeakRegularity.VertexPartition.exists_ramsey_regular_bound
#print axioms UniformTuran.admissible_one_coordinate_models
#print axioms UniformTuran.admissible_coordinate_models_divisible_of_one_le
#print axioms UniformTuran.Regularity.LabelSystem.addressClass_nonempty_of_tolerance
#print axioms UniformTuran.Regularity.LabelSystem.addressClass_card_bounds_of_tolerance
#print axioms UniformTuran.Regularity.IsRegular.pullbackCells
#print axioms UniformTuran.Regularity.DenseCounting.regular_complex_embedding
#print axioms UniformTuran.Regularity.regular_complex_host_embedding
#print axioms UniformTuran.Regularity.LabelSystem.isFree_retainedConfiguration
#print axioms UniformTuran.Regularity.LabelSystem.retainedAddressLaw_avoids
#print axioms UniformTuran.Regularity.AddressSelection.exists_clusters_and_global_lower_of_counted_partition
#print axioms UniformTuran.Regularity.exists_finite_model_of_regular_partition
#print axioms UniformTuran.finiteModelReduction_of_strongRegularity
#print axioms UniformTuran.paperMainTheorem_of_strongRegularity
#print axioms UniformTuran.StrongRegularity.LabelEnergy.exists_lower_face_refinement_of_badCarrier
#print axioms UniformTuran.StrongRegularity.PartitionState.noncrossing_volume_le
#print axioms UniformTuran.StrongRegularity.partitionEnergy_comp_equiv
#print axioms UniformTuran.StrongRegularity.PartitionState.codeEquiv_code
#print axioms UniformTuran.StrongRegularity.regularityLemma_two
#print axioms UniformTuran.StrongRegularity.partitionExistence_of_regularityLemma
#print axioms UniformTuran.StrongRegularity.PartitionState.LowRegular.fullCell_restrict_allowed
#print axioms UniformTuran.StrongRegularity.exists_grouped_regular_approximation
#print axioms UniformTuran.StrongRegularity.uniformColorEnergy_gain_of_repair
#print axioms UniformTuran.StrongRegularity.initialGrowth_of_one_le
#print axioms UniformTuran.StrongRegularity.regularityLemma_succ_of_normalization
#print axioms UniformTuran.StrongRegularity.PartitionState.exists_coarse_coloring_of_refinement
#print axioms UniformTuran.StrongRegularity.PartitionState.physicalAddressSlice_regular_to_tuple
#print axioms UniformTuran.StrongRegularity.equitableNormalization_of_approximation
#print axioms UniformTuran.StrongRegularity.regularityLemma_succ_of_approximation
#print axioms UniformTuran.StrongRegularity.exists_two_scale_regular_partitions
#print axioms UniformTuran.StrongRegularity.exists_trivial_grouped_approximation
#print axioms UniformTuran.StrongRegularity.PartitionState.exists_perfect_color_of_local_repairs
#print axioms UniformTuran.StrongRegularity.sum_approximationLocalBudget_le
#print axioms UniformTuran.StrongRegularity.TwoScaleRegularData.exists_profile_repair
#print axioms UniformTuran.StrongRegularity.approximationLemma_of_regularityLemma
#print axioms UniformTuran.StrongRegularity.regularityLemma_all
#print axioms UniformTuran.StrongRegularity.approximationLemma_all
#print axioms UniformTuran.StrongRegularity.partitionExistence
#print axioms UniformTuran.paperMainTheorem
#print axioms UniformTuran.uniformTuranDensity_eq_zero_iff_positionConsistentOrdering
#print axioms UniformTuran.uniformTuranDensity_gap
