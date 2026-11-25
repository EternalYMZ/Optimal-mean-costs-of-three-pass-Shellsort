import Shellsort.F09NoncoprimeCost

-- Print the definitions of the input law, execution counters and finite minima.
#print Shellsort.RankPlacement
#print Shellsort.uniformAverage
#print Shellsort.LegalThreePassPair
#print Shellsort.insertCompared
#print Shellsort.gapInsertionCost
#print Shellsort.gapComparisonCost
#print Shellsort.threePassInsertionCost
#print Shellsort.threePassComparisonCost
#print Shellsort.threePassPairMeanShifts
#print Shellsort.threePassPairMeanComparisons
#print Shellsort.optimalThreePassMeanShifts
#print Shellsort.optimalThreePassMeanComparisons
#check Shellsort.gapInsertionOutputAt_eq

-- Print the full statement and the axioms in its transitive proof for each root.
#check Shellsort.F09.verified_three_pass_optimum
#print axioms Shellsort.F09.verified_three_pass_optimum
#check Shellsort.F09.verified_optimal_gap_families
#print axioms Shellsort.F09.verified_optimal_gap_families
#check Shellsort.F09.verified_optimal_regret
#print axioms Shellsort.F09.verified_optimal_regret
#check Shellsort.F09.verified_variational_shapes
#print axioms Shellsort.F09.verified_variational_shapes
#check Shellsort.F09.verified_kappa_precise
#print axioms Shellsort.F09.verified_kappa_precise
#check Shellsort.F09.verified_noncoprime_separation
#print axioms Shellsort.F09.verified_noncoprime_separation
#check Shellsort.F09.verified_global_scale_minimum
#print axioms Shellsort.F09.verified_global_scale_minimum
#check Shellsort.F09.actual_critical_uniform
#print axioms Shellsort.F09.actual_critical_uniform
#check Shellsort.F09.order_optimal_iff_finite
#print axioms Shellsort.F09.order_optimal_iff_finite
#check Shellsort.F09.comparison_order_optimal_iff_finite
#print axioms Shellsort.F09.comparison_order_optimal_iff_finite
#check Shellsort.F09.verified_noncoprime_cost_floor
#print axioms Shellsort.F09.verified_noncoprime_cost_floor
#check Shellsort.F09.verified_noncoprime_cost_penalty
#print axioms Shellsort.F09.verified_noncoprime_cost_penalty
#check Shellsort.F09.verified_exact_minimizers_coprime
#print axioms Shellsort.F09.verified_exact_minimizers_coprime
