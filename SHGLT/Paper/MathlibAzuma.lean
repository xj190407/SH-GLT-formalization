import Mathlib.Probability.Moments.SubGaussian
import SHGLT.Paper.TraceNorm

/-!
Mathlib bridge for the repeated-pull martingale concentration used in
Appendix A.3/A.9.  These are library theorems, not custom axioms.
-/

#check ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
#check ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
#check ProbabilityTheory.HasSubgaussianMGF.neg
