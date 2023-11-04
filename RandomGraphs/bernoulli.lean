import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Probability.Moments

open MeasureTheory
open ProbabilityTheory

-- Bernoulli random variable X
variable (X : Bool → ℝ) (hX : ∀ b, X b = if b then 1 else 0)
-- Bernoulli PMF f
variable (f : PMF Bool) (p : NNReal) (hp : p ≤ 1) (hf: f = PMF.bernoulli p (by simp [hp]))
-- Bernoulli measure μ on Bool
variable (μ : Measure Bool) (hμ : μ = f.toMeasure) [MeasureSpace Bool]

-- the probability of `true` is p, using the PMF
example : f true = p := by
  simp only [hf, ENNReal.coe_le_one_iff, hp, PMF.bernoulli_apply, ge_iff_le, ENNReal.one_le_coe_iff,
    cond_true]

-- the probability of `true` is p, using the measure μ
@[simp]
lemma prob_true : μ {true} = p := by
  simp only [hμ, hf, PMF.toMeasure_apply_fintype, Fintype.univ_bool, Finset.mem_singleton,
    Set.mem_singleton_iff, Bool.not_eq_true, not_false_eq_true, Finset.sum_insert,
    Set.indicator_of_mem, PMF.bernoulli_apply, ge_iff_le, ENNReal.one_le_coe_iff, cond_true,
    Finset.sum_singleton, Set.indicator_of_not_mem, add_zero]

#check prob_true
#print prob_true

lemma bernoulli_expectation : ∫ x, X x ∂μ = p := by
  simp [hμ, hX, hf, hp]
  -- split integral into two parts, {true} and {false}
  sorry
