import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Probability.Moments

open MeasureTheory ProbabilityTheory NNReal

-- 0 ≤ p ≤ 1
variable (p : NNReal) (hp : p ≤ 1)

-- like `hp` but with type `ENNReal`
lemma hp' : (p : ENNReal) ≤ 1 := by
  simp [hp]

-- two random variables X and Y
variable (X Y : Ω → ℝ)
-- We don't actually care what the probability space is
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
-- X and Y are Bernoulli. I'm not sure what is the best definition.
variable
  (hX : Measure.map (fun ω ↦ if (X ω = 1) then true else false) μ = (PMF.bernoulli p (hp' p hp)).toMeasure)
  (h0Y : μ {w | Y w = 0} = 1-p) (h1Y : μ {w | Y w = 1} = p)

-- X and Y are independent
variable (hIndep : IndepFun X Y μ)

-- ∫ |X| ∂μ is finite
@[simp]
lemma integrable : Integrable X μ := by
  sorry

-- ∫ X ∂μ = p
@[simp]
lemma bernoulli_expectation : ∫ x, X x ∂μ = p := by
  -- split integral into two parts, {w | X w = 0} and {w | X w = 1}
  sorry

-- ∫ X + Y ∂μ = 2p
lemma bernoulli_sum_expectation : ∫ x, X x + Y x ∂μ = 2*p := by
  simp only [integrable, integral_add, bernoulli_expectation p]
  ring
