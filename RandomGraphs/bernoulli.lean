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

structure Bernoulli
  (B : Ω → ℕ) (p : NNReal)
  [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  : Prop :=
  (le_one : p ≤ 1)
  (prob_0 : μ {w | B w = 0} = 1-p)
  (prob_1 : μ {w | B w = 1} = p)

#check Bernoulli

-- ∫ |X| ∂μ is finite
@[simp]
lemma integrable [Fintype Ω] : Integrable X μ := by
  sorry

-- ∫ X ∂μ = p
@[simp]
lemma bernoulli_expectation : ∫ ω, X ω ∂μ = p := by
  -- split integral into two parts, {w | X w = 0} and {w | X w = 1}
  sorry
