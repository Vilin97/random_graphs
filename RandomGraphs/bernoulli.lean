import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Probability.Moments

open MeasureTheory ProbabilityTheory NNReal

structure Bernoulli
  [MeasurableSpace Ω]
  (B : SimpleFunc Ω ℝ) (p : NNReal)
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  : Prop :=
  (le_one : p ≤ 1)
  (range : SimpleFunc.range B = {0, 1})
  (prob_0 : μ (B⁻¹' {0}) = 1-p)
  (prob_1 : μ (B⁻¹' {1}) = p)

variable [MeasurableSpace Ω]

@[simp]
lemma measurable (B : SimpleFunc Ω ℝ) (μ : Measure Ω) : AEStronglyMeasurable B μ := SimpleFunc.aestronglyMeasurable B
@[simp]
lemma integrable (B : SimpleFunc Ω ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] : Integrable B μ := SimpleFunc.integrable_of_isFiniteMeasure B

-- ∫ X ∂μ = p
@[simp]
lemma bernoulli_expectation {B : SimpleFunc Ω ℝ} {p : NNReal} {μ : Measure Ω} [IsProbabilityMeasure μ] (h : Bernoulli B p μ) : ∫ ω, B ω ∂μ = p := by
  rw [←SimpleFunc.integral_eq_integral B (integrable B μ)]
  simp only [SimpleFunc.integral_eq, h.range, Finset.mem_singleton, zero_ne_one, smul_eq_mul,
    not_false_eq_true, Finset.sum_insert, mul_zero, Finset.sum_singleton, h.prob_1,
    ENNReal.coe_toReal, mul_one, zero_add]
