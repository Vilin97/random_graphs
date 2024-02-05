import RandomGraphs.erdos_renyi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Exponential

#check Real.log
#check Real.exp

open MeasureTheory ProbabilityTheory BigOperators

variable [Fintype V] [DecidableEq V]
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (G : Ω → SimpleGraph V) [∀ ω e, Decidable (Edge (G ω) e)]

-- probability of connected graph is exp(-exp(-c))
theorem probability_of_connected (hp : p = ((Real.log n) + c)/n) (hG : ErdosRenyi G p μ) : μ { ω | (G ω).is_connected } = Real.exp (-Real.exp (-c)) := by
sorry