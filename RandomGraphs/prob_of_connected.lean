import RandomGraphs.erdos_renyi
import RandomGraphs.isolated_vertex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.MetricSpace.PseudoMetric

#check Real.log
#check Real.exp

open MeasureTheory ProbabilityTheory BigOperators

variable [Fintype V] [DecidableEq V]
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (G : Ω → SimpleGraph V) [∀ ω e, Decidable (Edge (G ω) e)]

-- the expected value of isolated vertex indicator is (1-p)^(n-1)
-- theorem isolated_vertex_expectation (h : ErdosRenyi G p μ) (hn : Fintype.card V = n) (vi : V) : ∫ ω, (isolated_vertex_3 G vi) ω ∂μ = (1 - p)^(n - 1) := by
  --simp only [bernoulli_expectation (h.bernoulli_edges)]
  --sorry

-- the expected vaule of number of isolated vertices in Graph G_{n,p} is n(1-p)^(n-1)
-- theorem isolated_vertices_ingraph_expectation  (h : ErdosRenyi G p μ) (hn : Fintype.card V = n) (vi : V): ∫ ω, (isolated_vertex_3 G vi) ω ∂μ = n*(1 - p)^(n - 1) := by
--sorry

-- lim n → infinity (probability of connected graph) is exp(-exp(-c))
theorem probability_of_connected (hp : p = ((Real.log n) + c)/n) (hG : ErdosRenyi G (Real.toNNReal p) μ) : Filter.tendsto (λ (n: ℕ → ℝ) μ { ω | (G ω).Connected} filter.at_top (nhds (Real.toNNReal (Real.exp (-Real.exp (-c)))))):= by
sorry
