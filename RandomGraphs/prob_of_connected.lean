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
--   simp only [bernoulli_expectation (h.bernoulli_edges)]
--   sorry

-- the expected vaule of number of isolated vertices in Graph G_{n,p} is n(1-p)^(n-1)
-- theorem isolated_vertices_ingraph_expectation  (h : ErdosRenyi G p μ) (hn : Fintype.card V = n) (vi : V): ∫ ω, (isolated_vertex_3 G vi) ω ∂μ = n*(1 - p)^(n - 1) := by
--sorry

-- lim n → infinity (probability of connected graph) is exp(-exp(-c))
-- theorem probability_of_connected (hp : p = ((Real.log n) + c)/n) (hG : ErdosRenyi G (Real.toNNReal p) μ) : Filter.tendsto (λ (n: ℕ → ℝ) μ { ω | (G ω).Connected} filter.at_top (nhds (Real.toNNReal (Real.exp (-Real.exp (-c)))))):= by
-- sorry


-- Unsure how to remove the Σ i in finset.range n segment

-- theorem taylor_series_log_expansion (x : ℝ) (hx: |x| < 1) : Filter.TendsTo (λ (n : ℕ) ∑ i in finset.range n, (-(x^i)/i)) atTop (log (1 - x)) := by
--   sorry

-- theorem taylor_series_bounding (c : ℝ) (n: ℕ) : Filter.TendsTo (fun n => Σ i in finset.range n, (Real.toNNReal ((Real.log n) + c)/ n)^n) atTop (n * p²) := by
--   sorry


-- theorem main_theorem (c: ℝ) (Gn : ℕ → Ω → SimpleGraph V) (h: ∀ n ∈ ℕ, ErdosRenyi (Gn n) (Real.toNNReal ((Real.log n) + c) / n) μ): Filter.Tendsto (fun n => ENNReal.toReal (μ {ω | (Gn n ω).Connected})) Filter.atTop (nhds (Real.exp (-Real.exp (-c)))) := by
--   sorry




-- Things that don't really make sense (but that I didn't want to delete yet?):

-- variable (n : ℕ)
-- variable (c: ℝ)
-- def probability := (n + c)/n
-- Real.toNNReal ((Real.log n) + c)/ n

-- def probability: (Real.toNNReal ((Real.log n) + c)/ n) := by
--   sorry

-- def ErdosRenyi_n_p : ErdosRenyi G p μ := by
--   sorry

-- -- This is a method of defining the probability that no vertex is isolated
-- -- or saying the expected number of isolated vertices is 0
-- -- so E(X_0) = n(1 - p)^(n-1)
-- def expected_isolated (n: ℕ) (c: R): n + c := by
--   sorry

-- def connected_probability (ErdosRenyi G p μ): () := by
--   sorry

-- theorem main_theorem (c : ℝ): Filter.TendsTo (G) filter.atTop (nhds (Real.exp (-Real.exp (-c)))) := by
--   sorry
-- theorem main_theorem (c: ℝ) (ErdosRenyi G p μ): Filter.TendsTo ()

-- {ω | (G ω).Connected} filter.atTop (nhds (Real.toNNReal (Real.exp (-Real.exp (-c)))))
