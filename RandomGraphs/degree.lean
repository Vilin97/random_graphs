import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Probability.Independence.Basic
import RandomGraphs.bernoulli
import RandomGraphs.erdos_renyi


open MeasureTheory ProbabilityTheory BigOperators

variable [Fintype V] [DecidableEq V]
variable (p : NNReal) (hp : p ≤ 1)
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (G : Ω → SimpleGraph V) [∀ ω e, Decidable (Edge (G ω) e)]



-- Degree(G, v) = Edge indicators of the form G {v, w} summed over all vertices w
def Degree (G : SimpleGraph V) (v : V) [∀ e : Sym2 V, Decidable (Edge G e)]: ℕ := ∑ w, EdgeInd' G ⟦(v, w)⟧

--do not need 0 ≤ k ≤ n - 1 since choose returns 0 outside of these bounds
theorem degree_distribution (h : ErdosRenyi G p μ) (v : V) (k : ℕ):
  μ {ω | Degree (G ω) v = k} = (p ^ k : NNReal) * (p ^ (Fintype.card V-1-k): NNReal) * (Fintype.card V - 1).choose k := by
  sorry

--not sure this is the right statement yet
theorem expected_degree (h : ErdosRenyi G p μ) (v : V) : ∫ ω, (Degree (G ω) v : ℝ) ∂μ = (Fintype.card V - 1) * p := by
  sorry
