import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Probability.Independence.Basic
import RandomGraphs.bernoulli
import RandomGraphs.erdos_renyi
import RandomGraphs.simple_func

open MeasureTheory ProbabilityTheory BigOperators

variable [Fintype V] [DecidableEq V]
variable (p : NNReal) (hp : p ≤ 1)
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (G : Ω → SimpleGraph V) [∀ ω e, Decidable (Edge (G ω) e)]


-- Degree(G, v) = Edge indicators of the form G {v, w} summed over all vertices w
def Degree (G: SimpleGraph V) (v : V) [∀ e : Sym2 V, Decidable (Edge G e)] : ℕ := ∑ w, EdgeInd' G ⟦(v, w)⟧


--do not need 0 ≤ k ≤ n - 1 since choose returns 0 outside of these bounds
--note: this should be changed if we allow self edges, which we implicity do by using Sym2 V
theorem degree_distribution (h : ErdosRenyi G p μ measurable_edge) (v : V) (k : ℕ):
  μ {ω | Degree (G ω) v = k} = (p ^ k : NNReal) * (p ^ (Fintype.card V-1-k): NNReal) * (Fintype.card V - 1).choose k := by sorry


--the expected degree of a vertex is (|V| - 1)p
theorem expected_degree (h : ErdosRenyi G p μ measurable_edge) (v : V) : ∫ ω, (Degree (G ω) v : ℝ) ∂μ = (Fintype.card V - 1) * p := by sorry
  --This code needs two things: removing the diagonal edges and integrability of the EdgeInd function,
  --can probably be done in a similar way to the expected edges proof.
  /-simp only [Degree, Nat.cast_sum]
  rw [integral_finset_sum]
  have edge_exp : ∀e : Sym2 V, ∫ ω, ((EdgeInd' (G ω) e) : ℝ) ∂μ = p := by
    intro e
    exact bernoulli_expectation (h.bernoulli_edges e)
  simp [edge_exp]
  have h' : Finset.card (Finset.univ : Finset V) = Fintype.card V :=
    rfl
  exact Or.inl h'-/
