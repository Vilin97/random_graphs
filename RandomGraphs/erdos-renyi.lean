import RandomGraphs.bernoulli
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory BigOperators

variable [Fintype V] [DecidableEq V]

-- is e an edge in G?
def Edge (G : SimpleGraph V) (e : Sym2 V) : Prop := e ∈ G.edgeSet
def EdgeInd (G : SimpleGraph V) (e : Sym2 V) [Decidable (Edge G e)]: ℕ := if (Edge G e) then 1 else 0
def NumEdges (G : SimpleGraph V) [∀ e : Sym2 V, Decidable (Edge G e)] : ℕ := ∑ e, EdgeInd G e

-- Erdos-Renyi random graph
structure ErdosRenyi
  (G : Ω → SimpleGraph V) (p : NNReal) [∀ ω e, Decidable (Edge (G ω) e)]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  : Prop :=
  (le_one : p ≤ 1)
  -- probability of an edge is p
  (bernoulli_edges : ∀ (v w : V), μ {ω | Edge (G ω) ⟦(v, w)⟧} = p)
  -- edges are independent
  (independent_edges : iIndepFun inferInstance (fun e ω ↦ Edge (G ω) e) μ)

variable (p : NNReal) (hp : p ≤ 1)
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (G : Ω → SimpleGraph V) [∀ ω e, Decidable (Edge (G ω) e)]

#check ErdosRenyi G p μ

theorem expected_edge_count (h : ErdosRenyi G p μ) : ∫ ω, (NumEdges (G ω) : ℝ) ∂μ = p * (Fintype.card V).choose 2 := by
  sorry
