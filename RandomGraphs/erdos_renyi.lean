import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Sym.Card
import RandomGraphs.bernoulli
import RandomGraphs.simple_func
import Init.Classical

open MeasureTheory ProbabilityTheory BigOperators

-- finite type of vertices
variable [Fintype V] [DecidableEq V]

-- is e an edge in G?
def Edge (G : SimpleGraph V) (e : Sym2 V) : Prop := e ∈ G.edgeSet
def EdgeInd' (G : SimpleGraph V) (e : Sym2 V) [Decidable (Edge G e)] : ℕ := if (Edge G e) then 1 else 0

@[simp]
lemma edge_ind_finite_range (G : Ω → SimpleGraph V) (e : Sym2 V) [∀ ω, Decidable (Edge (G ω) e)] : Set.Finite (Set.range fun ω => (EdgeInd' (G ω) e : ℝ)) := by
  apply @Set.Finite.subset ℝ {0,1} _ (Set.range fun ω => (EdgeInd' (G ω) e : ℝ)) _
  simp only [Set.mem_singleton_iff, zero_ne_one, Set.finite_singleton, Set.Finite.insert]
  simp [EdgeInd']
  rintro x ⟨ω, hx⟩
  rw [← hx]
  simp only [Set.mem_singleton_iff, zero_ne_one, Set.mem_insert_iff, ite_eq_right_iff, one_ne_zero,
    ite_eq_left_iff]
  exact Classical.em (¬Edge (G ω) e)

-- the SimpleFunc that is 1 on edges and 0 on non-edges
def EdgeInd (G : Ω → SimpleGraph V) [∀ ω, Decidable (Edge (G ω) e)] [MeasurableSpace Ω] (measurable_edge : ∀ x:ℝ, MeasurableSet {ω | EdgeInd' (G ω) e = x}) : SimpleFunc Ω ℝ :=
  SimpleFunc.mk (fun ω => EdgeInd' (G ω) e) (measurable_edge) (edge_ind_finite_range G e)

def NumEdges (G : Ω → SimpleGraph V) [∀ e ω, Decidable (Edge (G ω) e)] [MeasurableSpace Ω] (measurable_edge : ∀ (e : Sym2 V) (x : ℝ), MeasurableSet {ω | EdgeInd' (G ω) e = x}) : SimpleFunc Ω ℝ :=
  ∑ e, (EdgeInd G (measurable_edge e))

-- Erdos-Renyi random graph
structure ErdosRenyi
  (G : Ω → SimpleGraph V) (p : NNReal) [∀ ω e, Decidable (Edge (G ω) e)]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (measurable_edge : ∀ (e : Sym2 V) (x : ℝ), MeasurableSet {ω | EdgeInd' (G ω) e = x})
  : Prop :=
  (le_one : p ≤ 1)
  -- edges are bernoulli distributed
  (bernoulli_edges : ∀ (e : Sym2 V), Bernoulli ((EdgeInd G (measurable_edge e)) : SimpleFunc Ω ℝ) p μ)
  -- edges are independent
  (independent_edges : iIndepFun inferInstance (fun e ω ↦ Edge (G ω) e) μ)

variable (p : NNReal) (hp : p ≤ 1)
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (G : Ω → SimpleGraph V) [∀ ω e, Decidable (Edge (G ω) e)]
variable (measurable_edge : ∀ (e : Sym2 V) (x : ℝ), MeasurableSet {ω | EdgeInd' (G ω) e = x})

theorem expected_edge_count (h : ErdosRenyi G p μ measurable_edge) : ∫ ω, (NumEdges G measurable_edge) ω ∂μ = (Fintype.card (Sym2 V)) * p := by
  simp only [NumEdges, SimpleFunc.coe_sum, Finset.sum_apply]
  rw [integral_finset_sum]
  have exp_edge : ∀ e : Sym2 V, ∫ ω, (EdgeInd G (measurable_edge e)) ω ∂μ = p
  {
    intro e
    exact bernoulli_expectation (h.bernoulli_edges e)
  }
  simp only [exp_edge, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card]
  simp only [Finset.mem_univ, integrable, forall_true_left, implies_true]
