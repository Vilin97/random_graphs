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
  (bernoulli_edges : ∀ {e : Sym2 V}, (¬e.IsDiag) → Bernoulli ((EdgeInd G (measurable_edge e)) : SimpleFunc Ω ℝ) p μ)
  -- edges are independent
  (independent_edges : iIndepFun inferInstance (fun e ω ↦ Edge (G ω) e) μ)

variable (p : NNReal) (hp : p ≤ 1)
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (G : Ω → SimpleGraph V) [∀ ω e, Decidable (Edge (G ω) e)]
variable (measurable_edge : ∀ (e : Sym2 V) (x : ℝ), MeasurableSet {ω | EdgeInd' (G ω) e = x})

@[simp]
lemma diag_edge_ind (e : Sym2 V) (h : e.IsDiag) : ∀ω, (EdgeInd G (measurable_edge e)) ω = 0 := by
  intro ω
  simp only [EdgeInd, EdgeInd', Edge, Nat.cast_eq_zero]
  have : e ∉ (G ω).edgeSet := by
    intro he
    exfalso
    exact SimpleGraph.not_isDiag_of_mem_edgeSet (G ω) he h
  simp only [this, ite_false]

@[simp]
lemma expected_diag_edge_ind (e : Sym2 V) (h : e.IsDiag) : ∫ ω, (EdgeInd G (measurable_edge e)) ω ∂μ = 0 := by
  simp only [diag_edge_ind G measurable_edge e h, integral_zero]

@[simp]
lemma expected_non_diag_edge_ind (e : Sym2 V) (he : ¬e.IsDiag) (h : ErdosRenyi G p μ measurable_edge) : ∫ ω, (EdgeInd G (measurable_edge e)) ω ∂μ = p := by
  simp only [bernoulli_expectation (h.bernoulli_edges he)]

lemma num_edges_skip_diag (h : ErdosRenyi G p μ measurable_edge) : NumEdges G measurable_edge = ∑ e in (Finset.univ.filter (fun e => ¬e.IsDiag)), (EdgeInd G (measurable_edge e)) := by
sorry

theorem expected_edge_count (h : ErdosRenyi G p μ measurable_edge) : ∫ ω, (NumEdges G measurable_edge) ω ∂μ = (Fintype.card (Sym2 V) - n) * p := by
  simp only [NumEdges, SimpleFunc.coe_sum, Finset.sum_apply]
  rw [integral_finset_sum]
  sorry
  -- simp only [exp_edge, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card]
  -- simp only [Finset.mem_univ, integrable, forall_true_left, implies_true]

-- TODO: switch from Sym2 to the type of distinct pairs. An edge like [a,a] should not be allowed.
-- TODO: clean up the measurable_edge assumption. It should not be necessary to drag it around everywhere.
