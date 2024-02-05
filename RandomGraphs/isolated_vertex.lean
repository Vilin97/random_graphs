import RandomGraphs.erdos_renyi

-- finite type of vertices
variable [Fintype V] [DecidableEq V]

-- make an edge from a pair of vertices
abbrev edge (v w : V) (h : v ≠ w) : EdgeType V := ⟨⟦(v, w)⟧, h⟩

def isolated_vertex_1 (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) := SimpleGraph.degree G v = 0

def isolated_vertex_2 (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) := ∀ w, w ≠ v → ¬ G.Adj v w

def isolated_vertex_3 (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) := ∀ w, (h : v ≠ w) → ¬ Edge G (edge v w h)
