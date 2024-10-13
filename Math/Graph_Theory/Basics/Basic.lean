import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic

-- definition of a graph
structure Graph (V : Type) where
  vertices : Set V
  edges : V -> V -> Prop


-- definition of a full graph: everything is connected
structure FullGraph (V : Type) extends Graph V where
  full : ∀ V₁ V₂ : V, V₁ ∈ vertices → V₂ ∈ vertices → edges V₁ V₂


-- full graph with n elements
def FullGraph_n (n : ℕ) : FullGraph (Fin n) := {
  vertices := Set.univ
  edges := λ _ _ => true
  full := by simp
}


-- cycle graph with n elements
-- each node is connected to exactly two other nodes so that they form a closed cycle.
def Cycle_graph_n (n : ℕ) : Graph (Fin n) := {
  vertices := Set.univ
  edges := λ v w => (w = (v + 1) % n) ∨ (w = (v + n - 1) % n)
}


def Path_graph_n (n : ℕ) : Graph (Fin n) := {
  vertices := Set.univ
  edges := λ v w => (w = v % n + 1 ∧ v % n ≠ n-1) ∨ (w = v % n - 1 ∧ v % n ≠ 0)
}
