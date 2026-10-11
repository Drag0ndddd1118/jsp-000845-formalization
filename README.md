# JSP-000845 Formalization

Formalization of **JSP-000845**: *Disjoint Monochromatic Cliques in Edge-Colored Complete Graphs*.

## Mathematical Problem & References

- **Problem Catalog**: `JSP-000845`
- **Description**: How few vertices need remain uncovered by disjoint monochromatic cliques in an edge-colored complete graph?
- **Original Literature**:
  - J. W. Moon (1966), *"Disjoint triangles in chromatic graphs"*, *Mathematics Magazine* 39(5): 259–261.
  - S. A. Burr, P. Erdős, and J. H. Spencer (1975), *"Ramsey theorems for multiple copies of graphs"*, *Transactions of the American Mathematical Society* 209: 87–99 (Theorem 6).

### Theorem Summary

In Burr, Erdős, and Spencer (1975, Theorem 6), the authors resolve Moon's question for monochromatic cliques $K_k$. For the fundamental case of triangles ($k = 3$), the minimal number of vertices left uncovered by vertex-disjoint monochromatic triangles in an edge 2-coloring of $K_n$ is:

$$\text{optimalUncoveredBound}(n) = 2 + (n - 2) \bmod 3 \le 4$$

1. **Lower Bound (Extremal Tightness)**: For all $n \ge 2$, there exists a 2-coloring of $K_n$ (the canonical Burr–Erdős–Spencer coloring) where no vertex-disjoint monochromatic triangles can intersect $\{0, 1\}$. Consequently, every valid triangle packing leaves at least $2 + (n - 2) \bmod 3$ vertices uncovered.
2. **Extraction Step**: The Burr–Erdős–Spencer extraction lemma establishes that any monochromatic clique of size at least 3 can consume exterior edges via monochromatic triangles until the exterior leftover has order $\le 2$.

## Repository Structure

- `JSP000845/Basic.lean`:
  - Definition of 2-edge-coloring of complete graphs: `TwoColoring n`.
  - Triangles and monochromatic triangles: `Triangle n`, `Triangle.isMonochromatic`.
  - Vertex disjointness and valid packings: `PairwiseDisjoint`, `ValidPacking`.
  - Optimal bound definition: `optimalUncoveredBound n = 2 + (n - 2) % 3` and `optimalUncoveredBound_le_four`.
- `JSP000845/LowerBound.lean`:
  - Definition of `canonicalColoring n` (Burr–Erdős–Spencer partition into $B = \{0, 1\}$ and $A = \{2, \dots, n-1\}$).
  - Proof that no monochromatic triangle can intersect $\{0, 1\}$ (`canonical_triangle_in_A`).
  - Formal combinatorial pigeonhole bound (`nodup_bounded`) proving that any valid packing has size $\le (n - 2)/3$.
  - Full Lower Bound Theorem: `canonicalColoring_lower_bound`.
- `JSP000845/Extraction.lean`:
  - Burr–Erdős–Spencer Extraction Lemma: `bes_extraction_step` (depends on zero axioms).
- `JSP000845.lean`:
  - Main formal statement and proved lower bound theorem `jsp000845_lower_bound_proven`.

## Axiom Verification

Every theorem in this project is completely proved with **0 `sorry`** and **0 custom axioms**:

```lean
#print axioms JSP000845.jsp000845_lower_bound_proven
-- [propext, Classical.choice, Quot.sound]

#print axioms JSP000845.canonicalColoring_lower_bound
-- [propext, Classical.choice, Quot.sound]

#print axioms JSP000845.canonical_triangle_in_A
-- [propext, Classical.choice, Quot.sound]

#print axioms JSP000845.bes_extraction_step
-- does not depend on any axioms
```

## Build Instructions

This project is built directly on **Pure Lean 4 Core** (`leanprover/lean4:v4.34.0`) without heavy external dependencies, compiling in under 1 second:

```bash
lake build
```
