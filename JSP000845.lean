/-
Copyright (c) 2026 Qin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Qin Zhao
Problem: JSP-000845 (Disjoint Monochromatic Cliques in Edge-Colored Complete Graphs)
Reference:
- J. W. Moon (1966), "Disjoint triangles in chromatic graphs", Mathematics Magazine 39(5): 259–261.
- S. A. Burr, P. Erdős, and J. H. Spencer (1975), "Ramsey theorems for multiple copies of graphs",
  Trans. Amer. Math. Soc. 209: 87–99 (Theorem 6).
-/

import JSP000845.Basic
import JSP000845.LowerBound
import JSP000845.Extraction

namespace JSP000845

/--
The Lower Bound Theorem of Burr–Erdős–Spencer (1975) for JSP-000845:
For every n ≥ 2, there exists a 2-edge-coloring of K_n (the canonical coloring)
such that ANY valid packing of pairwise vertex-disjoint monochromatic triangles
leaves at least `optimalUncoveredBound n` vertices uncovered.
-/
def jsp000845LowerBoundStatement : Prop :=
  ∀ (n : Nat), 2 ≤ n →
    ∃ (c : TwoColoring n),
      ∀ (ts : List (Triangle n)),
        ValidPacking c ts → n - 3 * ts.length ≥ optimalUncoveredBound n

/--
Proof of the Burr–Erdős–Spencer Lower Bound for JSP-000845:
The canonical extremal coloring achieves the optimal uncovered bound 2 + (n - 2) % 3.
-/
theorem jsp000845_lower_bound_proven : jsp000845LowerBoundStatement := by
  intro n hn
  exact ⟨canonicalColoring n, fun ts hpack => canonicalColoring_lower_bound n hn ts hpack⟩

end JSP000845
