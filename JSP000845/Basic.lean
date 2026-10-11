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

namespace JSP000845

/-- An edge 2-coloring of the complete graph on `n` vertices. -/
structure TwoColoring (n : Nat) where
  color : Fin n → Fin n → Bool
  symm : ∀ u v, color u v = color v u
  irrefl : ∀ u, color u u = false

/-- Standard colors: false is Red, true is Blue. -/
def ColorRed : Bool := false
def ColorBlue : Bool := true

/-- A triangle specified by three pairwise distinct vertices. -/
structure Triangle (n : Nat) where
  u : Fin n
  v : Fin n
  w : Fin n
  uv_ne : u ≠ v
  vw_ne : v ≠ w
  wu_ne : w ≠ u

/-- Vertices of a triangle as a list. -/
def Triangle.vertices {n : Nat} (t : Triangle n) : List (Fin n) :=
  [t.u, t.v, t.w]

/-- A triangle is monochromatic under coloring `c` if all three edges share the same color. -/
def Triangle.isMonochromatic {n : Nat} (c : TwoColoring n) (t : Triangle n) : Prop :=
  c.color t.u t.v = c.color t.v t.w ∧ c.color t.v t.w = c.color t.w t.u

/-- Specific color of a monochromatic triangle. -/
def Triangle.hasColor {n : Nat} (c : TwoColoring n) (t : Triangle n) (col : Bool) : Prop :=
  c.color t.u t.v = col ∧ c.color t.v t.w = col ∧ c.color t.w t.u = col

theorem Triangle.hasColor_isMonochromatic {n : Nat} (c : TwoColoring n) (t : Triangle n) (col : Bool)
    (h : t.hasColor c col) : t.isMonochromatic c := by
  rcases h with ⟨h1, h2, h3⟩
  exact ⟨by rw [h1, h2], by rw [h2, h3]⟩

/-- Two triangles are vertex-disjoint if they share no vertices. -/
def Triangle.Disjoint {n : Nat} (t₁ t₂ : Triangle n) : Prop :=
  t₁.u ≠ t₂.u ∧ t₁.u ≠ t₂.v ∧ t₁.u ≠ t₂.w ∧
  t₁.v ≠ t₂.u ∧ t₁.v ≠ t₂.v ∧ t₁.v ≠ t₂.w ∧
  t₁.w ≠ t₂.u ∧ t₁.w ≠ t₂.v ∧ t₁.w ≠ t₂.w

theorem Triangle.Disjoint_symm {n : Nat} {t₁ t₂ : Triangle n} (h : Triangle.Disjoint t₁ t₂) :
    Triangle.Disjoint t₂ t₁ := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact ⟨Ne.symm h1, Ne.symm h4, Ne.symm h7,
         Ne.symm h2, Ne.symm h5, Ne.symm h8,
         Ne.symm h3, Ne.symm h6, Ne.symm h9⟩

/-- A list of triangles is pairwise vertex-disjoint. -/
def PairwiseDisjoint {n : Nat} : List (Triangle n) → Prop
  | [] => True
  | t :: ts => (∀ s ∈ ts, Triangle.Disjoint t s) ∧ PairwiseDisjoint ts

/-- A valid packing of monochromatic triangles under coloring `c`. -/
def ValidPacking {n : Nat} (c : TwoColoring n) (ts : List (Triangle n)) : Prop :=
  PairwiseDisjoint ts ∧ ∀ t ∈ ts, t.isMonochromatic c

/-- The optimal uncovered bound for triangles: 2 + (n - 2) % 3. -/
def optimalUncoveredBound (n : Nat) : Nat :=
  2 + (n - 2) % 3

theorem optimalUncoveredBound_le_four (n : Nat) : optimalUncoveredBound n ≤ 4 := by
  unfold optimalUncoveredBound
  have hrem : (n - 2) % 3 < 3 := Nat.mod_lt _ (by decide)
  omega

end JSP000845
