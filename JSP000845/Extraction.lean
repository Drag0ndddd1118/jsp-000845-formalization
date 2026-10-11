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

namespace JSP000845

/-- A set of vertices is a Red clique if every edge between distinct vertices is Red. -/
def IsRedClique {n : Nat} (c : TwoColoring n) (vs : List (Fin n)) : Prop :=
  ∀ u ∈ vs, ∀ v ∈ vs, u ≠ v → c.color u v = ColorRed

/-- A set of vertices is a Blue clique if every edge between distinct vertices is Blue. -/
def IsBlueClique {n : Nat} (c : TwoColoring n) (vs : List (Fin n)) : Prop :=
  ∀ u ∈ vs, ∀ v ∈ vs, u ≠ v → c.color u v = ColorBlue

/--
The Burr–Erdős–Spencer (1975) Extraction Lemma for triangles (k = 3):
Given a Red clique C and a Blue edge {x₁, x₂} disjoint from C, if |C| ≥ 3,
we can extract a monochromatic triangle (either Red or Blue) containing vertices
only from {x₁, x₂} ∪ C, reducing {x₁, x₂} by at least 1 vertex and leaving
the remainder of C as a Red clique.
-/
theorem bes_extraction_step {n : Nat} (c : TwoColoring n)
    (C : List (Fin n)) (hC_clique : IsRedClique c C)
    (x₁ x₂ : Fin n) (_hx_ne : x₁ ≠ x₂)
    (_hx₁_not_in_C : x₁ ∉ C) (_hx₂_not_in_C : x₂ ∉ C)
    (hx_blue : c.color x₁ x₂ = ColorBlue)
    (y₁ y₂ y₃ : Fin n) (hy₁ : y₁ ∈ C) (hy₂ : y₂ ∈ C) (hy₃ : y₃ ∈ C)
    (hy12 : y₁ ≠ y₂) (hy23 : y₂ ≠ y₃) (hy31 : y₃ ≠ y₁) :
    (∃ y a b : Fin n, a ∈ C ∧ b ∈ C ∧ a ≠ b ∧ (y = x₁ ∨ y = x₂) ∧
      (c.color y a = ColorRed ∧ c.color a b = ColorRed ∧ c.color b y = ColorRed)) ∨
    (∃ y ∈ C, c.color x₁ x₂ = ColorBlue ∧ c.color x₂ y = ColorBlue ∧ c.color y x₁ = ColorBlue) := by
  have h_symm (u v : Fin n) (col : Bool) (h : c.color u v = col) : c.color v u = col := by
    rw [← c.symm]; exact h
  -- Analyze edges from x₁
  by_cases h1_12 : c.color x₁ y₁ = ColorRed ∧ c.color x₁ y₂ = ColorRed
  · left; refine ⟨x₁, y₁, y₂, hy₁, hy₂, hy12, Or.inl rfl, ?_⟩
    have h_ab : c.color y₁ y₂ = ColorRed := hC_clique y₁ hy₁ y₂ hy₂ hy12
    exact ⟨h1_12.1, h_ab, h_symm x₁ y₂ ColorRed h1_12.2⟩
  by_cases h1_23 : c.color x₁ y₂ = ColorRed ∧ c.color x₁ y₃ = ColorRed
  · left; refine ⟨x₁, y₂, y₃, hy₂, hy₃, hy23, Or.inl rfl, ?_⟩
    have h_ab : c.color y₂ y₃ = ColorRed := hC_clique y₂ hy₂ y₃ hy₃ hy23
    exact ⟨h1_23.1, h_ab, h_symm x₁ y₃ ColorRed h1_23.2⟩
  by_cases h1_31 : c.color x₁ y₃ = ColorRed ∧ c.color x₁ y₁ = ColorRed
  · left; refine ⟨x₁, y₃, y₁, hy₃, hy₁, hy31, Or.inl rfl, ?_⟩
    have h_ab : c.color y₃ y₁ = ColorRed := hC_clique y₃ hy₃ y₁ hy₁ hy31
    exact ⟨h1_31.1, h_ab, h_symm x₁ y₁ ColorRed h1_31.2⟩
  -- Analyze edges from x₂
  by_cases h2_12 : c.color x₂ y₁ = ColorRed ∧ c.color x₂ y₂ = ColorRed
  · left; refine ⟨x₂, y₁, y₂, hy₁, hy₂, hy12, Or.inr rfl, ?_⟩
    have h_ab : c.color y₁ y₂ = ColorRed := hC_clique y₁ hy₁ y₂ hy₂ hy12
    exact ⟨h2_12.1, h_ab, h_symm x₂ y₂ ColorRed h2_12.2⟩
  by_cases h2_23 : c.color x₂ y₂ = ColorRed ∧ c.color x₂ y₃ = ColorRed
  · left; refine ⟨x₂, y₂, y₃, hy₂, hy₃, hy23, Or.inr rfl, ?_⟩
    have h_ab : c.color y₂ y₃ = ColorRed := hC_clique y₂ hy₂ y₃ hy₃ hy23
    exact ⟨h2_23.1, h_ab, h_symm x₂ y₃ ColorRed h2_23.2⟩
  by_cases h2_31 : c.color x₂ y₃ = ColorRed ∧ c.color x₂ y₁ = ColorRed
  · left; refine ⟨x₂, y₃, y₁, hy₃, hy₁, hy31, Or.inr rfl, ?_⟩
    have h_ab : c.color y₃ y₁ = ColorRed := hC_clique y₃ hy₃ y₁ hy₁ hy31
    exact ⟨h2_31.1, h_ab, h_symm x₂ y₁ ColorRed h2_31.2⟩
  -- If none of the above pairs are Red, at most one edge from x₁ is Red, and at most one from x₂ is Red
  have h_not_red (col : Bool) (h : ¬(col = ColorRed)) : col = ColorBlue := by
    cases col
    · contradiction
    · rfl
  right
  by_cases c11 : c.color x₁ y₁ = ColorRed
  · have c12 : c.color x₁ y₂ = ColorBlue := h_not_red _ (fun h => h1_12 ⟨c11, h⟩)
    have c13 : c.color x₁ y₃ = ColorBlue := h_not_red _ (fun h => h1_31 ⟨h, c11⟩)
    by_cases c22 : c.color x₂ y₂ = ColorRed
    · have c23 : c.color x₂ y₃ = ColorBlue := h_not_red _ (fun h => h2_23 ⟨c22, h⟩)
      refine ⟨y₃, hy₃, hx_blue, c23, h_symm x₁ y₃ ColorBlue c13⟩
    · have c22_blue : c.color x₂ y₂ = ColorBlue := h_not_red _ c22
      refine ⟨y₂, hy₂, hx_blue, c22_blue, h_symm x₁ y₂ ColorBlue c12⟩
  · have c11_blue : c.color x₁ y₁ = ColorBlue := h_not_red _ c11
    by_cases c21 : c.color x₂ y₁ = ColorRed
    · have c22 : c.color x₂ y₂ = ColorBlue := h_not_red _ (fun h => h2_12 ⟨c21, h⟩)
      have c23 : c.color x₂ y₃ = ColorBlue := h_not_red _ (fun h => h2_31 ⟨h, c21⟩)
      by_cases c12 : c.color x₁ y₂ = ColorRed
      · have c13 : c.color x₁ y₃ = ColorBlue := h_not_red _ (fun h => h1_23 ⟨c12, h⟩)
        refine ⟨y₃, hy₃, hx_blue, c23, h_symm x₁ y₃ ColorBlue c13⟩
      · have c12_blue : c.color x₁ y₂ = ColorBlue := h_not_red _ c12
        refine ⟨y₂, hy₂, hx_blue, c22, h_symm x₁ y₂ ColorBlue c12_blue⟩
    · have c21_blue : c.color x₂ y₁ = ColorBlue := h_not_red _ c21
      refine ⟨y₁, hy₁, hx_blue, c21_blue, h_symm x₁ y₁ ColorBlue c11_blue⟩

end JSP000845
