/-
Copyright (c) 2026 Qin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Qin Zhao
Problem: JSP-000845 (Disjoint Monochromatic Cliques in Edge-Colored Complete Graphs)
Reference:
- S. A. Burr, P. Erdős, and J. H. Spencer (1975), "Ramsey theorems for multiple copies of graphs",
  Trans. Amer. Math. Soc. 209: 87–99 (Theorem 6).
-/

import JSP000845.Basic

namespace JSP000845

def canonicalEdgeColor (u v : Nat) : Bool :=
  if u = v then false
  else if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) then ColorRed
  else if (u < 2 ∧ v ≥ 2) ∨ (u ≥ 2 ∧ v < 2) then ColorBlue
  else ColorRed

theorem canonicalEdgeColor_symm (u v : Nat) : canonicalEdgeColor u v = canonicalEdgeColor v u := by
  unfold canonicalEdgeColor
  by_cases h : u = v
  · rw [h]
  · have h' : ¬(v = u) := fun eq => h eq.symm
    have h1 : ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) ↔ ((v = 0 ∧ u = 1) ∨ (v = 1 ∧ u = 0)) := by
      constructor
      · intro h; rcases h with ⟨a, b⟩ | ⟨a, b⟩
        · right; exact ⟨b, a⟩
        · left; exact ⟨b, a⟩
      · intro h; rcases h with ⟨a, b⟩ | ⟨a, b⟩
        · right; exact ⟨b, a⟩
        · left; exact ⟨b, a⟩
    have h2 : ((u < 2 ∧ v ≥ 2) ∨ (u ≥ 2 ∧ v < 2)) ↔ ((v < 2 ∧ u ≥ 2) ∨ (v ≥ 2 ∧ u < 2)) := by
      constructor
      · intro h; rcases h with ⟨a, b⟩ | ⟨a, b⟩
        · right; exact ⟨b, a⟩
        · left; exact ⟨b, a⟩
      · intro h; rcases h with ⟨a, b⟩ | ⟨a, b⟩
        · right; exact ⟨b, a⟩
        · left; exact ⟨b, a⟩
    by_cases c1 : (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)
    · have c1' : (v = 0 ∧ u = 1) ∨ (v = 1 ∧ u = 0) := h1.mp c1
      simp [h, h', c1, c1']
    · have c1' : ¬((v = 0 ∧ u = 1) ∨ (v = 1 ∧ u = 0)) := fun c => c1 (h1.mpr c)
      by_cases c2 : (u < 2 ∧ v ≥ 2) ∨ (u ≥ 2 ∧ v < 2)
      · have c2' : (v < 2 ∧ u ≥ 2) ∨ (v ≥ 2 ∧ u < 2) := h2.mp c2
        simp [h, h', c1, c1', c2, c2']
      · have c2' : ¬((v < 2 ∧ u ≥ 2) ∨ (v ≥ 2 ∧ u < 2)) := fun c => c2 (h2.mpr c)
        simp [h, h', c1, c1', c2, c2']

theorem canonicalEdgeColor_irrefl (u : Nat) : canonicalEdgeColor u u = false := by
  unfold canonicalEdgeColor
  simp

def canonicalColoring (n : Nat) : TwoColoring n where
  color u v := canonicalEdgeColor u.val v.val
  symm u v := canonicalEdgeColor_symm u.val v.val
  irrefl u := canonicalEdgeColor_irrefl u.val

theorem canonical_color_eq {n : Nat} (u v : Fin n) :
    (canonicalColoring n).color u v = canonicalEdgeColor u.val v.val := rfl

theorem canonical_cross_lt_ge {n : Nat} {u v : Fin n} (hu : u.val < 2) (hv : v.val ≥ 2) :
    (canonicalColoring n).color u v = ColorBlue := by
  rw [canonical_color_eq]
  unfold canonicalEdgeColor
  have hne : ¬(u.val = v.val) := by omega
  have h01 : ¬((u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0)) := by omega
  have hcross : (u.val < 2 ∧ v.val ≥ 2) ∨ (u.val ≥ 2 ∧ v.val < 2) := Or.inl ⟨hu, hv⟩
  simp [hne, h01, hcross]

theorem canonical_cross_ge_lt {n : Nat} {u v : Fin n} (hu : u.val ≥ 2) (hv : v.val < 2) :
    (canonicalColoring n).color u v = ColorBlue := by
  rw [canonical_color_eq]
  unfold canonicalEdgeColor
  have hne : ¬(u.val = v.val) := by omega
  have h01 : ¬((u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0)) := by omega
  have hcross : (u.val < 2 ∧ v.val ≥ 2) ∨ (u.val ≥ 2 ∧ v.val < 2) := Or.inr ⟨hu, hv⟩
  simp [hne, h01, hcross]

theorem canonical_in_A {n : Nat} {u v : Fin n} (h : u ≠ v) (hu : u.val ≥ 2) (hv : v.val ≥ 2) :
    (canonicalColoring n).color u v = ColorRed := by
  rw [canonical_color_eq]
  unfold canonicalEdgeColor
  have hne : ¬(u.val = v.val) := fun eq => h (Fin.ext eq)
  have h01 : ¬((u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0)) := by omega
  have hcross : ¬((u.val < 2 ∧ v.val ≥ 2) ∨ (u.val ≥ 2 ∧ v.val < 2)) := by omega
  simp [hne, h01, hcross]

theorem canonical_in_B {n : Nat} {u v : Fin n} (h : u ≠ v) (hu : u.val < 2) (hv : v.val < 2) :
    (canonicalColoring n).color u v = ColorRed := by
  rw [canonical_color_eq]
  unfold canonicalEdgeColor
  have hne : ¬(u.val = v.val) := fun eq => h (Fin.ext eq)
  have h01 : (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) := by omega
  simp [hne, h01]

/--
Key Theorem: In the canonical coloring, any monochromatic triangle must have
all three vertices in A (i.e., with indices ≥ 2). No vertex in {0, 1} can be part
of any monochromatic triangle.
-/
theorem canonical_triangle_in_A (n : Nat) (t : Triangle n)
    (h : t.isMonochromatic (canonicalColoring n)) :
    t.u.val ≥ 2 ∧ t.v.val ≥ 2 ∧ t.w.val ≥ 2 := by
  rcases h with ⟨huv_vw, hvw_wu⟩
  by_cases hcol : (canonicalColoring n).color t.u t.v = ColorRed
  · have h_uv_red : (canonicalColoring n).color t.u t.v = ColorRed := hcol
    have h_vw_red : (canonicalColoring n).color t.v t.w = ColorRed := by rw [← huv_vw, hcol]
    have h_wu_red : (canonicalColoring n).color t.w t.u = ColorRed := by rw [← hvw_wu, ← huv_vw, hcol]
    have h_no_cross (x y : Fin n) (hx : x.val < 2) (hy : y.val ≥ 2) :
        (canonicalColoring n).color x y ≠ ColorRed := by
      rw [canonical_cross_lt_ge hx hy]; decide
    have h_no_cross2 (x y : Fin n) (hx : x.val ≥ 2) (hy : y.val < 2) :
        (canonicalColoring n).color x y ≠ ColorRed := by
      rw [canonical_cross_ge_lt hx hy]; decide
    by_cases hu_ge : t.u.val ≥ 2
    · by_cases hv_ge : t.v.val ≥ 2
      · by_cases hw_ge : t.w.val ≥ 2
        · exact ⟨hu_ge, hv_ge, hw_ge⟩
        · have hw_lt : t.w.val < 2 := by omega
          exact False.elim ((h_no_cross2 t.v t.w hv_ge hw_lt) h_vw_red)
      · have hv_lt : t.v.val < 2 := by omega
        exact False.elim ((h_no_cross2 t.u t.v hu_ge hv_lt) h_uv_red)
    · have hu_lt : t.u.val < 2 := by omega
      by_cases hv_ge : t.v.val ≥ 2
      · exact False.elim ((h_no_cross t.u t.v hu_lt hv_ge) h_uv_red)
      · have hv_lt : t.v.val < 2 := by omega
        by_cases hw_ge : t.w.val ≥ 2
        · exact False.elim ((h_no_cross2 t.w t.u hw_ge hu_lt) h_wu_red)
        · have hw_lt : t.w.val < 2 := by omega
          have h1 : t.u.val ≠ t.v.val := fun eq => t.uv_ne (Fin.ext eq)
          have h2 : t.v.val ≠ t.w.val := fun eq => t.vw_ne (Fin.ext eq)
          have h3 : t.w.val ≠ t.u.val := fun eq => t.wu_ne (Fin.ext eq)
          omega
  · have h_uv_blue : (canonicalColoring n).color t.u t.v = ColorBlue := by
      cases hc : (canonicalColoring n).color t.u t.v
      · contradiction
      · rfl
    have h_vw_blue : (canonicalColoring n).color t.v t.w = ColorBlue := by rw [← huv_vw, h_uv_blue]
    have h_wu_blue : (canonicalColoring n).color t.w t.u = ColorBlue := by rw [← hvw_wu, ← huv_vw, h_uv_blue]
    have h_no_AA (x y : Fin n) (hxy : x ≠ y) (hx : x.val ≥ 2) (hy : y.val ≥ 2) :
        (canonicalColoring n).color x y ≠ ColorBlue := by
      rw [canonical_in_A hxy hx hy]; decide
    have h_no_BB (x y : Fin n) (hxy : x ≠ y) (hx : x.val < 2) (hy : y.val < 2) :
        (canonicalColoring n).color x y ≠ ColorBlue := by
      rw [canonical_in_B hxy hx hy]; decide
    by_cases hu : t.u.val < 2
    · by_cases hv : t.v.val < 2
      · exact False.elim ((h_no_BB t.u t.v t.uv_ne hu hv) h_uv_blue)
      · have hv_ge : t.v.val ≥ 2 := by omega
        by_cases hw : t.w.val < 2
        · exact False.elim ((h_no_BB t.w t.u t.wu_ne hw hu) h_wu_blue)
        · have hw_ge : t.w.val ≥ 2 := by omega
          exact False.elim ((h_no_AA t.v t.w t.vw_ne hv_ge hw_ge) h_vw_blue)
    · have hu_ge : t.u.val ≥ 2 := by omega
      by_cases hv : t.v.val ≥ 2
      · exact False.elim ((h_no_AA t.u t.v t.uv_ne hu_ge hv) h_uv_blue)
      · have hv_lt : t.v.val < 2 := by omega
        by_cases hw : t.w.val ≥ 2
        · exact False.elim ((h_no_AA t.w t.u t.wu_ne hw hu_ge) h_wu_blue)
        · have hw_lt : t.w.val < 2 := by omega
          exact False.elim ((h_no_BB t.v t.w t.vw_ne hv_lt hw_lt) h_vw_blue)

-- Pigeonhole and counting helpers

def countRange (l : List Nat) : Nat → Nat
  | 0 => 0
  | K + 1 => countRange l K + List.count K l

theorem count_le_one_of_nodup (a : Nat) (l : List Nat) (h : l.Nodup) : List.count a l ≤ 1 := by
  induction l with
  | nil => rw [List.count_nil]; omega
  | cons b xs ih =>
    rw [List.nodup_cons] at h
    rw [List.count_cons]
    split
    · rename_i hb
      have heq : b = a := of_decide_eq_true hb
      subst heq
      rw [List.count_eq_zero_of_not_mem h.1]
      omega
    · exact ih h.2

theorem countRange_le (l : List Nat) (h : l.Nodup) (K : Nat) : countRange l K ≤ K := by
  induction K with
  | zero => dsimp [countRange]; omega
  | succ K ih =>
    dsimp [countRange]
    have h1 := count_le_one_of_nodup K l h
    omega

theorem count_cons_of_ne (a b : Nat) (l : List Nat) (hne : a ≠ b) :
    List.count a (b :: l) = List.count a l := by
  rw [List.count_cons]
  have h : (b == a) = false := by
    apply decide_eq_false
    intro eq
    exact hne eq.symm
  simp [h]

theorem count_cons_of_eq (a : Nat) (l : List Nat) :
    List.count a (a :: l) = List.count a l + 1 := by
  rw [List.count_cons]
  have h : (a == a) = true := decide_eq_true rfl
  simp

theorem countRange_cons_of_ge (b : Nat) (l : List Nat) (K : Nat) (hb : b ≥ K) :
    countRange (b :: l) K = countRange l K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    dsimp [countRange]
    have hne : K ≠ b := by omega
    rw [count_cons_of_ne K b l hne]
    have ih' := ih (by omega)
    rw [ih']

theorem countRange_cons_of_lt (b : Nat) (l : List Nat) (K : Nat) (hb : b < K) :
    countRange (b :: l) K = countRange l K + 1 := by
  induction K with
  | zero => omega
  | succ K ih =>
    dsimp [countRange]
    by_cases heq : b = K
    · subst heq
      rw [count_cons_of_eq b l]
      rw [countRange_cons_of_ge b l b (by omega)]
      omega
    · have h_lt : b < K := by omega
      rw [ih h_lt]
      have hne : K ≠ b := by omega
      rw [count_cons_of_ne K b l hne]
      omega

theorem length_le_countRange (l : List Nat) (K : Nat) (h : ∀ x ∈ l, x < K) :
    l.length ≤ countRange l K := by
  induction l with
  | nil => dsimp; omega
  | cons x xs ih =>
    have hx : x < K := h x (List.Mem.head xs)
    have hxs : ∀ y ∈ xs, y < K := fun y hy => h y (List.Mem.tail x hy)
    rw [countRange_cons_of_lt x xs K hx]
    have ih' := ih hxs
    dsimp [List.length]
    omega

theorem nodup_bounded (l : List Nat) (K : Nat) (hnd : l.Nodup) (h : ∀ x ∈ l, x < K) :
    l.length ≤ K := by
  have h1 := length_le_countRange l K h
  have h2 := countRange_le l hnd K
  omega

theorem arith_lower (n m : Nat) (hn : 2 ≤ n) (h : 3 * m ≤ n - 2) :
    n - 3 * m ≥ optimalUncoveredBound n := by
  unfold optimalUncoveredBound
  omega

/-- The list of all vertices occurring in a list of triangles. -/
def packingVertices {n : Nat} : List (Triangle n) → List (Fin n)
  | [] => []
  | t :: ts => t.u :: t.v :: t.w :: packingVertices ts

theorem packingVertices_length {n : Nat} (ts : List (Triangle n)) :
    (packingVertices ts).length = 3 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    dsimp [packingVertices, List.length]
    omega

theorem not_mem_packing_of_disjoint {n : Nat} (ts : List (Triangle n)) (t : Triangle n)
    (hdisj : ∀ s ∈ ts, Triangle.Disjoint t s) :
    t.u ∉ packingVertices ts ∧ t.v ∉ packingVertices ts ∧ t.w ∉ packingVertices ts := by
  induction ts with
  | nil =>
    dsimp [packingVertices]
    simp
  | cons s rest ih =>
    have hs : Triangle.Disjoint t s := hdisj s (List.Mem.head rest)
    have hrest : ∀ s' ∈ rest, Triangle.Disjoint t s' := fun s' h => hdisj s' (List.Mem.tail s h)
    have ⟨ihu, ihv, ihw⟩ := ih hrest
    rcases hs with ⟨hu1, hu2, hu3, hv1, hv2, hv3, hw1, hw2, hw3⟩
    dsimp [packingVertices]
    simp only [List.mem_cons]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      rcases h with h | h | h | h
      · exact hu1 h
      · exact hu2 h
      · exact hu3 h
      · exact ihu h
    · intro h
      rcases h with h | h | h | h
      · exact hv1 h
      · exact hv2 h
      · exact hv3 h
      · exact ihv h
    · intro h
      rcases h with h | h | h | h
      · exact hw1 h
      · exact hw2 h
      · exact hw3 h
      · exact ihw h

theorem pairwiseDisjoint_nodup {n : Nat} (ts : List (Triangle n)) (h : PairwiseDisjoint ts) :
    (packingVertices ts).Nodup := by
  induction ts with
  | nil =>
    dsimp [packingVertices]
    exact List.nodup_nil
  | cons t rest ih =>
    rcases h with ⟨hdisj, hrest⟩
    have ih_nd := ih hrest
    have ⟨nu, nv, nw⟩ := not_mem_packing_of_disjoint rest t hdisj
    dsimp [packingVertices]
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons]
      intro h
      rcases h with h | h | h
      · exact t.uv_ne h
      · exact t.wu_ne.symm h
      · exact nu h
    · rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · simp only [List.mem_cons]
        intro h
        rcases h with h | h
        · exact t.vw_ne h
        · exact nv h
      · rw [List.nodup_cons]
        exact ⟨nw, ih_nd⟩

theorem nodup_map_of_inj_on {α β : Type} (f : α → β) (l : List α)
    (hnd : l.Nodup)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    (l.map f).Nodup := by
  induction l with
  | nil =>
    dsimp [List.map]
    exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    dsimp [List.map]
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨y, hy, hf⟩
      have heq : x = y := hinj x (List.Mem.head xs) y (List.Mem.tail x hy) hf.symm
      subst heq
      exact hnd.1 hy
    · apply ih hnd.2
      intro a ha b hb hf
      exact hinj a (List.Mem.tail x ha) b (List.Mem.tail x hb) hf

theorem packingVertices_ge_two {n : Nat} (ts : List (Triangle n))
    (hmono : ∀ t ∈ ts, t.isMonochromatic (canonicalColoring n))
    (x : Fin n) (hx : x ∈ packingVertices ts) : x.val ≥ 2 := by
  induction ts with
  | nil =>
    dsimp [packingVertices] at hx
    contradiction
  | cons t rest ih =>
    have ht_mono : t.isMonochromatic (canonicalColoring n) := hmono t (List.Mem.head rest)
    have ht_A := canonical_triangle_in_A n t ht_mono
    have hrest_mono : ∀ s ∈ rest, s.isMonochromatic (canonicalColoring n) :=
      fun s hs => hmono s (List.Mem.tail t hs)
    dsimp [packingVertices] at hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx_rest
    · exact ht_A.1
    · exact ht_A.2.1
    · exact ht_A.2.2
    · exact ih hrest_mono hx_rest

/--
Theorem: Burr–Erdős–Spencer Lower Bound.
In the canonical coloring on K_n (for n ≥ 2), ANY valid packing of pairwise
vertex-disjoint monochromatic triangles leaves at least `optimalUncoveredBound n`
vertices uncovered.
-/
theorem canonicalColoring_lower_bound (n : Nat) (hn : 2 ≤ n) (ts : List (Triangle n))
    (hpack : ValidPacking (canonicalColoring n) ts) :
    n - 3 * ts.length ≥ optimalUncoveredBound n := by
  rcases hpack with ⟨hdisj, hmono⟩
  have hnd : (packingVertices ts).Nodup := pairwiseDisjoint_nodup ts hdisj
  let f : Fin n → Nat := fun x => x.val - 2
  have hinj : ∀ x ∈ packingVertices ts, ∀ y ∈ packingVertices ts, f x = f y → x = y := by
    intro x hx y hy hf
    have hx2 : x.val ≥ 2 := packingVertices_ge_two ts hmono x hx
    have hy2 : y.val ≥ 2 := packingVertices_ge_two ts hmono y hy
    dsimp [f] at hf
    have heq : x.val = y.val := by omega
    exact Fin.ext heq
  have hnd_map : ((packingVertices ts).map f).Nodup := nodup_map_of_inj_on f (packingVertices ts) hnd hinj
  have hlt : ∀ y ∈ (packingVertices ts).map f, y < n - 2 := by
    intro y hy
    rw [List.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx2 : x.val ≥ 2 := packingVertices_ge_two ts hmono x hx
    have hx_lt : x.val < n := x.isLt
    dsimp [f]
    omega
  have h_bound := nodup_bounded ((packingVertices ts).map f) (n - 2) hnd_map hlt
  rw [List.length_map, packingVertices_length] at h_bound
  exact arith_lower n ts.length hn h_bound

end JSP000845
