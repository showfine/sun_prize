import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset SimpleGraph
open scoped SimpleGraph

namespace JSP000628

universe u

noncomputable section
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Erdős Problem 767 / JSP-000628:
    A graph contains a cycle where some vertex has at least `k` incident chords. -/
def HasCycleWithKIncidentChords (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.edges.Nodup ∧ c.support.dropLast.Nodup ∧ 3 ≤ c.length ∧
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

/-!
### 模块一：子图性质与删点边数拆分
-/

/-- 删点后的诱导子图不包含带 k 弦的圈（子图保避免性） -/
lemma avoid_of_induce {V : Type u} [Fintype V] [DecidableEq V] {k : ℕ} {G : SimpleGraph V}
    {s : Set V} (hG : ¬HasCycleWithKIncidentChords k G) :
    ¬HasCycleWithKIncidentChords k (G.induce s) := by
  sorry

/-- 删去一个点后，原图的边数等于子图边数加上该点的度数 -/
lemma card_edgeFinset_eq_add_degree {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    G.edgeFinset.card = (G.induce {x | x ≠ v}).edgeFinset.card + G.degree v := by
  -- 1. 证明两部分边集互斥（不相交）
  have hd : Disjoint (G.edgeFinset.filter (fun e => v ∈ e)) (G.edgeFinset.filter (fun e => ¬ v ∈ e)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_filter] at he1 he2
    exact he2.2 he1.2
  -- 2. 证明两部分边集的并集恰好是全图边集
  have h_union : (G.edgeFinset.filter (fun e => v ∈ e)) ∪ (G.edgeFinset.filter (fun e => ¬ v ∈ e)) = G.edgeFinset := by
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  -- 3. 不相交基数求和（完全证毕，0 sorry）
  have h_part : G.edgeFinset.card =
      (G.edgeFinset.filter (fun e => v ∈ e)).card +
      (G.edgeFinset.filter (fun e => ¬ v ∈ e)).card := by
    rw [← Finset.card_union_of_disjoint hd, h_union]
  -- 4. 与 v 关联的边数等于 G.degree v (构造与邻域的双射，纯 rfl 完全证毕)
  have h_inc : (G.edgeFinset.filter (fun e => v ∈ e)).card = G.degree v := by
    have h_img : G.edgeFinset.filter (fun e => v ∈ e) =
        (G.neighborFinset v).image (fun w => s(v, w)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_image, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_neighborFinset]
      constructor
      · intro ⟨he, hv⟩
        revert he hv
        refine Sym2.inductionOn e (fun x y he hv => ?_)
        simp only [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact ⟨y, he, rfl⟩
        · exact ⟨x, he.symm, Sym2.eq_swap⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw, by simp⟩
    rw [h_img, Finset.card_image_of_injOn]
    · rfl
    · intro x _ y _ hxy
      rw [Sym2.eq_iff] at hxy
      rcases hxy with ⟨-, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  -- 5. 不与 v 关联的边数等于诱导子图边数 (构造诱导子图边集的单射双射，完全证毕)
  have h_ind : (G.edgeFinset.filter (fun e => ¬ v ∈ e)).card = (G.induce {x | x ≠ v}).edgeFinset.card := by
    let f : Sym2 {x : V // x ≠ v} → Sym2 V := Sym2.map Subtype.val
    have hf_inj : ∀ a b, f a = f b → a = b := by
      intro a b
      refine Sym2.inductionOn a (fun x1 y1 => ?_)
      refine Sym2.inductionOn b (fun x2 y2 => ?_)
      intro hab
      change s(x1.val, y1.val) = s(x2.val, y2.val) at hab
      rw [Sym2.eq_iff] at hab ⊢
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have h_img : G.edgeFinset.filter (fun e => ¬ v ∈ e) =
        ((G.induce {x | x ≠ v}).edgeFinset).image f := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · intro ⟨he, hv⟩
        revert he hv
        refine Sym2.inductionOn e (fun x y he hv => ?_)
        have hx : x ≠ v := by
          intro h
          apply hv
          rw [Sym2.mem_iff]
          exact Or.inl h.symm
        have hy : y ≠ v := by
          intro h
          apply hv
          rw [Sym2.mem_iff]
          exact Or.inr h.symm
        refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, rfl⟩
        rw [SimpleGraph.mem_edgeFinset] at he ⊢
        exact he
      · rintro ⟨e', he', rfl⟩
        revert he'
        refine Sym2.inductionOn e' (fun ⟨x, hx⟩ ⟨y, hy⟩ he' => ?_)
        rw [SimpleGraph.mem_edgeFinset] at he' ⊢
        refine ⟨he', ?_⟩
        change ¬ v ∈ s(x, y)
        intro h
        rw [Sym2.mem_iff] at h
        rcases h with rfl | rfl
        · exact hx rfl
        · exact hy rfl
    rw [h_img, Finset.card_image_of_injective _ hf_inj]
  rw [h_part, h_inc, h_ind, add_comm]

/-- Jiang (2004) 度数递减归纳步（统一宇宙 u，彻底消除 mismatch） -/
lemma induction_step_deg_le {V : Type u} [Fintype V] [DecidableEq V] {k n : ℕ}
    (hV : Fintype.card V = n + 1) (G : SimpleGraph V) (v : V)
    (hn : 3 * k + 3 ≤ n)
    (hdeg : G.degree v ≤ k + 1)
    (h_avoid : ¬HasCycleWithKIncidentChords k G)
    (hind : ∀ {W : Type u} [Fintype W] [DecidableEq W],
      Fintype.card W = n → ∀ (H : SimpleGraph W), ¬HasCycleWithKIncidentChords k H →
      H.edgeFinset.card ≤ (k + 1) * n - (k + 1) ^ 2) :
    G.edgeFinset.card ≤ (k + 1) * (n + 1) - (k + 1) ^ 2 := by
  have hcard : Fintype.card {x : V // x ≠ v} = n := by
    rw [Fintype.card_subtype_compl, hV]
    simp
  let H := G.induce {x | x ≠ v}
  have hH_avoid : ¬HasCycleWithKIncidentChords k H := avoid_of_induce h_avoid
  have h_ind_bound := hind hcard H hH_avoid
  have h_distrib : (k + 1) * (n + 1) = (k + 1) * n + (k + 1) := by ring
  have h_le_sq : (k + 1) ^ 2 ≤ (k + 1) * n := by
    rw [sq]
    exact Nat.mul_le_mul_left (k + 1) (by omega)
  have h_sub : (k + 1) * (n + 1) - (k + 1) ^ 2 = ((k + 1) * n - (k + 1) ^ 2) + (k + 1) := by
    rw [h_distrib]
    omega
  rw [h_sub]
  have h_deg := card_edgeFinset_eq_add_degree G v
  rw [h_deg]
  exact add_le_add h_ind_bound hdeg

/-!
### 模块二：Jiang (2004) 核心代数二次放缩（已证毕）
-/

lemma jiang_quadratic_bound (k c : ℕ) (n : ℕ) (hn : n = 3 * k + 3) (hc : c ≤ n) :
    c * (n - c) + c * (k + 1) ≤ 2 * ((k + 1) * n - (k + 1) ^ 2) := by
  subst hn
  have hsub1 : c ≤ 3 * k + 3 := hc
  have hsub2 : (k + 1) ^ 2 ≤ (k + 1) * (3 * k + 3) := by
    rw [sq]
    exact Nat.mul_le_mul_left (k + 1) (by omega)
  zify [hsub1, hsub2]
  have h_diff : 2 * (((k : ℤ) + 1) * (3 * (k : ℤ) + 3) - ((k : ℤ) + 1) ^ 2) -
      ((c : ℤ) * (3 * (k : ℤ) + 3 - (c : ℤ)) + (c : ℤ) * ((k : ℤ) + 1)) =
      ((c : ℤ) - (2 * (k : ℤ) + 2)) ^ 2 := by ring
  have h_pos : 0 ≤ 2 * (((k : ℤ) + 1) * (3 * (k : ℤ) + 3) - ((k : ℤ) + 1) ^ 2) -
      ((c : ℤ) * (3 * (k : ℤ) + 3 - (c : ℤ)) + (c : ℤ) * ((k : ℤ) + 1)) := by
    rw [h_diff]
    exact sq_nonneg _
  linarith

/-!
### 模块三：Czipszer 最小度引理与低度数顶点的存在性
-/

lemma czipszer_min_degree {V : Type u} [Fintype V] [DecidableEq V] {k n : ℕ}
    (hV : Fintype.card V = n + 1) (G : SimpleGraph V)
    (hmin : ∀ v, k + 2 ≤ G.degree v) :
    HasCycleWithKIncidentChords k G := by
  sorry

lemma exists_vert_deg_le_of_avoid {V : Type u} [Fintype V] [DecidableEq V] {k n : ℕ}
    (hV : Fintype.card V = n + 1) (G : SimpleGraph V)
    (h_avoid : ¬HasCycleWithKIncidentChords k G) :
    ∃ v : V, G.degree v ≤ k + 1 := by
  by_contra! h
  have hmin : ∀ v, k + 2 ≤ G.degree v := fun v => h v
  exact h_avoid (czipszer_min_degree hV G hmin)

/-!
### 模块四：Bondy 引理与基准步 (n = 3k + 3)
-/

lemma jiang_base_case {k : ℕ} (hk : 1 ≤ k) {V : Type u} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 3 * k + 3) (G : SimpleGraph V)
    (h_avoid : ¬HasCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤ (k + 1) * (3 * k + 3) - (k + 1) ^ 2 := by
  sorry

/-!
### 模块五：主定理总装 (Jiang 2004 Theorem 1 for JSP-000628)
-/

lemma erdos_767_upper_bound_card (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 3 * k + 3 + m)
      (G : SimpleGraph V),
      ¬HasCycleWithKIncidentChords k G →
      G.edgeFinset.card ≤ (k + 1) * (3 * k + 3 + m) - (k + 1) ^ 2 := by
  induction m with
  | zero =>
    intro V _ _ hV G hG
    exact jiang_base_case hk hV G hG
  | succ m ih =>
    intro V _ _ hV G hG
    obtain ⟨v, hv⟩ := exists_vert_deg_le_of_avoid hV G hG
    have hn : 3 * k + 3 ≤ 3 * k + 3 + m := by omega
    exact induction_step_deg_le hV G v hn hv hG (fun hW H hH => ih hW H hH)

/-- Erdős Problem 767 / JSP-000628 终极大定理 -/
theorem erdos_767_upper_bound (k : ℕ) (hk : 1 ≤ k) :
    ∀ (n : ℕ) (hn : 3 * k + 3 ≤ n) (G : SimpleGraph (Fin n)),
      ¬HasCycleWithKIncidentChords k G →
      G.edgeFinset.card ≤ (k + 1) * n - (k + 1) ^ 2 := by
  intro n hn G hG
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact erdos_767_upper_bound_card k hk m (Fintype.card_fin (3 * k + 3 + m)) G hG

#print axioms erdos_767_upper_bound

end

end JSP000628
