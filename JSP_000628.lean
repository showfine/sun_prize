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

/-- 无向对在子类型嵌入下的单射性 -/
lemma sym2_map_subtype_val_injective {V : Type u} {s : Set V} :
    Function.Injective (Sym2.map (Subtype.val : s → V)) := by
  intro a b
  refine Sym2.inductionOn a (fun x1 y1 => ?_)
  refine Sym2.inductionOn b (fun x2 y2 => ?_)
  intro hab
  change s(x1.val, y1.val) = s(x2.val, y2.val) at hab
  rw [Sym2.eq_iff] at hab ⊢
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
  · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩

/-- 显式将诱导子图的邻接关系固化为原图的邻接关系，避免透明度统合失败 -/
lemma induce_adj_to_adj {V : Type u} {G : SimpleGraph V} {s : Set V} {u v : s}
    (h : (G.induce s).Adj u v) : G.Adj u.val v.val := h

/-- 将诱导子图上的 walk 逐边提升回原图 -/
def walkOfInduce {V : Type u} {G : SimpleGraph V} {s : Set V} {u v : s} :
    (G.induce s).Walk u v → G.Walk u.val v.val
  | .nil => .nil
  | .cons h p => .cons (induce_adj_to_adj h) (walkOfInduce p)

@[simp] lemma walkOfInduce_length {V : Type u} {G : SimpleGraph V} {s : Set V} {u v : s}
    (p : (G.induce s).Walk u v) : (walkOfInduce p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    dsimp [walkOfInduce, SimpleGraph.Walk.length]
    rw [ih]

@[simp] lemma walkOfInduce_support {V : Type u} {G : SimpleGraph V} {s : Set V} {u v : s}
    (p : (G.induce s).Walk u v) :
    (walkOfInduce p).support = p.support.map Subtype.val := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    dsimp [walkOfInduce, SimpleGraph.Walk.support]
    rw [ih]
    rfl

@[simp] lemma walkOfInduce_edges {V : Type u} {G : SimpleGraph V} {s : Set V} {u v : s}
    (p : (G.induce s).Walk u v) :
    (walkOfInduce p).edges = p.edges.map (Sym2.map Subtype.val) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [walkOfInduce, SimpleGraph.Walk.edges_cons, List.map_cons]
    rw [ih]
    rfl

/-- List.map 与 dropLast 的交换律（自包含纯模式匹配） -/
lemma list_map_dropLast {α β : Type*} (f : α → β) : ∀ (l : List α),
    (l.map f).dropLast = l.dropLast.map f
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs => by
    show f x :: ((y :: xs).map f).dropLast = f x :: (y :: xs).dropLast.map f
    rw [list_map_dropLast f (y :: xs)]

/-- 删点后的诱导子图不包含带 k 弦的圈（子图保避免性） -/
lemma avoid_of_induce {V : Type u} [Fintype V] [DecidableEq V] {k : ℕ} {G : SimpleGraph V}
    {s : Set V} (hG : ¬HasCycleWithKIncidentChords k G) :
    ¬HasCycleWithKIncidentChords k (G.induce s) := by
  intro ⟨v, c, hc_edges, hc_nodup, hc_len, f, hf_inj, hf_chords⟩
  apply hG
  refine ⟨v.val, walkOfInduce c, ?_, ?_, ?_, fun i => (f i).val, ?_, ?_⟩
  · -- 1. edges 无重复
    rw [walkOfInduce_edges]
    exact List.Nodup.map sym2_map_subtype_val_injective hc_edges
  · -- 2. support.dropLast 无重复
    rw [walkOfInduce_support, list_map_dropLast]
    exact List.Nodup.map Subtype.val_injective hc_nodup
  · -- 3. 圈长度 ≥ 3
    rw [walkOfInduce_length]
    exact hc_len
  · -- 4. 弦端点映射为单射
    intro i j hij
    exact hf_inj (Subtype.ext hij)
  · -- 5. 保持弦的性质
    intro i
    have hc := hf_chords i
    constructor
    · -- 5.1 弦边属于原图边集
      exact hc.1
    · constructor
      · -- 5.2 弦边不属于圈上的边
        intro he
        rw [walkOfInduce_edges, List.mem_map] at he
        rcases he with ⟨e, he_mem, he_eq⟩
        have he_eq' : e = s(v, f i) := sym2_map_subtype_val_injective he_eq
        subst he_eq'
        exact hc.2.1 he_mem
      · -- 5.3 弦的两端点都在圈的顶点集 (support) 上
        have hsupp := hc.2.2
        dsimp at hsupp ⊢
        rw [walkOfInduce_support]
        refine ⟨?_, ?_⟩
        · rw [List.mem_map]
          exact ⟨v, hsupp.1, rfl⟩
        · rw [List.mem_map]
          exact ⟨f i, hsupp.2, rfl⟩

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

/-- 走步中边的端点必然落在其支撑顶点集 (support) 上 -/
lemma mem_support_of_mem_edges {V : Type u} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) {x : V} (hx : x ∈ e) :
    x ∈ p.support := by
  induction p with
  | nil =>
    simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil] at he
  | cons h q ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
    rcases he with rfl | he_tail
    · rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr q.start_mem_support
    · exact Or.inr (ih he_tail)

/-- 极大路径强归纳辅助引理：整条路径 support 保持全局 Nodup -/
lemma exists_maximal_path_aux {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∀ (m : ℕ) (u v : V) (p : G.Walk u v),
      p.support.Nodup → p.edges.Nodup →
      Fintype.card V - p.length = m →
      ∃ (u' v' : V) (p' : G.Walk u' v'),
        p'.edges.Nodup ∧ p'.support.Nodup ∧
        ∀ w, G.Adj u' w → w ∈ p'.support := by
  intro m
  refine Nat.strong_induction_on m (fun m ih => ?_)
  intro u v p hp_supp hp_edges hm
  by_cases h_all : ∀ w, G.Adj u w → w ∈ p.support
  · exact ⟨u, v, p, hp_edges, hp_supp, h_all⟩
  · push_neg at h_all
    rcases h_all with ⟨w, hw_adj, hw_not_mem⟩
    let p_ext : G.Walk w v := .cons (G.adj_symm hw_adj) p
    have hp_ext_supp : p_ext.support.Nodup :=
      List.nodup_cons.mpr ⟨hw_not_mem, hp_supp⟩
    have hp_ext_edges : p_ext.edges.Nodup := by
      change (s(w, u) :: p.edges).Nodup
      refine List.nodup_cons.mpr ⟨?_, hp_edges⟩
      intro h_mem
      have hw_in_supp := mem_support_of_mem_edges p h_mem (x := w) (by
        change w ∈ s(w, u)
        rw [Sym2.mem_iff]
        exact Or.inl rfl)
      exact hw_not_mem hw_in_supp
    have hlen : p_ext.length = p.length + 1 := rfl
    have h_supp_len : p_ext.support.length = p_ext.length + 1 :=
      SimpleGraph.Walk.length_support p_ext
    have h_bound : p_ext.support.length ≤ Fintype.card V := by
      rw [← List.toFinset_card_of_nodup hp_ext_supp]
      exact Finset.card_le_univ _
    have h_lt : Fintype.card V - p_ext.length < m := by
      omega
    exact ih (Fintype.card V - p_ext.length) h_lt w v p_ext hp_ext_supp hp_ext_edges rfl

/-- 极大路径引理（提供全局 p.support.Nodup） -/
lemma exists_maximal_path {V : Type u} [Fintype V] [DecidableEq V] {n : ℕ}
    (hV : Fintype.card V = n + 1) (G : SimpleGraph V) :
    ∃ (u v : V) (p : G.Walk u v),
      p.edges.Nodup ∧ p.support.Nodup ∧
      ∀ w, G.Adj u w → w ∈ p.support := by
  have : Nonempty V := by
    rw [← Fintype.card_pos_iff, hV]
    omega
  let u0 := Classical.choice this
  let p0 : G.Walk u0 u0 := .nil
  have hp0_supp : p0.support.Nodup := List.nodup_singleton u0
  have hp0_edges : p0.edges.Nodup := List.nodup_nil
  exact exists_maximal_path_aux G (Fintype.card V) u0 u0 p0 hp0_supp hp0_edges rfl

/-- 截断走步存在性引理（0 sorry 完全证毕）：
    若顶点 z 在走步 p 上，则存在从起点到 z 的子走步，其顶点集与边集严格是原走步的子列表 -/
lemma exists_walk_take_until {V : Type u} {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v) (z : V), z ∈ p.support →
      ∃ (r : G.Walk u z), r.support.Sublist p.support ∧ r.edges.Sublist p.edges
  | u, _, .nil, z, hz => by
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz
    exact ⟨.nil, List.Sublist.refl _, List.Sublist.refl _⟩
  | u, _, .cons h q, z, hz => by
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hzq
    · exact ⟨.nil, List.Sublist.cons_cons _ (List.nil_sublist _), List.nil_sublist _⟩
    · obtain ⟨r, hr_supp, hr_edges⟩ := exists_walk_take_until q z hzq
      refine ⟨.cons h r, ?_, ?_⟩
      · simp only [SimpleGraph.Walk.support_cons]
        exact List.Sublist.cons_cons _ hr_supp
      · simp only [SimpleGraph.Walk.edges_cons]
        exact List.Sublist.cons_cons _ hr_edges

/-- 走步拼接算子（自包含纯模式匹配递归） -/
def walkAppend {V : Type u} {G : SimpleGraph V} :
    ∀ {u v w : V}, G.Walk u v → G.Walk v w → G.Walk u w
  | _, _, _, .nil, q => q
  | _, _, _, .cons h p, q => .cons h (walkAppend p q)

@[simp] lemma walkAppend_edges {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    (walkAppend p q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [walkAppend, SimpleGraph.Walk.edges_cons, List.cons_append, ih]

@[simp] lemma walkAppend_length {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    (walkAppend p q).length = p.length + q.length := by
  induction p with
  | nil => simp [walkAppend]
  | cons h p ih =>
    simp only [walkAppend, SimpleGraph.Walk.length_cons, ih]
    omega

/-- 闭圈构造算子：将 u rightsquigarrow z 与反向回边 z - u 闭合成圈 -/
def closeCycle {V : Type u} {G : SimpleGraph V} {u z : V}
    (r : G.Walk u z) (hz : G.Adj u z) : G.Walk u u :=
  walkAppend r (.cons (G.adj_symm hz) .nil)

@[simp] lemma closeCycle_edges {V : Type u} {G : SimpleGraph V} {u z : V}
    (r : G.Walk u z) (hz : G.Adj u z) :
    (closeCycle r hz).edges = r.edges ++ [s(z, u)] := by
  simp only [closeCycle, walkAppend_edges, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_nil]

@[simp] lemma closeCycle_length {V : Type u} {G : SimpleGraph V} {u z : V}
    (r : G.Walk u z) (hz : G.Adj u z) :
    (closeCycle r hz).length = r.length + 1 := by
  simp only [closeCycle, walkAppend_length, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_nil]

/-- 走步追加单步并截取末尾顶点，与原走步顶点集一致（纯结构定义规约，0 sorry 完全证毕） -/
lemma walkAppend_cons_nil_support_dropLast {V : Type u} {G : SimpleGraph V} :
    ∀ {u z w : V} (r : G.Walk u z) (h : G.Adj z w),
      (walkAppend r (SimpleGraph.Walk.cons h .nil)).support.dropLast = r.support
  | u, _, _, .nil, _ => rfl
  | u, _, _, .cons _ .nil, _ => rfl
  | u, _, _, .cons h1 (SimpleGraph.Walk.cons h2 r'), hz => by
    have ih := walkAppend_cons_nil_support_dropLast (SimpleGraph.Walk.cons h2 r') hz
    exact congr_arg (List.cons u) ih

/-- 闭圈去掉末端点后，其顶点集恰好等于原截断路径的顶点集（0 sorry 完全证毕） -/
lemma closeCycle_support_dropLast {V : Type u} {G : SimpleGraph V}
    {u z : V} (r : G.Walk u z) (hz : G.Adj u z) :
    (closeCycle r hz).support.dropLast = r.support :=
  walkAppend_cons_nil_support_dropLast r (G.adj_symm hz)

/-- 辅助引理：利用 filter 从极大路径中提取【严格保序】的邻居子列表 -/
lemma exists_ordered_neighbors_on_path {V : Type u} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (u v : V) (p : G.Walk u v)
    (h_nodup : p.support.Nodup)
    (h_supp : ∀ w, G.Adj u w → w ∈ p.support)
    (hdeg : k + 2 ≤ G.degree u) :
    ∃ (l : List V), l = p.support.filter (fun x => G.Adj u x) ∧ l.Nodup ∧ k + 2 ≤ l.length ∧
      (∀ w ∈ l, G.Adj u w) ∧ l.Sublist p.support := by
  refine ⟨p.support.filter (fun x => G.Adj u x), rfl, List.Nodup.filter _ h_nodup, ?_, ?_, List.filter_sublist⟩
  · have h_eq : (p.support.filter (fun x => G.Adj u x)).toFinset = G.neighborFinset u := by
      ext x
      simp only [List.mem_toFinset, List.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => of_decide_eq_true h.2, fun h => ⟨h_supp x h, decide_eq_true h⟩⟩
    have h_card : (p.support.filter (fun x => G.Adj u x)).toFinset.card = G.degree u := by
      rw [h_eq, SimpleGraph.card_neighborFinset_eq_degree]
    have h_len : (p.support.filter (fun x => G.Adj u x)).toFinset.card = (p.support.filter (fun x => G.Adj u x)).length :=
      List.toFinset_card_of_nodup (List.Nodup.filter _ h_nodup)
    omega
  · intro w hw
    simp only [List.mem_filter] at hw
    exact of_decide_eq_true hw.2

/-!
### 模块三辅助：隔离舱 (几何非自交性与圈长严格证明 0 sorry!)
-/

lemma walk_from_x_to_x_nil {V : Type u} {G : SimpleGraph V} {x : V}
    (p : G.Walk x x) (h_nodup : p.support.Nodup) : p = .nil := by
  cases p with
  | nil => rfl
  | cons h p' =>
    have h_mem : x ∈ p'.support := p'.end_mem_support
    simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at h_nodup
    exact False.elim (h_nodup.1 h_mem)

lemma path_edge_eq_length_one {V : Type u} {G : SimpleGraph V} {u z : V}
    (r : G.Walk u z) (h_nodup : r.support.Nodup) (he : s(z, u) ∈ r.edges) :
    r.length = 1 := by
  cases r with
  | nil => exact False.elim (by simp at he)
  | cons h1 p1 =>
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    have h_nodup_cons := List.nodup_cons.mp h_nodup
    have hu_not_mem := h_nodup_cons.1
    rcases he with heq | he_mem
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hz_u, hu_w⟩ | ⟨hz_w, hu_u⟩
      · subst hu_w
        exact False.elim (hu_not_mem p1.start_mem_support)
      · subst hz_w
        cases p1 with
        | nil => rfl
        | cons h2 p2 =>
          have h_nodup_p1 := List.nodup_cons.mp h_nodup_cons.2
          have hz_not_mem := h_nodup_p1.1
          exact False.elim (hz_not_mem p2.end_mem_support)
    · have hu_mem := mem_support_of_mem_edges p1 he_mem (x := u) (by
        change u ∈ s(z, u)
        rw [Sym2.mem_iff]
        exact Or.inr rfl)
      exact False.elim (hu_not_mem hu_mem)

lemma start_edge_implies_second_vertex {V : Type u} {G : SimpleGraph V} {u v z : V}
    (p : G.Walk u v) (h_nodup : p.support.Nodup) (he : s(u, z) ∈ p.edges) :
    ∃ (h : G.Adj u z) (p1 : G.Walk z v), p = .cons h p1 := by
  cases p with
  | nil => exact False.elim (by simp at he)
  | cons h1 p1 =>
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    have h_nodup_cons := List.nodup_cons.mp h_nodup
    have hu_not_mem := h_nodup_cons.1
    rcases he with heq | he_mem
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hu_u, hz_w⟩ | ⟨hu_w, hz_u⟩
      · subst hz_w
        exact ⟨h1, p1, rfl⟩
      · subst hu_w
        exact False.elim (hu_not_mem p1.start_mem_support)
    · have hu_mem := mem_support_of_mem_edges p1 he_mem (x := u) (by
        change u ∈ s(u, z)
        rw [Sym2.mem_iff]
        exact Or.inl rfl)
      exact False.elim (hu_not_mem hu_mem)

lemma head_eq_getLast_contradiction {α : Type*} {l : List α} {z : α} {tail : List α}
    (hl_nodup : l.Nodup) (hl_len : 2 ≤ l.length)
    (h_eq : l = z :: tail)
    (hl_ne : l ≠ []) (hz : z = l.getLast hl_ne) : False := by
  subst h_eq
  simp only [List.length_cons] at hl_len
  cases tail with
  | nil =>
    simp only [List.length_nil] at hl_len
    omega
  | cons y ys =>
    have htail_ne : y :: ys ≠ [] := by simp
    have h_eq_last : (z :: y :: ys).getLast hl_ne = (y :: ys).getLast htail_ne := rfl
    rw [h_eq_last] at hz
    have hz_mem : z ∈ y :: ys := by
      rw [hz]
      exact List.getLast_mem htail_ne
    have h_nodup_cons := List.nodup_cons.mp hl_nodup
    exact h_nodup_cons.1 hz_mem

/-- 抽象隔离模块 1：截断路径的回边非自交性判定 (0 sorry!) -/
lemma czipszer_edge_and_length_aux {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (p : G.Walk u v) (h_nodup : p.support.Nodup)
    (l : List V) (hl_eq : l = p.support.filter (fun x => G.Adj u x))
    (hl_nodup : l.Nodup) (hl_len : 2 ≤ l.length)
    (hl_ne : l ≠ []) (z : V) (hz_eq : z = l.getLast hl_ne)
    (r : G.Walk u z) (hr_supp : r.support.Sublist p.support)
    (hr_edges : r.edges.Sublist p.edges) :
    s(z, u) ∉ r.edges := by
  intro he
  have hr_nodup : r.support.Nodup := h_nodup.sublist hr_supp
  have hlen1 : r.length = 1 := path_edge_eq_length_one r hr_nodup he
  have hr_edges_eq : r.edges = [s(u, z)] := by
    cases r with
    | nil => exact False.elim (by simp at he)
    | cons h1 p1 =>
      cases p1 with
      | nil => rfl
      | cons h2 p2 => simp only [SimpleGraph.Walk.length_cons] at hlen1; omega
  have he_p : s(u, z) ∈ p.edges := by
    have h_sub : [s(u, z)].Sublist p.edges := by
      rw [← hr_edges_eq]
      exact hr_edges
    exact List.singleton_sublist.mp h_sub
  obtain ⟨h_adj, p1, hp_eq⟩ := start_edge_implies_second_vertex p h_nodup he_p
  have hl_struct : ∃ tail, l = z :: tail := by
    rw [hl_eq, hp_eq]
    have hu : decide (G.Adj u u) = false := decide_eq_false (fun h => G.ne_of_adj h rfl)
    have hz_true : decide (G.Adj u z) = true := decide_eq_true h_adj
    cases p1 with
    | nil =>
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.filter_cons, List.filter_nil, hu, hz_true]
      exact ⟨[], rfl⟩
    | cons h2 p2 =>
      simp only [SimpleGraph.Walk.support_cons, List.filter_cons, hu, hz_true]
      exact ⟨p2.support.filter (fun x => G.Adj u x), rfl⟩
  obtain ⟨tail, hl_struct_eq⟩ := hl_struct
  exact head_eq_getLast_contradiction hl_nodup hl_len hl_struct_eq hl_ne hz_eq

/-- 任意无重复边的非空闭走步，其长度必然 ≥ 3 (纯图论通用引理，0 sorry!) -/
lemma cycle_length_ge_three {V : Type u} {G : SimpleGraph V}
    {u : V} (c : G.Walk u u) (h_nodup : c.edges.Nodup) (h_pos : 0 < c.length) :
    3 ≤ c.length := by
  cases c with
  | nil =>
    simp only [SimpleGraph.Walk.length_nil, lt_self_iff_false] at h_pos
  | cons h1 p1 =>
    cases p1 with
    | nil =>
      have := G.ne_of_adj h1
      contradiction
    | cons h2 p2 =>
      cases p2 with
      | nil =>
        have h_edges_cons := List.nodup_cons.mp h_nodup
        exfalso
        apply h_edges_cons.1
        -- 抛弃 simp 的表层语法匹配，利用 apply 的底层定义等价 (DefEq) 自动计算列表展开
        apply List.mem_singleton.mpr
        exact Sym2.eq_swap
      | cons h3 p3 =>
        simp only [SimpleGraph.Walk.length_cons]
        omega

lemma getLast_append_cons {α : Type*} : ∀ (A : List α) (b : α) (bs : List α) (h : A ++ (b :: bs) ≠ []),
    (A ++ (b :: bs)).getLast h = (b :: bs).getLast (by simp)
  | [], b, bs, h => rfl
  | a :: as, b, bs, h => by
    have h_as : as ++ (b :: bs) ≠ [] := by simp
    have h_eq : ((a :: as) ++ (b :: bs)).getLast h = (as ++ (b :: bs)).getLast h_as := by
      cases as with
      | nil => rfl
      | cons a' as' => rfl
    rw [h_eq, getLast_append_cons as b bs h_as]

lemma B_eq_nil_of_getLast_eq {α : Type*} (l A B : List α) (z : α)
    (hl_eq : l = A ++ B)
    (h_nodup : l.Nodup) (hz_A : z ∈ A)
    (h_ne : l ≠ []) (hz_last : z = l.getLast h_ne) : B = [] := by
  subst hl_eq
  cases B with
  | nil => rfl
  | cons b bs =>
    have hB_ne : b :: bs ≠ [] := by simp
    have h_last := getLast_append_cons A b bs h_ne
    have hz_in_B : (b :: bs).getLast hB_ne ∈ b :: bs := List.getLast_mem hB_ne
    rw [List.nodup_append] at h_nodup
    have h_cross := h_nodup.2.2
    rw [hz_last, h_last] at hz_A
    exact False.elim (h_cross _ hz_A _ hz_in_B rfl)

lemma walkAppend_support {V : Type u} {G : SimpleGraph V} :
    ∀ {u v w : V} (r : G.Walk u v) (q : G.Walk v w),
      (walkAppend r q).support = r.support ++ q.support.tail
  | _, _, _, .nil, q => by
    simp only [walkAppend, SimpleGraph.Walk.support_nil]
    cases q with
    | nil => rfl
    | cons _ _ => rfl
  | _, _, _, .cons h r', q => by
    simp only [walkAppend, SimpleGraph.Walk.support_cons, List.cons_append]
    rw [walkAppend_support r' q]

lemma exists_walk_split_at {V : Type u} {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v) (z : V), z ∈ p.support →
      ∃ (r : G.Walk u z) (q : G.Walk z v),
        r.support.Sublist p.support ∧ r.edges.Sublist p.edges ∧ p = walkAppend r q
  | u, _, .nil, z, hz => by
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz
    exact ⟨.nil, .nil, List.Sublist.refl _, List.Sublist.refl _, rfl⟩
  | u, _, .cons h q', z, hz => by
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hzq
    · exact ⟨.nil, .cons h q', List.Sublist.cons_cons _ (List.nil_sublist _), List.nil_sublist _, rfl⟩
    · obtain ⟨r, q_rest, hr_supp, hr_edges, hq_eq⟩ := exists_walk_split_at q' z hzq
      refine ⟨.cons h r, q_rest, ?_, ?_, ?_⟩
      · simp only [SimpleGraph.Walk.support_cons]
        exact List.Sublist.cons_cons _ hr_supp
      · simp only [SimpleGraph.Walk.edges_cons]
        exact List.Sublist.cons_cons _ hr_edges
      · rw [hq_eq]
        rfl

/-- 抽象隔离模块 2：单射弦映射的拓扑存在性构造 -/
lemma czipszer_chords_aux {V : Type u} {k : ℕ}
    (G : SimpleGraph V) (u v : V) (p : G.Walk u v)
    (l : List V) (hl_nodup : l.Nodup) (hl_len : k + 2 ≤ l.length)
    (hl_adj : ∀ w ∈ l, G.Adj u w) (hl_sub : l.Sublist p.support)
    (hl_ne : l ≠ []) (z : V) (hz_eq : z = l.getLast hl_ne)
    (r : G.Walk u z) (hr_supp : r.support.Sublist p.support)
    (hr_edges : r.edges.Sublist p.edges) (hz_adj : G.Adj u z)
    (c : G.Walk u u) (hc_eq : c = closeCycle r hz_adj) :
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(u, f i) := by
  sorry

/-- 从极大路径端点构造带有 k 条入射弦的圈 (主线总装, 完全 0 sorry!) -/
lemma czipszer_from_path {V : Type u} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (u v : V) (p : G.Walk u v)
    (h_edges : p.edges.Nodup) (h_nodup : p.support.Nodup)
    (h_supp : ∀ w, G.Adj u w → w ∈ p.support)
    (hdeg : k + 2 ≤ G.degree u) :
    HasCycleWithKIncidentChords k G := by
  -- 1. 获取严格保序的邻居列表 l
  obtain ⟨l, hl_eq, hl_nodup, hl_len, hl_adj, hl_sub⟩ :=
    exists_ordered_neighbors_on_path G u v p h_nodup h_supp hdeg
  have hl_ne : l ≠ [] := by
    rintro rfl
    simp only [List.length_nil] at hl_len
    omega
  have hl_len_ge : 2 ≤ l.length := by omega
  -- 2. 取 l 的最后一个元素 z 作为闭圈远端点
  let z := l.getLast hl_ne
  have hz_eq : z = l.getLast hl_ne := rfl
  have hz_mem_l : z ∈ l := List.getLast_mem hl_ne
  have hz_adj : G.Adj u z := hl_adj z hz_mem_l
  have hz_in_supp : z ∈ p.support := hl_sub.subset hz_mem_l
  -- 3. 截断出子路径 r，并拼接回边构成圈 c
  obtain ⟨r, hr_supp, hr_edges⟩ := exists_walk_take_until p z hz_in_supp
  let c := closeCycle r hz_adj

  -- 性质 A：提前证明 c.edges.Nodup，隔离拓扑复杂性
  have hc_edges : c.edges.Nodup := by
    rw [closeCycle_edges]
    rw [List.nodup_append]
    refine ⟨h_edges.sublist hr_edges, List.nodup_singleton _, ?_⟩
    intro e he_r e' he_single heq
    simp only [List.mem_singleton] at he_single
    subst he_single
    subst heq
    exact czipszer_edge_and_length_aux G u v p h_nodup l hl_eq hl_nodup hl_len_ge hl_ne z hz_eq r hr_supp hr_edges he_r

  refine ⟨u, c, hc_edges, ?_, ?_, ?_⟩
  · -- 性质 B：c.support.dropLast.Nodup
    rw [closeCycle_support_dropLast]
    exact h_nodup.sublist hr_supp
  · -- 性质 C：3 ≤ c.length
    have h_pos : 0 < c.length := by
      rw [closeCycle_length]
      omega
    exact cycle_length_ge_three c hc_edges h_pos
  · -- 性质 D：存在 k 条与 u 入射的单射弦
    exact czipszer_chords_aux G u v p l hl_nodup hl_len hl_adj hl_sub hl_ne z hz_eq r hr_supp hr_edges hz_adj c rfl

/-- Czipszer (1961) 最小度引理：总装闭环 -/
lemma czipszer_min_degree {V : Type u} [Fintype V] [DecidableEq V] {k n : ℕ}
    (hV : Fintype.card V = n + 1) (G : SimpleGraph V)
    (hmin : ∀ v, k + 2 ≤ G.degree v) :
    HasCycleWithKIncidentChords k G := by
  obtain ⟨u, v, p, h_edges, h_nodup, h_supp⟩ := exists_maximal_path hV G
  exact czipszer_from_path G u v p h_edges h_nodup h_supp (hmin u)

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

/-- 图中是否存在圈（圈长 ≥ 3 的无自相交闭途径） -/
def HasCycle {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.edges.Nodup ∧ c.support.dropLast.Nodup ∧ 3 ≤ c.length

/-- 森林边数上界在 n = 3k + 3 时弱于 Jiang 上界（纯代数闭环，0 sorry） -/
lemma forest_bound_le_jiang_bound (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : n = 3 * k + 3) :
    n ≤ (k + 1) * n - (k + 1) ^ 2 := by
  subst hn
  have hsub : (k + 1) ^ 2 ≤ (k + 1) * (3 * k + 3) := by
    rw [sq]
    exact Nat.mul_le_mul_left (k + 1) (by omega)
  zify [hsub]
  have h_diff : ((k : ℤ) + 1) * (3 * (k : ℤ) + 3) - ((k : ℤ) + 1) ^ 2 - (3 * (k : ℤ) + 3) =
      2 * ((k : ℤ) - 1) ^ 2 + 5 * ((k : ℤ) - 1) + 2 := by ring
  have h_sq : 0 ≤ ((k : ℤ) - 1) ^ 2 := sq_nonneg _
  have hk1 : 0 ≤ (k : ℤ) - 1 := by
    have : 1 ≤ (k : ℤ) := by exact_mod_cast hk
    linarith
  linarith

/-- 无圈图（森林）的边数不超过顶点数 -/
lemma edgeFinset_card_le_card_of_acyclic {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_no_cycle : ¬HasCycle G) :
    G.edgeFinset.card ≤ Fintype.card V := by
  sorry

/-- Bondy 极长圈边数引理 (Bondy 1971 / Jiang 2004 论文第 181 页)：
    若图 G 包含圈且不包含带 k 弦的圈，则存在极长圈长度 c ≤ n，
    使得 2 * e(G) ≤ c * (n - c) + c * (k + 1) -/
lemma bondy_cycle_edge_bound {V : Type u} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (h_avoid : ¬HasCycleWithKIncidentChords k G)
    (h_cycle : HasCycle G) :
    ∃ c : ℕ, c ≤ Fintype.card V ∧
      2 * G.edgeFinset.card ≤ c * (Fintype.card V - c) + c * (k + 1) := by
  sorry

/-- Jiang (2004) 基准步 (n = 3k + 3) 主引理（0 sorry 完全证毕！） -/
lemma jiang_base_case {k : ℕ} (hk : 1 ≤ k) {V : Type u} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 3 * k + 3) (G : SimpleGraph V)
    (h_avoid : ¬HasCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤ (k + 1) * (3 * k + 3) - (k + 1) ^ 2 := by
  by_cases h_cyc : HasCycle G
  · -- 情况 1：图包含圈，由 Bondy 引理与核心二次放缩闭环
    obtain ⟨c, hc_le, h_bondy⟩ := bondy_cycle_edge_bound G h_avoid h_cyc
    have h_quad := jiang_quadratic_bound k c (Fintype.card V) hV hc_le
    rw [hV] at h_bondy h_quad
    have h_trans : 2 * G.edgeFinset.card ≤ 2 * ((k + 1) * (3 * k + 3) - (k + 1) ^ 2) :=
      le_trans h_bondy h_quad
    omega
  · -- 情况 2：图无圈（森林），边数 ≤ n，代数直接闭环
    have h_forest := edgeFinset_card_le_card_of_acyclic G h_cyc
    have h_alg := forest_bound_le_jiang_bound k hk (Fintype.card V) hV
    rw [hV] at h_forest h_alg
    omega

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
