import Mathlib

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace JSP000628

namespace JiangBaseCase

universe u

-- BEGIN Linkage
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!
# Vertex 2-connectivity and cycle-linkage bookkeeping for Erdős Problem 58

This file deliberately keeps the usual deletion definition of vertex
2-connectivity separate from the conclusion of the two-path form of Menger's
theorem.  `TwoLinkage` is the finite certificate delivered by that theorem.

The last section contains the length and parity calculation used when two
vertex-disjoint cycles are joined by a `TwoLinkage`: of the parallel and
crossed pairings, exactly one consists of odd closed walks, and the sum of the
two lengths in either pairing is the sum of the old cycle lengths plus twice
the total length of the linking paths.
-/

namespace Erdos58

open SimpleGraph


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- The standard finite-graph definition of vertex 2-connectivity: there are
at least three vertices, the graph is connected, and deleting any one vertex
leaves a connected graph. -/
def TwoConnected (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧
    ∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected

namespace TwoConnected

omit [DecidableEq V] in
theorem card_three_le (hG : TwoConnected G) : 3 ≤ Fintype.card V := hG.1

omit [DecidableEq V] in
theorem connected (hG : TwoConnected G) : G.Connected := hG.2.1

omit [DecidableEq V] in
theorem delete_connected (hG : TwoConnected G) (v : V) :
    (G.induce ({v}ᶜ : Set V)).Connected :=
  hG.2.2 v

omit [DecidableEq V] in
theorem nontrivial (hG : TwoConnected G) : Nontrivial V := by
  classical
  exact Fintype.one_lt_card_iff_nontrivial.mp (by
    have h := hG.card_three_le
    omega)

omit [DecidableEq V] in
theorem exists_ne (hG : TwoConnected G) (v : V) : ∃ w : V, w ≠ v := by
  classical
  let := hG.nontrivial
  exact _root_.exists_ne v

omit [DecidableEq V] in
theorem exists_two_ne (hG : TwoConnected G) (v : V) :
    ∃ x y : V, x ≠ v ∧ y ≠ v ∧ x ≠ y := by
  classical
  have hcard : 2 ≤ Fintype.card ({v}ᶜ : Set V) := by
    rw [Fintype.card_compl_set, Set.card_singleton]
    have h := hG.card_three_le
    omega
  let : Nontrivial ({v}ᶜ : Set V) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ({v}ᶜ : Set V)
  have hx : (x : V) ≠ v := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
  have hy : (y : V) ≠ v := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.2
  exact ⟨x, y, hx, hy, fun h ↦ hxy (Subtype.ext h)⟩

omit [DecidableEq V] in
/-- In a 2-connected graph, any two vertices other than `z` can be joined by
a simple path avoiding `z`.  This is the direct path-level content of the
connectivity of `G - z`. -/
theorem exists_path_avoiding (hG : TwoConnected G) (z : V) {x y : V}
    (hx : x ≠ z) (hy : y ≠ z) :
    ∃ p : G.Walk x y, p.IsPath ∧ z ∉ p.support := by
  classical
  let x' : ({z}ᶜ : Set V) := ⟨x, hx⟩
  let y' : ({z}ᶜ : Set V) := ⟨y, hy⟩
  obtain ⟨p, hp⟩ := (hG.delete_connected z).exists_isPath x' y'
  let e : G.induce ({z}ᶜ : Set V) ↪g G :=
    SimpleGraph.Embedding.induce ({z}ᶜ : Set V)
  let q := p.map e.toHom
  have hqpath : q.IsPath := hp.map e.injective
  have hqavoid : z ∉ q.support := by
    intro hz
    have hsupport : q.support = p.support.map e := by
      exact SimpleGraph.Walk.support_map e.toHom p
    rw [hsupport, List.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have hwne : (w : V) ≠ z := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using w.2
    exact hwne hwz
  have hex : e x' = x := by rfl
  have hey : e y' = y := by rfl
  let q' : G.Walk x y := q.copy hex hey
  have hq'path : q'.IsPath :=
    (SimpleGraph.Walk.isPath_copy q hex hey).2 hqpath
  have hq'avoid : z ∉ q'.support := by
    simpa only [q', SimpleGraph.Walk.support_copy] using hqavoid
  exact ⟨q', hq'path, hq'avoid⟩

omit [DecidableEq V] in
/-- Any two distinct neighbors of a vertex in a 2-connected graph lie with
that vertex on a simple cycle.  This is a useful rigorously proved special
linkage consequence which needs only one application of
`exists_path_avoiding`, rather than the full two-set Menger theorem. -/
theorem exists_cycle_through_two_neighbors (hG : TwoConnected G)
    {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z) :
    ∃ c : G.Walk x x, c.IsCycle := by
  classical
  obtain ⟨p, hp, hpx⟩ :=
    hG.exists_path_avoiding x hxy.ne.symm hxz.ne.symm
  let q : G.Walk y x := p.concat hxz.symm
  have hq : q.IsPath := hp.concat hpx hxz.symm
  have hedge : s(x, y) ∉ q.edges := by
    intro hedge
    have hedge' : s(y, x) ∈ q.edges := by
      simpa only [Sym2.eq_swap] using hedge
    have hlen : q.length = 1 := hq.length_eq_one_of_mem_edges hedge'
    have hplen : p.length = 0 := by
      have hq_length : q.length = p.length + 1 := by simp [q]
      omega
    exact hyz (p.eq_of_length_eq_zero hplen)
  exact ⟨Walk.cons hxy q, (Walk.cons_isCycle_iff q hxy).2 ⟨hq, hedge⟩⟩

end TwoConnected

/-! ## Two-linkage certificates -/

/-- A certificate consisting of two fully vertex-disjoint paths from `A` to
`B`.  Disjointness of their complete supports implies, in particular, that
the two endpoints in `A` are distinct and the two endpoints in `B` are
distinct.  The `interior` fields record the usual truncation convention in
the set form of Menger's theorem. -/
structure TwoLinkage (G : SimpleGraph V) (A B : Set V) where
  a₁ : V
  a₂ : V
  b₁ : V
  b₂ : V
  p : G.Walk a₁ b₁
  q : G.Walk a₂ b₂
  p_isPath : p.IsPath
  q_isPath : q.IsPath
  a₁_mem : a₁ ∈ A
  a₂_mem : a₂ ∈ A
  b₁_mem : b₁ ∈ B
  b₂_mem : b₂ ∈ B
  disjoint_support : p.support.Disjoint q.support
  p_interior : ∀ x ∈ p.support.tail.dropLast, x ∉ A ∪ B
  q_interior : ∀ x ∈ q.support.tail.dropLast, x ∉ A ∪ B

namespace TwoLinkage

variable {A B : Set V}

omit [DecidableEq V] [Fintype V] in
theorem a_ne (L : TwoLinkage G A B) : L.a₁ ≠ L.a₂ := by
  intro h
  exact L.disjoint_support L.p.start_mem_support (h.symm ▸ L.q.start_mem_support)

omit [DecidableEq V] [Fintype V] in
theorem b_ne (L : TwoLinkage G A B) : L.b₁ ≠ L.b₂ := by
  intro h
  exact L.disjoint_support L.p.end_mem_support (h.symm ▸ L.q.end_mem_support)

omit [DecidableEq V] [Fintype V] in
theorem p_nonempty (L : TwoLinkage G A B) (hAB : Disjoint A B) : 0 < L.p.length := by
  by_contra h
  have hp0 : L.p.length = 0 := by omega
  have hab : L.a₁ = L.b₁ := L.p.eq_of_length_eq_zero hp0
  exact Set.disjoint_left.1 hAB L.a₁_mem (hab.symm ▸ L.b₁_mem)

omit [DecidableEq V] [Fintype V] in
theorem q_nonempty (L : TwoLinkage G A B) (hAB : Disjoint A B) : 0 < L.q.length := by
  by_contra h
  have hq0 : L.q.length = 0 := by omega
  have hab : L.a₂ = L.b₂ := L.q.eq_of_length_eq_zero hq0
  exact Set.disjoint_left.1 hAB L.a₂_mem (hab.symm ▸ L.b₂_mem)

omit [DecidableEq V] [Fintype V] in
theorem total_length_pos [Finite V] (L : TwoLinkage G A B) (hAB : Disjoint A B) :
    0 < L.p.length + L.q.length := by
  classical
  let := Fintype.ofFinite V
  have hp := L.p_nonempty hAB
  omega

end TwoLinkage

/-! ## The four closed walks obtained by splicing two cycles -/

/-- Data needed for the purely formal splicing calculation.  The walks `c₁`
and `c₂` are the complementary `a₁`--`a₂` arcs of the first cycle; `d₁` and
`d₂` are the complementary `b₁`--`b₂` arcs of the second.  They are stored
with a common orientation so that reversing them closes the linking paths. -/
structure SpliceData (G : SimpleGraph V) where
  a₁ : V
  a₂ : V
  b₁ : V
  b₂ : V
  p : G.Walk a₁ b₁
  q : G.Walk a₂ b₂
  c₁ : G.Walk a₁ a₂
  c₂ : G.Walk a₁ a₂
  d₁ : G.Walk b₁ b₂
  d₂ : G.Walk b₁ b₂

namespace SpliceData

/-- Close `p` using a second linking path and one arc from each old cycle. -/
def close {a₁ a₂ b₁ b₂ : V} (p : G.Walk a₁ b₁) (d : G.Walk b₁ b₂)
    (q : G.Walk a₂ b₂) (c : G.Walk a₁ a₂) : G.Walk a₁ a₁ :=
  ((p.append d).append q.reverse).append c.reverse

variable (S : SpliceData G)

def parallel₁ : G.Walk S.a₁ S.a₁ := close S.p S.d₁ S.q S.c₁
def parallel₂ : G.Walk S.a₁ S.a₁ := close S.p S.d₂ S.q S.c₂
def crossed₁ : G.Walk S.a₁ S.a₁ := close S.p S.d₂ S.q S.c₁
def crossed₂ : G.Walk S.a₁ S.a₁ := close S.p S.d₁ S.q S.c₂

/-- The remaining geometric obligation after the length/parity calculation:
the four closed walks produced by the two arc pairings are simple cycles. -/
def SplicesAreCycles : Prop :=
  S.parallel₁.IsCycle ∧ S.parallel₂.IsCycle ∧
    S.crossed₁.IsCycle ∧ S.crossed₂.IsCycle

omit [DecidableEq V] [Fintype V] in
@[simp] theorem length_close {a₁ a₂ b₁ b₂ : V}
    (p : G.Walk a₁ b₁) (d : G.Walk b₁ b₂)
    (q : G.Walk a₂ b₂) (c : G.Walk a₁ a₂) :
    (close p d q c).length = p.length + d.length + q.length + c.length := by
  simp [close]

omit [DecidableEq V] [Fintype V] in
@[simp] theorem length_parallel₁ [Finite V] :
    S.parallel₁.length = S.p.length + S.d₁.length + S.q.length + S.c₁.length := by
  classical
  let := Fintype.ofFinite V
  simp [parallel₁]

omit [DecidableEq V] [Fintype V] in
@[simp] theorem length_parallel₂ [Finite V] :
    S.parallel₂.length = S.p.length + S.d₂.length + S.q.length + S.c₂.length := by
  classical
  let := Fintype.ofFinite V
  simp [parallel₂]

omit [DecidableEq V] [Fintype V] in
@[simp] theorem length_crossed₁ [Finite V] :
    S.crossed₁.length = S.p.length + S.d₂.length + S.q.length + S.c₁.length := by
  classical
  let := Fintype.ofFinite V
  simp [crossed₁]

omit [DecidableEq V] [Fintype V] in
@[simp] theorem length_crossed₂ [Finite V] :
    S.crossed₂.length = S.p.length + S.d₁.length + S.q.length + S.c₂.length := by
  classical
  let := Fintype.ofFinite V
  simp [crossed₂]

omit [DecidableEq V] [Fintype V] in
/-- The sum of the two parallel splices. -/
theorem parallel_sum [Finite V] {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen) :
    S.parallel₁.length + S.parallel₂.length =
      cLen + dLen + 2 * (S.p.length + S.q.length) := by
  classical
  let := Fintype.ofFinite V
  simp only [length_parallel₁, length_parallel₂]
  omega

omit [DecidableEq V] [Fintype V] in
/-- The crossed pairing has the same total length as the parallel pairing. -/
theorem crossed_sum [Finite V] {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen) :
    S.crossed₁.length + S.crossed₂.length =
      cLen + dLen + 2 * (S.p.length + S.q.length) := by
  classical
  let := Fintype.ofFinite V
  simp only [length_crossed₁, length_crossed₂]
  omega

omit [DecidableEq V] [Fintype V] in
/-- If the two old cycles are odd, the two members of each pairing have the
same parity. -/
theorem parallel_same_parity [Finite V]
    (hc : Odd (S.c₁.length + S.c₂.length))
    (hd : Odd (S.d₁.length + S.d₂.length)) :
    (Odd S.parallel₁.length ↔ Odd S.parallel₂.length) := by
  classical
  let := Fintype.ofFinite V
  simp only [length_parallel₁, length_parallel₂]
  simp only [Nat.odd_iff] at hc hd ⊢
  omega

omit [DecidableEq V] [Fintype V] in
theorem crossed_same_parity [Finite V]
    (hc : Odd (S.c₁.length + S.c₂.length))
    (hd : Odd (S.d₁.length + S.d₂.length)) :
    (Odd S.crossed₁.length ↔ Odd S.crossed₂.length) := by
  classical
  let := Fintype.ofFinite V
  simp only [length_crossed₁, length_crossed₂]
  simp only [Nat.odd_iff] at hc hd ⊢
  omega

omit [DecidableEq V] [Fintype V] in
/-- Exactly one of the parallel and crossed first splices is odd. -/
theorem odd_parallel₁_iff_not_odd_crossed₁ [Finite V]
    (hd : Odd (S.d₁.length + S.d₂.length)) :
    (Odd S.parallel₁.length ↔ ¬ Odd S.crossed₁.length) := by
  classical
  let := Fintype.ofFinite V
  simp only [length_parallel₁, length_crossed₁]
  simp only [Nat.odd_iff] at hd ⊢
  omega

omit [DecidableEq V] [Fintype V] in
/-- Consequently one of the two pairings consists of two odd closed walks. -/
theorem odd_pairing [Finite V]
    (hc : Odd (S.c₁.length + S.c₂.length))
    (hd : Odd (S.d₁.length + S.d₂.length)) :
    (Odd S.parallel₁.length ∧ Odd S.parallel₂.length) ∨
      (Odd S.crossed₁.length ∧ Odd S.crossed₂.length) := by
  classical
  let := Fintype.ofFinite V
  have hp := S.parallel_same_parity hc hd
  have hx := S.crossed_same_parity hc hd
  have hpx := S.odd_parallel₁_iff_not_odd_crossed₁ hd
  by_cases h₁ : Odd S.parallel₁.length
  · exact Or.inl ⟨h₁, hp.mp h₁⟩
  · have h₂ : Odd S.crossed₁.length := by tauto
    exact Or.inr ⟨h₂, hx.mp h₂⟩

omit [DecidableEq V] [Fintype V] in
/-- If the second old cycle is at least as long as the first and the linking
paths have positive total length, then in each pairing at least one new
closed walk is strictly longer than the first old cycle. -/
theorem parallel_one_longer [Finite V] {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen) (hcd : cLen ≤ dLen)
    (hlink : 0 < S.p.length + S.q.length) :
    cLen < S.parallel₁.length ∨ cLen < S.parallel₂.length := by
  classical
  let := Fintype.ofFinite V
  have hsum := S.parallel_sum hc hd
  omega

omit [DecidableEq V] [Fintype V] in
theorem crossed_one_longer [Finite V] {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen) (hcd : cLen ≤ dLen)
    (hlink : 0 < S.p.length + S.q.length) :
    cLen < S.crossed₁.length ∨ cLen < S.crossed₂.length := by
  classical
  let := Fintype.ofFinite V
  have hsum := S.crossed_sum hc hd
  omega

omit [DecidableEq V] [Fintype V] in
/-- The exact conclusion needed in the longest-odd-cycle argument, once the
four spliced closed walks have separately been shown to be simple cycles. -/
theorem exists_odd_longer_splice [Finite V]
    {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen)
    (hcodd : Odd cLen) (hdodd : Odd dLen)
    (hcd : cLen ≤ dLen) (hlink : 0 < S.p.length + S.q.length) :
    (Odd S.parallel₁.length ∧ cLen < S.parallel₁.length) ∨
      (Odd S.parallel₂.length ∧ cLen < S.parallel₂.length) ∨
      (Odd S.crossed₁.length ∧ cLen < S.crossed₁.length) ∨
      (Odd S.crossed₂.length ∧ cLen < S.crossed₂.length) := by
  classical
  let := Fintype.ofFinite V
  have hcp : Odd (S.c₁.length + S.c₂.length) := hc ▸ hcodd
  have hdp : Odd (S.d₁.length + S.d₂.length) := hd ▸ hdodd
  rcases S.odd_pairing hcp hdp with hp | hx
  · rcases S.parallel_one_longer hc hd hcd hlink with h₁ | h₂
    · exact Or.inl ⟨hp.1, h₁⟩
    · exact Or.inr (Or.inl ⟨hp.2, h₂⟩)
  · rcases S.crossed_one_longer hc hd hcd hlink with h₁ | h₂
    · exact Or.inr (Or.inr (Or.inl ⟨hx.1, h₁⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hx.2, h₂⟩))

omit [DecidableEq V] [Fintype V] in
/-- Cycle-valued form of `exists_odd_longer_splice`.  It cleanly separates
the finite support-disjointness argument (`SplicesAreCycles`) from the
universal arithmetic/parity argument proved above. -/
theorem exists_odd_longer_cycle [Finite V]
    {cLen dLen : ℕ}
    (hcycles : S.SplicesAreCycles)
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen)
    (hcodd : Odd cLen) (hdodd : Odd dLen)
    (hcd : cLen ≤ dLen) (hlink : 0 < S.p.length + S.q.length) :
    ∃ c : G.Walk S.a₁ S.a₁,
      c.IsCycle ∧ Odd c.length ∧ cLen < c.length := by
  classical
  let := Fintype.ofFinite V
  rcases S.exists_odd_longer_splice hc hd hcodd hdodd hcd hlink with
    h | h | h | h
  · exact ⟨S.parallel₁, hcycles.1, h.1, h.2⟩
  · exact ⟨S.parallel₂, hcycles.2.1, h.1, h.2⟩
  · exact ⟨S.crossed₁, hcycles.2.2.1, h.1, h.2⟩
  · exact ⟨S.crossed₂, hcycles.2.2.2, h.1, h.2⟩

end SpliceData

end Erdos58
-- END Linkage

-- BEGIN TwoLinkage
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# The finite two-linkage interface

The `TwoLinkage` certificate in `Linkage.lean` uses *fully* vertex-disjoint
paths.  Consequently, two vertices are needed at each end: the often-quoted
version with merely nonempty connected sets is false when one of the sets is
a singleton.  This file records that sharp obstruction.

It also proves the two elementary pieces surrounding the set form of
Menger's theorem which are needed in the Erdős 58 application:

* two-connectivity and the two endpoint-cardinality hypotheses rule out an
  `A`--`B` separator having fewer than two vertices;
* any two fully disjoint `A`--`B` paths can be truncated at their first/last
  visits to the endpoint sets to give the stronger `TwoLinkage` certificate,
  including its interior-avoidance fields.

Mathlib v4.33 does not contain vertex Menger's theorem.  Accordingly the
packing statement is kept as an explicit hypothesis in
`TwoConnected.twoLinkage_of_rawPacking`; the graph-specific separator
condition which finite Menger consumes is proved below without any gap.
-/

namespace Erdos58

open SimpleGraph


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
variable {A B S : Set V}

namespace TwoLinkage

omit [DecidableEq V] [Fintype V] in
/-- Two fully support-disjoint paths force at least two vertices in their
left endpoint set. -/
theorem two_le_ncard_left [Finite V] (L : TwoLinkage G A B) : 2 ≤ A.ncard := by
  classical
  let := Fintype.ofFinite V
  have hsub : ({L.a₁, L.a₂} : Set V) ⊆ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact L.a₁_mem
    · exact L.a₂_mem
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite A)
  rw [Set.ncard_pair L.a_ne] at hcard
  exact hcard

omit [DecidableEq V] [Fintype V] in
/-- Two fully support-disjoint paths force at least two vertices in their
right endpoint set. -/
theorem two_le_ncard_right [Finite V] (L : TwoLinkage G A B) : 2 ≤ B.ncard := by
  classical
  let := Fintype.ofFinite V
  have hsub : ({L.b₁, L.b₂} : Set V) ⊆ B := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact L.b₁_mem
    · exact L.b₂_mem
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite B)
  rw [Set.ncard_pair L.b_ne] at hcard
  exact hcard

omit [DecidableEq V] [Fintype V] in
theorem endpoint_cardinality [Finite V] (L : TwoLinkage G A B) :
    2 ≤ A.ncard ∧ 2 ≤ B.ncard := by
  classical
  let := Fintype.ofFinite V
  exact
  ⟨L.two_le_ncard_left, L.two_le_ncard_right⟩

end TwoLinkage

/-! ## Separators of cardinality at most one -/

/-- `S` meets every walk whose first vertex lies in `A` and last vertex lies
in `B`.  This formulation permits separator vertices in `A` or `B`, as in
the set form of vertex Menger's theorem. -/
def IsABSeparator (G : SimpleGraph V) (A B S : Set V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B →
    ∀ p : G.Walk a b, ∃ x, x ∈ S ∧ x ∈ p.support

namespace TwoConnected

omit [DecidableEq V] in
/-- The exact graph-specific input to finite set-Menger: when both endpoint
sets have at least two vertices, deletion connectivity rules out every
separator of cardinality less than two.  No connectivity hypothesis on the
sets themselves is needed. -/
theorem not_isABSeparator_of_ncard_lt_two
    (hG : TwoConnected G) (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard)
    (hS : S.ncard < 2) : ¬IsABSeparator G A B S := by
  classical
  intro hsep
  have hSle : S.ncard ≤ 1 := by omega
  rcases Set.eq_empty_or_nonempty S with hSempty | ⟨z, hzS⟩
  · let z : V := Classical.choice hG.connected.nonempty
    obtain ⟨a, haA, -⟩ := A.exists_ne_of_one_lt_ncard (by omega) z
    obtain ⟨b, hbB, -⟩ := B.exists_ne_of_one_lt_ncard (by omega) z
    obtain ⟨p, hp⟩ := hG.connected.exists_isPath a b
    obtain ⟨x, hxS, -⟩ := hsep haA hbB p
    simp [hSempty] at hxS
  · have hSsub : S.Subsingleton :=
      (Set.ncard_le_one (Set.toFinite S)).mp hSle
    obtain ⟨a, haA, haz⟩ := A.exists_ne_of_one_lt_ncard (by omega) z
    obtain ⟨b, hbB, hbz⟩ := B.exists_ne_of_one_lt_ncard (by omega) z
    obtain ⟨p, hp, hpz⟩ := hG.exists_path_avoiding z haz hbz
    obtain ⟨x, hxS, hxp⟩ := hsep haA hbB p
    exact hpz (hSsub hxS hzS ▸ hxp)

omit [DecidableEq V] in
theorem no_small_isABSeparator
    (hG : TwoConnected G) (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    ∀ S : Set V, IsABSeparator G A B S → 2 ≤ S.ncard := by
  classical
  intro S hsep
  by_contra h
  exact hG.not_isABSeparator_of_ncard_lt_two hA hB (by omega) hsep

end TwoConnected

/-! ## Truncating a raw path packing -/

/-- Two fully vertex-disjoint paths whose endpoints lie in `A` and `B`, but
whose interiors have not yet been cleaned of later visits to `A ∪ B`. -/
structure RawTwoPathPacking (G : SimpleGraph V) (A B : Set V) where
  a₁ : V
  a₂ : V
  b₁ : V
  b₂ : V
  p : G.Walk a₁ b₁
  q : G.Walk a₂ b₂
  p_isPath : p.IsPath
  q_isPath : q.IsPath
  a₁_mem : a₁ ∈ A
  a₂_mem : a₂ ∈ A
  b₁_mem : b₁ ∈ B
  b₂_mem : b₂ ∈ B
  disjoint_support : p.support.Disjoint q.support

namespace RawTwoPathPacking

/-- The data returned by canonical first/last-hit truncation of one path. -/
structure CleanSubpath {a b : V} (p : G.Walk a b) (A B : Set V) where
  left : V
  right : V
  walk : G.Walk left right
  isPath : walk.IsPath
  left_mem : left ∈ A
  right_mem : right ∈ B
  support_subset : walk.support ⊆ p.support
  interior : ∀ x ∈ walk.support.tail.dropLast, x ∉ A ∪ B

omit [DecidableEq V] [Fintype V] in
/-- A path with endpoints in `A` and `B` has a subpath with the same endpoint
conditions, no internal visit to either endpoint set, and support contained
in the original support.  We first stop at the first `B`-vertex, then reverse
and stop at the first `A`-vertex. -/
private theorem exists_clean_subpath [Finite V]
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (ha : a ∈ A) (hb : b ∈ B) :
    Nonempty (CleanSubpath p A B) := by
  classical
  let := Fintype.ofFinite V
  have hBmeet : {x ∈ B.toFinset | x ∈ p.support}.Nonempty := by
    refine ⟨b, ?_⟩
    simp [hb]
  obtain ⟨b', hb'B, hb'p, hfirstB⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq B.toFinset hBmeet
  let pB : G.Walk a b' := p.takeUntil b' hb'p
  have ha_pB : a ∈ pB.support := pB.start_mem_support
  have hAmeet : {x ∈ A.toFinset | x ∈ pB.reverse.support}.Nonempty := by
    refine ⟨a, ?_⟩
    simp_all
  obtain ⟨a', ha'A, ha'pr, hfirstA⟩ :=
    pB.reverse.exists_mem_support_forall_mem_support_imp_eq A.toFinset hAmeet
  let r₀ : G.Walk b' a' := pB.reverse.takeUntil a' ha'pr
  let r : G.Walk a' b' := r₀.reverse
  have hpB : pB.IsPath := hp.takeUntil hb'p
  have hr₀ : r₀.IsPath := hpB.reverse.takeUntil ha'pr
  have hr : r.IsPath := hr₀.reverse
  have hr₀_sub : r₀.support ⊆ pB.reverse.support :=
    pB.reverse.support_takeUntil_subset_support ha'pr
  have hpB_sub : pB.support ⊆ p.support :=
    p.support_takeUntil_subset_support hb'p
  have hr_sub : r.support ⊆ p.support := by
    intro x hxr
    have hxr₀ : x ∈ r₀.support := by simpa [r] using hxr
    have hxpBr : x ∈ pB.reverse.support := hr₀_sub hxr₀
    have hxpB : x ∈ pB.support := by simpa using hxpBr
    exact hpB_sub hxpB
  refine ⟨{
    left := a'
    right := b'
    walk := r
    isPath := hr
    left_mem := by simpa using ha'A
    right_mem := by simpa using hb'B
    support_subset := hr_sub
    interior := ?_ }⟩
  intro x hxint hxAB
  have htailne : r.support.tail ≠ [] := by
    intro h
    simp [h] at hxint
  have hxdrop : x ∈ r.support.dropLast := by
    rw [← r.cons_tail_support, List.dropLast_cons_of_ne_nil htailne]
    exact List.mem_cons_of_mem _ hxint
  have hxtail : x ∈ r.support.tail := List.mem_of_mem_dropLast hxint
  have hxane : x ≠ a' := by
    have hne := hr.support_nodup.rel_head_tail hxtail
    simpa using hne.symm
  have hxbne : x ≠ b' := by
    have hne := hr.support_nodup.rel_dropLast_getLast hxdrop
    simpa using hne
  have hxr₀ : x ∈ r₀.support := by
    have hxr : x ∈ r.support := List.mem_of_mem_tail hxtail
    simpa [r] using hxr
  rcases hxAB with hxA | hxB
  · have hxa' := hfirstA x (by simpa using hxA) hxr₀
    exact hxane hxa'
  · have hxpBr : x ∈ pB.reverse.support := hr₀_sub hxr₀
    have hxpB : x ∈ pB.support := by simpa using hxpBr
    have hxb' := hfirstB x (by simpa using hxB) hxpB
    exact hxbne hxb'

/-- The canonical cleaned subpath selected from one path. -/
noncomputable def cleanSubpath
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (ha : a ∈ A) (hb : b ∈ B) : CleanSubpath p A B :=
  Classical.choice (exists_clean_subpath p hp ha hb)

/-- Cleaning the interiors of the two raw paths preserves full support
disjointness and yields the repository's downstream `TwoLinkage`
certificate. -/
noncomputable def toTwoLinkage (P : RawTwoPathPacking G A B) :
    TwoLinkage G A B := by
  let P₁ := cleanSubpath P.p P.p_isPath P.a₁_mem P.b₁_mem
  let P₂ := cleanSubpath P.q P.q_isPath P.a₂_mem P.b₂_mem
  exact
    { a₁ := P₁.left
      a₂ := P₂.left
      b₁ := P₁.right
      b₂ := P₂.right
      p := P₁.walk
      q := P₂.walk
      p_isPath := P₁.isPath
      q_isPath := P₂.isPath
      a₁_mem := P₁.left_mem
      a₂_mem := P₂.left_mem
      b₁_mem := P₁.right_mem
      b₂_mem := P₂.right_mem
      disjoint_support := fun x hxp hxq ↦
        P.disjoint_support (P₁.support_subset hxp) (P₂.support_subset hxq)
      p_interior := P₁.interior
      q_interior := P₂.interior }

end RawTwoPathPacking

/-! ## The finite set-Menger interface -/

/-- The cardinal-two instance of finite set-Menger, formulated using the
walk and separator types of this development.  Keeping this proposition
named makes the one theorem absent from Mathlib v4.33 an explicit dependency
of the final existence result. -/
def SatisfiesSetMengerTwo (G : SimpleGraph V) : Prop :=
  ∀ A B : Set V,
    (∀ S : Set V, IsABSeparator G A B S → 2 ≤ S.ncard) →
      Nonempty (RawTwoPathPacking G A B)

namespace TwoConnected

omit [DecidableEq V] in
/-- The post-Menger step: once the finite set form of Menger supplies two
fully support-disjoint `A`--`B` paths, their canonical truncations form a
`TwoLinkage`. -/
theorem twoLinkage_of_rawPacking (_hG : TwoConnected G)
    (P : RawTwoPathPacking G A B) : Nonempty (TwoLinkage G A B) := by
  classical
  exact ⟨P.toTwoLinkage⟩

omit [DecidableEq V] in
/-- Set-Menger plus the checked deletion-connectivity argument gives the
desired linkage.  The endpoint-cardinality assumptions are sharp by
`TwoLinkage.endpoint_cardinality`. -/
theorem twoLinkage_of_setMenger (hG : TwoConnected G)
    (hMenger : SatisfiesSetMengerTwo G)
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    Nonempty (TwoLinkage G A B) := by
  classical
  obtain ⟨P⟩ := hMenger A B (hG.no_small_isABSeparator hA hB)
  exact hG.twoLinkage_of_rawPacking P

omit [DecidableEq V] in
/-- Under finite set-Menger, the two cardinality bounds are not only
sufficient but exactly characterize existence of the full-support-disjoint
linkage certificate. -/
theorem twoLinkage_iff_endpoint_cardinality (hG : TwoConnected G)
    (hMenger : SatisfiesSetMengerTwo G) :
    Nonempty (TwoLinkage G A B) ↔ 2 ≤ A.ncard ∧ 2 ≤ B.ncard := by
  classical
  constructor
  · rintro ⟨L⟩
    exact L.endpoint_cardinality
  · rintro ⟨hA, hB⟩
    exact hG.twoLinkage_of_setMenger hMenger hA hB

end TwoConnected

end Erdos58
-- END TwoLinkage

-- BEGIN Basic
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Erdős Problem 58: cycle-length infrastructure

This file records the elementary interface between odd cycle lengths, cycles
represented by closed walks, and copies of cycle graphs.  It also supplies the
finite-cardinality facts and the exact calculation for complete graphs that
are used in the resolution of Erdős Problem 58.
-/

open Set
open scoped SimpleGraph

namespace Erdos58

noncomputable section

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

/-- The set of odd lengths of (simple) cycles in `G`.

A cycle is represented in Mathlib by a nonempty closed walk whose edges and
all vertices apart from the repeated endpoint are distinct. -/
def oddCycleLengths (G : SimpleGraph V) : Set ℕ :=
  {n | Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

@[simp] lemma mem_oddCycleLengths {n : ℕ} :
    n ∈ oddCycleLengths G ↔
      Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n :=
  Iff.rfl

lemma odd_of_mem_oddCycleLengths {n : ℕ} (hn : n ∈ oddCycleLengths G) : Odd n :=
  hn.1

lemma three_le_of_mem_oddCycleLengths {n : ℕ} (hn : n ∈ oddCycleLengths G) : 3 ≤ n := by
  obtain ⟨_, v, p, hp, rfl⟩ := hn
  exact hp.three_le_length

/-- A number is an odd cycle length precisely when it is odd, is at least
three, and its cycle graph occurs as a (not necessarily induced) copy. -/
lemma mem_oddCycleLengths_iff_odd_and_two_lt_and_cycleGraph_isContained {n : ℕ} :
    n ∈ oddCycleLengths G ↔
      Odd n ∧ 2 < n ∧ SimpleGraph.cycleGraph n ⊑ G := by
  constructor
  · rintro ⟨hn, v, p, hp, rfl⟩
    exact ⟨hn, hp.three_le_length,
      (SimpleGraph.cycleGraph_isContained_iff hp.three_le_length).2 ⟨v, p, hp, rfl⟩⟩
  · rintro ⟨hn, hn3, hcopy⟩
    obtain ⟨v, p, hp, hlen⟩ :=
      (SimpleGraph.cycleGraph_isContained_iff hn3).1 hcopy
    exact ⟨hn, v, p, hp, hlen⟩

lemma mem_oddCycleLengths_iff_cycleGraph_isContained {n : ℕ}
    (hn : 3 ≤ n) :
    n ∈ oddCycleLengths G ↔ Odd n ∧ SimpleGraph.cycleGraph n ⊑ G := by
  rw [mem_oddCycleLengths_iff_odd_and_two_lt_and_cycleGraph_isContained]
  constructor
  · rintro ⟨hodd, -, hcopy⟩
    exact ⟨hodd, hcopy⟩
  · rintro ⟨hodd, hcopy⟩
    exact ⟨hodd, by omega, hcopy⟩

alias mem_oddCycleLengths_iff_cycleGraph_isContained_of_three_le :=
  mem_oddCycleLengths_iff_cycleGraph_isContained

/-- Injective graph homomorphisms preserve every odd cycle length.  The
injectivity assumption is necessary: an arbitrary graph homomorphism can
identify nonadjacent vertices of a cycle. -/
lemma oddCycleLengths_mono_hom (f : G →g H) (hf : Function.Injective f) :
    oddCycleLengths G ⊆ oddCycleLengths H := by
  rintro n ⟨hn, v, p, hp, rfl⟩
  exact ⟨hn, f v, p.map f, hp.map hf, by simp⟩

/-- Copies of graphs preserve every odd cycle length. -/
lemma oddCycleLengths_mono_copy (f : SimpleGraph.Copy G H) :
    oddCycleLengths G ⊆ oddCycleLengths H :=
  oddCycleLengths_mono_hom f.toHom f.injective

/-- Graph containment preserves every odd cycle length. -/
lemma oddCycleLengths_mono_isContained (h : G ⊑ H) :
    oddCycleLengths G ⊆ oddCycleLengths H :=
  oddCycleLengths_mono_copy h.some

/-- Passing to a supergraph on the same vertex type cannot destroy an odd
cycle length. -/
lemma oddCycleLengths_mono (h : G ≤ G') :
    oddCycleLengths G ⊆ oddCycleLengths G' := by
  rintro n ⟨hn, v, p, hp, rfl⟩
  exact ⟨hn, v, p.mapLe h, hp.mapLe h, p.length_mapLe h⟩

/-- Every odd cycle in an induced graph is an odd cycle in the ambient graph. -/
lemma oddCycleLengths_induce_subset (G : SimpleGraph V) (s : Set V) :
    oddCycleLengths (G.induce s) ⊆ oddCycleLengths G :=
  oddCycleLengths_mono_hom (SimpleGraph.Embedding.induce (G := G) s).toHom
    (SimpleGraph.Embedding.induce (G := G) s).injective

/-- The coercion of a subgraph cannot have an odd cycle length absent from
the ambient graph. -/
lemma oddCycleLengths_subgraph_subset (G' : G.Subgraph) :
    oddCycleLengths G'.coe ⊆ oddCycleLengths G :=
  oddCycleLengths_mono_isContained G'.coe_isContained

/-- A cycle in a finite graph has at most as many edges as the graph has
vertices. -/
lemma length_le_natCard_of_isCycle [Finite V] {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) : p.length ≤ Nat.card V := by
  let _ := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card]
  have h := hp.support_nodup.length_le_card
  rw [List.length_tail, p.length_support] at h
  omega

lemma mem_oddCycleLengths_le_natCard [Finite V] {n : ℕ}
    (hn : n ∈ oddCycleLengths G) : n ≤ Nat.card V := by
  obtain ⟨_, v, p, hp, rfl⟩ := hn
  exact length_le_natCard_of_isCycle hp

/-- A finite graph has only finitely many odd cycle lengths. -/
lemma oddCycleLengths_finite [Finite V] (G : SimpleGraph V) :
    (oddCycleLengths G).Finite :=
  (Set.finite_le_nat (Nat.card V)).subset fun _ hn ↦
    mem_oddCycleLengths_le_natCard hn

/-- Odd-cycle-length cardinality is monotone under injective graph
homomorphisms into a finite graph. -/
lemma ncard_oddCycleLengths_mono_hom [Finite W] (f : G →g H)
    (hf : Function.Injective f) :
    (oddCycleLengths G).ncard ≤ (oddCycleLengths H).ncard :=
  Set.ncard_le_ncard (oddCycleLengths_mono_hom f hf) (oddCycleLengths_finite H)

lemma ncard_oddCycleLengths_mono_isContained [Finite W] (h : G ⊑ H) :
    (oddCycleLengths G).ncard ≤ (oddCycleLengths H).ncard :=
  Set.ncard_le_ncard (oddCycleLengths_mono_isContained h) (oddCycleLengths_finite H)

lemma ncard_oddCycleLengths_induce_le [Finite V] (G : SimpleGraph V) (s : Set V) :
    (oddCycleLengths (G.induce s)).ncard ≤ (oddCycleLengths G).ncard :=
  Set.ncard_le_ncard (oddCycleLengths_induce_subset G s) (oddCycleLengths_finite G)

/-- A coarse but convenient cardinal bound on the set of odd cycle lengths. -/
lemma ncard_oddCycleLengths_le_natCard [Finite V] (G : SimpleGraph V) :
    (oddCycleLengths G).ncard ≤ Nat.card V := by
  refine (Set.ncard_le_ncard ?_ (Set.finite_Icc 1 (Nat.card V))).trans ?_
  · intro n hn
    have hn3 := three_le_of_mem_oddCycleLengths hn
    exact ⟨by omega, mem_oddCycleLengths_le_natCard hn⟩
  · rw [Set.ncard_Icc_nat]
    omega

/-- The complete graph on `n` vertices has precisely the odd cycle lengths
between `3` and `n`. -/
theorem oddCycleLengths_completeGraph (n : ℕ) :
    oddCycleLengths (SimpleGraph.completeGraph (Fin n)) =
      {m : ℕ | Odd m ∧ 3 ≤ m ∧ m ≤ n} := by
  ext m
  rw [mem_oddCycleLengths_iff_odd_and_two_lt_and_cycleGraph_isContained]
  simp only [Set.mem_ofPred_eq, SimpleGraph.isContained_top_iff,
    Fin.nonempty_embedding_iff]
  constructor
  · rintro ⟨hodd, hm3, hmn⟩
    exact ⟨hodd, by omega, hmn⟩
  · rintro ⟨hodd, hm3, hmn⟩
    exact ⟨hodd, by omega, hmn⟩

/-- Thus `K_(2k+2)` has exactly the `k` odd cycle lengths
`3, 5, ..., 2k+1`. -/
theorem oddCycleLengths_completeGraph_two_mul_add_two (k : ℕ) :
    oddCycleLengths (SimpleGraph.completeGraph (Fin (2 * k + 2))) =
      Set.range (fun i : Fin k ↦ 2 * (i : ℕ) + 3) := by
  rw [oddCycleLengths_completeGraph]
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨hmodd, hm3, hmle⟩
    obtain ⟨j, rfl⟩ := hmodd
    have hj : j - 1 < k := by omega
    refine ⟨⟨j - 1, hj⟩, ?_⟩
    change 2 * (j - 1) + 3 = 2 * j + 1
    omega
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    refine ⟨⟨(i : ℕ) + 1, by omega⟩, by omega, by omega⟩

/-- Exact complete-graph lower bound used in the equality case of Erdős
Problem 58. -/
@[simp] theorem ncard_oddCycleLengths_completeGraph_two_mul_add_two (k : ℕ) :
    (oddCycleLengths (SimpleGraph.completeGraph (Fin (2 * k + 2)))).ncard = k := by
  rw [oddCycleLengths_completeGraph_two_mul_add_two]
  rw [Set.ncard_range_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    change 2 * (i : ℕ) + 3 = 2 * (j : ℕ) + 3 at hij
    omega

end

end Erdos58
-- END Basic

-- BEGIN CycleArcs
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The definitions `IsArm`, `ArmsDisj`, and the indexed-arc proof below are
adapted from `ListColoring.RubinCases` at commit
80a728c86f28222a58b11a777f9d22419fd2fb69 of
https://github.com/rkirov/list-color-function, released under Apache 2.0.
-/

/-!
# The two complementary arcs of a cycle

This file turns a `SimpleGraph.Walk.IsCycle` and two distinct vertices on it
into its two complementary arcs.  Two interfaces are supplied:

* `exists_arcs_of_cycle` gives explicitly indexed arms, which is convenient
  for length calculations and splicing constructions;
* `exists_path_arcs_of_cycle` gives actual Mathlib walks, proves that both are
  simple paths of positive length, and records support and edge exhaustion.

The construction rotates the cycle to begin at the first endpoint and splits
at the first occurrence of the second endpoint.
-/

open Set
open scoped SimpleGraph

namespace Erdos58

variable {V : Type*} {G : SimpleGraph V}

/-- `IsArm G s t P k` says that `P 0, ..., P k` is a simple path in `G`
from `s` to `t`, of positive length `k`. -/
def IsArm (G : SimpleGraph V) (s t : V) (P : ℕ → V) (k : ℕ) : Prop :=
  1 ≤ k ∧ P 0 = s ∧ P k = t ∧ (∀ j, j < k → G.Adj (P j) (P (j + 1))) ∧
    (∀ j, 0 < j → j < k → P j ≠ s ∧ P j ≠ t) ∧
    (∀ j j', 0 < j → j < k → 0 < j' → j' < k → P j = P j' → j = j')

/-- Two indexed arms are internally vertex-disjoint. -/
def ArmsDisj (P : ℕ → V) (k : ℕ) (Q : ℕ → V) (l : ℕ) : Prop :=
  ∀ j j', 0 < j → j < k → 0 < j' → j' < l → P j ≠ Q j'

/-- Internal disjointness of arms is symmetric. -/
theorem ArmsDisj.symm {P Q : ℕ → V} {k l : ℕ}
    (h : ArmsDisj P k Q l) : ArmsDisj Q l P k :=
  fun j j' hj hjk hj' hj'k e ↦ h j' j hj' hj'k hj hjk e.symm

/-- A path walk, indexed by `Walk.getVert`, is an arm. -/
theorem isArm_of_walk {s t : V} (p : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t) :
    IsArm G s t p.getVert p.length := by
  have hinj := hp.getVert_injOn
  refine ⟨?_, p.getVert_zero, p.getVert_length, fun j hj ↦ p.adj_getVert_succ hj, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos p.length with h | h
    · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h) hst
    · exact h
  · intro j hj0 hjl
    constructor
    · intro he
      have : j = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, p.getVert_zero])
      omega
    · intro he
      have : j = p.length := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, p.getVert_length])
      omega
  · intro j j' _ hjl _ hj'l he
    exact hinj (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) he

/-- Two simple paths that meet only at their common endpoints give internally
disjoint indexed arms. -/
theorem armsDisj_of_walks {s t : V} (p q : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t)
    (h : ∀ x ∈ p.support, x ∈ q.support → x = s ∨ x = t) :
    ArmsDisj p.getVert p.length q.getVert q.length := by
  intro j j' hj0 hjl hj0' hj'l he
  have hmem : p.getVert j ∈ q.support := he ▸ q.getVert_mem_support j'
  rcases h _ (p.getVert_mem_support j) hmem with hs | ht
  · exact (isArm_of_walk p hp hst).2.2.2.2.1 j hj0 hjl |>.1 hs
  · exact (isArm_of_walk p hp hst).2.2.2.2.1 j hj0 hjl |>.2 ht

/-- A step of a walk is one of its edges. -/
theorem getVert_mem_edges {x y : V} (p : G.Walk x y) : ∀ {i : ℕ}, i < p.length →
    s(p.getVert i, p.getVert (i + 1)) ∈ p.edges := by
  induction p with
  | nil => intro i hi; simp at hi
  | @cons u v w h q ih =>
      intro i hi
      cases i with
      | zero => simp
      | succ i =>
          simp only [SimpleGraph.Walk.length_cons] at hi
          simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.edges_cons,
            List.mem_cons]
          exact Or.inr (ih (by omega))

/-- The two indexed arcs of a cycle between two distinct vertices.

The arcs have positive lengths adding to the cycle length, are internally
disjoint simple arms, use only vertices and edges of the cycle, and together
exhaust the cycle support. -/
theorem exists_arcs_of_cycle {v : V} {c : G.Walk v v} (hc : c.IsCycle) {a b : V}
    (ha : a ∈ c.support) (hb : b ∈ c.support) (hab : a ≠ b) :
    ∃ (A B : ℕ → V) (α β : ℕ), 1 ≤ α ∧ 1 ≤ β ∧ α + β = c.length ∧
      IsArm G a b A α ∧ IsArm G a b B β ∧ ArmsDisj A α B β ∧
      (∀ t, t ≤ α → A t ∈ c.support) ∧ (∀ t, t ≤ β → B t ∈ c.support) ∧
      (∀ t, t < α → s(A t, A (t + 1)) ∈ c.edges) ∧
      (∀ t, t < β → s(B t, B (t + 1)) ∈ c.edges) ∧
      (∀ x, x ∈ c.support →
        (∃ t, t ≤ α ∧ A t = x) ∨ (∃ t, t ≤ β ∧ B t = x)) := by
  classical
  set c' : G.Walk a a := c.rotate a ha with hc'def
  have hc' : c'.IsCycle := (SimpleGraph.Walk.isCycle_rotate ha).mpr hc
  have hlen : c'.length = c.length := SimpleGraph.Walk.length_rotate c a ha
  have hmem : ∀ x : V, x ∈ c'.support ↔ x ∈ c.support := fun x ↦
    SimpleGraph.Walk.mem_support_rotate_iff c a ha
  have hedg : ∀ e : Sym2 V, e ∈ c'.edges ↔ e ∈ c.edges := fun _ ↦
    (SimpleGraph.Walk.rotate_edges c a ha).mem_iff
  set L : ℕ := c'.length with hLdef
  have h3 : 3 ≤ L := hc'.three_le_length
  have hinj : Set.InjOn c'.getVert {i | i ≤ L - 1} := hc'.getVert_injOn'
  have h0 : c'.getVert 0 = a := c'.getVert_zero
  have hLa : c'.getVert L = a := c'.getVert_length
  obtain ⟨j, hjget, hjle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ((hmem b).mpr hb)
  have hj0 : j ≠ 0 := by rintro rfl; exact hab (h0.symm.trans hjget)
  have hjL : j ≠ L := by rintro rfl; exact hab (hLa.symm.trans hjget)
  have hjlt : j < L := lt_of_le_of_ne hjle hjL
  have hj1 : 1 ≤ j := by omega
  refine ⟨c'.getVert, fun t ↦ c'.getVert (L - t), j, L - j, hj1, by omega,
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hj1, h0, hjget, fun t ht ↦ c'.adj_getVert_succ (by omega), ?_, ?_⟩
    · intro t ht0 htj
      refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
      · have : t = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, h0])
        omega
      · have : t = j := hinj (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, ← hjget])
        omega
    · intro t t' _ htj _ ht'j he
      exact hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) he
  · refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · change c'.getVert (L - 0) = a
      rw [Nat.sub_zero]
      exact hLa
    · change c'.getVert (L - (L - j)) = b
      rw [show L - (L - j) = j from by omega]
      exact hjget
    · intro t ht
      change G.Adj (c'.getVert (L - t)) (c'.getVert (L - (t + 1)))
      have hstep := c'.adj_getVert_succ (i := L - t - 1) (by omega)
      rw [show L - t - 1 + 1 = L - t from by omega] at hstep
      rw [show L - (t + 1) = L - t - 1 from by omega]
      exact hstep.symm
    · intro t ht0 htb
      change c'.getVert (L - t) ≠ a ∧ c'.getVert (L - t) ≠ b
      refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
      · have : L - t = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, h0])
        omega
      · have : L - t = j := hinj (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, ← hjget])
        omega
    · intro t t' _ htb _ ht'b he
      have he' : c'.getVert (L - t) = c'.getVert (L - t') := he
      have : L - t = L - t' := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) he'
      omega
  · intro t t' ht0 htj ht0' ht'b he
    have he' : c'.getVert t = c'.getVert (L - t') := he
    have : t = L - t' := hinj (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) he'
    omega
  · exact fun t _ ↦ (hmem _).mp (c'.getVert_mem_support t)
  · exact fun t _ ↦ (hmem _).mp (c'.getVert_mem_support (L - t))
  · exact fun t ht ↦ (hedg _).mp (getVert_mem_edges c' (by omega))
  · intro t ht
    change s(c'.getVert (L - t), c'.getVert (L - (t + 1))) ∈ c.edges
    have hstep := getVert_mem_edges c' (i := L - t - 1) (by omega)
    rw [show L - t - 1 + 1 = L - t from by omega] at hstep
    rw [show L - (t + 1) = L - t - 1 from by omega, Sym2.eq_swap]
    exact (hedg _).mp hstep
  · intro x hx
    obtain ⟨n, hn, hnL⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ((hmem x).mpr hx)
    rcases (by omega : n ≤ j ∨ j < n) with h | h
    · exact Or.inl ⟨n, h, hn⟩
    · refine Or.inr ⟨L - n, by omega, ?_⟩
      change c'.getVert (L - (L - n)) = x
      rw [show L - (L - n) = n from by omega]
      exact hn

/-- A walk-level version of the complementary-arc construction.

Both returned walks run from `a` to `b`.  They are nonempty simple paths,
their lengths sum to the cycle length, and their only possible common
vertices are their endpoints.  Their supports together exhaust the original
cycle support, and every arc edge belongs to the original cycle. -/
theorem exists_path_arcs_of_cycle {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    {a b : V} (ha : a ∈ c.support) (hb : b ∈ c.support) (hab : a ≠ b) :
    ∃ (p q : G.Walk a b), p.IsPath ∧ q.IsPath ∧
      1 ≤ p.length ∧ 1 ≤ q.length ∧ p.length + q.length = c.length ∧
      (∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b) ∧
      (∀ x, x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support) ∧
      (∀ e, e ∈ p.edges → e ∈ c.edges) ∧
      (∀ e, e ∈ q.edges → e ∈ c.edges) := by
  classical
  let c' : G.Walk a a := c.rotate a ha
  have hc' : c'.IsCycle := (SimpleGraph.Walk.isCycle_rotate ha).mpr hc
  have hb' : b ∈ c'.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mpr hb
  let p : G.Walk a b := c'.takeUntil b hb'
  let r : G.Walk b a := c'.dropUntil b hb'
  let q : G.Walk a b := r.reverse
  have hdecomp : p.append r = c' := by
    exact c'.take_spec hb'
  have hpPath : p.IsPath := hc'.isPath_takeUntil hb'
  have happCycle : (p.append r).IsCycle := by
    rw [hdecomp]
    exact hc'
  have hrPath : r.IsPath := by
    exact happCycle.isPath_of_append_right (SimpleGraph.Walk.not_nil_of_ne hab)
  have hqPath : q.IsPath := hrPath.reverse
  have hpPos : 1 ≤ p.length := by
    have : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne hab)
    omega
  have hqPos : 1 ≤ q.length := by
    have : 0 < r.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne hab.symm)
    have : 1 ≤ r.length := by omega
    simpa [q] using this
  have hlen : p.length + q.length = c.length := by
    have := congrArg SimpleGraph.Walk.length hdecomp
    simpa [q, c', SimpleGraph.Walk.length_rotate] using this
  have htailNodup : (p.support.tail ++ r.support.tail).Nodup := by
    rw [← SimpleGraph.Walk.tail_support_append]
    rw [hdecomp]
    exact hc'.support_nodup
  have hmeet : ∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b := by
    intro x hxp hxq
    by_contra h
    push Not at h
    have hxpt : x ∈ p.support.tail :=
      (SimpleGraph.Walk.mem_support_iff p).mp hxp |>.resolve_left h.1
    have hxr : x ∈ r.support := by
      simpa [q, SimpleGraph.Walk.support_reverse] using hxq
    have hxrt : x ∈ r.support.tail :=
      (SimpleGraph.Walk.mem_support_iff r).mp hxr |>.resolve_left h.2
    exact (List.disjoint_of_nodup_append htailNodup hxpt hxrt)
  have hsupp : ∀ x, x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support := by
    intro x
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c a ha]
    change x ∈ c'.support ↔ x ∈ p.support ∨ x ∈ q.support
    rw [← hdecomp, SimpleGraph.Walk.mem_support_append_iff]
    simp only [q, SimpleGraph.Walk.support_reverse, List.mem_reverse]
  have hedg : ∀ e : Sym2 V, e ∈ c'.edges ↔ e ∈ c.edges := fun _ ↦
    (SimpleGraph.Walk.rotate_edges c a ha).mem_iff
  have hpEdges : ∀ e, e ∈ p.edges → e ∈ c.edges := by
    intro e he
    apply (hedg e).mp
    exact SimpleGraph.Walk.edges_takeUntil_subset_edges c' hb' he
  have hqEdges : ∀ e, e ∈ q.edges → e ∈ c.edges := by
    intro e he
    apply (hedg e).mp
    apply SimpleGraph.Walk.edges_dropUntil_subset_edges c' hb'
    simpa [q, SimpleGraph.Walk.edges_reverse] using he
  exact ⟨p, q, hpPath, hqPath, hpPos, hqPos, hlen, hmeet, hsupp, hpEdges, hqEdges⟩

end Erdos58
-- END CycleArcs

-- BEGIN Menger
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# The two-path case of vertex Menger for Erdős Problem 58

This file proves the finite `k = 2` consequence of vertex Menger needed in
Gyárfás's proof.  The proof first establishes Whitney's elementary
characterization: in a finite vertex-two-connected graph, every two vertices
belong to a common simple cycle.  It then applies this result after adjoining
two fresh vertices attached to the two endpoint sets.  Removing those fresh
vertices from the two complementary arcs of the resulting cycle gives two
fully vertex-disjoint paths between the endpoint sets.

The endpoint sets must each contain at least two vertices.  This hypothesis is
sharp for the repository's `TwoLinkage`, whose two paths have disjoint *full*
supports.
-/

namespace Erdos58

open SimpleGraph


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Two vertices occur on one genuine simple cycle. -/
def OnCommonCycle (G : SimpleGraph V) (x y : V) : Prop :=
  ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support

/-! ## Adjoining two endpoint vertices -/

/-- Original vertices together with two fresh endpoint vertices.  `false` is
the left endpoint and `true` the right endpoint. -/
abbrev LinkAugment (V : Type u) := Sum V Bool

/-- Add a fresh vertex adjacent precisely to `A` and a second fresh vertex
adjacent precisely to `B`. -/
def linkAugment (G : SimpleGraph V) (A B : Set V) :
    SimpleGraph (LinkAugment V) where
  Adj s t :=
    match s, t with
    | Sum.inl x, Sum.inl y => G.Adj x y
    | Sum.inl x, Sum.inr false => x ∈ A
    | Sum.inr false, Sum.inl x => x ∈ A
    | Sum.inl x, Sum.inr true => x ∈ B
    | Sum.inr true, Sum.inl x => x ∈ B
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro s t h
    cases s with
    | inl x =>
        cases t with
        | inl y => exact h.symm
        | inr i => cases i <;> exact h
    | inr i =>
        cases t with
        | inl x => cases i <;> exact h
        | inr k =>
            cases i <;> cases k <;> exact False.elim h⟩
  loopless := ⟨by
    intro s h
    cases s with
    | inl x => exact h.ne rfl
    | inr i => cases i <;> exact False.elim h⟩

omit [DecidableEq V] [Fintype V] in
@[simp] theorem linkAugment_adj_inl_inl {A B : Set V} {x y : V} :
    (linkAugment G A B).Adj (Sum.inl x) (Sum.inl y) ↔ G.Adj x y :=
  Iff.rfl

omit [DecidableEq V] [Fintype V] in
@[simp] theorem linkAugment_adj_inl_left {A B : Set V} {x : V} :
    (linkAugment G A B).Adj (Sum.inl x) (Sum.inr false) ↔ x ∈ A :=
  Iff.rfl

omit [DecidableEq V] [Fintype V] in
@[simp] theorem linkAugment_adj_left_inl {A B : Set V} {x : V} :
    (linkAugment G A B).Adj (Sum.inr false) (Sum.inl x) ↔ x ∈ A :=
  Iff.rfl

omit [DecidableEq V] [Fintype V] in
@[simp] theorem linkAugment_adj_inl_right {A B : Set V} {x : V} :
    (linkAugment G A B).Adj (Sum.inl x) (Sum.inr true) ↔ x ∈ B :=
  Iff.rfl

omit [DecidableEq V] [Fintype V] in
@[simp] theorem linkAugment_adj_right_inl {A B : Set V} {x : V} :
    (linkAugment G A B).Adj (Sum.inr true) (Sum.inl x) ↔ x ∈ B :=
  Iff.rfl

/-- The canonical embedding of the old graph into its endpoint augmentation. -/
def linkAugmentEmbedding (G : SimpleGraph V) (A B : Set V) :
    G ↪g linkAugment G A B where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

namespace TwoConnected

omit [DecidableEq V] in
/-- Every edge of a finite vertex-two-connected graph belongs to a simple
cycle.  The proof chooses a second neighbor of one endpoint by finding a path
in the graph with the other endpoint deleted. -/
theorem exists_cycle_through_edge (hG : TwoConnected G) {x y : V}
    (hxy : G.Adj x y) :
    ∃ c : G.Walk x x, c.IsCycle ∧ y ∈ c.support := by
  classical
  obtain ⟨r, s, hry, hsy, hrs⟩ := hG.exists_two_ne y
  let t : V := if r = x then s else r
  have hty : t ≠ y := by
    dsimp [t]
    split <;> assumption
  have htx : t ≠ x := by
    dsimp [t]
    split_ifs with hrx
    · exact fun hsx ↦ hrs (hrx.trans hsx.symm)
    · exact hrx
  obtain ⟨p, hp, hpy⟩ := hG.exists_path_avoiding y hxy.ne hty
  have hp_nonNil : ¬ p.Nil := by
    exact Walk.not_nil_of_ne htx.symm
  let w : V := p.snd
  have hxw : G.Adj x w := p.adj_snd hp_nonNil
  have hwy : w ≠ y := by
    intro h
    exact hpy (h ▸ List.mem_of_mem_tail (p.snd_mem_tail_support hp_nonNil))
  obtain ⟨q₀, hq₀, hq₀x⟩ :=
    hG.exists_path_avoiding x hxy.ne.symm hxw.ne.symm
  let q : G.Walk y x := q₀.concat hxw.symm
  have hq : q.IsPath := hq₀.concat hq₀x hxw.symm
  have hedge : s(x, y) ∉ q.edges := by
    intro he
    have he' : s(y, x) ∈ q.edges := by simpa [Sym2.eq_swap] using he
    have hlen : q.length = 1 := hq.length_eq_one_of_mem_edges he'
    have hq₀len : q₀.length = 0 := by
      have : q.length = q₀.length + 1 := by simp [q]
      omega
    exact hwy (q₀.eq_of_length_eq_zero hq₀len).symm
  let c : G.Walk x x := Walk.cons hxy q
  have hc : c.IsCycle := (Walk.cons_isCycle_iff q hxy).2 ⟨hq, hedge⟩
  refine ⟨c, hc, ?_⟩
  simp [c]

omit [DecidableEq V] [Fintype V] in
/-- The two arcs between distinct vertices of a cycle.  One of them contains
any specified third vertex of the cycle. -/
private theorem exists_cycle_arc_through
    {z : V} {c : G.Walk z z} (hc : c.IsCycle)
    {x w t : V} (hx : x ∈ c.support) (hw : w ∈ c.support)
    (ht : t ∈ c.support) (hxw : x ≠ w) :
    ∃ r : G.Walk x w,
      r.IsPath ∧ t ∈ r.support ∧ (∀ v ∈ r.support, v ∈ c.support) := by
  classical
  let c' : G.Walk x x := c.rotate x hx
  have hc' : c'.IsCycle := hc.rotate hx
  have hw' : w ∈ c'.support := by
    simpa [c'] using (c.mem_support_rotate_iff x hx).2 hw
  have ht' : t ∈ c'.support := by
    simpa [c'] using (c.mem_support_rotate_iff x hx).2 ht
  let r₁ : G.Walk x w := c'.takeUntil w hw'
  let d : G.Walk w x := c'.dropUntil w hw'
  let r₂ : G.Walk x w := d.reverse
  have hr₁ : r₁.IsPath := hc'.isPath_takeUntil hw'
  have hr₂ : r₂.IsPath := by
    apply Walk.isPath_reverse_iff d |>.mpr
    have hcycleappend : (r₁.append d).IsCycle := by
      simpa [r₁, d] using hc'
    exact Walk.IsCycle.isPath_of_append_right (Walk.not_nil_of_ne hxw) hcycleappend
  have hr₁_sub : ∀ v ∈ r₁.support, v ∈ c.support := by
    intro v hv
    have hv' : v ∈ c'.support := c'.support_takeUntil_subset_support hw' hv
    exact (c.mem_support_rotate_iff x hx).1 (by simpa [c'] using hv')
  have hr₂_sub : ∀ v ∈ r₂.support, v ∈ c.support := by
    intro v hv
    have hvd : v ∈ d.support := by simpa [r₂] using hv
    have hv' : v ∈ c'.support := c'.support_dropUntil_subset_support hw' hvd
    exact (c.mem_support_rotate_iff x hx).1 (by simpa [c'] using hv')
  by_cases htr₁ : t ∈ r₁.support
  · exact ⟨r₁, hr₁, htr₁, hr₁_sub⟩
  · refine ⟨r₂, hr₂, ?_, hr₂_sub⟩
    have htappend : t ∈ (r₁.append d).support := by
      simpa [r₁, d, Walk.take_spec c' hw'] using ht'
    rw [Walk.mem_support_append_iff] at htappend
    have htd : t ∈ d.support := htappend.resolve_left htr₁
    simpa [r₂] using htd

omit [DecidableEq V] [Fintype V] in
/-- Extend a common cycle through `root` and `x` across an edge `x-y`.

The old cycle is avoided at `x`: in `G-x`, take a path from `y` to `root`
and stop at its first hit `w` on the old cycle.  The `x-w` arc of the old
cycle which contains `root`, together with the new path and the edge `x-y`,
is the required cycle. -/
private theorem onCommonCycle_of_adj_of_avoiding_path [Finite V]
    {root x y : V} (hxy : G.Adj x y) (hcycle : OnCommonCycle G root x)
    (p : G.Walk y root) (hp : p.IsPath) (hpx : x ∉ p.support) :
    OnCommonCycle G root y := by
  classical
  let := Fintype.ofFinite V
  rcases hcycle with ⟨z, c, hc, hroot, hx⟩
  by_cases hyc : y ∈ c.support
  · exact ⟨z, c, hc, hroot, hyc⟩
  let Cset : Finset V := c.support.toFinset
  have hmeet : {v ∈ Cset | v ∈ p.support}.Nonempty := by
    refine ⟨root, ?_⟩
    simp [Cset, hroot]
  obtain ⟨w, hwC, hwp, hfirst⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq Cset hmeet
  have hwc : w ∈ c.support := by simpa [Cset] using hwC
  have hxw : x ≠ w := by
    intro h
    exact hpx (h ▸ hwp)
  let q : G.Walk y w := p.takeUntil w hwp
  have hq : q.IsPath := hp.takeUntil hwp
  obtain ⟨r, hr, hrootr, hrsub⟩ :=
    exists_cycle_arc_through hc hx hwc hroot hxw
  let body : G.Walk x y := r.append q.reverse
  have hdisj : r.support.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro v hvr hvqtail
    have hvc : v ∈ c.support := hrsub v hvr
    have hvq : v ∈ q.support := by
      have : v ∈ q.reverse.support := List.mem_of_mem_tail hvqtail
      simpa using this
    have hvw : v = w := hfirst v (by simpa [Cset] using hvc) hvq
    subst v
    have hne := hq.reverse.support_nodup.rel_head_tail hvqtail
    exact hne (by simp)
  have hbody : body.IsPath := by
    simp only [Walk.isPath_def, body, Walk.support_append]
    exact List.Nodup.append hr.support_nodup hq.reverse.support_nodup.tail hdisj
  have hedge : s(y, x) ∉ body.edges := by
    intro he
    simp only [body, Walk.edges_append, List.mem_append] at he
    rcases he with her | heq
    · have hyv : y ∈ r.support := r.fst_mem_support_of_mem_edges her
      exact hyc (hrsub y hyv)
    · have hex : s(x, y) ∈ q.edges := by
        simpa [Walk.edges_reverse, Sym2.eq_swap] using heq
      have hxp : x ∈ p.support := by
        exact p.support_takeUntil_subset_support hwp
          (q.fst_mem_support_of_mem_edges hex)
      exact hpx hxp
  let d : G.Walk y y := Walk.cons hxy.symm body
  have hd : d.IsCycle := (Walk.cons_isCycle_iff body hxy.symm).2 ⟨hbody, hedge⟩
  refine ⟨y, d, hd, ?_, ?_⟩
  · have : root ∈ body.support := by
      simp only [body, Walk.mem_support_append_iff]
      exact Or.inl hrootr
    simp only [d, Walk.support_cons, List.mem_cons]
    exact Or.inr this
  · simp [d]

omit [DecidableEq V] in
/-- The preceding geometric extension supplied by deletion connectivity. -/
private theorem onCommonCycle_of_adj
    (hG : TwoConnected G) {root x y : V} (hrx : root ≠ x)
    (hxy : G.Adj x y) (hcycle : OnCommonCycle G root x) :
    OnCommonCycle G root y := by
  classical
  obtain ⟨p, hp, hpx⟩ := hG.exists_path_avoiding x hxy.ne.symm hrx
  exact onCommonCycle_of_adj_of_avoiding_path hxy hcycle p hp hpx

omit [DecidableEq V] in
/-- Propagate the common-cycle property along an adjacency chain which
avoids the fixed root. -/
private theorem onCommonCycle_along_chain
    (hG : TwoConnected G) {root x : V} :
    ∀ (l : List V), List.IsChain G.Adj (x :: l) →
      root ∉ x :: l → OnCommonCycle G root x →
      ∀ y ∈ x :: l, OnCommonCycle G root y := by
  classical
  intro l
  induction l generalizing x with
  | nil =>
      intro _ _ hcycle y hy
      simp only [List.mem_singleton] at hy
      simpa [hy] using hcycle
  | cons v l ih =>
      intro hchain hroot hcycle y hy
      have hc := List.isChain_cons_cons.mp hchain
      have hrel : G.Adj x v := hc.1
      have htailchain : List.IsChain G.Adj (v :: l) := hc.2
      have hrootx : root ≠ x := by
        intro h
        exact hroot (by simp [h])
      have hroottail : root ∉ v :: l := by
        intro h
        exact hroot (List.mem_cons_of_mem x h)
      have hnext : OnCommonCycle G root v :=
        onCommonCycle_of_adj hG hrootx hrel hcycle
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hcycle
      · exact ih htailchain hroottail hnext y (by simpa only [List.mem_cons] using hy)

omit [DecidableEq V] in
/-- Once a cycle contains `root` and the initial vertex of a path which
avoids `root`, adjacency-chain propagation gives a cycle through `root` and
the other endpoint. -/
private theorem onCommonCycle_along_path
    (hG : TwoConnected G) {root x y : V}
    (p : G.Walk x y) (_hp : p.IsPath) (hroot : root ∉ p.support)
    (hcycle : OnCommonCycle G root x) :
    OnCommonCycle G root y := by
  classical
  exact onCommonCycle_along_chain hG p.support.tail
    (by rw [p.cons_tail_support]; exact p.isChain_adj_support)
    (by rw [p.cons_tail_support]; exact hroot) hcycle y
    (by rw [p.cons_tail_support]; exact p.end_mem_support)

omit [DecidableEq V] in
/-- Every vertex of a finite vertex-two-connected graph lies on a simple
cycle. -/
theorem onCommonCycle_refl (hG : TwoConnected G) (x : V) :
    OnCommonCycle G x x := by
  classical
  obtain ⟨t, htx⟩ := hG.exists_ne x
  obtain ⟨p, hp⟩ := hG.connected.exists_isPath x t
  have hp_nonNil : ¬ p.Nil := Walk.not_nil_of_ne htx.symm
  have hxsnd : G.Adj x p.snd := p.adj_snd hp_nonNil
  obtain ⟨c, hc, -⟩ := hG.exists_cycle_through_edge hxsnd
  exact ⟨x, c, hc, c.start_mem_support, c.start_mem_support⟩

omit [DecidableEq V] in
/-- Whitney's common-cycle characterization, in the direction needed here:
any two vertices of a finite vertex-two-connected graph lie on one simple
cycle. -/
theorem onCommonCycle (hG : TwoConnected G) (x y : V) :
    OnCommonCycle G x y := by
  classical
  by_cases hxy : x = y
  · subst y
    exact hG.onCommonCycle_refl x
  obtain ⟨p, hp⟩ := hG.connected.exists_isPath x y
  cases p with
  | nil => exact (hxy rfl).elim
  | @cons x v y h p =>
      have hp' : p.IsPath := hp.of_cons
      have hxnot : x ∉ p.support := (Walk.cons_isPath_iff h p).1 hp |>.2
      obtain ⟨c, hc, hv⟩ := hG.exists_cycle_through_edge h
      have hbase : OnCommonCycle G x v :=
        ⟨x, c, hc, c.start_mem_support, hv⟩
      exact onCommonCycle_along_path hG p hp' hxnot hbase

/-! ## The two-endpoint augmentation is two-connected -/

/-- A common anchor, joined to every vertex, proves connectedness. -/
private theorem connected_of_walks_to
    {W : Type*} {H : SimpleGraph W} (r : W)
    (h : ∀ w : W, Nonempty (H.Walk w r)) : H.Connected := by
  refine { preconnected := ?_, nonempty := ⟨r⟩ }
  intro u v
  obtain ⟨p⟩ := h u
  obtain ⟨q⟩ := h v
  exact ⟨p.append q.reverse⟩

/-- If every vertex other than `z` has a walk to a fixed surviving anchor,
and every such walk avoids `z`, then deleting `z` leaves a connected graph. -/
private theorem connected_induce_compl_singleton_of_walks_to
    {W : Type*} {H : SimpleGraph W} (z r : W) (hr : r ≠ z)
    (h : ∀ w : W, w ≠ z →
      ∃ p : H.Walk w r, z ∉ p.support) :
    (H.induce ({z}ᶜ : Set W)).Connected := by
  classical
  let r' : ({z}ᶜ : Set W) := ⟨r, by simpa using hr⟩
  refine { preconnected := ?_, nonempty := ⟨r'⟩ }
  intro u v
  have hu' : (u : W) ∉ ({z} : Set W) := u.2
  have hv' : (v : W) ∉ ({z} : Set W) := v.2
  have hu : (u : W) ≠ z := fun huz ↦ hu' (by simpa using huz)
  have hv : (v : W) ≠ z := fun hvz ↦ hv' (by simpa using hvz)
  obtain ⟨p, hp⟩ := h u hu
  obtain ⟨q, hq⟩ := h v hv
  let w : H.Walk u v := p.append q.reverse
  have hw : ∀ x ∈ w.support, x ∈ ({z}ᶜ : Set W) := by
    intro x hx
    rw [Walk.mem_support_append_iff] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rcases hx with hxp | hxq
    · exact fun hzx ↦ hp (hzx ▸ hxp)
    · have hxq' : x ∈ q.support := by simpa using hxq
      exact fun hzx ↦ hq (hzx ▸ hxq')
  let wi := w.induce ({z}ᶜ : Set W) hw
  exact ⟨wi.copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

omit [DecidableEq V] [Fintype V] in
/-- A base-graph walk maps to a walk between the corresponding old vertices
of the augmentation. -/
private theorem exists_old_walk (hG : G.Connected) (A B : Set V) (x y : V) :
    ∃ p : (linkAugment G A B).Walk (Sum.inl x) (Sum.inl y),
      ∀ z ∈ p.support, z ∈ Set.range (Sum.inl : V → LinkAugment V) := by
  obtain ⟨p⟩ := hG x y
  let r := p.map (linkAugmentEmbedding G A B).toHom
  have hr : ∀ z ∈ r.support,
      z ∈ Set.range (Sum.inl : V → LinkAugment V) := by
    intro z hz
    simp only [r, Walk.support_map, List.mem_map] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Set.mem_range_self w
  let hx : (linkAugmentEmbedding G A B) x = Sum.inl x := rfl
  let hy : (linkAugmentEmbedding G A B) y = Sum.inl y := rfl
  let r' := r.copy hx hy
  have hsupp : r'.support = r.support := Walk.support_copy r hx hy
  refine ⟨r', ?_⟩
  intro z hz
  exact hr z (hsupp ▸ hz)

omit [DecidableEq V] in
/-- A base-graph path avoiding `z` maps to an augmentation walk avoiding the
old copy of `z`. -/
private theorem exists_old_walk_avoiding (hG : TwoConnected G)
    (A B : Set V) (z : V) {x y : V} (hx : x ≠ z) (hy : y ≠ z) :
    ∃ p : (linkAugment G A B).Walk (Sum.inl x) (Sum.inl y),
      Sum.inl z ∉ p.support := by
  classical
  obtain ⟨p, -, hpz⟩ := hG.exists_path_avoiding z hx hy
  refine ⟨p.map (linkAugmentEmbedding G A B).toHom, ?_⟩
  intro hz
  change (linkAugmentEmbedding G A B) z ∈
    (p.map (linkAugmentEmbedding G A B).toHom).support at hz
  rw [Walk.support_map, List.mem_map] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  exact hpz ((Sum.inl_injective hwz) ▸ hw)

omit [DecidableEq V] [Fintype V] in
/-- The endpoint augmentation is connected as soon as both endpoint sets are
nonempty. -/
private theorem linkAugment_connected [Finite V] (hG : G.Connected)
    {A B : Set V} (hA : A.Nonempty) (hB : B.Nonempty) :
    (linkAugment G A B).Connected := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  apply connected_of_walks_to (H := linkAugment G A B) (Sum.inl a)
  intro w
  cases w with
  | inl x =>
      obtain ⟨p, -⟩ := exists_old_walk hG A B x a
      exact ⟨p⟩
  | inr i =>
      cases i with
      | false =>
          exact ⟨Walk.cons (linkAugment_adj_left_inl.mpr ha) Walk.nil⟩
      | true =>
          obtain ⟨p, -⟩ := exists_old_walk hG A B b a
          exact ⟨Walk.cons (linkAugment_adj_right_inl.mpr hb) p⟩

omit [DecidableEq V] in
/-- Deleting an old vertex leaves the endpoint augmentation connected. -/
private theorem linkAugment_delete_old_connected (hG : TwoConnected G)
    {A B : Set V} (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) (z : V) :
    ((linkAugment G A B).induce
      ({Sum.inl z}ᶜ : Set (LinkAugment V))).Connected := by
  classical
  obtain ⟨a, ha, haz⟩ := A.exists_ne_of_one_lt_ncard (by omega) z
  obtain ⟨b, hb, hbz⟩ := B.exists_ne_of_one_lt_ncard (by omega) z
  apply connected_induce_compl_singleton_of_walks_to
    (H := linkAugment G A B) (Sum.inl z) (Sum.inl a) (by simpa)
  intro w hw
  cases w with
  | inl x =>
      have hxz : x ≠ z := by
        intro hxz
        exact hw (by simp [hxz])
      exact exists_old_walk_avoiding hG A B z hxz haz
  | inr i =>
      cases i with
      | false =>
          refine ⟨Walk.cons (linkAugment_adj_left_inl.mpr ha) Walk.nil, ?_⟩
          simp [haz.symm]
      | true =>
          obtain ⟨p, hp⟩ := exists_old_walk_avoiding hG A B z hbz haz
          refine ⟨Walk.cons (linkAugment_adj_right_inl.mpr hb) p, ?_⟩
          simpa using hp

omit [DecidableEq V] [Fintype V] in
/-- Deleting the left fresh endpoint leaves the augmentation connected. -/
private theorem linkAugment_delete_left_connected [Finite V] (hG : G.Connected)
    {A B : Set V} (hB : B.Nonempty) :
    ((linkAugment G A B).induce
      ({Sum.inr false}ᶜ : Set (LinkAugment V))).Connected := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨b, hb⟩ := hB
  apply connected_induce_compl_singleton_of_walks_to
    (H := linkAugment G A B) (Sum.inr false) (Sum.inl b) (by simp)
  intro w hw
  cases w with
  | inl x =>
      obtain ⟨p, hpold⟩ := exists_old_walk hG A B x b
      refine ⟨p, ?_⟩
      intro h
      obtain ⟨y, hy⟩ := hpold _ h
      cases hy
  | inr i =>
      cases i with
      | false => exact (hw rfl).elim
      | true =>
          refine ⟨Walk.cons (linkAugment_adj_right_inl.mpr hb) Walk.nil, ?_⟩
          simp

omit [DecidableEq V] [Fintype V] in
/-- Deleting the right fresh endpoint leaves the augmentation connected. -/
private theorem linkAugment_delete_right_connected [Finite V] (hG : G.Connected)
    {A B : Set V} (hA : A.Nonempty) :
    ((linkAugment G A B).induce
      ({Sum.inr true}ᶜ : Set (LinkAugment V))).Connected := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨a, ha⟩ := hA
  apply connected_induce_compl_singleton_of_walks_to
    (H := linkAugment G A B) (Sum.inr true) (Sum.inl a) (by simp)
  intro w hw
  cases w with
  | inl x =>
      obtain ⟨p, hpold⟩ := exists_old_walk hG A B x a
      refine ⟨p, ?_⟩
      intro h
      obtain ⟨y, hy⟩ := hpold _ h
      cases hy
  | inr i =>
      cases i with
      | false =>
          refine ⟨Walk.cons (linkAugment_adj_left_inl.mpr ha) Walk.nil, ?_⟩
          simp
      | true => exact (hw rfl).elim

omit [DecidableEq V] in
/-- Adding one fresh vertex on each side makes the graph two-connected when
the base graph is two-connected and each attachment set has at least two
vertices. -/
theorem linkAugment_twoConnected (hG : TwoConnected G) {A B : Set V}
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    TwoConnected (linkAugment G A B) := by
  classical
  have hAne : A.Nonempty := (Set.ncard_pos (Set.toFinite A)).mp (by omega)
  have hBne : B.Nonempty := (Set.ncard_pos (Set.toFinite B)).mp (by omega)
  refine ⟨?_, linkAugment_connected hG.connected hAne hBne, ?_⟩
  · have hcard := hG.card_three_le
    simp [LinkAugment]
    omega
  · intro z
    cases z with
    | inl x => exact linkAugment_delete_old_connected hG hA hB x
    | inr i =>
        cases i with
        | false => exact linkAugment_delete_left_connected hG.connected hBne
        | true => exact linkAugment_delete_right_connected hG.connected hAne

/-! ## Removing the two fresh endpoints from the cycle arcs -/

/-- The old-vertex middle of a path from the left fresh endpoint to the
right fresh endpoint. -/
private structure StrippedAugmentPath (G : SimpleGraph V) (A B : Set V)
    (p : (linkAugment G A B).Walk (Sum.inr false) (Sum.inr true)) where
  a : V
  b : V
  walk : (linkAugment G A B).Walk (Sum.inl a) (Sum.inl b)
  isPath : walk.IsPath
  a_mem : a ∈ A
  b_mem : b ∈ B
  support_subset_tail : walk.support ⊆ p.support.tail
  old_support : ∀ x ∈ walk.support,
    x ∈ Set.range (Sum.inl : V → LinkAugment V)

omit [DecidableEq V] [Fintype V] in
/-- Strip the two fresh endpoints from an augmentation path.  Simplicity
ensures that neither fresh endpoint occurs in the remaining middle. -/
private theorem strip_augment_path [Finite V] {A B : Set V}
    (p : (linkAugment G A B).Walk (Sum.inr false) (Sum.inr true))
    (hp : p.IsPath) : Nonempty (StrippedAugmentPath G A B p) := by
  classical
  let := Fintype.ofFinite V
  have hp_nonNil : ¬p.Nil := Walk.not_nil_of_ne (by simp)
  have htailPath : p.tail.IsPath := hp.tail
  have htail_nonNil : ¬p.tail.Nil := by
    intro hnil
    have hsnd : p.snd = Sum.inr true := htailPath.nil_iff_eq.mp hnil
    have hadj := p.adj_snd hp_nonNil
    rw [hsnd] at hadj
    simp [linkAugment] at hadj
  have hpen : p.tail.penultimate = p.penultimate := by
    have h := Walk.penultimate_cons_of_not_nil
      (p.adj_snd hp_nonNil) p.tail htail_nonNil
    rw [p.cons_tail_eq hp_nonNil] at h
    exact h.symm
  have hleft := p.adj_snd hp_nonNil
  have hright := p.adj_penultimate hp_nonNil
  cases hs : p.snd with
  | inr i =>
    rw [hs] at hleft
    cases i <;> simp [linkAugment] at hleft
  | inl a =>
    rw [hs] at hleft
    cases ht : p.penultimate with
    | inr i =>
      rw [ht] at hright
      cases i <;> simp [linkAugment] at hright
    | inl b =>
      rw [ht] at hright
      have ha : a ∈ A := by simpa using hleft
      have hb : b ∈ B := by simpa using hright
      let m₀ := p.tail.dropLast
      have hm₀ : m₀.IsPath := hp.tail.dropLast
      have hmend : p.tail.penultimate = Sum.inl b := hpen.trans ht
      let m : (linkAugment G A B).Walk (Sum.inl a) (Sum.inl b) :=
        m₀.copy hs hmend
      have hmsub : m.support ⊆ p.support.tail := by
        intro x hx
        have hx₀ : x ∈ m₀.support := by simpa [m] using hx
        have hxdrop : x ∈ p.tail.support.dropLast := by
          simpa [m₀, Walk.support_dropLast htail_nonNil] using hx₀
        have hxtail : x ∈ p.tail.support := List.mem_of_mem_dropLast hxdrop
        simpa [p.support_tail_of_not_nil hp_nonNil] using hxtail
      have halpha : Sum.inr false ∉ p.support.tail := by
        have hn := hp.support_nodup
        rw [← p.cons_tail_support] at hn
        exact (List.nodup_cons.mp hn).1
      have hbeta : Sum.inr true ∉ m.support := by
        intro hx
        have hx₀ : Sum.inr true ∈ m₀.support := by simpa [m] using hx
        have hn := hp.tail.support_nodup
        rw [← p.tail.support_dropLast_concat htail_nonNil] at hn
        exact hn.disjoint hx₀ (by simp)
      refine ⟨{
        a := a
        b := b
        walk := m
        isPath := by simpa [m] using hm₀
        a_mem := ha
        b_mem := hb
        support_subset_tail := hmsub
        old_support := ?_ }⟩
      intro x hx
      cases x with
      | inl v => exact ⟨v, rfl⟩
      | inr i =>
          cases i with
          | false => exact (halpha (hmsub hx)).elim
          | true => exact (hbeta hx).elim

omit [DecidableEq V] [Fintype V] in
/-- A walk in the augmentation all of whose vertices are old is the image of
a unique old-graph walk.  Only existence and the mapping equality are needed
below. -/
private theorem exists_old_preimage {A B : Set V} {a b : V}
    (p : (linkAugment G A B).Walk (Sum.inl a) (Sum.inl b))
    (hold : ∀ x ∈ p.support,
      x ∈ Set.range (Sum.inl : V → LinkAugment V)) :
    ∃ q : G.Walk a b, q.map (linkAugmentEmbedding G A B).toHom = p := by
  classical
  let e := linkAugmentEmbedding G A B
  have hold' : ∀ x ∈ p.support, x ∈ Set.range e := by
    intro x hx
    obtain ⟨v, hv⟩ := hold x hx
    refine ⟨v, ?_⟩
    change Sum.inl v = x
    exact hv
  let p' := p.induce (Set.range e) hold'
  let q₀ := p'.map e.isoInduceRange.symm.toHom
  have hqa : e.isoInduceRange.symm
      ⟨Sum.inl a, Set.mem_range_self a⟩ = a := by
    exact e.isoInduceRange.symm_apply_apply a
  have hqb : e.isoInduceRange.symm
      ⟨Sum.inl b, Set.mem_range_self b⟩ = b := by
    exact e.isoInduceRange.symm_apply_apply b
  let q : G.Walk a b := q₀.copy hqa hqb
  refine ⟨q, ?_⟩
  apply Walk.ext_support
  calc
    (q.map (linkAugmentEmbedding G A B).toHom).support =
        (q₀.map e.toHom).support := by
      simp [q, e]
    _ = p.support := by
      simp only [q₀, Walk.support_map, List.map_map]
      change List.map (fun x : Set.range e => e (e.isoInduceRange.symm x))
          p'.support = p.support
      have hfun : (fun x : Set.range e => e (e.isoInduceRange.symm x)) =
          (fun x : Set.range e => (x : LinkAugment V)) := by
        funext x
        exact congrArg Subtype.val (e.isoInduceRange.apply_symm_apply x)
      rw [hfun]
      change ((p.induce (Set.range e) hold').support.map Subtype.val) = p.support
      rw [Walk.support_induce]
      exact List.attachWith_map_subtype_val hold'

omit [DecidableEq V] [Fintype V] in
/-- Pull a stripped augmentation path back to the base graph, retaining the
exact equality after mapping it into the augmentation. -/
private theorem StrippedAugmentPath.exists_old_path [Finite V] {A B : Set V}
    {p : (linkAugment G A B).Walk (Sum.inr false) (Sum.inr true)}
    (S : StrippedAugmentPath G A B p) :
    ∃ q : G.Walk S.a S.b,
      q.IsPath ∧ q.map (linkAugmentEmbedding G A B).toHom = S.walk := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨q, hq⟩ := exists_old_preimage S.walk S.old_support
  refine ⟨q, ?_, hq⟩
  have hmapped : (q.map (linkAugmentEmbedding G A B).toHom).IsPath := by
    rw [Walk.isPath_def, hq]
    exact S.isPath.support_nodup
  exact (Walk.isPath_map_iff_of_injective
    (f := (linkAugmentEmbedding G A B).toHom)
    (linkAugmentEmbedding G A B).injective).mp hmapped

omit [DecidableEq V] in
/-- The fresh-endpoint cycle in the augmentation yields two fully disjoint
base-graph paths from `A` to `B`. -/
theorem exists_rawTwoPathPacking (hG : TwoConnected G) {A B : Set V}
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    Nonempty (RawTwoPathPacking G A B) := by
  classical
  let H := linkAugment G A B
  have hH : TwoConnected H := hG.linkAugment_twoConnected hA hB
  obtain ⟨z, c, hc, hleft, hright⟩ :=
    hH.onCommonCycle (Sum.inr false) (Sum.inr true)
  obtain ⟨p, q, hp, hq, -, -, -, hmeet, -, -, -⟩ :=
    exists_path_arcs_of_cycle hc hleft hright (by simp)
  obtain ⟨P⟩ := strip_augment_path p hp
  obtain ⟨Q⟩ := strip_augment_path q hq
  obtain ⟨pG, hpG, hpmap⟩ := P.exists_old_path
  obtain ⟨qG, hqG, hqmap⟩ := Q.exists_old_path
  have hdisj : pG.support.Disjoint qG.support := by
    rw [List.disjoint_left]
    intro x hxp hxq
    have hxp' : Sum.inl x ∈ P.walk.support := by
      have hxpmap : (linkAugmentEmbedding G A B) x ∈
          (pG.map (linkAugmentEmbedding G A B).toHom).support := by
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨x, hxp, rfl⟩
      rw [hpmap] at hxpmap
      exact hxpmap
    have hxq' : Sum.inl x ∈ Q.walk.support := by
      have hxqmap : (linkAugmentEmbedding G A B) x ∈
          (qG.map (linkAugmentEmbedding G A B).toHom).support := by
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨x, hxq, rfl⟩
      rw [hqmap] at hxqmap
      exact hxqmap
    have hxpArc : Sum.inl x ∈ p.support :=
      List.mem_of_mem_tail (P.support_subset_tail hxp')
    have hxqArc : Sum.inl x ∈ q.support :=
      List.mem_of_mem_tail (Q.support_subset_tail hxq')
    rcases hmeet (Sum.inl x) hxpArc hxqArc with h | h <;> simp at h
  exact ⟨{
    a₁ := P.a
    a₂ := Q.a
    b₁ := P.b
    b₂ := Q.b
    p := pG
    q := qG
    p_isPath := hpG
    q_isPath := hqG
    a₁_mem := P.a_mem
    a₂_mem := Q.a_mem
    b₁_mem := P.b_mem
    b₂_mem := Q.b_mem
    disjoint_support := hdisj }⟩

omit [DecidableEq V] in
/-- The unconditional finite two-path Menger consequence needed for the
Gyárfás argument.  The endpoint-cardinality hypotheses are sharp for full
support disjointness. -/
theorem exists_twoLinkage (hG : TwoConnected G) {A B : Set V}
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    Nonempty (TwoLinkage G A B) := by
  classical
  obtain ⟨P⟩ := hG.exists_rawTwoPathPacking hA hB
  exact hG.twoLinkage_of_rawPacking P

end TwoConnected

end Erdos58
-- END Menger

-- BEGIN Aligned

namespace E767AlignedAlt

open SimpleGraph


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- `q` meets the vertices of the oriented path `p` in their `p`-order.

The filtered-sublist presentation is equivalent to the usual pairwise
"appears before" definition for simple paths, but behaves substantially
better under taking prefixes and suffixes. -/
def Aligned {x y a b : V} (p : G.Walk x y) (q : G.Walk a b) : Prop :=
  (q.support.filter fun v => v ∈ p.support).Sublist p.support

omit [Fintype V] in
@[simp] lemma filter_mem_self (l : List V) :
    l.filter (fun v => v ∈ l) = l := by
  apply List.filter_eq_self.mpr
  simp

omit [Fintype V] in
lemma aligned_refl {x y : V} (p : G.Walk x y) : Aligned p p := by
  simp [Aligned]

omit [Fintype V] in
/-- Taking a sublist of the second path preserves alignment. -/
lemma aligned_of_support_sublist {x y a b c d : V}
    {p : G.Walk x y} {q : G.Walk a b} {r : G.Walk c d}
    (hq : Aligned p q) (hrq : r.support.Sublist q.support) :
    Aligned p r := by
  exact (hrq.filter _).trans hq

omit [Fintype V] in
lemma aligned_takeUntil {x y a b u : V}
    {p : G.Walk x y} {q : G.Walk a b} (hq : Aligned p q)
    (hu : u ∈ q.support) : Aligned p (q.takeUntil u hu) := by
  apply aligned_of_support_sublist hq
  exact q.support_takeUntil_prefix_support hu |>.sublist

omit [Fintype V] in
lemma aligned_dropUntil {x y a b u : V}
    {p : G.Walk x y} {q : G.Walk a b} (hq : Aligned p q)
    (hu : u ∈ q.support) : Aligned p (q.dropUntil u hu) := by
  apply aligned_of_support_sublist hq
  exact q.support_dropUntil_suffix_support hu |>.sublist

omit [Fintype V] [DecidableEq V] in
lemma isPath_append_of_disjoint_tail {a b c : V}
    {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.support.Disjoint q.support.tail) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  exact List.Nodup.append hp.support_nodup hq.support_nodup.tail hd

omit [Fintype V] in
lemma isPath_append_dropUntil_of_first_hit {a b c u : V}
    {p : G.Walk a u} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath) (hu : u ∈ q.support)
    (hfirst : ∀ v, v ∈ q.support → v ∈ p.support → v = u) :
    (p.append (q.dropUntil u hu)).IsPath := by
  apply isPath_append_of_disjoint_tail hp (hq.dropUntil hu)
  rw [List.disjoint_left]
  intro v hvp hvqtail
  have hvqdrop : v ∈ (q.dropUntil u hu).support := List.mem_of_mem_tail hvqtail
  have hvq : v ∈ q.support := q.support_dropUntil_subset_support hu hvqdrop
  have hvu : v = u := hfirst v hvq hvp
  subst v
  exact (hq.dropUntil hu).support_nodup.rel_head_tail hvqtail (by simp)

omit [Fintype V] in
lemma filter_eq_ite_singleton_of_nodup_of_forall_eq
    (l : List V) (s : V → Prop) [DecidablePred s] (u : V)
    (hl : l.Nodup) (honly : ∀ v, v ∈ l → s v → v = u) :
    l.filter s = if u ∈ l ∧ s u then [u] else [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hnodup := List.nodup_cons.mp hl
      have ih' := ih hnodup.2 (fun v hv hsv ↦ honly v (by simp [hv]) hsv)
      by_cases hsa : s a
      · have hau : a = u := honly a (by simp) hsa
        subst a
        have hul : u ∉ l := hnodup.1
        simp [hsa, hul, ih']
      · simp only [List.filter_cons, hsa, ih']
        by_cases hu : u ∈ l ∧ s u
        · have huna : u ≠ a := by
            intro hua
            exact hsa (hua ▸ hu.2)
          simp [hu, huna]
        · by_cases hua : u = a
          · subst a
            simp [hsa]
          · simp [hu, hua]

omit [Fintype V] in
/-- Adding the common initial edge to both the reference path and an aligned
path preserves alignment, provided the new initial vertex is genuinely new. -/
lemma aligned_cons {x v y b : V} {h : G.Adj x v}
    {p : G.Walk v y} {q : G.Walk v b}
    (_hxp : x ∉ p.support) (hxq : x ∉ q.support) (hq : Aligned p q) :
    Aligned (Walk.cons h p) (Walk.cons h q) := by
  unfold Aligned at hq ⊢
  have hfilter :
      (Walk.cons h q).support.filter
          (fun w => w ∈ (Walk.cons h p).support) =
        x :: q.support.filter (fun w => w ∈ p.support) := by
    simp only [Walk.support_cons, List.filter_cons]
    rw [if_pos (by simp)]
    congr 1
    apply List.filter_congr
    intro w hw
    simp only [List.mem_cons]
    have hwne : w ≠ x := by
      intro hwx
      exact hxq (hwx ▸ hw)
    simp [hwne]
  rw [hfilter, Walk.support_cons]
  exact hq.cons_cons x

omit [Fintype V] in
/-- A path aligned with the tail remains aligned with the whole reference
path when the removed first vertex is absent from it. -/
lemma aligned_cons_reference {x v y a b : V} {h : G.Adj x v}
    {p : G.Walk v y} {q : G.Walk a b}
    (hxq : x ∉ q.support) (hq : Aligned p q) :
    Aligned (Walk.cons h p) q := by
  unfold Aligned at hq ⊢
  have hfilter :
      q.support.filter (fun w => w ∈ (Walk.cons h p).support) =
        q.support.filter (fun w => w ∈ p.support) := by
    apply List.filter_congr
    intro w hw
    simp only [Walk.support_cons, List.mem_cons]
    have hwne : w ≠ x := by
      intro hwx
      exact hxq (hwx ▸ hw)
    simp [hwne]
  rw [hfilter, Walk.support_cons]
  exact hq.cons x

omit [Fintype V] in
/-- If a new reference initial vertex is also the initial vertex of `q`,
then it may be added in front of a path already aligned with the reference
tail. -/
lemma aligned_cons_left {x v y b : V} {h : G.Adj x v}
    {p : G.Walk v y} {q : G.Walk x b}
    (hxp : x ∉ p.support) (hxq : x ∉ q.support.tail)
    (hq : Aligned p q) :
    Aligned (Walk.cons h p) q := by
  unfold Aligned at hq ⊢
  have hfilter :
      q.support.filter (fun w => w ∈ (Walk.cons h p).support) =
        x :: q.support.filter (fun w => w ∈ p.support) := by
    conv_lhs => rw [← q.cons_tail_support]
    conv_rhs => rw [← q.cons_tail_support]
    simp only [Walk.support_cons, List.filter_cons]
    rw [if_pos (by simp), if_neg (by simpa using hxp)]
    congr 1
    apply List.filter_congr
    intro w hw
    simp only [List.mem_cons]
    have hwne : w ≠ x := by
      intro h
      exact hxq (h ▸ hw)
    simp [hwne]
  rw [hfilter, Walk.support_cons]
  exact hq.cons_cons x

omit [Fintype V] in
/-- Alignment of the Case-2 splice: a path from the new root which first
meets the old reference path at its endpoint is followed by the suffix of an
already aligned branch through that endpoint. -/
lemma aligned_cons_append_dropUntil_of_first_hit
    {x v y b u : V} {h : G.Adj x v}
    {p : G.Walk v y} {q : G.Walk x u} {r : G.Walk v b}
    (hxp : x ∉ p.support) (hxr : x ∉ r.support)
    (hq : q.IsPath) (hr : Aligned p r) (hu : u ∈ r.support)
    (hfirstP : ∀ w, w ∈ p.support → w ∈ q.support → w = u) :
    Aligned (Walk.cons h p) (q.append (r.dropUntil u hu)) := by
  let d := r.dropUntil u hu
  have hd : Aligned p d := aligned_dropUntil hr hu
  have hqd :
      q.support.filter (fun w => w ∈ p.support) =
        if u ∈ p.support then [u] else [] := by
    have hf := filter_eq_ite_singleton_of_nodup_of_forall_eq
      q.support (fun w => w ∈ p.support) u hq.support_nodup
      (fun w hwq hwp => hfirstP w hwp hwq)
    simpa using hf
  have hqfull :
      q.support.filter (fun w => w ∈ (Walk.cons h p).support) =
        x :: (if u ∈ p.support then [u] else []) := by
    rw [← q.cons_tail_support, List.filter_cons]
    rw [if_pos (by simp)]
    have hxqt : x ∉ q.support.tail := by
      intro hx
      have hne := hq.support_nodup.rel_head_tail hx
      exact hne (by simp only [q.head_support])
    have htailFull :
        q.support.tail.filter (fun w => w ∈ (Walk.cons h p).support) =
          q.support.tail.filter (fun w => w ∈ p.support) := by
      apply List.filter_congr
      intro w hw
      simp only [Walk.support_cons, List.mem_cons]
      have hwne : w ≠ x := by
        intro hwx
        exact hxqt (hwx ▸ hw)
      simp [hwne]
    rw [htailFull]
    have htailP :
        q.support.tail.filter (fun w => w ∈ p.support) =
          q.support.filter (fun w => w ∈ p.support) := by
      have hs :
          (x :: q.support.tail).filter (fun w => w ∈ p.support) =
            q.support.filter (fun w => w ∈ p.support) := congrArg
        (fun l : List V => l.filter (fun w => w ∈ p.support))
        q.cons_tail_support
      have hskip :
          (x :: q.support.tail).filter (fun w => w ∈ p.support) =
            q.support.tail.filter (fun w => w ∈ p.support) := by
        simp only [List.filter_cons]
        rw [if_neg (by simpa using hxp)]
      exact hskip.symm.trans hs
    rw [htailP, hqd]
  have hxdt : x ∉ d.support.tail := by
    intro hx
    exact hxr (r.support_dropUntil_subset_support hu (List.mem_of_mem_tail hx))
  have hdtail :
      d.support.tail.filter (fun w => w ∈ (Walk.cons h p).support) =
        d.support.tail.filter (fun w => w ∈ p.support) := by
    apply List.filter_congr
    intro w hw
    simp only [Walk.support_cons, List.mem_cons]
    have hwne : w ≠ x := by
      intro hwx
      exact hxdt (hwx ▸ hw)
    simp [hwne]
  unfold Aligned at hd ⊢
  rw [Walk.support_append, List.filter_append, hqfull, hdtail,
    Walk.support_cons]
  change
    (x :: ((if u ∈ p.support then [u] else []) ++
      d.support.tail.filter (fun w => w ∈ p.support))).Sublist
      (x :: p.support)
  apply List.Sublist.cons_cons
  have hdSupport :
      d.support.filter (fun w => w ∈ p.support) =
        (if u ∈ p.support then [u] else []) ++
          d.support.tail.filter (fun w => w ∈ p.support) := by
    conv_lhs => rw [← d.cons_tail_support]
    simp only [List.filter_cons]
    by_cases hup : u ∈ p.support <;> simp [hup]
  rw [← hdSupport]
  exact hd

omit [Fintype V] in
lemma start_not_mem_dropUntil_of_ne {v y u : V} {p : G.Walk v y}
    (hp : p.IsPath) (hu : u ∈ p.support) (huv : u ≠ v) :
    v ∉ (p.dropUntil u hu).support := by
  intro hv
  obtain ⟨t, ht⟩ := p.support_dropUntil_suffix_support hu
  have hnd : (t ++ (p.dropUntil u hu).support).Nodup := by
    rw [ht]
    exact hp.support_nodup
  have hsep := (List.nodup_append.mp hnd).2.2
  cases t with
  | nil =>
      have hs : (p.dropUntil u hu).support = p.support := by simpa using ht
      have huv' : u = v := by
        calc
          u = (p.dropUntil u hu).support.head
              (p.dropUntil u hu).support_ne_nil :=
            (p.dropUntil u hu).head_support.symm
          _ = p.support.head p.support_ne_nil := by simp only [hs]
          _ = v := p.head_support
      exact huv huv'
  | cons a t =>
      have hav : a = v := by
        have hcons : a :: (t ++ (p.dropUntil u hu).support) =
            v :: p.support.tail := by
          simpa [p.cons_tail_support] using ht
        exact List.cons.inj hcons |>.1
      exact hsep a (by simp) v hv hav

omit [Fintype V] [DecidableEq V] in
private lemma tail_sublist_of_cons_sublist_append_cons
    {w : V} {cs pre post : List V}
    (hwpre : w ∉ pre) (hwpost : w ∉ post)
    (h : (w :: cs).Sublist (pre ++ w :: post)) :
    cs.Sublist post := by
  induction pre with
  | nil =>
      simp only [List.nil_append] at h
      rcases List.cons_sublist_cons'.mp h with hbad | hgood
      · exact (hwpost (hbad.subset (by simp))).elim
      · exact hgood.2
  | cons a pre ih =>
      have haw : w ≠ a := by
        intro hwa
        exact hwpre (by simp [hwa])
      have hwpre' : w ∉ pre := by
        intro hw
        exact hwpre (by simp [hw])
      apply ih hwpre'
      exact h.of_cons_of_ne haw

omit [DecidableEq V] [Fintype V] in
private lemma append_tail_sublist_of_infix_of_last
    {w : V} {a cs l : List V}
    (hl : l.Nodup) (ha : a <:+: l) (ha0 : a ≠ [])
    (halast : a.getLast ha0 = w) (hc : (w :: cs).Sublist l) :
    (a ++ cs).Sublist l := by
  classical
  obtain ⟨pre, post, hprepost⟩ := ha
  have hadecomp := a.dropLast_append_getLast ha0
  rw [halast] at hadecomp
  have heq : pre ++ a.dropLast ++ w :: post = pre ++ a ++ post := by
    calc
      pre ++ a.dropLast ++ w :: post =
          pre ++ (a.dropLast ++ [w]) ++ post := by
        simp only [List.append_assoc, List.singleton_append]
      _ = pre ++ a ++ post := by rw [hadecomp]
  have hl' : (pre ++ a.dropLast ++ w :: post).Nodup := by
    rw [heq, hprepost]
    exact hl
  have hc' : (w :: cs).Sublist (pre ++ a.dropLast ++ w :: post) := by
    rw [heq, hprepost]
    exact hc
  have hparts := List.nodup_append.mp hl'
  have htailparts := List.nodup_cons.mp hparts.2.1
  have hwpre : w ∉ pre ++ a.dropLast := by
    intro hw
    exact hparts.2.2 w hw w (by simp) rfl
  have hwpost : w ∉ post := htailparts.1
  have hcs : cs.Sublist post :=
    tail_sublist_of_cons_sublist_append_cons hwpre hwpost hc'
  have hkeep : (a ++ cs).Sublist (a ++ post) :=
    (List.Sublist.refl a).append hcs
  have hskip : (a ++ cs).Sublist (pre ++ a ++ post) := by
    simpa [List.append_assoc] using (List.nil_sublist pre).append hkeep
  rw [hprepost] at hskip
  exact hskip

omit [Fintype V] in
lemma aligned_cons_indirect_splice
    {x v y z u w : V} {h : G.Adj x v}
    {ref : G.Walk v y} {q : G.Walk x u} {t : G.Walk u w}
    {r : G.Walk v z}
    (hxref : x ∉ ref.support) (hxr : x ∉ r.support)
    (href : ref.IsPath) (hq : q.IsPath) (huref : u ∈ ref.support)
    (hfirstRef : ∀ a, a ∈ ref.support → a ∈ q.support → a = u)
    (htinfix : t.support <:+: ref.support)
    (hwr : w ∈ r.support) (hwtref : w ∈ ref.support)
    (har : Aligned ref r) :
    Aligned (Walk.cons h ref)
      ((q.append t).append (r.dropUntil w hwr)) := by
  let s := r.dropUntil w hwr
  have hsAligned : Aligned ref s := aligned_dropUntil har hwr
  have hqRef :
      q.support.filter (fun a => a ∈ ref.support) = [u] := by
    have hfilter := filter_eq_ite_singleton_of_nodup_of_forall_eq
      q.support (fun a => a ∈ ref.support) u hq.support_nodup
      (fun a haq haref => hfirstRef a haref haq)
    simpa [huref] using hfilter
  have hxqtail : x ∉ q.support.tail := by
    intro hx
    have hne := hq.support_nodup.rel_head_tail hx
    exact hne (by simp only [q.head_support])
  have hqFull :
      q.support.filter (fun a => a ∈ (Walk.cons h ref).support) = [x, u] := by
    rw [← q.cons_tail_support, List.filter_cons]
    rw [if_pos (by simp)]
    have htailFull :
        q.support.tail.filter (fun a => a ∈ (Walk.cons h ref).support) =
          q.support.tail.filter (fun a => a ∈ ref.support) := by
      apply List.filter_congr
      intro a ha
      simp only [Walk.support_cons, List.mem_cons]
      have hax : a ≠ x := by
        intro hax
        exact hxqtail (hax ▸ ha)
      simp [hax]
    rw [htailFull]
    have htailRef :
        q.support.tail.filter (fun a => a ∈ ref.support) =
          q.support.filter (fun a => a ∈ ref.support) := by
      have hs :
          (x :: q.support.tail).filter (fun a => a ∈ ref.support) =
            q.support.filter (fun a => a ∈ ref.support) := congrArg
        (fun l : List V => l.filter (fun a => a ∈ ref.support))
        q.cons_tail_support
      have hskip :
          (x :: q.support.tail).filter (fun a => a ∈ ref.support) =
            q.support.tail.filter (fun a => a ∈ ref.support) := by
        simp only [List.filter_cons]
        rw [if_neg (by simpa using hxref)]
      exact hskip.symm.trans hs
    rw [htailRef, hqRef]
  have htfilter :
      t.support.filter (fun a => a ∈ ref.support) = t.support := by
    apply List.filter_eq_self.mpr
    intro a ha
    simpa using htinfix.subset ha
  have hxttail : x ∉ t.support.tail := by
    intro hx
    exact hxref (htinfix.subset (List.mem_of_mem_tail hx))
  have htTailFull :
      t.support.tail.filter (fun a => a ∈ (Walk.cons h ref).support) =
        t.support.tail := by
    apply List.filter_eq_self.mpr
    intro a ha
    simp only [Walk.support_cons, List.mem_cons]
    simpa using Or.inr (htinfix.subset (List.mem_of_mem_tail ha))
  have hxstail : x ∉ s.support.tail := by
    intro hx
    exact hxr (r.support_dropUntil_subset_support hwr (List.mem_of_mem_tail hx))
  have hsTailFull :
      s.support.tail.filter (fun a => a ∈ (Walk.cons h ref).support) =
        s.support.tail.filter (fun a => a ∈ ref.support) := by
    apply List.filter_congr
    intro a ha
    simp only [Walk.support_cons, List.mem_cons]
    have hax : a ≠ x := by
      intro hax
      exact hxstail (hax ▸ ha)
    simp [hax]
  have hsCommonCons :
      w :: s.support.tail.filter (fun a => a ∈ ref.support) =
        s.support.filter (fun a => a ∈ ref.support) := by
    conv_rhs => rw [← s.cons_tail_support]
    simp only [List.filter_cons]
    rw [if_pos (by simpa using hwtref)]
  have htailSub :
      (t.support ++ s.support.tail.filter (fun a => a ∈ ref.support)).Sublist
        ref.support := by
    apply append_tail_sublist_of_infix_of_last href.support_nodup htinfix
      t.support_ne_nil t.getLast_support
    rw [hsCommonCons]
    exact hsAligned
  unfold Aligned at hsAligned ⊢
  rw [Walk.support_append, Walk.support_append, List.filter_append,
    List.filter_append, hqFull, htTailFull, hsTailFull, Walk.support_cons]
  simpa [List.append_assoc] using htailSub.cons_cons x

omit [DecidableEq V] [Fintype V] in
lemma isPath_append_of_meet_eq_end {a b c : V}
    {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ t, t ∈ p.support → t ∈ q.support → t = b) :
    (p.append q).IsPath := by
  classical
  apply isPath_append_of_disjoint_tail hp hq
  rw [List.disjoint_left]
  intro t htp htqt
  have htb := hmeet t htp (List.mem_of_mem_tail htqt)
  subst t
  exact hq.support_nodup.rel_head_tail htqt (by simp)

omit [Fintype V] in
lemma isPath_indirect_splice
    {x u w v z : V} {q : G.Walk x u} {r : G.Walk u w}
    {a : G.Walk v z}
    (hq : q.IsPath) (hr : r.IsPath) (ha : a.IsPath) (hw : w ∈ a.support)
    (hqr : ∀ t, t ∈ q.support → t ∈ r.support → t = u)
    (hqa : ∀ t, t ∈ q.support → t ∈ a.support → t = u)
    (hua : u ∉ a.support)
    (hra : ∀ t, t ∈ r.support → t ∈ a.support → t = w) :
    ((q.append r).append (a.dropUntil w hw)).IsPath := by
  have hqrs : (q.append r).IsPath := isPath_append_of_meet_eq_end hq hr hqr
  apply isPath_append_of_meet_eq_end hqrs (ha.dropUntil hw)
  intro t htqr hta
  rw [Walk.mem_support_append_iff] at htqr
  have hta' : t ∈ a.support := a.support_dropUntil_subset_support hw hta
  rcases htqr with htq | htr
  · have htu : t = u := hqa t htq hta'
    exact (hua (htu ▸ hta')).elim
  · exact hra t htr hta'

/-- The certificate in Dirac's aligned two-path lemma.  The explicit
intersection equation is easier to use than a nested `List.Disjoint` after
the two paths have their common first vertex. -/
structure AlignedFan {x y z : V} (p : G.Walk x y) where
  toZ : G.Walk x z
  toY : G.Walk x y
  toZ_isPath : toZ.IsPath
  toY_isPath : toY.IsPath
  meet_eq_start : ∀ ⦃w : V⦄, w ∈ toZ.support → w ∈ toY.support → w = x
  toZ_aligned : Aligned p toZ
  toY_aligned : Aligned p toY

omit [Fintype V] in
@[simp] lemma aligned_nil {x y a : V} (p : G.Walk x y) :
    Aligned p (.nil : G.Walk a a) := by
  by_cases ha : a ∈ p.support
  · simp [Aligned, ha]
  · simp [Aligned, ha]

omit [Fintype V] in
lemma aligned_edge_of_avoids_end {x y z : V} (hxy : G.Adj x y)
    (q : G.Walk x z) (hq : q.IsPath) (hy : y ∉ q.support) :
    Aligned hxy.toWalk q := by
  have hxnot : x ∉ q.support.tail := by
    have hn := hq.support_nodup
    rw [← q.cons_tail_support, List.nodup_cons] at hn
    exact hn.1
  have hynot : y ∉ q.support.tail := fun h ↦ hy (List.mem_of_mem_tail h)
  have hfilter : q.support.tail.filter (fun v ↦ v ∈ [x, y]) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hax : a ≠ x := fun h ↦ hxnot (h ▸ ha)
    have hay : a ≠ y := fun h ↦ hynot (h ▸ ha)
    simp [hax, hay]
  unfold Aligned
  rw [hxy.support_toWalk, ← q.cons_tail_support]
  rw [List.filter_cons_of_pos (by simp), hfilter]
  exact (List.nil_sublist [y]).cons_cons x

/-- A path in `G - v` from `x` toward `y`, stopped at its first point on
the reference path or either old branch. -/
lemma exists_first_connector
    (hG : Erdos58.TwoConnected G) {x v y z : V}
    (hxv : G.Adj x v) (p : G.Walk v y) (hvy : v ≠ y)
    (a : G.Walk v z) (b : G.Walk v y) :
    ∃ (u : V) (q : G.Walk x u),
      q.IsPath ∧ v ∉ q.support ∧
      u ∈ p.support.toFinset ∪ a.support.toFinset ∪ b.support.toFinset ∧
      (∀ t, t ∈ p.support.toFinset ∪ a.support.toFinset ∪ b.support.toFinset →
        t ∈ q.support → t = u) := by
  obtain ⟨r, hr, hrv⟩ := hG.exists_path_avoiding v hxv.ne hvy.symm
  let S : Finset V :=
    p.support.toFinset ∪ a.support.toFinset ∪ b.support.toFinset
  have hmeet : {t ∈ S | t ∈ r.support}.Nonempty := by
    refine ⟨y, ?_⟩
    simp [S]
  obtain ⟨u, huS, huR, hfirst⟩ :=
    r.exists_mem_support_forall_mem_support_imp_eq S hmeet
  let q : G.Walk x u := r.takeUntil u huR
  refine ⟨u, q, hr.takeUntil huR, ?_, huS, ?_⟩
  · intro hvq
    exact hrv (r.support_takeUntil_subset_support huR hvq)
  · intro t htS htq
    exact hfirst t htS htq

omit [Fintype V] in
/-- Starting at a reference vertex, walk forward to the first point on
either old branch.  Its support is a contiguous segment of the reference. -/
lemma exists_first_branch_hit_along_reference
    {v y z u : V} (p : G.Walk v y) (hp : p.IsPath)
    (a : G.Walk v z) (b : G.Walk v y) (hu : u ∈ p.support) :
    ∃ (w : V) (r : G.Walk u w),
      r.IsPath ∧ r.support.IsInfix p.support ∧
      w ∈ a.support.toFinset ∪ b.support.toFinset ∧
      (∀ t, t ∈ a.support.toFinset ∪ b.support.toFinset →
        t ∈ r.support → t = w) := by
  let d : G.Walk u y := p.dropUntil u hu
  let S : Finset V := a.support.toFinset ∪ b.support.toFinset
  have hmeet : {t ∈ S | t ∈ d.support}.Nonempty := by
    refine ⟨y, ?_⟩
    simp [S, d]
  obtain ⟨w, hwS, hwd, hfirst⟩ :=
    d.exists_mem_support_forall_mem_support_imp_eq S hmeet
  let r : G.Walk u w := d.takeUntil w hwd
  refine ⟨w, r, (hp.dropUntil hu).takeUntil hwd, ?_, hwS, ?_⟩
  · exact (d.support_takeUntil_prefix_support hwd).isInfix.trans
      (p.support_dropUntil_suffix_support hu).isInfix
  · intro t htS htr
    exact hfirst t htS htr

namespace AlignedFan

/-- Indirect Case 2: the connector first hits the reference path, then a
forward reference segment first hits the old `z` branch. -/
noncomputable def lift_indirect_toZ {x v y z u w : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p)
    (hp : p.IsPath) (hxp : x ∉ p.support) (hxZ : x ∉ F.toZ.support)
    (hxY : x ∉ F.toY.support)
    (q : G.Walk x u) (t : G.Walk u w) (hq : q.IsPath) (ht : t.IsPath)
    (hqv : v ∉ q.support) (huP : u ∈ p.support)
    (huZ : u ∉ F.toZ.support) (huY : u ∉ F.toY.support)
    (hwZ : w ∈ F.toZ.support) (hwP : w ∈ p.support)
    (hvw : v ≠ w) (htinfix : t.support <:+: p.support)
    (hfirstP : ∀ a, a ∈ p.support → a ∈ q.support → a = u)
    (hfirstZq : ∀ a, a ∈ F.toZ.support → a ∈ q.support → a = u)
    (hfirstYq : ∀ a, a ∈ F.toY.support → a ∈ q.support → a = u)
    (hfirstZt : ∀ a, a ∈ F.toZ.support → a ∈ t.support → a = w)
    (hfirstYt : ∀ a, a ∈ F.toY.support → a ∈ t.support → a = w) :
    AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := (q.append t).append (F.toZ.dropUntil w hwZ)
  let ry : G.Walk x y := Walk.cons h F.toY
  have hqr : ∀ a, a ∈ q.support → a ∈ t.support → a = u := by
    intro a haq hat
    exact hfirstP a (htinfix.subset hat) haq
  have hrz : rz.IsPath := isPath_indirect_splice hq ht F.toZ_isPath hwZ
    hqr (fun a haq haZ => hfirstZq a haZ haq) huZ
    (fun a hat haZ => hfirstZt a haZ hat)
  have hry : ry.IsPath := (Walk.cons_isPath_iff h F.toY).2
    ⟨F.toY_isPath, hxY⟩
  have hwY : w ∉ F.toY.support := by
    intro hwY
    exact hvw (F.meet_eq_start hwZ hwY).symm
  have hvSuffix : v ∉ (F.toZ.dropUntil w hwZ).support :=
    start_not_mem_dropUntil_of_ne F.toZ_isPath hwZ hvw.symm
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := ?_
      toY_aligned := aligned_cons hxp hxY F.toY_aligned }
  · intro a haZ haY
    simp only [ry, Walk.support_cons, List.mem_cons] at haY
    rcases haY with rfl | haY
    · rfl
    · simp only [rz, Walk.mem_support_append_iff] at haZ
      rcases haZ with haqt | haS
      · rcases haqt with haq | hat
        · have hau : a = u := hfirstYq a haY haq
          exact (huY (hau ▸ haY)).elim
        · have haw : a = w := hfirstYt a haY hat
          exact (hwY (haw ▸ haY)).elim
      · have haOldZ := F.toZ.support_dropUntil_subset_support hwZ haS
        have hav : a = v := F.meet_eq_start haOldZ haY
        exact (hvSuffix (hav ▸ haS)).elim
  · exact aligned_cons_indirect_splice hxp hxZ hp hq huP
      hfirstP htinfix hwZ hwP F.toZ_aligned

/-- Symmetric indirect Case 2, with the forward reference segment first
hitting the old `y` branch. -/
noncomputable def lift_indirect_toY {x v y z u w : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p)
    (hp : p.IsPath) (hxp : x ∉ p.support) (hxZ : x ∉ F.toZ.support)
    (hxY : x ∉ F.toY.support)
    (q : G.Walk x u) (t : G.Walk u w) (hq : q.IsPath) (ht : t.IsPath)
    (hqv : v ∉ q.support) (huP : u ∈ p.support)
    (huZ : u ∉ F.toZ.support) (huY : u ∉ F.toY.support)
    (hwY : w ∈ F.toY.support) (hwP : w ∈ p.support)
    (hvw : v ≠ w) (htinfix : t.support <:+: p.support)
    (hfirstP : ∀ a, a ∈ p.support → a ∈ q.support → a = u)
    (hfirstZq : ∀ a, a ∈ F.toZ.support → a ∈ q.support → a = u)
    (hfirstYq : ∀ a, a ∈ F.toY.support → a ∈ q.support → a = u)
    (hfirstZt : ∀ a, a ∈ F.toZ.support → a ∈ t.support → a = w)
    (hfirstYt : ∀ a, a ∈ F.toY.support → a ∈ t.support → a = w) :
    AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := Walk.cons h F.toZ
  let ry : G.Walk x y := (q.append t).append (F.toY.dropUntil w hwY)
  have hqr : ∀ a, a ∈ q.support → a ∈ t.support → a = u := by
    intro a haq hat
    exact hfirstP a (htinfix.subset hat) haq
  have hrz : rz.IsPath := (Walk.cons_isPath_iff h F.toZ).2
    ⟨F.toZ_isPath, hxZ⟩
  have hry : ry.IsPath := isPath_indirect_splice hq ht F.toY_isPath hwY
    hqr (fun a haq haY => hfirstYq a haY haq) huY
    (fun a hat haY => hfirstYt a haY hat)
  have hwZ : w ∉ F.toZ.support := by
    intro hwZ
    exact hvw (F.meet_eq_start hwZ hwY).symm
  have hvSuffix : v ∉ (F.toY.dropUntil w hwY).support :=
    start_not_mem_dropUntil_of_ne F.toY_isPath hwY hvw.symm
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := aligned_cons hxp hxZ F.toZ_aligned
      toY_aligned := ?_ }
  · intro a haZ haY
    simp only [rz, Walk.support_cons, List.mem_cons] at haZ
    rcases haZ with rfl | haZ
    · rfl
    · simp only [ry, Walk.mem_support_append_iff] at haY
      rcases haY with haqt | haS
      · rcases haqt with haq | hat
        · have hau : a = u := hfirstZq a haZ haq
          exact (huZ (hau ▸ haZ)).elim
        · have haw : a = w := hfirstZt a haZ hat
          exact (hwZ (haw ▸ haZ)).elim
      · have haOldY := F.toY.support_dropUntil_subset_support hwY haS
        have hav : a = v := F.meet_eq_start haZ haOldY
        exact (hvSuffix (hav ▸ haS)).elim
  · exact aligned_cons_indirect_splice hxp hxY hp hq huP
      hfirstP htinfix hwY hwP F.toY_aligned

/-- Case 2 when the first connector hits the old `z`-branch directly. -/
noncomputable def lift_of_first_hit_toZ {x v y z u : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p)
    (hxp : x ∉ p.support) (hxZ : x ∉ F.toZ.support)
    (hxY : x ∉ F.toY.support) (q : G.Walk x u) (hq : q.IsPath)
    (hqv : v ∉ q.support) (huZ : u ∈ F.toZ.support)
    (hfirstP : ∀ w, w ∈ p.support → w ∈ q.support → w = u)
    (hfirstZ : ∀ w, w ∈ F.toZ.support → w ∈ q.support → w = u)
    (hfirstY : ∀ w, w ∈ F.toY.support → w ∈ q.support → w = u) :
    AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := q.append (F.toZ.dropUntil u huZ)
  let ry : G.Walk x y := Walk.cons h F.toY
  have huv : u ≠ v := by
    intro huv
    exact hqv (huv ▸ q.end_mem_support)
  have hvSuffix : v ∉ (F.toZ.dropUntil u huZ).support :=
    start_not_mem_dropUntil_of_ne F.toZ_isPath huZ huv
  have hrz : rz.IsPath :=
    isPath_append_dropUntil_of_first_hit hq F.toZ_isPath huZ hfirstZ
  have hry : ry.IsPath := (Walk.cons_isPath_iff h F.toY).2
    ⟨F.toY_isPath, hxY⟩
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := ?_
      toY_aligned := aligned_cons hxp hxY F.toY_aligned }
  · intro w hwz hwy
    simp only [ry, Walk.support_cons, List.mem_cons] at hwy
    rcases hwy with rfl | hwy
    · rfl
    · simp only [rz, Walk.mem_support_append_iff] at hwz
      rcases hwz with hwq | hwS
      · have hwu : w = u := hfirstY w hwy hwq
        have huY : u ∈ F.toY.support := hwu ▸ hwy
        have huv' : u = v := F.meet_eq_start huZ huY
        exact (hqv (huv' ▸ q.end_mem_support)).elim
      · have hwZ : w ∈ F.toZ.support :=
          F.toZ.support_dropUntil_subset_support huZ hwS
        have hwv : w = v := F.meet_eq_start hwZ hwy
        exact (hvSuffix (hwv ▸ hwS)).elim
  · exact aligned_cons_append_dropUntil_of_first_hit hxp hxZ hq
      F.toZ_aligned huZ hfirstP

/-- Case 2 when the first connector hits the old `y`-branch directly. -/
noncomputable def lift_of_first_hit_toY {x v y z u : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p)
    (hxp : x ∉ p.support) (hxZ : x ∉ F.toZ.support)
    (hxY : x ∉ F.toY.support) (q : G.Walk x u) (hq : q.IsPath)
    (hqv : v ∉ q.support) (huY : u ∈ F.toY.support)
    (hfirstP : ∀ w, w ∈ p.support → w ∈ q.support → w = u)
    (hfirstZ : ∀ w, w ∈ F.toZ.support → w ∈ q.support → w = u)
    (hfirstY : ∀ w, w ∈ F.toY.support → w ∈ q.support → w = u) :
    AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := Walk.cons h F.toZ
  let ry : G.Walk x y := q.append (F.toY.dropUntil u huY)
  have huv : u ≠ v := by
    intro huv
    exact hqv (huv ▸ q.end_mem_support)
  have hvSuffix : v ∉ (F.toY.dropUntil u huY).support :=
    start_not_mem_dropUntil_of_ne F.toY_isPath huY huv
  have hrz : rz.IsPath := (Walk.cons_isPath_iff h F.toZ).2
    ⟨F.toZ_isPath, hxZ⟩
  have hry : ry.IsPath :=
    isPath_append_dropUntil_of_first_hit hq F.toY_isPath huY hfirstY
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := aligned_cons hxp hxZ F.toZ_aligned
      toY_aligned := ?_ }
  · intro w hwz hwy
    simp only [rz, Walk.support_cons, List.mem_cons] at hwz
    rcases hwz with rfl | hwz
    · rfl
    · simp only [ry, Walk.mem_support_append_iff] at hwy
      rcases hwy with hwq | hwS
      · have hwu : w = u := hfirstZ w hwz hwq
        have huZ : u ∈ F.toZ.support := hwu ▸ hwz
        have huv' : u = v := F.meet_eq_start huZ huY
        exact (hqv (huv' ▸ q.end_mem_support)).elim
      · have hwY : w ∈ F.toY.support :=
          F.toY.support_dropUntil_subset_support huY hwS
        have hwv : w = v := F.meet_eq_start hwz hwY
        exact (hvSuffix (hwv ▸ hwS)).elim
  · exact aligned_cons_append_dropUntil_of_first_hit hxp hxY hq
      F.toY_aligned huY hfirstP

/-- The inductive construction when the new reference-path initial vertex
already occurs on the `z` branch.  This is Case 1 of Dirac's proof. -/
noncomputable def lift_of_mem_toZ {x v y z : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p) (hxp : x ∉ p.support)
    (hx : x ∈ F.toZ.support) : AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := F.toZ.dropUntil x hx
  let ry : G.Walk x y := Walk.cons h F.toY
  have hx_toY : x ∉ F.toY.support := by
    intro hxY
    have hxv : x = v := F.meet_eq_start hx hxY
    exact h.ne hxv
  have hrz : rz.IsPath := F.toZ_isPath.dropUntil hx
  have hry : ry.IsPath := (Walk.cons_isPath_iff h F.toY).2
    ⟨F.toY_isPath, hx_toY⟩
  have hv_rz : v ∉ rz.support := by
    intro hv
    obtain ⟨t, ht⟩ := F.toZ.support_dropUntil_suffix_support hx
    have hnd : (t ++ rz.support).Nodup := by
      rw [ht]
      exact F.toZ_isPath.support_nodup
    have hsep := (List.nodup_append.mp hnd).2.2
    cases t with
    | nil =>
        have hsupport : rz.support = F.toZ.support := by simpa using ht
        have hxv : x = v := by
          calc
            x = rz.support.head rz.support_ne_nil := rz.head_support.symm
            _ = F.toZ.support.head F.toZ.support_ne_nil := by
              simp only [hsupport]
            _ = v := F.toZ.head_support
        exact h.ne hxv
    | cons a t =>
        have hav : a = v := by
          have hcons : a :: (t ++ rz.support) = v :: F.toZ.support.tail := by
            simpa [F.toZ.cons_tail_support] using ht
          exact List.cons.inj hcons |>.1
        exact hsep a (by simp) v hv hav
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := ?_
      toY_aligned := ?_ }
  · intro w hwz hwy
    simp only [ry, Walk.support_cons, List.mem_cons] at hwy
    rcases hwy with rfl | hwy
    · rfl
    · have hwz' : w ∈ F.toZ.support :=
        F.toZ.support_dropUntil_subset_support hx hwz
      have hwv : w = v := F.meet_eq_start hwz' hwy
      exact (hv_rz (hwv ▸ hwz)).elim
  · have hxrz : x ∉ rz.support.tail := by
      intro hxTail
      have hne := hrz.support_nodup.rel_head_tail hxTail
      exact hne (by simp only [rz.head_support])
    apply aligned_cons_left hxp hxrz
    exact aligned_dropUntil F.toZ_aligned hx
  · exact aligned_cons hxp hx_toY F.toY_aligned

/-- Symmetric Case 1: the new initial vertex occurs on the `y` branch. -/
noncomputable def lift_of_mem_toY {x v y z : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p) (hxp : x ∉ p.support)
    (hx : x ∈ F.toY.support) : AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := Walk.cons h F.toZ
  let ry : G.Walk x y := F.toY.dropUntil x hx
  have hx_toZ : x ∉ F.toZ.support := by
    intro hxZ
    have hxv : x = v := F.meet_eq_start hxZ hx
    exact h.ne hxv
  have hrz : rz.IsPath := (Walk.cons_isPath_iff h F.toZ).2
    ⟨F.toZ_isPath, hx_toZ⟩
  have hry : ry.IsPath := F.toY_isPath.dropUntil hx
  have hv_ry : v ∉ ry.support := by
    intro hv
    obtain ⟨t, ht⟩ := F.toY.support_dropUntil_suffix_support hx
    have hnd : (t ++ ry.support).Nodup := by
      rw [ht]
      exact F.toY_isPath.support_nodup
    have hsep := (List.nodup_append.mp hnd).2.2
    cases t with
    | nil =>
        have hsupport : ry.support = F.toY.support := by simpa using ht
        have hxv : x = v := by
          calc
            x = ry.support.head ry.support_ne_nil := ry.head_support.symm
            _ = F.toY.support.head F.toY.support_ne_nil := by
              simp only [hsupport]
            _ = v := F.toY.head_support
        exact h.ne hxv
    | cons a t =>
        have hav : a = v := by
          have hcons : a :: (t ++ ry.support) = v :: F.toY.support.tail := by
            simpa [F.toY.cons_tail_support] using ht
          exact List.cons.inj hcons |>.1
        exact hsep a (by simp) v hv hav
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := ?_
      toY_aligned := ?_ }
  · intro w hwz hwy
    simp only [rz, Walk.support_cons, List.mem_cons] at hwz
    rcases hwz with rfl | hwz
    · rfl
    · have hwy' : w ∈ F.toY.support :=
        F.toY.support_dropUntil_subset_support hx hwy
      have hwv : w = v := F.meet_eq_start hwz hwy'
      exact (hv_ry (hwv ▸ hwy)).elim
  · exact aligned_cons hxp hx_toZ F.toZ_aligned
  · have hxry : x ∉ ry.support.tail := by
      intro hxTail
      have hne := hry.support_nodup.rel_head_tail hxTail
      exact hne (by simp only [ry.head_support])
    apply aligned_cons_left hxp hxry
    exact aligned_dropUntil F.toY_aligned hx

end AlignedFan

/-- The initial-vertex case of the aligned-fan lemma. -/
noncomputable def AlignedFan.atStart {x y : V} (p : G.Walk x y)
    (hp : p.IsPath) : AlignedFan (z := x) p :=
  { toZ := .nil
    toY := p
    toZ_isPath := .nil
    toY_isPath := hp
    meet_eq_start := by
      intro w hw _
      simpa using hw
    toZ_aligned := aligned_nil p
    toY_aligned := aligned_refl p }

omit [Fintype V] [DecidableEq V] in
/-- An infix of a simple path which starts away from the path's initial
vertex cannot contain that initial vertex. -/
lemma start_not_mem_of_support_infix {v y u w : V}
    {p : G.Walk v y} {t : G.Walk u w} (hp : p.IsPath)
    (ht : t.support.IsInfix p.support) (huv : u ≠ v) :
    v ∉ t.support := by
  intro hvt
  obtain ⟨pre, post, hsplit⟩ := ht
  have hnd : (pre ++ t.support ++ post).Nodup := by
    rw [hsplit]
    exact hp.support_nodup
  cases pre with
  | nil =>
      have hcons : u :: (t.support.tail ++ post) = v :: p.support.tail := by
        calc
          u :: (t.support.tail ++ post) = (u :: t.support.tail) ++ post := rfl
          _ = t.support ++ post := by rw [t.cons_tail_support]
          _ = p.support := hsplit
          _ = v :: p.support.tail := p.cons_tail_support.symm
      exact huv (List.cons.inj hcons).1
  | cons a pre =>
      have hav : a = v := by
        have hcons : a :: (pre ++ t.support ++ post) =
            v :: p.support.tail := by
          simpa [p.cons_tail_support] using hsplit
        exact (List.cons.inj hcons).1
      have hnd' : (a :: (pre ++ t.support ++ post)).Nodup := by
        simpa only [List.cons_append, List.append_assoc] using hnd
      exact (List.nodup_cons.mp hnd').1 (by simp [hav, hvt])

/-- Dirac's aligned-two-path lemma, in the endpoint-distinct form used by
the lollipop proof. -/
theorem exists_alignedFan (hG : Erdos58.TwoConnected G) :
    ∀ {x y : V} (p : G.Walk x y), p.IsPath →
      ∀ {z : V}, z ∈ p.support → z ≠ y →
        Nonempty (AlignedFan (z := z) p) := by
  intro x y p
  induction p with
  | nil =>
      intro _ z hz hzy
      exact (hzy (by simpa using hz)).elim
  | @cons x v y h p ih =>
      intro hpath z hz hzy
      have hp : p.IsPath := (Walk.cons_isPath_iff h p).mp hpath |>.1
      have hxp : x ∉ p.support := (Walk.cons_isPath_iff h p).mp hpath |>.2
      by_cases hzx : z = x
      · subst z
        exact ⟨AlignedFan.atStart (Walk.cons h p) hpath⟩
      have hzp : z ∈ p.support := by
        simpa only [Walk.support_cons, List.mem_cons, hzx, false_or] using hz
      obtain ⟨F⟩ := ih hp hzp hzy
      by_cases hxZ : x ∈ F.toZ.support
      · exact ⟨F.lift_of_mem_toZ hxp hxZ⟩
      by_cases hxY : x ∈ F.toY.support
      · exact ⟨F.lift_of_mem_toY hxp hxY⟩
      have hvy : v ≠ y := by
        intro hvy
        subst y
        have hpNil : p = .nil := (Walk.isPath_iff_nil.mp hp).eq_nil
        subst p
        have hzv : z = v := by simpa using hzp
        exact hzy hzv
      obtain ⟨u, q, hq, hqv, huS, hfirst⟩ :=
        exists_first_connector hG h p hvy F.toZ F.toY
      have hfirstP : ∀ a, a ∈ p.support → a ∈ q.support → a = u := by
        intro a ha haq
        apply hfirst a
        · simp only [Finset.mem_union, List.mem_toFinset]
          exact Or.inl (Or.inl ha)
        · exact haq
      have hfirstZ : ∀ a, a ∈ F.toZ.support → a ∈ q.support → a = u := by
        intro a ha haq
        apply hfirst a
        · simp only [Finset.mem_union, List.mem_toFinset]
          exact Or.inl (Or.inr ha)
        · exact haq
      have hfirstY : ∀ a, a ∈ F.toY.support → a ∈ q.support → a = u := by
        intro a ha haq
        apply hfirst a
        · simp only [Finset.mem_union, List.mem_toFinset]
          exact Or.inr ha
        · exact haq
      simp only [Finset.mem_union, List.mem_toFinset] at huS
      rcases huS with (huP | huZ) | huY
      · by_cases huZ' : u ∈ F.toZ.support
        · exact ⟨F.lift_of_first_hit_toZ hxp hxZ hxY q hq hqv huZ'
            hfirstP hfirstZ hfirstY⟩
        by_cases huY' : u ∈ F.toY.support
        · exact ⟨F.lift_of_first_hit_toY hxp hxZ hxY q hq hqv huY'
            hfirstP hfirstZ hfirstY⟩
        have huZn : u ∉ F.toZ.support := huZ'
        have huYn : u ∉ F.toY.support := huY'
        obtain ⟨w, t, ht, htinfix, hwS, hfirstT⟩ :=
          exists_first_branch_hit_along_reference p hp F.toZ F.toY huP
        have hfirstZT : ∀ a, a ∈ F.toZ.support → a ∈ t.support → a = w := by
          intro a ha hat
          apply hfirstT a
          · simp only [Finset.mem_union, List.mem_toFinset]
            exact Or.inl ha
          · exact hat
        have hfirstYT : ∀ a, a ∈ F.toY.support → a ∈ t.support → a = w := by
          intro a ha hat
          apply hfirstT a
          · simp only [Finset.mem_union, List.mem_toFinset]
            exact Or.inr ha
          · exact hat
        have huv : u ≠ v := by
          intro huv
          exact hqv (huv ▸ q.end_mem_support)
        have hvw : v ≠ w := by
          intro hvw
          subst w
          exact start_not_mem_of_support_infix hp htinfix huv
            t.end_mem_support
        have hwP : w ∈ p.support := htinfix.subset t.end_mem_support
        simp only [Finset.mem_union, List.mem_toFinset] at hwS
        rcases hwS with hwZ | hwY
        · exact ⟨F.lift_indirect_toZ hp hxp hxZ hxY q t hq ht hqv huP
            huZn huYn hwZ hwP hvw htinfix hfirstP hfirstZ hfirstY
            hfirstZT hfirstYT⟩
        · exact ⟨F.lift_indirect_toY hp hxp hxZ hxY q t hq ht hqv huP
            huZn huYn hwY hwP hvw htinfix hfirstP hfirstZ hfirstY
            hfirstZT hfirstYT⟩
      · exact ⟨F.lift_of_first_hit_toZ hxp hxZ hxY q hq hqv huZ
          hfirstP hfirstZ hfirstY⟩
      · exact ⟨F.lift_of_first_hit_toY hxp hxZ hxY q hq hqv huY
          hfirstP hfirstZ hfirstY⟩

end E767AlignedAlt

#print axioms E767AlignedAlt.exists_alignedFan

-- END Aligned

-- BEGIN LongestCycle
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Finite longest paths and cycles for Erdős Problem 767

This file contains the small, self-contained maximum-path and maximum-cycle
interface used by the proof of Erdős Problem 767.  Keeping it local prevents
the formalization from depending on another Erdős-problem development.
-/

open Finset Set
open scoped SimpleGraph

namespace Erdos767LongestCycle

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path of maximum length among all paths in the graph. -/
def IsLongestPath {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧
    ∀ ⦃u v : V⦄ (q : G.Walk u v), q.IsPath → q.length ≤ p.length

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- Every nonempty finite graph has a longest path. -/
theorem exists_isLongestPath [Finite V] [Nonempty V] :
    ∃ (a b : V) (p : G.Walk a b), IsLongestPath p := by
  obtain ⟨a, b, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  exact ⟨a, b, p, hp, fun {_ _} q hq ↦ hmax _ _ q hq⟩

omit [Fintype V] [DecidableRel G.Adj] [DecidableEq V] in
/-- Every neighbor of the terminal endpoint of a longest path already lies
on the path. -/
theorem IsLongestPath.end_neighbor_mem_support {a b z : V}
    {p : G.Walk a b} (hp : IsLongestPath p) (hbz : G.Adj b z) :
    z ∈ p.support := by
  classical
  by_contra hz
  have hlonger : (p.concat hbz).IsPath := hp.1.concat hz hbz
  have hle := hp.2 (p.concat hbz) hlonger
  simp at hle

/-- The terminal neighbor set of a longest path lies in its support with the
terminal endpoint removed. -/
theorem IsLongestPath.neighborFinset_end_subset_erase {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) :
    G.neighborFinset b ⊆ p.support.toFinset.erase b := by
  intro z hz
  have hbz : G.Adj b z := (G.mem_neighborFinset b z).mp hz
  exact Finset.mem_erase.mpr
    ⟨hbz.ne.symm, List.mem_toFinset.mpr (hp.end_neighbor_mem_support hbz)⟩

omit [DecidableEq V] in
/-- The degree of the terminal endpoint is at most the length of a longest
path. -/
theorem IsLongestPath.degree_end_le_length {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) :
    G.degree b ≤ p.length := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset b).card ≤ (p.support.toFinset.erase b).card :=
      Finset.card_le_card hp.neighborFinset_end_subset_erase
    _ = p.length := by
      rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr p.end_mem_support)]
      rw [List.toFinset_card_of_nodup hp.1.support_nodup, p.length_support]
      omega

/-- A genuine cycle of maximum length. -/
def IsLongestCycle {z : V} (c : G.Walk z z) : Prop :=
  c.IsCycle ∧
    ∀ ⦃z' : V⦄ (c' : G.Walk z' z'), c'.IsCycle → c'.length ≤ c.length

omit [DecidableRel G.Adj] [DecidableEq V] in
/-- The length of a simple cycle is at most the order of the graph. -/
lemma isCycle_length_le_card {z : V} {c : G.Walk z z} (hc : c.IsCycle) :
    c.length ≤ Fintype.card V := by
  classical
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hsub : c.support.tail.toFinset ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnodup, Finset.card_univ] at hcard
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, c.length_support]
    omega
  simpa [hlen] using hcard

/-- The finite set of lengths of genuine cycles in `G`. -/
def cycleLengths (G : SimpleGraph V) : Finset ℕ :=
  (Finset.range (Fintype.card V + 1)).filter fun m ↦
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = m

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma mem_cycleLengths_iff {m : ℕ} :
    m ∈ cycleLengths G ↔
      ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = m := by
  classical
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).2
  · rintro ⟨z, c, hc, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (isCycle_length_le_card hc)),
      ⟨z, c, hc, rfl⟩⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A finite two-connected graph has a longest cycle. -/
theorem exists_isLongestCycle (hTwo : Erdos58.TwoConnected G) :
    ∃ (z : V) (c : G.Walk z z), IsLongestCycle c := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by
    have := hTwo.card_three_le
    omega)
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨y, hyx⟩ := hTwo.exists_ne x
  obtain ⟨p, hp⟩ := hTwo.connected.exists_isPath x y
  have hpnon : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hyx.symm
  have hxp : G.Adj x p.snd := p.adj_snd hpnon
  obtain ⟨c₀, hc₀, -⟩ := hTwo.exists_cycle_through_edge hxp
  have hnonempty : (cycleLengths G).Nonempty := by
    exact ⟨c₀.length, mem_cycleLengths_iff.mpr ⟨x, c₀, hc₀, rfl⟩⟩
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_max_image (cycleLengths G) id hnonempty
  obtain ⟨z, c, hc, hcm⟩ := mem_cycleLengths_iff.mp hm
  subst m
  refine ⟨z, c, hc, ?_⟩
  intro z' c' hc'
  have hc'mem := mem_cycleLengths_iff.mpr ⟨z', c', hc', rfl⟩
  simpa using hmax c'.length hc'mem

omit [Fintype V] [DecidableRel G.Adj] in
/-- The finite carrier of a genuine cycle has cardinality equal to its
length: the base vertex is the sole repetition in the closed support. -/
lemma cycleCarrier_card {z : V} {c : G.Walk z z} (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have hz : z ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
  rw [← c.cons_tail_support, List.toFinset_cons, Finset.insert_eq_of_mem
    (List.mem_toFinset.mpr hz), List.toFinset_card_of_nodup hc.support_nodup]
  rw [List.length_tail, c.length_support]
  omega

omit [DecidableRel G.Adj] [Fintype V] in
/-- A cycle lifted to the graph induced on its carrier is Hamiltonian. -/
lemma induced_cycle_isHamiltonianCycle {z : V} {c : G.Walk z z}
    (hc : c.IsCycle) :
    let C := c.support.toFinset
    let hC : ∀ x ∈ c.support, x ∈ (C : Set V) := fun _x hx ↦
      List.mem_toFinset.mpr hx
    (c.induce (C : Set V) hC).IsHamiltonianCycle := by
  classical
  dsimp only
  let C := c.support.toFinset
  let hC : ∀ x ∈ c.support, x ∈ (C : Set V) := fun x hx ↦
    List.mem_toFinset.mpr hx
  let q := c.induce (C : Set V) hC
  have hmap : q.map
      (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom = c := by
    change (c.induce (C : Set V) hC).map
      (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom = c
    exact SimpleGraph.Walk.map_induce c hC
  have hqcycle : q.IsCycle := by
    apply (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (p := q)
      (f := (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom)
      (SimpleGraph.Embedding.induce (G := G) (C : Set V)).injective).mp
    rw [hmap]
    exact hc
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨hqcycle, ?_⟩
  have hcardC : Fintype.card (C : Set V) = c.length := by
    exact (Fintype.card_coe C).trans (cycleCarrier_card hc)
  change q.length = Fintype.card (C : Set V)
  rw [hcardC]
  have hlength := congrArg SimpleGraph.Walk.length hmap
  rw [SimpleGraph.Walk.length_map] at hlength
  exact hlength

end

end Erdos767LongestCycle
-- END LongestCycle

-- BEGIN Lollipop

open scoped SimpleGraph

namespace Erdos767Scratch

open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A cycle together with a simple path whose only cycle vertex is its
initial vertex.  The terminal vertex is allowed to equal the initial vertex,
so every cycle has the degenerate lollipop with a nil tail. -/
structure Lollipop (G : SimpleGraph V) where
  cycleBase : V
  cycle : G.Walk cycleBase cycleBase
  cycle_isCycle : cycle.IsCycle
  start : V
  terminal : V
  tail : G.Walk start terminal
  tail_isPath : tail.IsPath
  start_mem_cycle : start ∈ cycle.support
  cycle_tail_inter : ∀ {x : V}, x ∈ cycle.support → x ∈ tail.support → x = start

namespace Lollipop

/-- The degenerate lollipop with nil tail based at the base vertex of a
cycle. -/
def nilOfCycle {z : V} (c : G.Walk z z) (hc : c.IsCycle) : Lollipop G where
  cycleBase := z
  cycle := c
  cycle_isCycle := hc
  start := z
  terminal := z
  tail := .nil
  tail_isPath := by simp
  start_mem_cycle := c.start_mem_support
  cycle_tail_inter := by
    intro x _hxC hxP
    simpa using hxP

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma nilOfCycle_cycle {z : V} (c : G.Walk z z) (hc : c.IsCycle) :
    (nilOfCycle c hc).cycle = c := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma nilOfCycle_tail_length {z : V} (c : G.Walk z z) (hc : c.IsCycle) :
    (nilOfCycle c hc).tail.length = 0 := rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- Finset form of the defining intersection condition. -/
lemma cycle_support_inter_tail_support (L : Lollipop G) :
    L.cycle.support.toFinset ∩ L.tail.support.toFinset = {L.start} := by
  ext x
  constructor
  · intro hx
    have hxC : x ∈ L.cycle.support := List.mem_toFinset.mp (Finset.mem_inter.mp hx).1
    have hxP : x ∈ L.tail.support := List.mem_toFinset.mp (Finset.mem_inter.mp hx).2
    simpa using L.cycle_tail_inter hxC hxP
  · intro hx
    have hxs : x = L.start := by simpa using hx
    subst x
    exact Finset.mem_inter.mpr
      ⟨List.mem_toFinset.mpr L.start_mem_cycle,
        List.mem_toFinset.mpr L.tail.start_mem_support⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The tail of a lollipop is shorter than the number of ambient vertices. -/
lemma tail_length_lt_card (L : Lollipop G) :
    L.tail.length < Fintype.card V :=
  L.tail_isPath.length_lt

end Lollipop

/-- A lexicographically best lollipop: its cycle is globally longest and,
among lollipops on a cycle of that length, its tail is globally longest. -/
structure BestLollipop (G : SimpleGraph V) extends Lollipop G where
  cycle_maximal : ∀ {z : V} (c : G.Walk z z), c.IsCycle → c.length ≤ cycle.length
  tail_maximal : ∀ (L : Lollipop G),
    L.cycle.length = cycle.length → L.tail.length ≤ tail.length

namespace BestLollipop

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A path from a vertex in a set to a vertex outside it contains an edge
crossing from the set to its complement. -/
lemma exists_crossing_edge_of_walk {a b : V} (S : Set V)
    (p : G.Walk a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ G.Adj x y := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a x b hax p ih =>
      by_cases hx : x ∈ S
      · exact ih hx hb
      · exact ⟨a, x, ha, hx, hax⟩

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- In a connected graph, every nonempty proper vertex set has a crossing
edge. -/
lemma exists_crossing_edge_of_connected (hconn : G.Connected) (S : Set V)
    {a b : V} (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ G.Adj x y := by
  classical
  obtain ⟨p, _hp⟩ := hconn.exists_isPath a b
  exact exists_crossing_edge_of_walk S p ha hb

/-- A crossing edge from a cycle to its complement is a positive lollipop
tail of length one. -/
def ofCycleCrossingEdge {z x y : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∉ c.support) (hxy : G.Adj x y) : Lollipop G where
  cycleBase := z
  cycle := c
  cycle_isCycle := hc
  start := x
  terminal := y
  tail := hxy.toWalk
  tail_isPath := hxy.isPath_toWalk
  start_mem_cycle := hx
  cycle_tail_inter := by
    intro w hwC hwP
    simp only [Adj.support_toWalk, List.mem_cons] at hwP
    rcases hwP with rfl | hwP
    · rfl
    · rcases hwP with rfl | hwP
      · exact (hy hwC).elim
      · simp at hwP

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma ofCycleCrossingEdge_tail_length {z x y : V}
    (c : G.Walk z z) (hc : c.IsCycle) (hx : x ∈ c.support)
    (hy : y ∉ c.support) (hxy : G.Adj x y) :
    (ofCycleCrossingEdge c hc hx hy hxy).tail.length = 1 := by
  simp [ofCycleCrossingEdge]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A lexicographically best lollipop exists in every finite two-connected
graph. -/
theorem exists_bestLollipop (hTwo : Erdos58.TwoConnected G) :
    Nonempty (BestLollipop G) := by
  classical
  obtain ⟨z, c, hc⟩ := Erdos767LongestCycle.exists_isLongestCycle hTwo
  let T : Set ℕ := {n | ∃ L : Lollipop G,
    L.cycle.length = c.length ∧ L.tail.length = n}
  have hTfinite : T.Finite := by
    apply Set.Finite.subset (Set.finite_le_nat (Fintype.card V))
    intro n hn
    obtain ⟨L, _hLc, rfl⟩ := hn
    exact L.tail_length_lt_card.le
  have hTnonempty : T.Nonempty := by
    refine ⟨0, Lollipop.nilOfCycle c hc.1, ?_, rfl⟩
    rfl
  obtain ⟨m, hm, hmmax⟩ := hTfinite.exists_maximal hTnonempty
  obtain ⟨L, hLcycle, hLtail⟩ := hm
  refine ⟨{
    toLollipop := L
    cycle_maximal := ?_
    tail_maximal := ?_ }⟩
  · intro z' c' hc'
    rw [hLcycle]
    exact hc.2 c' hc'
  · intro L' hL'cycle
    have hmem : L'.tail.length ∈ T := by
      exact ⟨L', hL'cycle.trans hLcycle, rfl⟩
    rw [hLtail]
    rcases le_total L'.tail.length m with hle | hge
    · exact hle
    · exact hmmax hmem hge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The selected cycle is globally longest (standalone projection form). -/
lemma isLongestCycle (B : BestLollipop G) :
    Erdos767LongestCycle.IsLongestCycle B.cycle := by
  refine ⟨B.cycle_isCycle, ?_⟩
  intro z' c' hc'
  exact B.cycle_maximal c' hc'

omit [DecidableRel G.Adj] in
/-- If the selected longest cycle is nonspanning, connectedness gives a
crossing edge and tail maximality forces the selected tail to be positive. -/
lemma tail_length_pos_of_cycle_not_spanning (hTwo : Erdos58.TwoConnected G)
    (B : BestLollipop G)
    (hnotspan : B.cycle.support.toFinset ≠ (Finset.univ : Finset V)) :
    0 < B.tail.length := by
  classical
  have hproper : ∃ y : V, y ∉ B.cycle.support := by
    by_contra h
    apply hnotspan
    ext y
    have hy : y ∈ B.cycle.support := not_not.mp (not_exists.mp h y)
    simp [hy]
  obtain ⟨y, hy⟩ := hproper
  obtain ⟨x, w, hx, hw, hxw⟩ := exists_crossing_edge_of_connected
    hTwo.connected ({v : V | v ∈ B.cycle.support})
    B.cycle.start_mem_support hy
  let L := ofCycleCrossingEdge B.cycle B.cycle_isCycle hx hw hxw
  have hle : L.tail.length ≤ B.tail.length := B.tail_maximal L rfl
  have hlen : L.tail.length = 1 := by
    simp [L, ofCycleCrossingEdge]
  omega

end BestLollipop

end

end Erdos767Scratch
-- END Lollipop

-- BEGIN NoConsecutive

open Finset

namespace Erdos767

/-!
A finite set of pairwise nonconsecutive natural numbers in the interval
`[ℓ + 1, c - ℓ - 1]` has at most half the size of the interval obtained by
adjoining one extra point at its right end.

The proof pairs every `i ∈ S` with `i + 1`.  The original set and the set
of successors are disjoint, while their union is contained in
`[ℓ + 1, c - ℓ]`.
-/
theorem two_mul_card_le_of_no_consecutive
    (S : Finset ℕ) (ell c : ℕ)
    (hlo : ∀ i ∈ S, ell + 1 ≤ i)
    (hhi : ∀ i ∈ S, i ≤ c - ell - 1)
    (hnc : ∀ i ∈ S, i + 1 ∉ S) :
    2 * S.card ≤ c - 2 * ell := by
  let T : Finset ℕ := S.image (fun i ↦ i + 1)
  have hTcard : T.card = S.card := by
    dsimp [T]
    exact card_image_of_injective S (fun _ _ h ↦ Nat.add_right_cancel h)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    change i ∈ S.image (fun j ↦ j + 1) at hiT
    rw [Finset.mem_image] at hiT
    obtain ⟨j, hjS, rfl⟩ := hiT
    exact hnc j hjS hiS
  have hunion : S ∪ T ⊆ Finset.Icc (ell + 1) (c - ell) := by
    intro i hi
    rw [Finset.mem_union] at hi
    rw [Finset.mem_Icc]
    rcases hi with hiS | hiT
    · exact ⟨hlo i hiS, by have := hhi i hiS; omega⟩
    · change i ∈ S.image (fun j ↦ j + 1) at hiT
      rw [Finset.mem_image] at hiT
      obtain ⟨j, hjS, rfl⟩ := hiT
      constructor
      · have := hlo j hjS
        omega
      · have := hhi j hjS
        have := hlo j hjS
        omega
  calc
    2 * S.card = S.card + T.card := by rw [hTcard]; omega
    _ = (S ∪ T).card := by rw [card_union_of_disjoint hdisj]
    _ ≤ (Finset.Icc (ell + 1) (c - ell)).card := card_le_card hunion
    _ = c - 2 * ell := by rw [Nat.card_Icc]; omega

end Erdos767

-- END NoConsecutive

-- BEGIN WalkIndex

/-!
Small, division-free indexing lemmas for paths and cycles.  These are intended
for the path-rotation/lollipop part of the proof of Erdős 767.
-/

open Finset
open scoped SimpleGraph

namespace E767WalkIndex

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V}

/-! ### Index sets and elementary path indexing -/

/-- The natural-number indices of all vertices of a walk. -/
def vertexIndices (p : G.Walk a b) : Finset ℕ := Finset.range (p.length + 1)

/-- The indices on a path at which the indexed vertex is adjacent to `x`. -/
def neighborIndices (p : G.Walk a b) (x : V) : Finset ℕ :=
  (vertexIndices p).filter fun i ↦ G.Adj x (p.getVert i)

/-- The indices on a path at which the indexed vertex is in `S`. -/
def indicesIn (p : G.Walk a b) (S : Finset V) : Finset ℕ :=
  (vertexIndices p).filter fun i ↦ p.getVert i ∈ S

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_vertexIndices {p : G.Walk a b} {i : ℕ} :
    i ∈ vertexIndices p ↔ i ≤ p.length := by
  simp [vertexIndices]

omit [DecidableEq V] [Fintype V] in
@[simp] theorem mem_neighborIndices {p : G.Walk a b} {x : V} {i : ℕ} :
    i ∈ neighborIndices p x ↔ i ≤ p.length ∧ G.Adj x (p.getVert i) := by
  classical
  simp [neighborIndices]

omit [DecidableRel G.Adj] [Fintype V] in
@[simp] theorem mem_indicesIn {p : G.Walk a b} {S : Finset V} {i : ℕ} :
    i ∈ indicesIn p S ↔ i ≤ p.length ∧ p.getVert i ∈ S := by
  classical
  simp [indicesIn]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem path_getVert_injOn_vertexIndices {p : G.Walk a b} (hp : p.IsPath) :
    Set.InjOn p.getVert (vertexIndices p : Set ℕ) := by
  classical
  intro i hi j hj hij
  exact hp.getVert_injOn (mem_vertexIndices.mp hi) (mem_vertexIndices.mp hj) hij

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem path_getVert_eq_iff {p : G.Walk a b} (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    p.getVert i = p.getVert j ↔ i = j := by
  exact ⟨hp.getVert_injOn hi hj, congrArg p.getVert⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem path_mem_support_iff_exists_index {p : G.Walk a b} (hp : p.IsPath) {x : V} :
    x ∈ p.support ↔ ∃! i, i ≤ p.length ∧ p.getVert i = x := by
  constructor
  · intro hx
    obtain ⟨i, hix, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    refine ⟨i, ⟨hi, hix⟩, ?_⟩
    rintro j ⟨hj, hjx⟩
    exact hp.getVert_injOn hj hi (hjx.trans hix.symm)
  · rintro ⟨i, ⟨hi, hix⟩, -⟩
    exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨i, hix, hi⟩

omit [DecidableRel G.Adj] [Fintype V] in
theorem path_support_toFinset_eq_image_vertexIndices {p : G.Walk a b} (_hp : p.IsPath) :
    p.support.toFinset = (vertexIndices p).image p.getVert := by
  classical
  ext x
  simp only [List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨i, hix, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    exact ⟨i, mem_vertexIndices.mpr hi, hix⟩
  · rintro ⟨i, hi, rfl⟩
    exact p.getVert_mem_support i

omit [Fintype V] [DecidableRel G.Adj] in
theorem path_support_toFinset_card {p : G.Walk a b} (hp : p.IsPath) :
    p.support.toFinset.card = p.length + 1 := by
  rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support]

omit [Fintype V] [DecidableRel G.Adj] in
theorem path_idxOf_getVert {p : G.Walk a b} (hp : p.IsPath)
    {i : ℕ} (hi : i ≤ p.length) :
    p.support.idxOf (p.getVert i) = i := by
  let fi : Fin p.support.length :=
    ⟨i, p.length_support ▸ Nat.lt_add_one_of_le hi⟩
  have h := List.get_idxOf hp.support_nodup fi
  have hget : p.support.get fi = p.getVert i := by
    exact (p.getVert_eq_support_getElem hi).symm
  rw [hget] at h
  simpa [fi] using h

/-! ### Exact cardinal transport along a path -/

omit [DecidableRel G.Adj] [Fintype V] in
theorem image_indicesIn {p : G.Walk a b} (_hp : p.IsPath) (S : Finset V) :
    (indicesIn p S).image p.getVert = p.support.toFinset ∩ S := by
  classical
  ext x
  simp only [Finset.mem_image, mem_indicesIn, Finset.mem_inter,
    List.mem_toFinset]
  constructor
  · rintro ⟨i, ⟨hi, hiS⟩, rfl⟩
    exact ⟨p.getVert_mem_support i, hiS⟩
  · rintro ⟨hxp, hxS⟩
    obtain ⟨i, hix, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxp
    exact ⟨i, ⟨hi, hix ▸ hxS⟩, hix⟩

omit [DecidableRel G.Adj] [Fintype V] in
theorem card_indicesIn {p : G.Walk a b} (hp : p.IsPath) (S : Finset V) :
    (indicesIn p S).card = (p.support.toFinset ∩ S).card := by
  classical
  rw [← image_indicesIn hp S, Finset.card_image_iff.mpr]
  exact hp.getVert_injOn.mono fun i hi ↦ (mem_indicesIn.mp hi).1

theorem image_neighborIndices {p : G.Walk a b} (_hp : p.IsPath) (x : V) :
    (neighborIndices p x).image p.getVert =
      G.neighborFinset x ∩ p.support.toFinset := by
  ext y
  simp only [Finset.mem_image, mem_neighborIndices, Finset.mem_inter,
    G.mem_neighborFinset, List.mem_toFinset]
  constructor
  · rintro ⟨i, ⟨hi, hxy⟩, rfl⟩
    exact ⟨hxy, p.getVert_mem_support i⟩
  · rintro ⟨hxy, hyp⟩
    obtain ⟨i, hiy, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyp
    exact ⟨i, ⟨hi, hiy ▸ hxy⟩, hiy⟩

theorem card_neighborIndices {p : G.Walk a b} (hp : p.IsPath) (x : V) :
    (neighborIndices p x).card =
      (G.neighborFinset x ∩ p.support.toFinset).card := by
  rw [← image_neighborIndices hp x, Finset.card_image_iff.mpr]
  exact hp.getVert_injOn.mono fun i hi ↦ (mem_neighborIndices.mp hi).1

theorem card_neighborIndices_eq_degree {p : G.Walk a b} (hp : p.IsPath) (x : V)
    (hN : G.neighborFinset x ⊆ p.support.toFinset) :
    (neighborIndices p x).card = G.degree x := by
  rw [card_neighborIndices hp x, Finset.inter_eq_left.mpr hN,
    G.card_neighborFinset_eq_degree]

/-! ### The terminal-neighbour index set -/

/-- The positions on `p` adjacent to its terminal endpoint. -/
def endNeighborIndices (p : G.Walk a b) : Finset ℕ := neighborIndices p b

omit [DecidableEq V] [Fintype V] in
@[simp] theorem mem_endNeighborIndices {p : G.Walk a b} {i : ℕ} :
    i ∈ endNeighborIndices p ↔ i ≤ p.length ∧ G.Adj b (p.getVert i) := by
  classical
  simp [endNeighborIndices]

omit [DecidableEq V] [Fintype V] in
theorem mem_endNeighborIndices_iff_lt {p : G.Walk a b} (_hp : p.IsPath) {i : ℕ} :
    i ∈ endNeighborIndices p ↔ i < p.length ∧ G.Adj b (p.getVert i) := by
  classical
  rw [mem_endNeighborIndices]
  constructor
  · rintro ⟨hi, hadj⟩
    exact ⟨by
      rcases hi.eq_or_lt with rfl | hlt
      · simp at hadj
      · exact hlt, hadj⟩
  · rintro ⟨hi, hadj⟩
    exact ⟨hi.le, hadj⟩

omit [DecidableEq V] [Fintype V] in
theorem endNeighborIndices_eq_filter_range {p : G.Walk a b} (hp : p.IsPath) :
    endNeighborIndices p =
      (Finset.range p.length).filter fun i ↦ G.Adj b (p.getVert i) := by
  classical
  ext i
  simp [mem_endNeighborIndices_iff_lt hp]

theorem card_endNeighborIndices {p : G.Walk a b} (hp : p.IsPath) :
    (endNeighborIndices p).card =
      (G.neighborFinset b ∩ p.support.toFinset).card := by
  exact card_neighborIndices hp b

theorem card_endNeighborIndices_eq_degree {p : G.Walk a b} (hp : p.IsPath)
    (hN : G.neighborFinset b ⊆ p.support.toFinset) :
    (endNeighborIndices p).card = G.degree b := by
  exact card_neighborIndices_eq_degree hp b hN

/-! ### `take`, `drop`, `takeUntil`, and `dropUntil` carriers -/

omit [DecidableRel G.Adj] [Fintype V] in
theorem take_support_toFinset_card {p : G.Walk a b} (hp : p.IsPath) (i : ℕ) :
    (p.take i).support.toFinset.card = min i p.length + 1 := by
  classical
  simpa using path_support_toFinset_card (hp.take i)

omit [DecidableRel G.Adj] [Fintype V] in
theorem drop_support_toFinset_card {p : G.Walk a b} (hp : p.IsPath) (i : ℕ) :
    (p.drop i).support.toFinset.card = p.length - i + 1 := by
  classical
  simpa using path_support_toFinset_card (hp.drop i)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem getVert_mem_take_support_iff {p : G.Walk a b} (hp : p.IsPath)
    {i j : ℕ} (hj : j ≤ p.length) :
    p.getVert j ∈ (p.take i).support ↔ j ≤ min i p.length := by
  constructor
  · intro hjmem
    obtain ⟨k, hkvert, hk⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hjmem
    rw [SimpleGraph.Walk.take_length] at hk
    have hki : k ≤ i := hk.trans (min_le_left _ _)
    have hkp : k ≤ p.length := hk.trans (min_le_right _ _)
    have hget : p.getVert k = p.getVert j := by
      simpa [SimpleGraph.Walk.take_getVert, min_eq_right hki] using hkvert
    have : k = j := hp.getVert_injOn hkp hj hget
    omega
  · intro hjmin
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨j, ?_, ?_⟩
    · simp [SimpleGraph.Walk.take_getVert, min_eq_right (hjmin.trans (min_le_left _ _))]
    · simpa using hjmin

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem getVert_mem_drop_support_iff {p : G.Walk a b} (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    p.getVert j ∈ (p.drop i).support ↔ i ≤ j := by
  constructor
  · intro hjmem
    obtain ⟨k, hkvert, hk⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hjmem
    rw [SimpleGraph.Walk.drop_length] at hk
    have hik : i + k ≤ p.length := by omega
    have hget : p.getVert (i + k) = p.getVert j := by
      simpa [SimpleGraph.Walk.drop_getVert] using hkvert
    have : i + k = j := hp.getVert_injOn hik hj hget
    omega
  · intro hij
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨j - i, ?_, ?_⟩
    · simp [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij]
    · rw [SimpleGraph.Walk.drop_length]
      omega

omit [DecidableRel G.Adj] [Fintype V] in
theorem takeUntil_getVert_support_card {p : G.Walk a b} (hp : p.IsPath)
    {i : ℕ} (hi : i ≤ p.length) :
    (p.takeUntil (p.getVert i) (p.getVert_mem_support i)).support.toFinset.card = i + 1 := by
  classical
  rw [path_support_toFinset_card (hp.takeUntil _),
    SimpleGraph.Walk.length_takeUntil, path_idxOf_getVert hp hi]

omit [DecidableRel G.Adj] [Fintype V] in
theorem dropUntil_getVert_support_card {p : G.Walk a b} (hp : p.IsPath)
    {i : ℕ} (hi : i ≤ p.length) :
    (p.dropUntil (p.getVert i) (p.getVert_mem_support i)).support.toFinset.card =
      p.length - i + 1 := by
  classical
  rw [path_support_toFinset_card (hp.dropUntil _),
    SimpleGraph.Walk.length_dropUntil, path_idxOf_getVert hp hi]

/-! ### Cycles indexed without repeating their initial vertex -/

/-- The indices `0, ..., c.length - 1` of the distinct vertices of a cycle. -/
def cycleIndices {v : V} (c : G.Walk v v) : Finset ℕ := Finset.range c.length

/-- The vertex carrier of a cycle, with the repeated terminal vertex removed. -/
def cycleVertexFinset {v : V} (c : G.Walk v v) : Finset V :=
  c.support.dropLast.toFinset

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_cycleIndices {v : V} {c : G.Walk v v} {i : ℕ} :
    i ∈ cycleIndices c ↔ i < c.length := by
  simp [cycleIndices]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem cycle_getVert_injOn_cycleIndices {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) :
    Set.InjOn c.getVert (cycleIndices c : Set ℕ) := by
  classical
  intro i hi j hj hij
  apply hc.getVert_injOn' (show i ≤ c.length - 1 by
      have := mem_cycleIndices.mp hi
      omega)
    (show j ≤ c.length - 1 by
      have := mem_cycleIndices.mp hj
      omega)
  exact hij

omit [Fintype V] [DecidableRel G.Adj] in
theorem cycle_support_dropLast_card {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    (cycleVertexFinset c).card = c.length := by
  rw [cycleVertexFinset, List.toFinset_card_of_nodup hc.nodup_dropLast_support,
    List.length_dropLast, c.length_support]
  omega

omit [Fintype V] [DecidableRel G.Adj] in
theorem cycle_support_toFinset_eq_cycleVertexFinset {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) :
    c.support.toFinset = cycleVertexFinset c := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hdecomp : c.support.dropLast ++ [v] = c.support :=
      c.dropLast_support_concat
    rw [← hdecomp, List.mem_toFinset] at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact List.mem_toFinset.mpr hx
    · subst x
      exact List.mem_toFinset.mpr (by
        apply (List.mem_dropLast_iff_idxOf_lt c.start_mem_support).mpr
        have hidx : c.support.idxOf v = 0 :=
          (List.idxOf_eq_zero_iff_head_eq c.support_ne_nil).mpr c.head_support
        rw [hidx, c.length_support]
        have := hc.three_le_length
        omega)
  · exact fun x hx ↦ List.mem_toFinset.mpr
      (List.mem_of_mem_dropLast (List.mem_toFinset.mp hx))

omit [DecidableRel G.Adj] [Fintype V] in
theorem cycleVertexFinset_eq_image_cycleIndices {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) :
    cycleVertexFinset c = (cycleIndices c).image c.getVert := by
  classical
  ext x
  simp only [cycleVertexFinset, List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hx
    have hxfull : x ∈ c.support := List.mem_of_mem_dropLast hx
    let i := c.support.idxOf x
    have hi : i < c.length := by
      have := List.mem_dropLast_iff_idxOf_lt hxfull
      rw [this] at hx
      simpa [i, c.length_support] using hx
    refine ⟨i, mem_cycleIndices.mpr hi, ?_⟩
    exact c.getVert_support_idxOf hxfull
  · rintro ⟨i, hi, rfl⟩
    have hil : i < c.length := mem_cycleIndices.mp hi
    have himem : c.getVert i ∈ c.support := c.getVert_mem_support i
    apply (List.mem_dropLast_iff_idxOf_lt himem).mpr
    have hidx : c.support.idxOf (c.getVert i) = i := by
      let fi : Fin c.support.dropLast.length :=
        ⟨i, by simpa [c.length_support] using hil⟩
      have h := List.get_idxOf hc.nodup_dropLast_support fi
      have hget : c.support.dropLast.get fi = c.getVert i := by
        rw [c.getVert_eq_support_getElem hil.le]
        exact List.getElem_dropLast fi.isLt
      rw [hget] at h
      have himemdrop : c.getVert i ∈ c.support.dropLast := by
        rw [← hget]
        exact List.getElem_mem _
      have hprefix : c.support.dropLast <+: c.support := by
        exact ⟨[v], c.dropLast_support_concat⟩
      calc
        c.support.idxOf (c.getVert i) =
            c.support.dropLast.idxOf (c.getVert i) :=
          (hprefix.idxOf_eq_of_mem himemdrop).symm
        _ = i := by simpa [fi] using h
    rw [hidx, c.length_support]
    omega

end E767WalkIndex

-- END WalkIndex

-- BEGIN Build

open Finset Set
open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] [DecidableEq V] in
lemma BestLollipop.neighbor_mem_cycle_or_tail (B : BestLollipop G)
    {w : V} (hw : G.Adj B.terminal w) :
    w ∈ B.cycle.support ∨ w ∈ B.tail.support := by
  classical
  by_contra hout
  push Not at hout
  let L : Lollipop G :=
    { cycleBase := B.cycleBase
      cycle := B.cycle
      cycle_isCycle := B.cycle_isCycle
      start := B.start
      terminal := w
      tail := B.tail.concat hw
      tail_isPath := B.tail_isPath.concat hout.2 hw
      start_mem_cycle := B.start_mem_cycle
      cycle_tail_inter := by
        intro v hvC hvP
        simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hvP
        rcases hvP with hvP | rfl
        · exact B.cycle_tail_inter hvC hvP
        · exact (hout.1 hvC).elim }
  have hle := B.tail_maximal L rfl
  simp [L] at hle

/-- Rotate the longest cycle of a best lollipop to the handle attachment. -/
def BestLollipop.rootedCycle (B : BestLollipop G) : G.Walk B.start B.start :=
  B.cycle.rotate B.start B.start_mem_cycle

omit [Fintype V] [DecidableRel G.Adj] in
lemma BestLollipop.rootedCycle_isCycle (B : BestLollipop G) :
    (rootedCycle B).IsCycle :=
  B.cycle_isCycle.rotate B.start_mem_cycle

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] lemma BestLollipop.rootedCycle_length (B : BestLollipop G) :
    (rootedCycle B).length = B.cycle.length := by
  simp [BestLollipop.rootedCycle]

omit [Fintype V] [DecidableRel G.Adj] in
lemma BestLollipop.rootedCycle_support_iff (B : BestLollipop G) (v : V) :
    v ∈ (rootedCycle B).support ↔ v ∈ B.cycle.support := by
  exact Walk.mem_support_rotate_iff _ _ _

omit [DecidableRel G.Adj] [Fintype V] in
lemma BestLollipop.rooted_meet (B : BestLollipop G) {v : V}
    (hvC : v ∈ (rootedCycle B).support) (hvP : v ∈ B.tail.support) :
    v = B.start := by
  classical
  exact B.cycle_tail_inter ((rootedCycle_support_iff B v).mp hvC) hvP

omit [DecidableRel G.Adj] [Fintype V] in
/-- Close the lollipop handle with either oriented arc from its attachment
to a cycle vertex adjacent to the tip. -/
lemma BestLollipop.exists_cycle_tail_append_arc (B : BestLollipop G)
    (htail : 0 < B.tail.length) {v : V}
    (hvC : v ∈ (rootedCycle B).support) (hvs : v ≠ B.start)
    (htv : G.Adj B.terminal v)
    (q : G.Walk B.start v) (hq : q.IsPath)
    (hqC : ∀ x, x ∈ q.support → x ∈ (rootedCycle B).support) :
    ∃ d : G.Walk B.start B.start,
      d.IsCycle ∧ d.length = B.tail.length + 1 + q.length := by
  classical
  have hvTail : v ∉ B.tail.support := by
    intro hv
    exact hvs (rooted_meet B hvC hv)
  let p : G.Walk B.start v := B.tail.concat htv
  have hp : p.IsPath := B.tail_isPath.concat hvTail htv
  have hdisj : p.support.tail.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro x hxp hxq
    have hxq' : x ∈ q.support := by
      have : x ∈ q.reverse.support := List.mem_of_mem_tail hxq
      simpa [Walk.support_reverse] using this
    have hxC := hqC x hxq'
    have hxp' : x ∈ p.support := List.mem_of_mem_tail hxp
    simp only [p, Walk.support_concat, List.mem_append,
      List.mem_singleton] at hxp'
    rcases hxp' with hxTail | rfl
    · have hxs : x = B.start := rooted_meet B hxC hxTail
      have hstartNot : B.start ∉ p.support.tail := by
        have hn := hp.support_nodup
        rw [← p.cons_tail_support, List.nodup_cons] at hn
        exact hn.1
      exact hstartNot (hxs ▸ hxp)
    · have hvNot : x ∉ q.reverse.support.tail := by
        have hn := hq.reverse.support_nodup
        rw [← q.reverse.cons_tail_support, List.nodup_cons] at hn
        exact hn.1
      exact hvNot hxq
  let d : G.Walk B.start B.start := p.append q.reverse
  have hd : d.IsCycle := by
    apply hp.isCycle_append hq.reverse hdisj
    left
    simp [p]
    omega
  refine ⟨d, hd, ?_⟩
  simp [d, p, Walk.length_append, Walk.length_concat]

/-- A subpath of a given route going from its last visit to `A` before its
first visit to `B`.  Its internal vertices avoid both endpoint blocks. -/
structure BlockEar {x y : V} (r : G.Walk x y) (A B : Finset V) where
  a : V
  b : V
  path : G.Walk a b
  isPath : path.IsPath
  a_mem : a ∈ A
  b_mem : b ∈ B
  support_subset : ∀ v, v ∈ path.support → v ∈ r.support
  meet_A : ∀ v, v ∈ path.support → v ∈ A → v = a
  meet_B : ∀ v, v ∈ path.support → v ∈ B → v = b

omit [Fintype V] [DecidableRel G.Adj] [DecidableEq V] in
/-- Extract the last-`A`/first-`B` subpath of a simple route. -/
theorem exists_blockEar {x y : V} {r : G.Walk x y} (hr : r.IsPath)
    (A B : Finset V) (hx : x ∈ A) (hy : y ∈ B) :
    Nonempty (BlockEar r A B) := by
  classical
  have hB : {v ∈ B | v ∈ r.support}.Nonempty := by
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, r.end_mem_support⟩⟩
  obtain ⟨b, hbB, hbR, hbFirst⟩ :=
    r.exists_mem_support_forall_mem_support_imp_eq B hB
  let pre : G.Walk x b := r.takeUntil b hbR
  have hpre : pre.IsPath := hr.takeUntil hbR
  have hxpre : x ∈ pre.support := pre.start_mem_support
  have hA : {v ∈ A | v ∈ pre.reverse.support}.Nonempty := by
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
    simp [Walk.support_reverse]
  obtain ⟨a, haA, haRev, haFirst⟩ :=
    pre.reverse.exists_mem_support_forall_mem_support_imp_eq A hA
  let qrev : G.Walk b a := pre.reverse.takeUntil a haRev
  let q : G.Walk a b := qrev.reverse
  have hq : q.IsPath := (hpre.reverse.takeUntil haRev).reverse
  refine ⟨{
    a := a
    b := b
    path := q
    isPath := hq
    a_mem := haA
    b_mem := hbB
    support_subset := ?_
    meet_A := ?_
    meet_B := ?_ }⟩
  · intro v hvq
    have hvrev : v ∈ qrev.support := by
      simpa [q, Walk.support_reverse] using hvq
    have hvpreRev : v ∈ pre.reverse.support :=
      pre.reverse.support_takeUntil_subset_support haRev hvrev
    have hvpre : v ∈ pre.support := by
      simpa [Walk.support_reverse] using hvpreRev
    exact r.support_takeUntil_subset_support hbR hvpre
  · intro v hvq hvA
    have hvrev : v ∈ qrev.support := by
      simpa [q, Walk.support_reverse] using hvq
    exact haFirst v hvA hvrev
  · intro v hvq hvB
    apply hbFirst v hvB
    have hvrev : v ∈ qrev.support := by
      simpa [q, Walk.support_reverse] using hvq
    have hvpreRev : v ∈ pre.reverse.support :=
      pre.reverse.support_takeUntil_subset_support haRev hvrev
    have hvpre : v ∈ pre.support := by
      simpa [Walk.support_reverse] using hvpreRev
    exact hvpre

/-- The reference path used in the aligned-fan part of Dirac's lollipop
argument: open the rooted cycle at its first edge, then traverse the handle. -/
def BestLollipop.referencePath (B : BestLollipop G) :
    G.Walk (rootedCycle B).snd B.terminal :=
  (rootedCycle B).tail.append B.tail

omit [DecidableRel G.Adj] [Fintype V] in
lemma BestLollipop.referencePath_isPath (B : BestLollipop G) :
    (referencePath B).IsPath := by
  classical
  let C := rootedCycle B
  have hC : C.IsCycle := rootedCycle_isCycle B
  have hD : C.tail.IsPath := hC.isPath_tail
  apply E767AlignedAlt.isPath_append_of_disjoint_tail hD B.tail_isPath
  rw [List.disjoint_left]
  intro v hvC hvP
  have hvCycle : v ∈ C.support := by
    have hvC' : v ∈ C.support.tail := by
      rw [← C.support_tail_of_not_nil hC.not_nil]
      exact hvC
    exact List.tail_subset C.support hvC'
  have hvTail : v ∈ B.tail.support := List.mem_of_mem_tail hvP
  have hvr : v = B.start := rooted_meet B hvCycle hvTail
  subst v
  have hn := B.tail_isPath.support_nodup
  rw [← B.tail.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hvP

omit [DecidableRel G.Adj] [Fintype V] in
lemma BestLollipop.reference_start_mem_cycle (B : BestLollipop G) :
    (rootedCycle B).snd ∈ (rootedCycle B).support := by
  classical
  let C := rootedCycle B
  exact List.tail_subset C.support
    (C.snd_mem_tail_support (rootedCycle_isCycle B).not_nil)

omit [Fintype V] [DecidableRel G.Adj] in
lemma BestLollipop.tail_support_subset_reference (B : BestLollipop G) :
    ∀ v, v ∈ B.tail.support → v ∈ (referencePath B).support := by
  intro v hv
  rw [referencePath, Walk.mem_support_append_iff]
  exact Or.inr hv

omit [Fintype V] [DecidableRel G.Adj] in
/-- Alignment preserves the order from any common vertex to the terminal
vertex of the aligned path. -/
lemma aligned_idxOf_le_end {x y a b : V}
    {W : G.Walk x y} {R : G.Walk a b}
    (hW : W.IsPath) (_hR : R.IsPath) (hal : E767AlignedAlt.Aligned W R)
    {v : V} (hvR : v ∈ R.support) (hvW : v ∈ W.support)
    (hbW : b ∈ W.support) :
    W.support.idxOf v ≤ W.support.idxOf b := by
  let rel : V → V → Prop := fun s t ↦
    W.support.idxOf s ≤ W.support.idxOf t
  have hpairW : W.support.Pairwise rel := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    let fi : Fin W.support.length := ⟨i, hi⟩
    let fj : Fin W.support.length := ⟨j, hj⟩
    dsimp [rel]
    change W.support.idxOf (W.support.get fi) ≤
      W.support.idxOf (W.support.get fj)
    rw [List.get_idxOf hW.support_nodup fi,
      List.get_idxOf hW.support_nodup fj]
    exact Nat.le_of_lt hij
  let L := R.support.filter fun w ↦ w ∈ W.support
  have hsub : L.Sublist W.support := by
    exact hal
  have hpairL : L.Pairwise rel := hpairW.sublist hsub
  have hvL : v ∈ L := by
    simp [L, hvR, hvW]
  have hbL : b ∈ L := by
    simp [L, R.end_mem_support, hbW]
  have hdecomp : R.support = R.support.dropLast ++ [b] :=
    R.dropLast_support_concat.symm
  let L₀ := R.support.dropLast.filter fun w ↦ w ∈ W.support
  have hLeq : L = L₀ ++ [b] := by
    change (R.support.filter fun w ↦ w ∈ W.support) =
      (R.support.dropLast.filter fun w ↦ w ∈ W.support) ++ [b]
    calc
      (R.support.filter fun w ↦ w ∈ W.support) =
          ((R.support.dropLast ++ [b]).filter fun w ↦ w ∈ W.support) := by
            exact congrArg (fun l : List V ↦
              l.filter fun w ↦ w ∈ W.support) hdecomp
      _ = (R.support.dropLast.filter fun w ↦ w ∈ W.support) ++ [b] := by
        rw [List.filter_append]
        simp [hbW]
  by_cases hvb : v = b
  · subst v
    exact le_rfl
  have hvL₀ : v ∈ L₀ := by
    rw [hLeq] at hvL
    simp only [List.mem_append, List.mem_singleton] at hvL
    exact hvL.resolve_right hvb
  have hpairAppend : (L₀ ++ [b]).Pairwise rel := by
    rw [← hLeq]
    exact hpairL
  exact (List.pairwise_append.mp hpairAppend).2.2 v hvL₀ b (by simp)

omit [DecidableRel G.Adj] [Fintype V] in
lemma BestLollipop.reference_idxOf_tail_getVert (B : BestLollipop G)
    {j : ℕ} (hj : j ≤ B.tail.length) :
    (referencePath B).support.idxOf (B.tail.getVert j) =
      (rootedCycle B).tail.length + j := by
  classical
  let D := (rootedCycle B).tail
  let W := referencePath B
  have hW : W.IsPath := referencePath_isPath B
  have hjW : D.length + j ≤ W.length := by
    simp [W, referencePath, D, Walk.length_append]
    omega
  have hget : W.getVert (D.length + j) = B.tail.getVert j := by
    simp [W, referencePath, D, Walk.getVert_append]
  rw [← hget]
  exact E767WalkIndex.path_idxOf_getVert hW hjW

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma exists_tail_index_of_mem_drop {x y : V} (P : G.Walk x y)
    {j : ℕ} (hj : j ≤ P.length) {v : V}
    (hv : v ∈ (P.drop j).support) :
    ∃ t : ℕ, j ≤ t ∧ t ≤ P.length ∧ P.getVert t = v := by
  obtain ⟨k, hkv, hk⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  refine ⟨j + k, by omega, ?_, ?_⟩
  · rw [Walk.drop_length] at hk
    omega
  · simpa [Walk.drop_getVert] using hkv

/-- The checked data extracted from the aligned fan in lollipop Case 2. -/
structure Case2FanData (B : BestLollipop G) (j₁ : ℕ) where
  j₁_min : ∀ i, i ∈ E767WalkIndex.endNeighborIndices B.tail → j₁ ≤ i
  F : E767AlignedAlt.AlignedFan
    (z := B.tail.getVert j₁) (BestLollipop.referencePath B)
  E₁ : BlockEar F.toZ (BestLollipop.rootedCycle B).support.dropLast.toFinset
    (B.tail.drop j₁).support.toFinset
  E₂ : BlockEar F.toY (BestLollipop.rootedCycle B).support.dropLast.toFinset
    (B.tail.drop j₁).support.toFinset
  b₁_eq : E₁.b = B.tail.getVert j₁
  j₂ : ℕ
  j₁_le_j₂ : j₁ ≤ j₂
  j₂_le : j₂ ≤ B.tail.length
  b₂_eq : E₂.b = B.tail.getVert j₂

theorem BestLollipop.exists_case2FanData
    (hTwo : Erdos58.TwoConnected G) (B : BestLollipop G)
    (hpos : 0 < B.tail.length) :
    ∃ j₁ : ℕ, j₁ ∈ E767WalkIndex.endNeighborIndices B.tail ∧
      Nonempty (Case2FanData B j₁) := by
  let J := E767WalkIndex.endNeighborIndices B.tail
  have hJ : J.Nonempty := by
    let i := B.tail.length - 1
    refine ⟨i, ?_⟩
    rw [E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath]
    constructor
    · dsimp [i]
      omega
    · have hadj := B.tail.adj_getVert_succ (i := i) (by dsimp [i]; omega)
      have hi : i + 1 = B.tail.length := by dsimp [i]; omega
      rw [hi, B.tail.getVert_length] at hadj
      exact hadj.symm
  let j₁ := J.min' hJ
  have hj₁J : j₁ ∈ J := Finset.min'_mem J hJ
  have hj₁lt : j₁ < B.tail.length :=
    (E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath).mp hj₁J |>.1
  let z := B.tail.getVert j₁
  let W := referencePath B
  have hzTail : z ∈ B.tail.support := B.tail.getVert_mem_support j₁
  have hzW : z ∈ W.support := tail_support_subset_reference B z hzTail
  have hzy : z ≠ B.terminal := by
    intro hzy
    have hjend := (B.tail_isPath.getVert_eq_end_iff hj₁lt.le).mp hzy
    omega
  obtain ⟨F⟩ := E767AlignedAlt.exists_alignedFan hTwo W
    (referencePath_isPath B) hzW hzy
  let X := (rootedCycle B).support.dropLast.toFinset
  let Y := (B.tail.drop j₁).support.toFinset
  have hxX : (rootedCycle B).snd ∈ X := by
    have hxF : (rootedCycle B).snd ∈ (rootedCycle B).support.toFinset :=
      List.mem_toFinset.mpr (reference_start_mem_cycle B)
    rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
      (rootedCycle_isCycle B)] at hxF
    exact hxF
  have hzY : z ∈ Y := by
    change z ∈ (B.tail.drop j₁).support.toFinset
    exact List.mem_toFinset.mpr (by simpa [z] using
      (B.tail.drop j₁).start_mem_support)
  have hyY : B.terminal ∈ Y := by
    exact List.mem_toFinset.mpr (B.tail.drop j₁).end_mem_support
  obtain ⟨E₁⟩ := exists_blockEar F.toZ_isPath X Y hxX hzY
  obtain ⟨E₂⟩ := exists_blockEar F.toY_isPath X Y hxX hyY
  have hE₁bY : E₁.b ∈ (B.tail.drop j₁).support :=
    List.mem_toFinset.mp E₁.b_mem
  obtain ⟨t₁, hj₁t₁, ht₁le, ht₁eq⟩ :=
    exists_tail_index_of_mem_drop B.tail hj₁lt.le hE₁bY
  have hE₁bF : E₁.b ∈ F.toZ.support :=
    E₁.support_subset E₁.b E₁.path.end_mem_support
  have hE₁bW : E₁.b ∈ W.support := by
    rw [← ht₁eq]
    exact tail_support_subset_reference B _ (B.tail.getVert_mem_support t₁)
  have hidx₁ := aligned_idxOf_le_end (referencePath_isPath B)
    F.toZ_isPath F.toZ_aligned hE₁bF hE₁bW hzW
  have ht₁j₁ : t₁ ≤ j₁ := by
    rw [← ht₁eq, reference_idxOf_tail_getVert B ht₁le,
      reference_idxOf_tail_getVert B hj₁lt.le] at hidx₁
    omega
  have ht₁ : t₁ = j₁ := by omega
  have hb₁ : E₁.b = B.tail.getVert j₁ := by
    rw [← ht₁eq, ht₁]
  have hE₂bY : E₂.b ∈ (B.tail.drop j₁).support :=
    List.mem_toFinset.mp E₂.b_mem
  obtain ⟨j₂, hj₁j₂, hj₂le, hb₂⟩ :=
    exists_tail_index_of_mem_drop B.tail hj₁lt.le hE₂bY
  refine ⟨j₁, hj₁J, ⟨{
    j₁_min := fun i hi ↦ Finset.min'_le J i hi
    F := F
    E₁ := E₁
    E₂ := E₂
    b₁_eq := hb₁
    j₂ := j₂
    j₁_le_j₂ := hj₁j₂
    j₂_le := hj₂le
    b₂_eq := hb₂.symm }⟩⟩

omit [Fintype V] in
lemma Case2FanData.j₁_lt_j₂ {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) : j₁ < D.j₂ := by
  have hb₁F : D.E₁.b ∈ D.F.toZ.support :=
    D.E₁.support_subset _ D.E₁.path.end_mem_support
  have hb₂F : D.E₂.b ∈ D.F.toY.support :=
    D.E₂.support_subset _ D.E₂.path.end_mem_support
  by_contra h
  have hj : D.j₂ = j₁ :=
    Nat.le_antisymm (Nat.le_of_not_gt h) D.j₁_le_j₂
  have hbb : D.E₁.b = D.E₂.b := by
    rw [D.b₁_eq, D.b₂_eq, hj]
  have hbx : D.E₁.b = (BestLollipop.rootedCycle B).snd := by
    exact D.F.meet_eq_start hb₁F (hbb ▸ hb₂F)
  have hxTail : (BestLollipop.rootedCycle B).snd ∈ B.tail.support := by
    rw [← hbx, D.b₁_eq]
    exact B.tail.getVert_mem_support j₁
  have hxs : (BestLollipop.rootedCycle B).snd = B.start :=
    BestLollipop.rooted_meet B
      (BestLollipop.reference_start_mem_cycle B) hxTail
  have hadj := (BestLollipop.rootedCycle B).adj_snd
    (BestLollipop.rootedCycle_isCycle B).not_nil
  exact hadj.ne hxs.symm

end

end E767DiracBuild

-- END Build

-- BEGIN Case1Core

open Finset
open SimpleGraph
open scoped SimpleGraph

namespace E767DiracCase1

noncomputable section

attribute [local instance] Classical.propDecidable


/-- The zero-based positions on a cycle at which its vertex is adjacent to
the terminal vertex of the lollipop handle.  We use `range C.length`, so the
repeated terminal copy of the initial cycle vertex is not counted twice. -/
def cycleNeighborIndices {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V}
    (C : G.Walk x x) (y : V) : Finset ℕ :=
  (Finset.range C.length).filter fun i ↦ G.Adj y (C.getVert i)

/-- Every neighbor of `y` which belongs to the non-repeated cycle carrier is
represented by an index in `cycleNeighborIndices`. -/
lemma cycle_neighbors_subset_index_image {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    {C : G.Walk x x} (hC : C.IsCycle) :
    G.neighborFinset y ∩ C.support.dropLast.toFinset ⊆
      (cycleNeighborIndices G C y).image C.getVert := by
  intro z hz
  have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp
    (Finset.mem_inter.mp hz).1
  have hzdrop : z ∈ C.support.dropLast :=
    List.mem_toFinset.mp (Finset.mem_inter.mp hz).2
  have hzdrop' : z ∈ C.dropLast.support := by
    rw [C.support_dropLast hC.not_nil]
    exact hzdrop
  obtain ⟨i, hi, hile⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzdrop'
  have hilt : i < C.length := by
    have hlenDrop : C.dropLast.length = C.length - 1 := C.length_dropLast
    rw [hlenDrop] at hile
    have hpos : 0 < C.length := by
      rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hC.not_nil
    omega
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hilt, ?_⟩
    rw [← C.getVert_dropLast hilt]
    exact hi.symm ▸ hyz
  · rw [← C.getVert_dropLast hilt, hi]

/-- The cycle-side neighbors of `y` are no more numerous than their index
set.  This form avoids choosing an inverse indexing map explicitly. -/
lemma card_cycle_neighbors_le_indices {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    {C : G.Walk x x} (hC : C.IsCycle) :
    (G.neighborFinset y ∩ C.support.dropLast.toFinset).card ≤
      (cycleNeighborIndices G C y).card := by
  calc
    (G.neighborFinset y ∩ C.support.dropLast.toFinset).card ≤
        ((cycleNeighborIndices G C y).image C.getVert).card :=
      Finset.card_le_card (cycle_neighbors_subset_index_image G hC)
    _ ≤ (cycleNeighborIndices G C y).card := Finset.card_image_le

/-- For a path ending at `y`, at most `P.length` vertices of the path are
neighbors of `y`.  The extra support vertex is `y` itself, which cannot be
its own neighbor in a simple graph. -/
lemma card_path_neighbors_le_length {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    {P : G.Walk x y} (hP : P.IsPath) :
    (G.neighborFinset y ∩ P.support.toFinset).card ≤ P.length := by
  have hsub : G.neighborFinset y ∩ P.support.toFinset ⊆
      P.support.toFinset.erase y := by
    intro z hz
    have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp
      (Finset.mem_inter.mp hz).1
    exact Finset.mem_erase.mpr
      ⟨hyz.ne.symm, (Finset.mem_inter.mp hz).2⟩
  calc
    (G.neighborFinset y ∩ P.support.toFinset).card ≤
        (P.support.toFinset.erase y).card := Finset.card_le_card hsub
    _ = P.length := by
      rw [Finset.card_erase_of_mem
        (List.mem_toFinset.mpr P.end_mem_support)]
      rw [List.toFinset_card_of_nodup hP.support_nodup, P.length_support]
      omega

/-- Maximality of the lollipop says that every neighbor of the terminal
vertex is already on the cycle or handle.  Under that cover, its degree is
bounded by the handle length plus the number of cycle-neighbor indices. -/
lemma degree_le_handle_add_cycle_indices {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} {C : G.Walk x x} {P : G.Walk x y}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset) :
    G.degree y ≤ P.length + (cycleNeighborIndices G C y).card := by
  let A : Finset V := G.neighborFinset y ∩ C.support.dropLast.toFinset
  let B : Finset V := G.neighborFinset y ∩ P.support.toFinset
  have hAB : G.neighborFinset y ⊆ A ∪ B := by
    intro z hz
    rcases Finset.mem_union.mp (hcover hz) with hzC | hzP
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hzC⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, hzP⟩)
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset y).card ≤ (A ∪ B).card :=
      Finset.card_le_card hAB
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ ≤ (cycleNeighborIndices G C y).card + P.length :=
      Nat.add_le_add (card_cycle_neighbors_le_indices G hC)
        (card_path_neighbors_le_length G hP)
    _ = P.length + (cycleNeighborIndices G C y).card := Nat.add_comm _ _

/-- A finite set of natural numbers contained in `[ell, c-ell)` and never
containing a number together with its successor occupies at most half of
that interval.  The strict upper bound is the exact one delivered by the two
cycle-splice inequalities in the lollipop argument. -/
lemma two_mul_card_le_of_nonconsecutive
    {S : Finset ℕ} {ell c : ℕ}
    (hS : S.Nonempty)
    (hbounds : ∀ i ∈ S, ell ≤ i ∧ i + 1 < c - ell)
    (hnext : ∀ i ∈ S, i + 1 ∉ S) :
    2 * S.card ≤ c - 2 * ell := by
  let T : Finset ℕ := S.image Nat.succ
  have hTcard : T.card = S.card := by
    dsimp [T]
    exact Finset.card_image_of_injective S Nat.succ_injective
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    obtain ⟨j, hjS, hji⟩ := Finset.mem_image.mp hiT
    have : j + 1 = i := by simpa [Nat.succ_eq_add_one] using hji
    exact hnext j hjS (this ▸ hiS)
  have hunion : S ∪ T ⊆ Finset.Ico ell (c - ell) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · have hiB := hbounds i hiS
      exact Finset.mem_Ico.mpr ⟨hiB.1, by omega⟩
    · obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hiT
      have hjB := hbounds j hjS
      exact Finset.mem_Ico.mpr ⟨by omega, by
        simpa [Nat.succ_eq_add_one] using hjB.2⟩
  obtain ⟨i, hiS⟩ := hS
  have hiB := hbounds i hiS
  have hell : 2 * ell ≤ c := by omega
  have hcard : 2 * S.card ≤ (c - ell) - ell := by
    calc
      2 * S.card = S.card + T.card := by rw [hTcard]; omega
      _ = (S ∪ T).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.Ico ell (c - ell)).card := Finset.card_le_card hunion
      _ = (c - ell) - ell := Nat.card_Ico ell (c - ell)
  omega

/-- Dirac's best-lollipop argument, Case 1 (the terminal vertex has a
neighbor on the cycle), reduced to its checked counting core.

`hbounds` and `hnext` are exactly the facts obtained from the two possible
cycle splices: every cycle-neighbor index is separated from both ends by the
handle length, and two such indices cannot be consecutive. -/
theorem best_lollipop_case1 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} {C : G.Walk x x} {P : G.Walk x y} {k : ℕ}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset)
    (hcycle : (cycleNeighborIndices G C y).Nonempty)
    (hbounds : ∀ i ∈ cycleNeighborIndices G C y,
      P.length ≤ i ∧ i + 1 < C.length - P.length)
    (hnext : ∀ i ∈ cycleNeighborIndices G C y,
      i + 1 ∉ cycleNeighborIndices G C y)
    (hdegree : k ≤ G.degree y) :
    2 * k ≤ C.length := by
  have hdegUpper := degree_le_handle_add_cycle_indices G hC hP hcover
  have hindex := two_mul_card_le_of_nonconsecutive hcycle hbounds hnext
  obtain ⟨i, hi⟩ := hcycle
  have hiB := hbounds i hi
  have hlen : 2 * P.length ≤ C.length := by omega
  omega

/-- The contradiction form used in the proof of Dirac's theorem: Case 1 is
impossible when the chosen longest cycle has length strictly below `2*k`. -/
theorem best_lollipop_case1_false {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} {C : G.Walk x x} {P : G.Walk x y} {k : ℕ}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset)
    (hcycle : (cycleNeighborIndices G C y).Nonempty)
    (hbounds : ∀ i ∈ cycleNeighborIndices G C y,
      P.length ≤ i ∧ i + 1 < C.length - P.length)
    (hnext : ∀ i ∈ cycleNeighborIndices G C y,
      i + 1 ∉ cycleNeighborIndices G C y)
    (hdegree : k ≤ G.degree y) (hshort : C.length < 2 * k) : False := by
  have := best_lollipop_case1 G hC hP hcover hcycle hbounds hnext hdegree
  omega

end

end E767DiracCase1

-- END Case1Core

-- BEGIN Case1Count

open Finset
open scoped SimpleGraph

namespace E767Case1Fixed

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Cycle-neighbour indices other than the lollipop attachment at index zero.
The attachment is already counted on the tail side of the degree estimate. -/
def positiveCycleNeighborIndices {x : V} (C : G.Walk x x) (y : V) : Finset ℕ :=
  (E767DiracCase1.cycleNeighborIndices G C y).erase 0

omit [Fintype V] in
@[simp] lemma mem_positiveCycleNeighborIndices {x y : V}
    {C : G.Walk x x} {i : ℕ} :
    i ∈ positiveCycleNeighborIndices C y ↔
      i ≠ 0 ∧ i < C.length ∧ G.Adj y (C.getVert i) := by
  simp [positiveCycleNeighborIndices, E767DiracCase1.cycleNeighborIndices]

/-- Corrected endpoint-degree estimate.  The index-zero cycle vertex is the
initial tail vertex, so it is charged to the tail rather than to the set of
cycle indices. -/
lemma degree_le_tail_add_positive_cycle_indices
    {x y : V} {C : G.Walk x x} {P : G.Walk x y}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset) :
    G.degree y ≤ P.length + (positiveCycleNeighborIndices C y).card := by
  let A : Finset V := G.neighborFinset y ∩ P.support.toFinset
  let S : Finset ℕ := positiveCycleNeighborIndices C y
  have hcover' : G.neighborFinset y ⊆ A ∪ S.image C.getVert := by
    intro z hz
    rcases Finset.mem_union.mp (hcover hz) with hzC | hzP
    · by_cases hzP' : z ∈ P.support.toFinset
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hzP'⟩)
      · apply Finset.mem_union_right
        have hzI : z ∈ G.neighborFinset y ∩ C.support.dropLast.toFinset :=
          Finset.mem_inter.mpr ⟨hz, hzC⟩
        obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp
          (E767DiracCase1.cycle_neighbors_subset_index_image G hC hzI)
        refine Finset.mem_image.mpr ⟨i, ?_, hiz⟩
        have hi0 : i ≠ 0 := by
          intro hi0
          subst i
          have hzx : z = x := by simpa using hiz.symm
          apply hzP'
          rw [hzx]
          exact List.mem_toFinset.mpr P.start_mem_support
        exact Finset.mem_erase.mpr ⟨hi0, hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hzP⟩)
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset y).card ≤ (A ∪ S.image C.getVert).card :=
      Finset.card_le_card hcover'
    _ ≤ A.card + (S.image C.getVert).card := Finset.card_union_le _ _
    _ ≤ P.length + S.card := Nat.add_le_add
      (E767DiracCase1.card_path_neighbors_le_length G hP) Finset.card_image_le

/-- The corrected counting core for Case 1 of the best-lollipop proof. -/
theorem case1_of_positive_indices
    {x y : V} {C : G.Walk x x} {P : G.Walk x y} {k : ℕ}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset)
    (hcycle : (positiveCycleNeighborIndices C y).Nonempty)
    (hlower : ∀ i ∈ positiveCycleNeighborIndices C y,
      P.length + 1 ≤ i)
    (hupper : ∀ i ∈ positiveCycleNeighborIndices C y,
      i ≤ C.length - P.length - 1)
    (hnext : ∀ i ∈ positiveCycleNeighborIndices C y,
      i + 1 ∉ positiveCycleNeighborIndices C y)
    (hdegree : k ≤ G.degree y) :
    2 * k ≤ C.length := by
  have hdeg := degree_le_tail_add_positive_cycle_indices hC hP hcover
  have hcard := Erdos767.two_mul_card_le_of_no_consecutive
    (positiveCycleNeighborIndices C y) P.length C.length hlower hupper hnext
  obtain ⟨i, hi⟩ := hcycle
  have hil := hlower i hi
  have hiu := hupper i hi
  omega

end

end E767Case1Fixed

-- END Case1Count

-- BEGIN Case1Geometry

open Finset
open scoped SimpleGraph

namespace Erdos767Scratch

open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Membership in the support of a `take` implies membership in the original
walk. -/
private lemma mem_support_of_mem_take {a b x : V} (p : G.Walk a b) (n : ℕ)
    (hx : x ∈ (p.take n).support) : x ∈ p.support := by
  obtain ⟨j, hjx, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  rw [Walk.take_getVert] at hjx
  exact hjx ▸ p.getVert_mem_support (min n j)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Membership in the support of a `drop` implies membership in the original
walk. -/
private lemma mem_support_of_mem_drop {a b x : V} (p : G.Walk a b) (n : ℕ)
    (hx : x ∈ (p.drop n).support) : x ∈ p.support := by
  obtain ⟨j, hjx, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  rw [Walk.drop_getVert] at hjx
  exact hjx ▸ p.getVert_mem_support (n + j)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A simple path of length at least two, closed by an edge between its
endpoints, gives a cycle.  The chosen orientation is convenient below. -/
private lemma isCycle_cons_reverse_of_isPath {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hlen : 2 ≤ p.length) (hba : G.Adj b a) :
    (p.reverse.cons hba.symm).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨hp.reverse, ?_⟩
  intro hedge
  have hedge' : s(a, b) ∈ p.edges := by
    simpa [Walk.edges_reverse] using hedge
  have hone := hp.length_eq_one_of_mem_edges hedge'
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The terminal of a positive lollipop tail is outside its cycle. -/
lemma Lollipop.terminal_not_mem_cycle (L : Lollipop G)
    (hpos : 0 < L.tail.length) : L.terminal ∉ L.cycle.support := by
  intro hyC
  have hEq : L.terminal = L.start :=
    L.cycle_tail_inter hyC L.tail.end_mem_support
  have hzero : L.tail.length = 0 := by
    symm
    apply L.tail_isPath.getVert_injOn (x₁ := 0) (x₂ := L.tail.length)
      (by simp) (by simp)
    rw [L.tail.getVert_zero, L.tail.getVert_length, hEq]
  omega

/-- The longest cycle rotated to start at the tail attachment. -/
def BestLollipop.rotatedCycle (B : BestLollipop G) :
    G.Walk B.start B.start :=
  B.cycle.rotate B.start B.start_mem_cycle

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] lemma BestLollipop.rotatedCycle_length (B : BestLollipop G) :
    B.rotatedCycle.length = B.cycle.length :=
  Walk.length_rotate B.cycle B.start B.start_mem_cycle

omit [Fintype V] [DecidableRel G.Adj] in
lemma BestLollipop.rotatedCycle_isCycle (B : BestLollipop G) :
    B.rotatedCycle.IsCycle :=
  B.cycle_isCycle.rotate B.start_mem_cycle

omit [Fintype V] [DecidableRel G.Adj] in
lemma BestLollipop.mem_cycle_of_mem_rotatedCycle (B : BestLollipop G) {w : V}
    (hw : w ∈ B.rotatedCycle.support) : w ∈ B.cycle.support :=
  (Walk.mem_support_rotate_iff B.cycle B.start B.start_mem_cycle).mp hw

omit [Fintype V] [DecidableRel G.Adj] [DecidableEq V] in
/-- In the complementary prefix and suffix obtained by deleting the cycle
edge at positions `i,i+1`, the only common vertex is the cycle base. -/
private lemma drop_succ_meet_take_eq_start {x : V} {C : G.Walk x x}
    (hC : C.IsCycle) {i : ℕ} (hi : i + 1 < C.length) :
    ∀ ⦃w : V⦄, w ∈ (C.drop (i + 1)).support →
      w ∈ (C.take i).support → w = x := by
  classical
  intro w hwD hwT
  obtain ⟨j, hjw, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hwD
  obtain ⟨k, hkw, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hwT
  rw [Walk.drop_getVert] at hjw
  rw [Walk.take_length, min_eq_left (by omega : i ≤ C.length)] at hkle
  rw [Walk.take_getVert, min_eq_right hkle] at hkw
  have hjbound : i + 1 + j ≤ C.length := by
    rw [Walk.drop_length] at hjle
    omega
  by_cases hjend : i + 1 + j = C.length
  · calc
      w = C.getVert (i + 1 + j) := hjw.symm
      _ = C.getVert C.length := by rw [hjend]
      _ = x := C.getVert_length
  · have hjlt : i + 1 + j < C.length := lt_of_le_of_ne hjbound hjend
    have hkeq : i + 1 + j = k := by
      apply hC.getVert_injOn' (x₁ := i + 1 + j) (x₂ := k)
      · change i + 1 + j ≤ C.length - 1
        omega
      · change k ≤ C.length - 1
        omega
      · exact hjw.trans hkw.symm
    omega

omit [DecidableRel G.Adj] [Fintype V] in
/-- Geometry of one positive-index cycle neighbor of the terminal.  Both
complementary cycle arcs can be closed through the lollipop tail, so longest-
cycle maximality puts the index in the exact interval
`[tail.length+1, cycle.length-tail.length-1]`. -/
theorem BestLollipop.cycle_neighbor_index_bounds
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    {i : ℕ} (hi : i < B.rotatedCycle.length) (hi0 : 0 < i)
    (hyi : G.Adj B.terminal (B.rotatedCycle.getVert i)) :
    B.tail.length + 1 ≤ i ∧
      i ≤ B.rotatedCycle.length - B.tail.length - 1 := by
  classical
  let C := B.rotatedCycle
  let A₁ : G.Walk (C.getVert i) B.start := C.drop i
  have hA₁ : A₁.IsPath := B.rotatedCycle_isCycle.isPath_drop hi0
  have hmeet₁ : ∀ ⦃w : V⦄, w ∈ A₁.support →
      w ∈ B.tail.support → w = B.start := by
    intro w hwA hwP
    apply B.cycle_tail_inter _ hwP
    apply B.mem_cycle_of_mem_rotatedCycle
    exact mem_support_of_mem_drop C i hwA
  let R₁ : G.Walk (C.getVert i) B.terminal := A₁.append B.tail
  have hR₁ : R₁.IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hA₁ B.tail_isPath hmeet₁
  have hR₁len : R₁.length =
      (C.length - i) + B.tail.length := by
    simp [R₁, A₁]
  have hR₁two : 2 ≤ R₁.length := by
    have hApos : 0 < C.length - i := Nat.sub_pos_of_lt hi
    rw [hR₁len]
    omega
  let D₁ : G.Walk (C.getVert i) (C.getVert i) :=
    R₁.reverse.cons hyi.symm
  have hD₁ : D₁.IsCycle :=
    isCycle_cons_reverse_of_isPath R₁ hR₁ hR₁two hyi
  have hD₁len : D₁.length =
      (C.length - i) + B.tail.length + 1 := by
    simp [D₁, hR₁len]
  have hmax₁ : D₁.length ≤ B.cycle.length := B.cycle_maximal D₁ hD₁
  have hmax₁' : D₁.length ≤ C.length := by simpa [C] using hmax₁
  have hlower : B.tail.length + 1 ≤ i := by
    rw [hD₁len] at hmax₁'
    omega
  let A₂ : G.Walk (C.getVert i) B.start := (C.take i).reverse
  have hA₂ : A₂.IsPath := (B.rotatedCycle_isCycle.isPath_take hi).reverse
  have hmeet₂ : ∀ ⦃w : V⦄, w ∈ A₂.support →
      w ∈ B.tail.support → w = B.start := by
    intro w hwA hwP
    apply B.cycle_tail_inter _ hwP
    apply B.mem_cycle_of_mem_rotatedCycle
    apply mem_support_of_mem_take C i
    simpa [A₂] using hwA
  let R₂ : G.Walk (C.getVert i) B.terminal := A₂.append B.tail
  have hR₂ : R₂.IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hA₂ B.tail_isPath hmeet₂
  have hiC : i ≤ C.length := by simpa [C] using hi.le
  have hR₂len : R₂.length = i + B.tail.length := by
    simp [R₂, A₂, min_eq_left hiC]
  have hR₂two : 2 ≤ R₂.length := by rw [hR₂len]; omega
  let D₂ : G.Walk (C.getVert i) (C.getVert i) :=
    R₂.reverse.cons hyi.symm
  have hD₂ : D₂.IsCycle :=
    isCycle_cons_reverse_of_isPath R₂ hR₂ hR₂two hyi
  have hD₂len : D₂.length = i + B.tail.length + 1 := by
    simp [D₂, hR₂len]
  have hmax₂ : D₂.length ≤ B.cycle.length := B.cycle_maximal D₂ hD₂
  have hmax₂' : D₂.length ≤ C.length := by simpa [C] using hmax₂
  have hupper : i ≤ C.length - B.tail.length - 1 := by
    rw [hD₂len] at hmax₂'
    omega
  exact ⟨hlower, hupper⟩

omit [DecidableRel G.Adj] [Fintype V] in
/-- Two positive cycle-neighbor indices of the lollipop terminal cannot be
consecutive: replacing their intervening cycle edge by the two-edge detour
through the terminal would produce a cycle one edge longer. -/
theorem BestLollipop.not_succ_cycle_neighbor
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    {i : ℕ} (hi : i + 1 < B.rotatedCycle.length)
    (hyi : G.Adj B.terminal (B.rotatedCycle.getVert i)) :
    ¬ G.Adj B.terminal (B.rotatedCycle.getVert (i + 1)) := by
  classical
  intro hyi1
  let C := B.rotatedCycle
  have hiC : i + 1 < C.length := by simpa [C] using hi
  let A : G.Walk (C.getVert (i + 1)) B.start := C.drop (i + 1)
  let Z : G.Walk B.start (C.getVert i) := C.take i
  have hA : A.IsPath := B.rotatedCycle_isCycle.isPath_drop (by omega)
  have hZ : Z.IsPath := B.rotatedCycle_isCycle.isPath_take (by omega)
  have hmeet : ∀ ⦃w : V⦄, w ∈ A.support → w ∈ Z.support → w = B.start := by
    intro w hwA hwZ
    exact drop_succ_meet_take_eq_start B.rotatedCycle_isCycle hiC hwA hwZ
  let R : G.Walk (C.getVert (i + 1)) (C.getVert i) := A.append Z
  have hR : R.IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hA hZ hmeet
  have hRlen : R.length = C.length - 1 := by
    simp [R, A, Z, min_eq_left (show i ≤ C.length by omega)]
    omega
  have hyOut : B.terminal ∉ B.cycle.support :=
    B.toLollipop.terminal_not_mem_cycle hpos
  have hyR : B.terminal ∉ R.support := by
    intro hy
    simp only [R, Walk.mem_support_append_iff] at hy
    rcases hy with hyA | hyZ
    · apply hyOut
      apply B.mem_cycle_of_mem_rotatedCycle
      exact mem_support_of_mem_drop C (i + 1) hyA
    · apply hyOut
      apply B.mem_cycle_of_mem_rotatedCycle
      exact mem_support_of_mem_take C i hyZ
  let S : G.Walk (C.getVert (i + 1)) B.terminal :=
    R.concat hyi.symm
  have hS : S.IsPath := hR.concat hyR hyi.symm
  have hSlen : S.length = C.length := by
    simp [S, hRlen]
    have := B.rotatedCycle_isCycle.three_le_length
    omega
  have hStwo : 2 ≤ S.length := by
    rw [hSlen]
    exact B.rotatedCycle_isCycle.three_le_length.trans' (by omega)
  let D : G.Walk (C.getVert (i + 1)) (C.getVert (i + 1)) :=
    S.reverse.cons hyi1.symm
  have hD : D.IsCycle :=
    isCycle_cons_reverse_of_isPath S hS hStwo hyi1
  have hDlen : D.length = C.length + 1 := by
    simp [D, hSlen]
  have hmax := B.cycle_maximal D hD
  have hmax' : D.length ≤ C.length := by simpa [C] using hmax
  rw [hDlen] at hmax'
  omega

omit [Fintype V] in
/-- The exact interval and successor-exclusion package consumed by the
nonconsecutive-index count. -/
theorem BestLollipop.positive_cycle_neighbor_geometry
    (B : BestLollipop G) (hpos : 0 < B.tail.length) :
    (∀ i ∈ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal,
      B.tail.length + 1 ≤ i) ∧
    (∀ i ∈ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal,
      i ≤ B.rotatedCycle.length - B.tail.length - 1) ∧
    (∀ i ∈ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal,
      i + 1 ∉ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [E767Case1Fixed.mem_positiveCycleNeighborIndices] at hi
    exact (B.cycle_neighbor_index_bounds hpos hi.2.1
      (Nat.pos_of_ne_zero hi.1) hi.2.2).1
  · intro i hi
    rw [E767Case1Fixed.mem_positiveCycleNeighborIndices] at hi
    exact (B.cycle_neighbor_index_bounds hpos hi.2.1
      (Nat.pos_of_ne_zero hi.1) hi.2.2).2
  · intro i hi hi1
    rw [E767Case1Fixed.mem_positiveCycleNeighborIndices] at hi hi1
    exact B.not_succ_cycle_neighbor hpos hi1.2.1 hi.2.2 hi1.2.2

/-- Fully assembled Case 1: if the positive cycle-neighbor set is nonempty,
the terminal degree is at most half the longest-cycle length. -/
theorem BestLollipop.two_mul_degree_terminal_le_cycle_length_case1
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    (hcover : G.neighborFinset B.terminal ⊆
      B.rotatedCycle.support.dropLast.toFinset ∪ B.tail.support.toFinset)
    (hnonempty : (E767Case1Fixed.positiveCycleNeighborIndices
      B.rotatedCycle B.terminal).Nonempty) :
    2 * G.degree B.terminal ≤ B.cycle.length := by
  obtain ⟨hlower, hupper, hnext⟩ := B.positive_cycle_neighbor_geometry hpos
  have hbound := E767Case1Fixed.case1_of_positive_indices
    B.rotatedCycle_isCycle B.tail_isPath hcover hnonempty
    hlower hupper hnext (k := G.degree B.terminal) (le_refl _)
  simpa using hbound

end

end Erdos767Scratch

-- END Case1Geometry

-- BEGIN Case1

open Finset
open scoped SimpleGraph

namespace Erdos767Scratch

open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] [DecidableEq V] in
/-- Tail maximality gives the standard terminal-neighbour cover. -/
lemma BestLollipop.neighbor_mem_cycle_or_tail' (B : BestLollipop G)
    {w : V} (hw : G.Adj B.terminal w) :
    w ∈ B.cycle.support ∨ w ∈ B.tail.support := by
  classical
  by_contra hout
  push Not at hout
  let L : Lollipop G :=
    { cycleBase := B.cycleBase
      cycle := B.cycle
      cycle_isCycle := B.cycle_isCycle
      start := B.start
      terminal := w
      tail := B.tail.concat hw
      tail_isPath := B.tail_isPath.concat hout.2 hw
      start_mem_cycle := B.start_mem_cycle
      cycle_tail_inter := by
        intro v hvC hvP
        simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hvP
        rcases hvP with hvP | rfl
        · exact B.cycle_tail_inter hvC hvP
        · exact (hout.1 hvC).elim }
  have hle := B.tail_maximal L rfl
  simp [L] at hle

omit [DecidableRel G.Adj] [Fintype V] in
/-- The non-repeated carrier of the rooted cycle is exactly the carrier of
the original longest cycle. -/
lemma BestLollipop.rotated_dropLast_toFinset_eq_cycle (B : BestLollipop G) :
    B.rotatedCycle.support.dropLast.toFinset = B.cycle.support.toFinset := by
  classical
  let C := B.rotatedCycle
  have hdrop : C.support.toFinset = C.support.dropLast.toFinset := by
    simpa [E767WalkIndex.cycleVertexFinset] using
      E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
        B.rotatedCycle_isCycle
  rw [← hdrop]
  ext w
  simp only [List.mem_toFinset]
  exact Walk.mem_support_rotate_iff B.cycle B.start B.start_mem_cycle

/-- The exact finset cover consumed by the checked Case-1 counting theorem. -/
lemma BestLollipop.neighborFinset_subset_rotatedCycle_union_tail
    (B : BestLollipop G) :
    G.neighborFinset B.terminal ⊆
      B.rotatedCycle.support.dropLast.toFinset ∪ B.tail.support.toFinset := by
  intro w hw
  have hadj : G.Adj B.terminal w := (G.mem_neighborFinset _ _).mp hw
  rcases B.neighbor_mem_cycle_or_tail' hadj with hwC | hwP
  · apply Finset.mem_union_left
    rw [B.rotated_dropLast_toFinset_eq_cycle]
    exact List.mem_toFinset.mpr hwC
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hwP)

/-- If the positive cycle-neighbour set is empty, every terminal neighbour
lies on the tail (the index-zero attachment already lies there). -/
lemma BestLollipop.all_neighbors_tail_of_positive_cycle_indices_empty
    (B : BestLollipop G)
    (hempty : E767Case1Fixed.positiveCycleNeighborIndices
      B.rotatedCycle B.terminal = ∅) :
    G.neighborFinset B.terminal ⊆ B.tail.support.toFinset := by
  intro w hw
  have hadj : G.Adj B.terminal w := (G.mem_neighborFinset _ _).mp hw
  rcases B.neighbor_mem_cycle_or_tail' hadj with hwC | hwP
  · by_cases hws : w = B.start
    · subst w
      exact List.mem_toFinset.mpr B.tail.start_mem_support
    have hwR : w ∈ B.rotatedCycle.support :=
      (Walk.mem_support_rotate_iff B.cycle B.start B.start_mem_cycle).mpr hwC
    have hwCarrier : w ∈ E767WalkIndex.cycleVertexFinset B.rotatedCycle := by
      rw [← E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
        B.rotatedCycle_isCycle, List.mem_toFinset]
      exact hwR
    rw [E767WalkIndex.cycleVertexFinset_eq_image_cycleIndices
      B.rotatedCycle_isCycle] at hwCarrier
    obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hwCarrier
    have hi0 : i ≠ 0 := by
      intro hi0
      subst i
      apply hws
      simpa using hiw.symm
    have hiS : i ∈ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal := by
      rw [E767Case1Fixed.mem_positiveCycleNeighborIndices]
      refine ⟨hi0, E767WalkIndex.mem_cycleIndices.mp hi, ?_⟩
      exact hiw ▸ hadj
    rw [hempty] at hiS
    simp at hiS
  · exact List.mem_toFinset.mpr hwP

/-- The complete output of Case 1, phrased as a dichotomy ready for the
aligned-fan Case 2: either the relative Dirac degree bound already holds, or
all neighbours of the terminal lie on the tail. -/
theorem BestLollipop.degree_bound_or_all_neighbors_tail
    (B : BestLollipop G) (hpos : 0 < B.tail.length) :
    2 * G.degree B.terminal ≤ B.cycle.length ∨
      G.neighborFinset B.terminal ⊆ B.tail.support.toFinset := by
  by_cases hS : (E767Case1Fixed.positiveCycleNeighborIndices
      B.rotatedCycle B.terminal).Nonempty
  · left
    exact B.two_mul_degree_terminal_le_cycle_length_case1 hpos
      B.neighborFinset_subset_rotatedCycle_union_tail hS
  · right
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    exact B.all_neighbors_tail_of_positive_cycle_indices_empty hS

end

end Erdos767Scratch

-- END Case1

-- BEGIN Case2EqualA

open Finset
open scoped SimpleGraph

namespace E767Case2EqualA

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] [Fintype V] in
/-- One rooted ear which avoids the lollipop attachment replaces the deleted
root edge of the cycle by at least two edges and hence lengthens the cycle. -/
private theorem exists_longer_cycle_of_rooted_ear_avoiding_attachment
    (B : BestLollipop G) (_hpos : 0 < B.tail.length)
    {b : V} (R : G.Walk B.rotatedCycle.snd b) (hR : R.IsPath)
    (hb : b ∈ B.tail.support)
    (hcycle : ∀ w, w ∈ R.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd)
    (havoid : B.start ∉ R.support) :
    ∃ D : G.Walk B.rotatedCycle.snd B.rotatedCycle.snd,
      D.IsCycle ∧ B.cycle.length < D.length := by
  classical
  let C := B.rotatedCycle
  let A : Finset V := C.support.dropLast.toFinset
  let T : Finset V := B.tail.support.toFinset
  have hxA : C.snd ∈ A := by
    have hxC : C.snd ∈ C.support := List.tail_subset C.support
      (C.snd_mem_tail_support B.rotatedCycle_isCycle.not_nil)
    have hxF : C.snd ∈ C.support.toFinset := List.mem_toFinset.mpr hxC
    rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
      B.rotatedCycle_isCycle] at hxF
    exact hxF
  have hbT : b ∈ T := List.mem_toFinset.mpr hb
  obtain ⟨K⟩ := E767DiracBuild.exists_blockEar hR A T hxA hbT
  have hKa : K.a = C.snd := by
    apply hcycle K.a
    · exact K.support_subset K.a K.path.start_mem_support
    · exact K.a_mem
  let E : G.Walk C.snd K.b := K.path.copy hKa rfl
  have hE : E.IsPath := by
    simpa [E, Walk.support_copy] using K.isPath
  have hEb : K.b ∈ B.tail.support := List.mem_toFinset.mp K.b_mem
  have hKb_ne_start : K.b ≠ B.start := by
    intro heq
    apply havoid
    have : K.b ∈ R.support :=
      K.support_subset K.b K.path.end_mem_support
    simpa [heq] using this
  have hx_ne_start : C.snd ≠ B.start := by
    have hadj : G.Adj B.start C.snd := C.adj_snd B.rotatedCycle_isCycle.not_nil
    exact hadj.ne.symm
  have hKb_ne_x : K.b ≠ C.snd := by
    intro heq
    have hKbC : K.b ∈ B.cycle.support := by
      apply B.mem_cycle_of_mem_rotatedCycle
      rw [heq]
      exact List.tail_subset C.support
        (C.snd_mem_tail_support B.rotatedCycle_isCycle.not_nil)
    have : K.b = B.start := B.cycle_tail_inter hKbC hEb
    exact hx_ne_start (heq.symm.trans this)
  let P : G.Walk B.start K.b := B.tail.takeUntil K.b hEb
  have hP : P.IsPath := B.tail_isPath.takeUntil hEb
  have hmeetCP : ∀ w : V, w ∈ C.tail.support →
      w ∈ P.support → w = B.start := by
    intro w hwC hwP
    apply B.cycle_tail_inter
    · apply B.mem_cycle_of_mem_rotatedCycle
      have hwC' : w ∈ C.support.tail := by
        rw [← C.support_tail_of_not_nil B.rotatedCycle_isCycle.not_nil]
        exact hwC
      exact List.tail_subset C.support hwC'
    · exact B.tail.support_takeUntil_subset_support hEb hwP
  let Q : G.Walk C.snd K.b := C.tail.append P
  have hQ : Q.IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end
      B.rotatedCycle_isCycle.isPath_tail hP hmeetCP
  have hdisj : Q.support.tail.Disjoint E.reverse.support.tail := by
    rw [List.disjoint_left]
    intro w hwQ hwE
    have hwQ' : w ∈ Q.support := List.mem_of_mem_tail hwQ
    have hwE' : w ∈ E.reverse.support := List.mem_of_mem_tail hwE
    have hwK : w ∈ K.path.support := by
      simpa [E, Walk.support_reverse, Walk.support_copy] using hwE'
    simp only [Q, Walk.mem_support_append_iff] at hwQ'
    rcases hwQ' with hwC | hwP
    · have hwCF : w ∈ A := by
        have hwC' : w ∈ C.support.tail := by
          rw [← C.support_tail_of_not_nil B.rotatedCycle_isCycle.not_nil]
          exact hwC
        have hwCs : w ∈ C.support := List.tail_subset C.support hwC'
        have hwCf : w ∈ C.support.toFinset := List.mem_toFinset.mpr hwCs
        rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
          B.rotatedCycle_isCycle] at hwCf
        exact hwCf
      have hwx : w = C.snd := (K.meet_A w hwK hwCF).trans hKa
      have hxnot : C.snd ∉ Q.support.tail := by
        have hn := hQ.support_nodup
        rw [← Q.cons_tail_support, List.nodup_cons] at hn
        exact hn.1
      exact hxnot (hwx ▸ hwQ)
    · have hwTail : w ∈ T := by
        apply List.mem_toFinset.mpr
        exact B.tail.support_takeUntil_subset_support hEb hwP
      have hwb : w = K.b := K.meet_B w hwK hwTail
      have hbnot : K.b ∉ E.reverse.support.tail := by
        have hn := hE.reverse.support_nodup
        rw [← E.reverse.cons_tail_support, List.nodup_cons] at hn
        exact hn.1
      exact hbnot (hwb ▸ hwE)
  let D : G.Walk C.snd C.snd := Q.append E.reverse
  have hQtwo : 1 < Q.length := by
    have htail : C.tail.length = C.length - 1 := C.length_tail
    have hthree : 3 ≤ C.length := by
      simpa [C] using B.rotatedCycle_isCycle.three_le_length
    have hle : C.tail.length ≤ Q.length := by simp [Q]
    omega
  have hD : D.IsCycle :=
    hQ.isCycle_append hE.reverse hdisj (Or.inl hQtwo)
  have hPpos : 0 < P.length := by
    rw [← Walk.not_nil_iff_lt_length]
    exact Walk.not_nil_of_ne hKb_ne_start.symm
  have hEpos : 0 < E.length := by
    rw [← Walk.not_nil_iff_lt_length]
    exact Walk.not_nil_of_ne hKb_ne_x.symm
  have hDlen : D.length = C.tail.length + P.length + E.length := by
    simp [D, Q, Walk.length_append]
  have hCtail : C.tail.length = C.length - 1 := C.length_tail
  have hlong : C.length < D.length := by
    rw [hDlen, hCtail]
    omega
  refine ⟨D, hD, ?_⟩
  simpa [C] using hlong

omit [DecidableRel G.Adj] [Fintype V] in
/-- Exceptional equal-last-cycle-endpoint branch of the aligned-fan proof.

After the two extracted ears have been rewritten to start at the common
cycle root, internal disjointness makes at least one ear avoid the deleted
cycle-edge endpoint.  Re-extracting its first hit on the whole lollipop tail
then gives the strictly longer replacement cycle. -/
theorem exists_longer_cycle_of_two_rooted_ears
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    {b₁ b₂ : V}
    (R₁ : G.Walk B.rotatedCycle.snd b₁)
    (R₂ : G.Walk B.rotatedCycle.snd b₂)
    (hR₁ : R₁.IsPath) (hR₂ : R₂.IsPath)
    (hb₁ : b₁ ∈ B.tail.support) (hb₂ : b₂ ∈ B.tail.support)
    (hcycle₁ : ∀ w, w ∈ R₁.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd)
    (hcycle₂ : ∀ w, w ∈ R₂.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd)
    (hmeet : ∀ w, w ∈ R₁.support → w ∈ R₂.support →
      w = B.rotatedCycle.snd) :
    ∃ D : G.Walk B.rotatedCycle.snd B.rotatedCycle.snd,
      D.IsCycle ∧ B.cycle.length < D.length := by
  classical
  by_cases hs₁ : B.start ∈ R₁.support
  · have hs₂ : B.start ∉ R₂.support := by
      intro hs₂
      have heq := hmeet B.start hs₁ hs₂
      have hadj : G.Adj B.start B.rotatedCycle.snd :=
        B.rotatedCycle.adj_snd B.rotatedCycle_isCycle.not_nil
      exact hadj.ne heq
    exact exists_longer_cycle_of_rooted_ear_avoiding_attachment
      B hpos R₂ hR₂ hb₂ hcycle₂ hs₂
  · exact exists_longer_cycle_of_rooted_ear_avoiding_attachment
      B hpos R₁ hR₁ hb₁ hcycle₁ hs₁

omit [DecidableRel G.Adj] [Fintype V] in
/-- Direct wrapper for the exceptional branch as it arises from the two
`BlockEar`s extracted from an aligned fan.  Equality of their last cycle
vertices and branch disjointness force that common vertex to be the fan
root, after which `exists_longer_cycle_of_two_rooted_ears` applies. -/
theorem exists_longer_cycle_of_equal_blockEars
    (B : BestLollipop G) (hpos : 0 < B.tail.length)
    {z₁ z₂ : V}
    (R₁ : G.Walk B.rotatedCycle.snd z₁)
    (R₂ : G.Walk B.rotatedCycle.snd z₂)
    (_hR₁ : R₁.IsPath) (_hR₂ : R₂.IsPath)
    (hmeet : ∀ w, w ∈ R₁.support → w ∈ R₂.support →
      w = B.rotatedCycle.snd)
    (Y : Finset V) (hYtail : Y ⊆ B.tail.support.toFinset)
    (E₁ : E767DiracBuild.BlockEar R₁
      B.rotatedCycle.support.dropLast.toFinset Y)
    (E₂ : E767DiracBuild.BlockEar R₂
      B.rotatedCycle.support.dropLast.toFinset Y)
    (haeq : E₁.a = E₂.a) :
    ∃ D : G.Walk B.rotatedCycle.snd B.rotatedCycle.snd,
      D.IsCycle ∧ B.cycle.length < D.length := by
  classical
  have ha₁root : E₁.a = B.rotatedCycle.snd := by
    apply hmeet E₁.a
    · exact E₁.support_subset E₁.a E₁.path.start_mem_support
    · rw [haeq]
      exact E₂.support_subset E₂.a E₂.path.start_mem_support
  have ha₂root : E₂.a = B.rotatedCycle.snd := haeq.symm.trans ha₁root
  let S₁ : G.Walk B.rotatedCycle.snd E₁.b := E₁.path.copy ha₁root rfl
  let S₂ : G.Walk B.rotatedCycle.snd E₂.b := E₂.path.copy ha₂root rfl
  have hS₁ : S₁.IsPath := by
    simpa [S₁, Walk.support_copy] using E₁.isPath
  have hS₂ : S₂.IsPath := by
    simpa [S₂, Walk.support_copy] using E₂.isPath
  have hb₁ : E₁.b ∈ B.tail.support :=
    List.mem_toFinset.mp (hYtail E₁.b_mem)
  have hb₂ : E₂.b ∈ B.tail.support :=
    List.mem_toFinset.mp (hYtail E₂.b_mem)
  have hcycle₁ : ∀ w, w ∈ S₁.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd := by
    intro w hwS hwC
    have hwE : w ∈ E₁.path.support := by simpa [S₁] using hwS
    exact (E₁.meet_A w hwE hwC).trans ha₁root
  have hcycle₂ : ∀ w, w ∈ S₂.support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = B.rotatedCycle.snd := by
    intro w hwS hwC
    have hwE : w ∈ E₂.path.support := by simpa [S₂] using hwS
    exact (E₂.meet_A w hwE hwC).trans ha₂root
  have hmeetS : ∀ w, w ∈ S₁.support → w ∈ S₂.support →
      w = B.rotatedCycle.snd := by
    intro w hw₁ hw₂
    have hwE₁ : w ∈ E₁.path.support := by simpa [S₁] using hw₁
    have hwE₂ : w ∈ E₂.path.support := by simpa [S₂] using hw₂
    exact hmeet w
      (E₁.support_subset w hwE₁) (E₂.support_subset w hwE₂)
  exact exists_longer_cycle_of_two_rooted_ears B hpos
    S₁ S₂ hS₁ hS₂ hb₁ hb₂ hcycle₁ hcycle₂ hmeetS

end

end E767Case2EqualA

-- END Case2EqualA

-- BEGIN Case2Splice

/-!
An abstract, walk-level certificate for the final (second) splice in the
best-lollipop proof of Dirac's circumference theorem.

The intended composite is

```
  a₂ --Q--> a₁ --R₁--> b₁ --A--> d --edge--> y --B--> b₂ --R₂⁻¹--> a₂.
```

`Q` is the chosen long arc of the old cycle.  `A`, the chord `d-y`, and `B`
are the two disjoint intervals on the lollipop handle.  The aligned-fork
argument is used upstream to establish `hbody` and `hdisj`; the present lemma
then checks the actual concatenation, simplicity, and the length estimate.
-/

open scoped SimpleGraph

namespace Erdos767DiracCase2

open SimpleGraph


variable {V : Type u} {G : SimpleGraph V}

/-- The open part of the Case 2 splice, from the second arc endpoint `a₁`
to the first arc endpoint `a₂`. -/
def spliceBody {a₁ a₂ b₁ b₂ d y : V}
    (R₁ : G.Walk a₁ b₁) (A : G.Walk b₁ d) (hdy : G.Adj d y)
    (B : G.Walk y b₂) (R₂ : G.Walk a₂ b₂) : G.Walk a₁ a₂ :=
  ((((R₁.append A).concat hdy).append B).append R₂.reverse)

@[simp] theorem spliceBody_length {a₁ a₂ b₁ b₂ d y : V}
    (R₁ : G.Walk a₁ b₁) (A : G.Walk b₁ d) (hdy : G.Adj d y)
    (B : G.Walk y b₂) (R₂ : G.Walk a₂ b₂) :
    (spliceBody R₁ A hdy B R₂).length =
      R₁.length + A.length + 1 + B.length + R₂.length := by
  simp [spliceBody, Walk.length_append, Walk.length_concat, Nat.add_assoc]

/-- A checked certificate for the second lollipop splice.

The hypotheses `hbody` and `hdisj` are exactly the qualitative output needed
from an aligned-fork certificate: the open spliced route is a simple path and
its vertices, apart from the joining endpoint, avoid the tail of the chosen
cycle arc.  `hmiddle` is the numeric neighbor-index count on the two handle
intervals.  The last two inequalities say that `Q` is the longer cycle arc
and that the old cycle has length below `2 * k`.
-/
theorem exists_longer_cycle_of_aligned_splice
    {a₁ a₂ b₁ b₂ d y z : V}
    (C : G.Walk z z) (Q : G.Walk a₂ a₁)
    (R₁ : G.Walk a₁ b₁) (A : G.Walk b₁ d) (hdy : G.Adj d y)
    (B : G.Walk y b₂) (R₂ : G.Walk a₂ b₂) (k : ℕ)
    (hC : C.IsCycle)
    (hQ : Q.IsPath)
    (hbody : (spliceBody R₁ A hdy B R₂).IsPath)
    (hdisj : Q.support.tail.Disjoint (spliceBody R₁ A hdy B R₂).support.tail)
    (hmiddle : k ≤ A.length + 1 + B.length)
    (hlongArc : C.length ≤ 2 * Q.length)
    (hshort : C.length < 2 * k) :
    ∃ D : G.Walk a₂ a₂,
      D.IsCycle ∧ Q.length + k ≤ D.length ∧ C.length < D.length := by
  let body : G.Walk a₁ a₂ := spliceBody R₁ A hdy B R₂
  let D : G.Walk a₂ a₂ := Q.append body
  have hQnontrivial : 1 < Q.length := by
    have hCthree : 3 ≤ C.length := hC.three_le_length
    omega
  have hDcycle : D.IsCycle := by
    exact hQ.isCycle_append hbody hdisj (Or.inl hQnontrivial)
  have hbodyMiddle : k ≤ body.length := by
    dsimp [body]
    rw [spliceBody_length]
    omega
  have hDlen : D.length = Q.length + body.length := by
    simp [D, Walk.length_append]
  have hQk : Q.length + k ≤ D.length := by
    rw [hDlen]
    omega
  have hOldLt : C.length < D.length := by
    rw [hDlen]
    omega
  exact ⟨D, hDcycle, hQk, hOldLt⟩

end Erdos767DiracCase2

-- END Case2Splice

-- BEGIN Case2Assembly

open Finset Set
open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
/-- The two last cycle vertices of the aligned ears are distinct.  Equality
would put both at the fan root and the checked exceptional splice would make
a cycle longer than the chosen longest cycle. -/
lemma Case2FanData.a_ne {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length) :
    D.E₁.a ≠ D.E₂.a := by
  intro haa
  have hYtail : (B.tail.drop j₁).support.toFinset ⊆
      B.tail.support.toFinset := by
    intro w hw
    have hw' := List.mem_toFinset.mp hw
    obtain ⟨i, hiw, _hi⟩ := Walk.mem_support_iff_exists_getVert.mp hw'
    rw [Walk.drop_getVert] at hiw
    exact List.mem_toFinset.mpr (hiw ▸ B.tail.getVert_mem_support (j₁ + i))
  obtain ⟨C, hC, hlong⟩ :=
    E767Case2EqualA.exists_longer_cycle_of_equal_blockEars B hpos
      D.F.toZ D.F.toY D.F.toZ_isPath D.F.toY_isPath D.F.meet_eq_start
      (B.tail.drop j₁).support.toFinset hYtail D.E₁ D.E₂ haa
  exact (Nat.not_lt_of_ge (B.cycle_maximal C hC)) hlong

end

end E767DiracBuild
-- END Case2Assembly

-- BEGIN Case2TailData

open Finset
open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The neighbor-index and actual tail-segment data used in the unequal-ear
branch of the aligned-fan splice. -/
structure Case2TailData (B : BestLollipop G) {j₁ : ℕ}
    (D : Case2FanData B j₁) where
  j' : ℕ
  j'_mem : j' ∈ E767WalkIndex.endNeighborIndices B.tail
  j'_lt : j' < D.j₂
  greatest : ∀ t ∈ E767WalkIndex.endNeighborIndices B.tail,
    t < D.j₂ → t ≤ j'
  A : G.Walk D.E₁.b (B.tail.getVert j')
  A_isPath : A.IsPath
  A_length : A.length = j' - j₁
  T : G.Walk (B.tail.getVert D.j₂) B.terminal
  T_isPath : T.IsPath
  T_length : T.length = B.tail.length - D.j₂
  chord : G.Adj (B.tail.getVert j') B.terminal
  degree_le : G.degree B.terminal ≤ A.length + 1 + T.length
  A_support_indices : ∀ v, v ∈ A.support →
    ∃ t, j₁ ≤ t ∧ t ≤ j' ∧ B.tail.getVert t = v
  T_support_indices : ∀ v, v ∈ T.support →
    ∃ t, D.j₂ ≤ t ∧ t ≤ B.tail.length ∧
      B.tail.getVert t = v

/-- Choose the greatest terminal-neighbor index below the second ear's first
suffix hit.  The two actual tail intervals contain enough vertices to pay
for every neighbor of the terminal. -/
theorem Case2FanData.exists_tailData
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁)
    (hj₁J : j₁ ∈ E767WalkIndex.endNeighborIndices B.tail)
    (hN : G.neighborFinset B.terminal ⊆ B.tail.support.toFinset) :
    Nonempty (Case2TailData B D) := by
  let J := E767WalkIndex.endNeighborIndices B.tail
  let L := J.filter fun t ↦ t < D.j₂
  have hj₁L : j₁ ∈ L := by
    simp only [L, Finset.mem_filter]
    exact ⟨hj₁J, D.j₁_lt_j₂⟩
  have hL : L.Nonempty := ⟨j₁, hj₁L⟩
  let j' := L.max' hL
  have hj'L : j' ∈ L := Finset.max'_mem L hL
  have hj'J : j' ∈ J := (Finset.mem_filter.mp hj'L).1
  have hj'lt : j' < D.j₂ := (Finset.mem_filter.mp hj'L).2
  have hgreatest : ∀ t ∈ J, t < D.j₂ → t ≤ j' := by
    intro t htJ htlt
    exact Finset.le_max' L t (Finset.mem_filter.mpr ⟨htJ, htlt⟩)
  have hj₁j' : j₁ ≤ j' := hgreatest j₁ hj₁J D.j₁_lt_j₂
  have hj'le : j' ≤ B.tail.length := by
    have := (E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath).mp
      hj'J |>.1
    omega
  let A₀ : G.Walk (B.tail.getVert j₁)
      ((B.tail.drop j₁).getVert (j' - j₁)) :=
    (B.tail.drop j₁).take (j' - j₁)
  have hAend : (B.tail.drop j₁).getVert (j' - j₁) =
      B.tail.getVert j' := by
    simp [Walk.drop_getVert, Nat.add_sub_of_le hj₁j']
  let A : G.Walk D.E₁.b (B.tail.getVert j') :=
    A₀.copy D.b₁_eq.symm hAend
  have hApath : A.IsPath := by
    simpa [A, A₀, Walk.support_copy] using
      (B.tail_isPath.drop j₁ |>.take (j' - j₁))
  have hAlen : A.length = j' - j₁ := by
    simp [A, A₀, Walk.length_copy, Walk.take_length, Walk.drop_length]
    omega
  let T : G.Walk (B.tail.getVert D.j₂) B.terminal := B.tail.drop D.j₂
  have hTpath : T.IsPath := B.tail_isPath.drop D.j₂
  have hTlen : T.length = B.tail.length - D.j₂ := by simp [T]
  have hchord : G.Adj (B.tail.getVert j') B.terminal := by
    exact ((E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath).mp
      hj'J).2.symm
  have hdegree : G.degree B.terminal ≤ A.length + 1 + T.length := by
    let Low := J.filter fun t ↦ t < D.j₂
    let High := J.filter fun t ↦ D.j₂ ≤ t
    have hJsub : J ⊆ Low ∪ High := by
      intro t ht
      by_cases hlt : t < D.j₂
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, hlt⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨ht, Nat.le_of_not_gt hlt⟩)
    have hLow : Low ⊆ Finset.Icc j₁ j' := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      have hj₁t : j₁ ≤ t := D.j₁_min t ht'.1
      exact Finset.mem_Icc.mpr ⟨hj₁t, hgreatest t ht'.1 ht'.2⟩
    have hHigh : High ⊆ Finset.Ico D.j₂ B.tail.length := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      have htell :=
        (E767WalkIndex.mem_endNeighborIndices_iff_lt B.tail_isPath).mp
          ht'.1 |>.1
      exact Finset.mem_Ico.mpr ⟨ht'.2, htell⟩
    have hcard : J.card ≤ (j' - j₁ + 1) +
        (B.tail.length - D.j₂) := by
      calc
        J.card ≤ (Low ∪ High).card := Finset.card_le_card hJsub
        _ ≤ Low.card + High.card := Finset.card_union_le _ _
        _ ≤ (Finset.Icc j₁ j').card +
            (Finset.Ico D.j₂ B.tail.length).card :=
          Nat.add_le_add (Finset.card_le_card hLow) (Finset.card_le_card hHigh)
        _ = (j' - j₁ + 1) + (B.tail.length - D.j₂) := by
          rw [Nat.card_Icc, Nat.card_Ico]
          omega
    have hJcard := E767WalkIndex.card_endNeighborIndices_eq_degree
      B.tail_isPath hN
    rw [← hJcard]
    rw [hAlen, hTlen]
    omega
  have hAsupp : ∀ v, v ∈ A.support →
      ∃ t, j₁ ≤ t ∧ t ≤ j' ∧ B.tail.getVert t = v := by
    intro v hv
    have hv₀ : v ∈ A₀.support := by simpa [A] using hv
    obtain ⟨r, hrv, hrle⟩ := Walk.mem_support_iff_exists_getVert.mp hv₀
    have hrle' : r ≤ j' - j₁ := by
      have hA₀len : A₀.length = (j' - j₁) ⊓ (B.tail.length - j₁) := by
        simp [A₀, Walk.drop_length]
      rw [hA₀len] at hrle
      omega
    refine ⟨j₁ + r, by omega, by omega, ?_⟩
    simpa [A₀, Walk.take_getVert, min_eq_right hrle', Walk.drop_getVert]
      using hrv
  have hTsupp : ∀ v, v ∈ T.support →
      ∃ t, D.j₂ ≤ t ∧ t ≤ B.tail.length ∧
        B.tail.getVert t = v := by
    intro v hv
    obtain ⟨r, hrv, hrle⟩ := Walk.mem_support_iff_exists_getVert.mp hv
    have hbound : D.j₂ + r ≤ B.tail.length := by
      have hTlen' : T.length = B.tail.length - D.j₂ := by simp [T]
      rw [hTlen'] at hrle
      have hj₂le := D.j₂_le
      omega
    refine ⟨D.j₂ + r, by omega, hbound, ?_⟩
    simpa [T, Walk.drop_getVert] using hrv
  exact ⟨{
    j' := j'
    j'_mem := hj'J
    j'_lt := hj'lt
    greatest := hgreatest
    A := A
    A_isPath := hApath
    A_length := hAlen
    T := T
    T_isPath := hTpath
    T_length := hTlen
    chord := hchord
    degree_le := hdegree
    A_support_indices := hAsupp
    T_support_indices := hTsupp }⟩

end

end E767DiracBuild
-- END Case2TailData

-- BEGIN SplicePath

open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

omit [DecidableEq V] [Fintype V] in
/-- A convenient qualitative constructor for the five-piece Case-2 body.
The geometric proof only has to establish the successive intersection
conditions; pathhood of the resulting nested append is then automatic. -/
lemma spliceBody_isPath_of_successive_meets
    {a₁ a₂ b₁ b₂ d y : V}
    (R₁ : G.Walk a₁ b₁) (A : G.Walk b₁ d) (hdy : G.Adj d y)
    (B : G.Walk y b₂) (R₂ : G.Walk a₂ b₂)
    (hR₁ : R₁.IsPath) (hA : A.IsPath) (hB : B.IsPath) (hR₂ : R₂.IsPath)
    (hR₁A : ∀ w, w ∈ R₁.support → w ∈ A.support → w = b₁)
    (hyR₁ : y ∉ R₁.support) (hyA : y ∉ A.support)
    (hpreB : ∀ w,
      w ∈ ((R₁.append A).concat hdy).support → w ∈ B.support → w = y)
    (hallR₂ : ∀ w,
      w ∈ (((R₁.append A).concat hdy).append B).support →
      w ∈ R₂.reverse.support → w = b₂) :
    (Erdos767DiracCase2.spliceBody R₁ A hdy B R₂).IsPath := by
  classical
  have hRA : (R₁.append A).IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hR₁ hA hR₁A
  have hyRA : y ∉ (R₁.append A).support := by
    intro hy
    rw [Walk.mem_support_append_iff] at hy
    exact hy.elim hyR₁ hyA
  have hRAy : ((R₁.append A).concat hdy).IsPath := hRA.concat hyRA hdy
  have hRAB : (((R₁.append A).concat hdy).append B).IsPath :=
    E767AlignedAlt.isPath_append_of_meet_eq_end hRAy hB hpreB
  exact E767AlignedAlt.isPath_append_of_meet_eq_end hRAB hR₂.reverse hallR₂

end E767DiracBuild

-- END SplicePath

-- BEGIN Case2Body

open Finset Set
open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The upper handle interval, oriented from the lollipop tip back to the
second ear. -/
def Case2TailData.returnPath {B : BestLollipop G} {j₁ : ℕ}
    {D : Case2FanData B j₁} (S : Case2TailData B D) :
    G.Walk B.terminal D.E₂.b :=
  S.T.reverse.copy rfl D.b₂_eq.symm

lemma Case2TailData.returnPath_isPath {B : BestLollipop G} {j₁ : ℕ}
    {D : Case2FanData B j₁} (S : Case2TailData B D) :
    S.returnPath.IsPath := by
  simpa [Case2TailData.returnPath, Walk.support_copy] using S.T_isPath.reverse

lemma Case2TailData.returnPath_support_indices
    {B : BestLollipop G} {j₁ : ℕ}
    {D : Case2FanData B j₁} (S : Case2TailData B D) :
    ∀ v, v ∈ S.returnPath.support →
      ∃ t, D.j₂ ≤ t ∧ t ≤ B.tail.length ∧ B.tail.getVert t = v := by
  intro v hv
  apply S.T_support_indices
  simpa [Case2TailData.returnPath, Walk.support_copy, Walk.support_reverse] using hv

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma tail_index_eq_of_getVert_eq {B : BestLollipop G}
    {i j : ℕ} (hi : i ≤ B.tail.length) (hj : j ≤ B.tail.length)
    (h : B.tail.getVert i = B.tail.getVert j) : i = j :=
  B.tail_isPath.getVert_injOn hi hj h

/-- The open five-piece route in Case 2 is a simple path. -/
theorem Case2FanData.spliceBody_isPath
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length)
    (S : Case2TailData B D) :
    (Erdos767DiracCase2.spliceBody
      D.E₁.path S.A S.chord S.returnPath D.E₂.path).IsPath := by
  have hj₁le : j₁ ≤ B.tail.length := D.j₁_le_j₂.trans D.j₂_le
  have hj₁ltell : j₁ < B.tail.length :=
    lt_of_lt_of_le D.j₁_lt_j₂ D.j₂_le
  have hR₁A : ∀ w, w ∈ D.E₁.path.support → w ∈ S.A.support →
      w = D.E₁.b := by
    intro w hwR hwA
    obtain ⟨t, hj₁t, htj', htw⟩ := S.A_support_indices w hwA
    have htell : t ≤ B.tail.length :=
      htj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
    have hwY : w ∈ (B.tail.drop j₁).support := by
      rw [← htw]
      exact (E767WalkIndex.getVert_mem_drop_support_iff B.tail_isPath
        hj₁le htell).mpr hj₁t
    exact D.E₁.meet_B w hwR (List.mem_toFinset.mpr hwY)
  have hyR₁ : B.terminal ∉ D.E₁.path.support := by
    intro hyR
    have hyY : B.terminal ∈ (B.tail.drop j₁).support :=
      (B.tail.drop j₁).end_mem_support
    have hyb := D.E₁.meet_B B.terminal hyR (List.mem_toFinset.mpr hyY)
    have hget : B.tail.getVert B.tail.length = B.tail.getVert j₁ := by
      simpa [D.b₁_eq] using hyb
    have := tail_index_eq_of_getVert_eq (B := B) (i := B.tail.length)
      (j := j₁) le_rfl hj₁le hget
    omega
  have hyA : B.terminal ∉ S.A.support := by
    intro hyA
    obtain ⟨t, hj₁t, htj', hty⟩ := S.A_support_indices _ hyA
    have htell : t ≤ B.tail.length :=
      htj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
    have hget : B.tail.getVert t = B.tail.getVert B.tail.length := by
      simpa using hty
    have heq := tail_index_eq_of_getVert_eq (B := B) htell le_rfl hget
    have hj'ltell : S.j' < B.tail.length := S.j'_lt.trans_le D.j₂_le
    omega
  have hpreU : ∀ w,
      w ∈ ((D.E₁.path.append S.A).concat S.chord).support →
      w ∈ S.returnPath.support → w = B.terminal := by
    intro w hwpre hwU
    obtain ⟨t, hj₂t, htell, htw⟩ := S.returnPath_support_indices w hwU
    rw [Walk.support_concat] at hwpre
    rcases List.mem_append.mp hwpre with hwRA | hwY
    · rw [Walk.mem_support_append_iff] at hwRA
      rcases hwRA with hwR | hwA
      · have hwY' : w ∈ (B.tail.drop j₁).support := by
          rw [← htw]
          exact (E767WalkIndex.getVert_mem_drop_support_iff B.tail_isPath
            hj₁le htell).mpr (D.j₁_le_j₂.trans hj₂t)
        have hwb := D.E₁.meet_B w hwR (List.mem_toFinset.mpr hwY')
        have hget : B.tail.getVert t = B.tail.getVert j₁ := by
          simpa [D.b₁_eq] using htw.trans hwb
        have heq := tail_index_eq_of_getVert_eq (B := B) htell hj₁le hget
        have hj₁ltj₂ := D.j₁_lt_j₂
        omega
      · obtain ⟨r, hj₁r, hrj', hrw⟩ := S.A_support_indices w hwA
        have hrle : r ≤ B.tail.length :=
          hrj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
        have hget : B.tail.getVert r = B.tail.getVert t := hrw.trans htw.symm
        have heq := tail_index_eq_of_getVert_eq (B := B) hrle htell hget
        have hrj₂ : r < D.j₂ := hrj'.trans_lt S.j'_lt
        omega
    · simpa using hwY
  have hallR₂ : ∀ w,
      w ∈ (((D.E₁.path.append S.A).concat S.chord).append
        S.returnPath).support →
      w ∈ D.E₂.path.reverse.support → w = D.E₂.b := by
    intro w hwAll hwR₂rev
    have hwR₂ : w ∈ D.E₂.path.support := by
      simpa [Walk.support_reverse] using hwR₂rev
    rw [Walk.mem_support_append_iff] at hwAll
    rcases hwAll with hwpre | hwU
    · rw [Walk.support_concat] at hwpre
      rcases List.mem_append.mp hwpre with hwRA | hwTip
      · rw [Walk.mem_support_append_iff] at hwRA
        rcases hwRA with hwR₁ | hwA
        · have hwF₁ := D.E₁.support_subset w hwR₁
          have hwF₂ := D.E₂.support_subset w hwR₂
          have hwroot := D.F.meet_eq_start hwF₁ hwF₂
          have hrootX : (BestLollipop.rootedCycle B).snd ∈
              (BestLollipop.rootedCycle B).support.dropLast.toFinset := by
            have hxF : (BestLollipop.rootedCycle B).snd ∈
                (BestLollipop.rootedCycle B).support.toFinset :=
              List.mem_toFinset.mpr (BestLollipop.reference_start_mem_cycle B)
            rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
              (BestLollipop.rootedCycle_isCycle B)] at hxF
            exact hxF
          have ha₁ : w = D.E₁.a :=
            D.E₁.meet_A w hwR₁ (hwroot ▸ hrootX)
          have ha₂ : w = D.E₂.a :=
            D.E₂.meet_A w hwR₂ (hwroot ▸ hrootX)
          exact (D.a_ne hpos (ha₁.symm.trans ha₂)).elim
        · obtain ⟨t, hj₁t, htj', htw⟩ := S.A_support_indices w hwA
          have htell : t ≤ B.tail.length :=
            htj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
          have hwY : w ∈ (B.tail.drop j₁).support := by
            rw [← htw]
            exact (E767WalkIndex.getVert_mem_drop_support_iff B.tail_isPath
              hj₁le htell).mpr hj₁t
          exact D.E₂.meet_B w hwR₂ (List.mem_toFinset.mpr hwY)
      · have hwy : w = B.terminal := by simpa using hwTip
        have hyY : B.terminal ∈ (B.tail.drop j₁).support :=
          (B.tail.drop j₁).end_mem_support
        have hwY : w ∈ (B.tail.drop j₁).support.toFinset := by
          rw [hwy]
          exact List.mem_toFinset.mpr hyY
        exact D.E₂.meet_B w hwR₂ hwY
    · obtain ⟨t, hj₂t, htell, htw⟩ := S.returnPath_support_indices w hwU
      have hwY : w ∈ (B.tail.drop j₁).support := by
        rw [← htw]
        exact (E767WalkIndex.getVert_mem_drop_support_iff B.tail_isPath
          hj₁le htell).mpr (D.j₁_le_j₂.trans hj₂t)
      exact D.E₂.meet_B w hwR₂ (List.mem_toFinset.mpr hwY)
  exact spliceBody_isPath_of_successive_meets
    D.E₁.path S.A S.chord S.returnPath D.E₂.path
    D.E₁.isPath S.A_isPath S.returnPath_isPath D.E₂.isPath
    hR₁A hyR₁ hyA hpreU hallR₂

/-- Every cycle vertex of the open Case-2 body is one of its two endpoints. -/
theorem Case2FanData.spliceBody_meets_cycle
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length)
    (S : Case2TailData B D) :
    ∀ w,
      w ∈ (Erdos767DiracCase2.spliceBody
        D.E₁.path S.A S.chord S.returnPath D.E₂.path).support →
      w ∈ B.rotatedCycle.support.dropLast.toFinset →
      w = D.E₁.a ∨ w = D.E₂.a := by
  intro w hwBody hwCycle
  have hwCycleOrig : w ∈ B.cycle.support := by
    apply B.mem_cycle_of_mem_rotatedCycle
    exact List.mem_of_mem_dropLast (List.mem_toFinset.mp hwCycle)
  change w ∈ ((((D.E₁.path.append S.A).concat S.chord).append
    S.returnPath).append D.E₂.path.reverse).support at hwBody
  rw [Walk.mem_support_append_iff] at hwBody
  rcases hwBody with hwBody | hwR₂rev
  · rw [Walk.mem_support_append_iff] at hwBody
    rcases hwBody with hwPre | hwU
    · rw [Walk.support_concat] at hwPre
      rcases List.mem_append.mp hwPre with hwRA | hwy
      · rw [Walk.mem_support_append_iff] at hwRA
        rcases hwRA with hwR₁ | hwA
        · exact Or.inl (D.E₁.meet_A w hwR₁ hwCycle)
        · obtain ⟨t, hj₁t, htj', htw⟩ := S.A_support_indices w hwA
          have htell : t ≤ B.tail.length :=
            htj'.trans (Nat.le_of_lt (S.j'_lt.trans_le D.j₂_le))
          have hwTail : w ∈ B.tail.support := by
            rw [← htw]
            exact B.tail.getVert_mem_support t
          have hwStart : w = B.start := B.cycle_tail_inter hwCycleOrig hwTail
          have hget : B.tail.getVert t = B.tail.getVert 0 := by
            simpa [hwStart] using htw
          have ht0 := tail_index_eq_of_getVert_eq (B := B) htell (by omega) hget
          have hj₁0 : j₁ = 0 := by omega
          have hbStart : D.E₁.b = B.start := by
            rw [D.b₁_eq, hj₁0]
            simp
          have hsCycle : B.start ∈
              (BestLollipop.rootedCycle B).support.dropLast.toFinset := by
            have hsFull : B.start ∈
                (BestLollipop.rootedCycle B).support.toFinset :=
              List.mem_toFinset.mpr
                (BestLollipop.rootedCycle B).start_mem_support
            rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
              (BestLollipop.rootedCycle_isCycle B)] at hsFull
            exact hsFull
          have hbCycle : D.E₁.b ∈
              (BestLollipop.rootedCycle B).support.dropLast.toFinset := by
            simpa [hbStart] using hsCycle
          have hba : D.E₁.b = D.E₁.a :=
            D.E₁.meet_A _ D.E₁.path.end_mem_support hbCycle
          exact Or.inl (hwStart.trans (hbStart.symm.trans hba))
      · have hyCycleOrig : B.terminal ∈ B.cycle.support := by
          have hwy' : w = B.terminal := by simpa using hwy
          rw [← hwy']
          exact hwCycleOrig
        exact (B.toLollipop.terminal_not_mem_cycle hpos hyCycleOrig).elim
    · obtain ⟨t, hj₂t, htell, htw⟩ := S.returnPath_support_indices w hwU
      have hwTail : w ∈ B.tail.support := by
        rw [← htw]
        exact B.tail.getVert_mem_support t
      have hwStart : w = B.start := B.cycle_tail_inter hwCycleOrig hwTail
      have hget : B.tail.getVert t = B.tail.getVert 0 := by
        simpa [hwStart] using htw
      have ht0 := tail_index_eq_of_getVert_eq (B := B) htell (by omega) hget
      have hj₂pos : 0 < D.j₂ := lt_of_le_of_lt (Nat.zero_le j₁) D.j₁_lt_j₂
      omega
  · have hwR₂ : w ∈ D.E₂.path.support := by
      simpa [Walk.support_reverse] using hwR₂rev
    exact Or.inr (D.E₂.meet_A w hwR₂ hwCycle)

/-- The selected long cycle arc and the open Case-2 body have disjoint tails,
the exact hypothesis needed to close them to a simple cycle. -/
theorem Case2FanData.longArc_disjoint_spliceBody
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length)
    (S : Case2TailData B D)
    (Q : G.Walk D.E₂.a D.E₁.a) (hQ : Q.IsPath)
    (hQcycle : ∀ v, v ∈ Q.support →
      v ∈ B.rotatedCycle.support.dropLast.toFinset) :
    Q.support.tail.Disjoint
      (Erdos767DiracCase2.spliceBody
        D.E₁.path S.A S.chord S.returnPath D.E₂.path).support.tail := by
  rw [List.disjoint_left]
  intro w hwQ hwBody
  have hwQs : w ∈ Q.support := List.mem_of_mem_tail hwQ
  have hwBs : w ∈ (Erdos767DiracCase2.spliceBody
      D.E₁.path S.A S.chord S.returnPath D.E₂.path).support :=
    List.mem_of_mem_tail hwBody
  rcases D.spliceBody_meets_cycle hpos S w hwBs (hQcycle w hwQs) with
    hw1 | hw2
  · have hBodyPath := D.spliceBody_isPath hpos S
    have hstartNot : D.E₁.a ∉
        (Erdos767DiracCase2.spliceBody
          D.E₁.path S.A S.chord S.returnPath D.E₂.path).support.tail := by
      have hn := hBodyPath.support_nodup
      rw [← (Erdos767DiracCase2.spliceBody
        D.E₁.path S.A S.chord S.returnPath D.E₂.path).cons_tail_support,
        List.nodup_cons] at hn
      exact hn.1
    exact hstartNot (hw1 ▸ hwBody)
  · have hstartNot : D.E₂.a ∉ Q.support.tail := by
      have hn := hQ.support_nodup
      rw [← Q.cons_tail_support, List.nodup_cons] at hn
      exact hn.1
    exact hstartNot (hw2 ▸ hwQ)

end

end E767DiracBuild

-- END Case2Body

-- BEGIN Case2LongArc

open Finset
open scoped SimpleGraph

namespace E767DiracBuild

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
/-- The longer complementary arc of the rooted longest cycle, oriented from
the second aligned ear to the first.  Its length is at least half the old
cycle length and all its vertices lie in the non-repeated cycle carrier. -/
theorem Case2FanData.exists_longArc
    {B : BestLollipop G} {j₁ : ℕ}
    (D : Case2FanData B j₁) (hpos : 0 < B.tail.length) :
    ∃ Q : G.Walk D.E₂.a D.E₁.a,
      Q.IsPath ∧
      B.cycle.length ≤ 2 * Q.length ∧
      (∀ v, v ∈ Q.support →
        v ∈ B.rotatedCycle.support.dropLast.toFinset) := by
  have ha₂ : D.E₂.a ∈ B.rotatedCycle.support :=
    List.mem_of_mem_dropLast (List.mem_toFinset.mp D.E₂.a_mem)
  have ha₁ : D.E₁.a ∈ B.rotatedCycle.support :=
    List.mem_of_mem_dropLast (List.mem_toFinset.mp D.E₁.a_mem)
  have hne : D.E₂.a ≠ D.E₁.a := (D.a_ne hpos).symm
  obtain ⟨P, Q, hP, hQ, hPpos, hQpos, hlen, hmeet, hcover,
      hPedge, hQedge⟩ :=
    Erdos58.exists_path_arcs_of_cycle B.rotatedCycle_isCycle
      ha₂ ha₁ hne
  have hcarrierP : ∀ v, v ∈ P.support →
      v ∈ B.rotatedCycle.support.dropLast.toFinset := by
    intro v hv
    have hvC : v ∈ B.rotatedCycle.support := (hcover v).mpr (Or.inl hv)
    have hvF : v ∈ B.rotatedCycle.support.toFinset :=
      List.mem_toFinset.mpr hvC
    rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
      B.rotatedCycle_isCycle] at hvF
    exact hvF
  have hcarrierQ : ∀ v, v ∈ Q.support →
      v ∈ B.rotatedCycle.support.dropLast.toFinset := by
    intro v hv
    have hvC : v ∈ B.rotatedCycle.support := (hcover v).mpr (Or.inr hv)
    have hvF : v ∈ B.rotatedCycle.support.toFinset :=
      List.mem_toFinset.mpr hvC
    rw [E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
      B.rotatedCycle_isCycle] at hvF
    exact hvF
  have hlen' : P.length + Q.length = B.cycle.length := by
    simpa using hlen
  rcases le_total P.length Q.length with hPQ | hQP
  · refine ⟨Q, hQ, ?_, hcarrierQ⟩
    omega
  · refine ⟨P, hP, ?_, hcarrierP⟩
    omega

end

end E767DiracBuild

-- END Case2LongArc

-- BEGIN RelativeLowDegree

open Finset Set
open scoped SimpleGraph

namespace Erdos767Scratch

open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Case 2 of the relative degree theorem: if every terminal neighbor lies
on the lollipop tail, the aligned-fan splice contradicts a cycle shorter
than twice the terminal degree. -/
theorem BestLollipop.relative_low_degree_case2
    (hTwo : Erdos58.TwoConnected G) (B : BestLollipop G)
    (hpos : 0 < B.tail.length)
    (hN : G.neighborFinset B.terminal ⊆ B.tail.support.toFinset) :
    2 * G.degree B.terminal ≤ B.cycle.length := by
  by_contra hbound
  have hshort : B.cycle.length < 2 * G.degree B.terminal := by omega
  obtain ⟨j₁, hj₁J, hD⟩ :=
    E767DiracBuild.BestLollipop.exists_case2FanData hTwo B hpos
  obtain ⟨D⟩ := hD
  obtain ⟨S⟩ :=
    E767DiracBuild.Case2FanData.exists_tailData D hj₁J hN
  obtain ⟨Q, hQ, hQlong, hQcycle⟩ :=
    E767DiracBuild.Case2FanData.exists_longArc D hpos
  have hbody := E767DiracBuild.Case2FanData.spliceBody_isPath D hpos S
  have hdisj := E767DiracBuild.Case2FanData.longArc_disjoint_spliceBody
    D hpos S Q hQ hQcycle
  have hmiddle : G.degree B.terminal ≤
      S.A.length + 1 + S.returnPath.length := by
    simpa [E767DiracBuild.Case2TailData.returnPath, Walk.length_copy]
      using S.degree_le
  obtain ⟨C, hC, _hsize, hlong⟩ :=
    Erdos767DiracCase2.exists_longer_cycle_of_aligned_splice
      B.cycle Q D.E₁.path S.A S.chord S.returnPath D.E₂.path
      (G.degree B.terminal) B.cycle_isCycle hQ hbody hdisj
      hmiddle hQlong hshort
  exact (Nat.not_lt_of_ge (B.cycle_maximal C hC)) hlong

omit [DecidableEq V] in
/-- Relative Dirac bound at the terminal of a positive best lollipop.  This
is the strengthened form used both for circumference and for exterior-edge
peeling arguments. -/
theorem BestLollipop.relative_low_degree
    (hTwo : Erdos58.TwoConnected G) (B : BestLollipop G)
    (hpos : 0 < B.tail.length) :
    2 * G.degree B.terminal ≤ B.cycle.length := by
  classical
  rcases B.degree_bound_or_all_neighbors_tail hpos with hcase₁ | hcase₂
  · exact hcase₁
  · exact B.relative_low_degree_case2 hTwo hpos hcase₂

omit [DecidableEq V] in
/-- Dirac's circumference theorem in minimum-degree lower-bound form. -/
theorem exists_cycle_length_ge_min_card_two_mul
    (hTwo : Erdos58.TwoConnected G) (k : ℕ)
    (hdegree : ∀ v : V, k ≤ G.degree v) :
    ∃ (z : V) (C : G.Walk z z), C.IsCycle ∧
      min (Fintype.card V) (2 * k) ≤ C.length := by
  classical
  obtain ⟨B⟩ := BestLollipop.exists_bestLollipop hTwo
  by_cases hspan : B.cycle.support.toFinset = (Finset.univ : Finset V)
  · refine ⟨B.cycleBase, B.cycle, B.cycle_isCycle, ?_⟩
    have hcard := Erdos767LongestCycle.cycleCarrier_card B.cycle_isCycle
    rw [hspan, Finset.card_univ] at hcard
    rw [← hcard]
    exact min_le_left _ _
  · have hpos := B.tail_length_pos_of_cycle_not_spanning hTwo hspan
    have hrel := B.relative_low_degree hTwo hpos
    have hk : 2 * k ≤ B.cycle.length :=
      (Nat.mul_le_mul_left 2 (hdegree B.terminal)).trans hrel
    exact ⟨B.cycleBase, B.cycle, B.cycle_isCycle,
      (min_le_right _ _).trans hk⟩

end

end Erdos767Scratch
-- END RelativeLowDegree

-- BEGIN EGApi

namespace E767EGApi

open scoped Sym2

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Deleting one vertex -/

/-- The graph induced on all vertices except `v`. -/
abbrev deleteVertex (G : SimpleGraph V) (v : V) :=
  G.induce ({v} : Set V)ᶜ

@[simp] lemma card_deleteVertex_type (v : V) :
    Fintype.card ↑(({v} : Set V)ᶜ) = Fintype.card V - 1 := by
  rw [Fintype.card_compl_set]
  simp

lemma card_edgeFinset_eq_deleteVertex_add_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.edgeFinset.card = (deleteVertex G v).edgeFinset.card + G.degree v := by
  have hdelete : (deleteVertex G v).edgeFinset.card =
      G.edgeFinset.card - G.degree v := by
    exact (G.card_edgeFinset_induce_compl_singleton v).trans
      (G.card_edgeFinset_deleteIncidenceSet v)
  rw [hdelete, Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)]

/-! ## Splitting at a closed set of vertices -/

/-- Ambient edges with both endpoints in `s`.  Taking a `Finset` rather than a `Set`
keeps the induced-subtype `Fintype` instance canonical. -/
def edgesInside (G : SimpleGraph V) (s : Finset V) [DecidableRel G.Adj] : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ s

lemma card_edgesInside (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    (edgesInside G s).card = (G.induce (↑s : Set V)).edgeFinset.card := by
  exact G.card_filter_edgeFinset_toFinset_subset s

/-- If every edge has both ends on the same side of `s`, the ambient edge set is the
disjoint union of the edges induced by `s` and by its complement. -/
lemma edgeFinset_eq_edgesInside_union_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V)
    (hclosed : ∀ u v, G.Adj u v → (u ∈ s ↔ v ∈ s)) :
    G.edgeFinset = edgesInside G s ∪ edgesInside G sᶜ := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      by_cases huv : G.Adj u v
      · have hsides := hclosed u v huv
        by_cases hu : u ∈ s
        · have hv : v ∈ s := hsides.mp hu
          simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, hu, hv,
            Finset.subset_iff]
        · have hv : v ∉ s := fun hv ↦ hu (hsides.mpr hv)
          simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, hu, hv,
            Finset.subset_iff]
      · simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, Finset.subset_iff]

lemma disjoint_edgesInside_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    Disjoint (edgesInside G s) (edgesInside G sᶜ) := by
  rw [Finset.disjoint_left]
  intro e hs hsc
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hu_pair : u ∈ s(u, v).toFinset := by simp
      have hu_s : u ∈ s := (Finset.mem_filter.mp hs).2 hu_pair
      have hu_sc : u ∈ sᶜ := (Finset.mem_filter.mp hsc).2 hu_pair
      exact (Finset.mem_compl.mp hu_sc) hu_s

/-- Exact edge-count decomposition across any vertex cut with no crossing edge. -/
lemma card_edgeFinset_eq_card_induce_add_card_induce_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V)
    (hclosed : ∀ u v, G.Adj u v → (u ∈ s ↔ v ∈ s)) :
    G.edgeFinset.card =
      (G.induce (↑s : Set V)).edgeFinset.card +
        (G.induce (↑(sᶜ) : Set V)).edgeFinset.card := by
  rw [edgeFinset_eq_edgesInside_union_compl G s hclosed,
    Finset.card_union_of_disjoint (disjoint_edgesInside_compl G s),
    card_edgesInside, card_edgesInside]

/-! ## Splitting at a binary separation (the parts may share a cutvertex) -/

lemma edgeFinset_eq_edgesInside_union_of_edge_cover
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcover : ∀ u v, G.Adj u v →
      (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) :
    G.edgeFinset = edgesInside G A ∪ edgesInside G B := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      by_cases huv : G.Adj u v
      · rcases hcover u v huv with hA | hB
        · simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, hA,
            Finset.subset_iff]
        · simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, hB,
            Finset.subset_iff]
      · simp [edgesInside, SimpleGraph.mem_edgeFinset, huv, Finset.subset_iff]

lemma disjoint_edgesInside_of_inter_card_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hinter : (A ∩ B).card ≤ 1) :
    Disjoint (edgesInside G A) (edgesInside G B) := by
  rw [Finset.disjoint_left]
  intro e heA heB
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj : G.Adj u v :=
        SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp heA).1
      have hp_u : u ∈ s(u, v).toFinset := by simp
      have hp_v : v ∈ s(u, v).toFinset := by simp
      have huA : u ∈ A := (Finset.mem_filter.mp heA).2 hp_u
      have hvA : v ∈ A := (Finset.mem_filter.mp heA).2 hp_v
      have huB : u ∈ B := (Finset.mem_filter.mp heB).2 hp_u
      have hvB : v ∈ B := (Finset.mem_filter.mp heB).2 hp_v
      have hpair : {u, v} ⊆ A ∩ B := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨huA, huB⟩
        · exact Finset.mem_inter.mpr ⟨hvA, hvB⟩
      have htwo : 2 ≤ (A ∩ B).card := by
        have := Finset.card_le_card hpair
        simpa [hadj.ne] using this
      omega

/-- Exact edge-count decomposition for a separation whose overlap has at most one vertex.
The hypothesis `hcover` is the convenient edge-level form of "no edge joins the two open
sides". -/
lemma card_edgeFinset_eq_card_induce_add_card_induce_of_separation
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcover : ∀ u v, G.Adj u v →
      (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (hinter : (A ∩ B).card ≤ 1) :
    G.edgeFinset.card =
      (G.induce (↑A : Set V)).edgeFinset.card +
        (G.induce (↑B : Set V)).edgeFinset.card := by
  rw [edgeFinset_eq_edgesInside_union_of_edge_cover G A B hcover,
    Finset.card_union_of_disjoint
      (disjoint_edgesInside_of_inter_card_le_one G A B hinter),
    card_edgesInside, card_edgesInside]

lemma card_sub_one_add_card_sub_one_le_of_separation
    (A B : Finset V) (hunion : A ∪ B = Finset.univ)
    (hinter : (A ∩ B).card ≤ 1) (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.card - 1) + (B.card - 1) ≤ Fintype.card V - 1 := by
  have hcount := Finset.card_union_add_card_inter A B
  rw [hunion, Finset.card_univ] at hcount
  have hApos : 1 ≤ A.card := Finset.one_le_card.mpr hA
  have hBpos : 1 ≤ B.card := Finset.one_le_card.mpr hB
  omega

omit [DecidableEq V] in
lemma card_coe_lt_card_of_ne_univ (A : Finset V)
    (hA : A ≠ Finset.univ) : Fintype.card ↑A < Fintype.card V := by
  simpa only [Fintype.card_coe, Finset.card_univ] using
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ A, hA⟩)

/-! ## A connected component supplies such a cut -/

omit [Fintype V] [DecidableEq V] in
lemma component_closed (G : SimpleGraph V) (C : G.ConnectedComponent) :
    ∀ u v, G.Adj u v → (u ∈ C.supp ↔ v ∈ C.supp) := by
  intro u v huv
  exact C.mem_supp_congr_adj huv

lemma card_edgeFinset_eq_component_add_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.ConnectedComponent) :
    G.edgeFinset.card =
      (G.induce (↑C.supp.toFinset : Set V)).edgeFinset.card +
        (G.induce (↑(C.supp.toFinsetᶜ) : Set V)).edgeFinset.card := by
  apply card_edgeFinset_eq_card_induce_add_card_induce_compl G C.supp.toFinset
  intro u v huv
  simpa using component_closed G C u v huv

omit [Fintype V] [DecidableEq V] in
/-- A failure of preconnectedness gives a nonempty proper component support. -/
lemma exists_component_with_nonempty_proper_support
    (G : SimpleGraph V) (hG : ¬ G.Preconnected) :
    ∃ C : G.ConnectedComponent, C.supp.Nonempty ∧ C.supp ≠ Set.univ := by
  simp only [SimpleGraph.Preconnected] at hG
  push Not at hG
  obtain ⟨u, v, huv⟩ := hG
  let C := G.connectedComponentMk u
  refine ⟨C, C.nonempty_supp, ?_⟩
  intro hC
  have hvC : v ∈ C.supp := by simp [hC]
  have huC : u ∈ C.supp := by simp [C]
  exact huv (C.reachable_of_mem_supp huC hvC)

omit [DecidableEq V] in
lemma card_component_pos (G : SimpleGraph V) (C : G.ConnectedComponent) :
    0 < Fintype.card C := by
  exact Fintype.card_pos_iff.mpr ⟨⟨C.out, C.out_eq⟩⟩

omit [DecidableEq V] in
lemma card_component_lt_of_support_ne_univ
    (G : SimpleGraph V) (C : G.ConnectedComponent) (hC : C.supp ≠ Set.univ) :
    Fintype.card C < Fintype.card V := by
  classical
  let e : C ≃ {x // x ∈ C.supp.toFinset} :=
    { toFun := fun x ↦ ⟨x, by simp⟩
      invFun := fun x ↦ ⟨x, by
        change ↑x ∈ C.supp
        exact Set.mem_toFinset.mp x.prop⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun x ↦ Subtype.ext rfl }
  rw [Fintype.card_congr e]
  have hne : C.supp.toFinset ≠ (Finset.univ : Finset V) := by
    intro h
    apply hC
    ext x
    have hx := Finset.ext_iff.mp h x
    simpa using hx
  simpa only [Fintype.card_coe, Finset.card_univ] using
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, hne⟩)

end

end E767EGApi

-- END EGApi

-- BEGIN ErdosGallai

namespace E767EGConditional

open scoped Sym2

noncomputable section

attribute [local instance] Classical.propDecidable


/-- Every genuine cycle has length at most `c`. -/
def CycleLengthAtMost {V : Type u} (G : SimpleGraph V) (c : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≤ c

/-- The only geometric input required by the Erdős--Gallai induction: in a
finite two-connected graph whose order exceeds the cycle bound, some vertex
has doubled degree at most that bound.  Dirac's circumference theorem gives
this immediately from `circumference ≥ min(order, 2 * minimumDegree)`. -/
def DiracCircumferencePrinciple : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (c : ℕ),
    2 ≤ c → c < Fintype.card W → H.Preconnected →
    (∀ w, (E767EGApi.deleteVertex H w).Preconnected) →
    CycleLengthAtMost H c → ∃ w, 2 * H.degree w ≤ c

lemma cycleLengthAtMost_induce {V : Type u}
    (G : SimpleGraph V) (c : ℕ) (h : CycleLengthAtMost G c) (S : Set V) :
    CycleLengthAtMost (G.induce S) c := by
  classical
  intro v p hp
  let f : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  have hm : (p.map f.toHom).IsCycle := hp.map f.injective
  simpa using h (f v) (p.map f.toHom) hm

private lemma twice_card_edgeFinset_le_complete {V : Type u}
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) := by
  classical
  calc
    2 * G.edgeFinset.card ≤ 2 * (Fintype.card V).choose 2 :=
      Nat.mul_le_mul_left 2 G.card_edgeFinset_le_card_choose_two
    _ = Fintype.card V * (Fintype.card V - 1) := by
      rw [Nat.choose_two_right, Nat.mul_comm 2,
        Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self _)]

private lemma component_support_toFinset_ne_univ
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : G.ConnectedComponent) (hC : C.supp ≠ Set.univ) :
    C.supp.toFinset ≠ (Finset.univ : Finset V) := by
  intro h
  apply hC
  ext x
  have hx := Finset.ext_iff.mp h x
  simpa using hx

private lemma component_support_toFinset_nonempty
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : G.ConnectedComponent) (hC : C.supp.Nonempty) :
    C.supp.toFinset.Nonempty := by
  obtain ⟨x, hx⟩ := hC
  exact ⟨x, Set.mem_toFinset.mpr hx⟩

private lemma compl_nonempty_of_ne_univ {V : Type u} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S ≠ Finset.univ) : Sᶜ.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hEmpty
  apply hS
  ext x
  have hx : x ∉ Sᶜ := by simp [hEmpty]
  simpa using hx

private lemma compl_ne_univ_of_nonempty {V : Type u} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S.Nonempty) : Sᶜ ≠ Finset.univ := by
  obtain ⟨x, hx⟩ := hS
  intro h
  have hxc : x ∈ Sᶜ := by simp [h]
  exact (Finset.mem_compl.mp hxc) hx

private lemma exists_disconnected_partition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hpre : ¬ G.Preconnected) :
    ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
      S ≠ Finset.univ ∧ Sᶜ ≠ Finset.univ ∧
      ∀ u v, G.Adj u v → (u ∈ S ↔ v ∈ S) := by
  obtain ⟨C, hCnon, hCproper⟩ :=
    E767EGApi.exists_component_with_nonempty_proper_support G hpre
  have hSnon : C.supp.toFinset.Nonempty :=
    component_support_toFinset_nonempty G C hCnon
  have hSproper : C.supp.toFinset ≠ Finset.univ :=
    component_support_toFinset_ne_univ G C hCproper
  have hSCnon : C.supp.toFinsetᶜ.Nonempty :=
    compl_nonempty_of_ne_univ C.supp.toFinset hSproper
  have hSCproper : C.supp.toFinsetᶜ ≠ Finset.univ :=
    compl_ne_univ_of_nonempty C.supp.toFinset hSnon
  refine ⟨C.supp.toFinset, hSnon, hSCnon, hSproper, hSCproper, ?_⟩
  intro u v huv
  simpa using E767EGApi.component_closed G C u v huv

private lemma combine_disconnected_bounds
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (S : Finset V)
    (hSnon : S.Nonempty) (hSCnon : Sᶜ.Nonempty)
    (hedge : G.edgeFinset.card =
      (G.induce (S : Set V)).edgeFinset.card +
        (G.induce (↑(Sᶜ) : Set V)).edgeFinset.card)
    (ihS : 2 * (G.induce (S : Set V)).edgeFinset.card ≤ c * (S.card - 1))
    (ihT : 2 * (G.induce (↑(Sᶜ) : Set V)).edgeFinset.card ≤ c * (Sᶜ.card - 1)) :
    2 * G.edgeFinset.card ≤ c * (Fintype.card V - 1) := by
  have hparts : (S.card - 1) + (Sᶜ.card - 1) ≤ Fintype.card V - 1 :=
    E767EGApi.card_sub_one_add_card_sub_one_le_of_separation
      S Sᶜ (by ext; simp) (by simp) hSnon hSCnon
  calc
    2 * G.edgeFinset.card =
        2 * (G.induce (S : Set V)).edgeFinset.card +
          2 * (G.induce (↑(Sᶜ) : Set V)).edgeFinset.card := by
      rw [hedge]
      omega
    _ ≤ c * (S.card - 1) + c * (Sᶜ.card - 1) := Nat.add_le_add ihS ihT
    _ = c * ((S.card - 1) + (Sᶜ.card - 1)) := by rw [Nat.mul_add]
    _ ≤ c * (Fintype.card V - 1) := Nat.mul_le_mul_left c hparts

/-- Conditional finite Erdős--Gallai circumference bound.  All separation,
edge-count, subtype-cardinality, and induction work is internal; the sole
input is `DiracCircumferencePrinciple`. -/
theorem erdosGallai_cycle_conditional (hDirac : DiracCircumferencePrinciple.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ)
    (hc : 2 ≤ c) (hcycle : CycleLengthAtMost G c) :
    2 * G.edgeFinset.card ≤ c * (Fintype.card V - 1) := by
  classical
  induction n : Fintype.card V using Nat.strong_induction_on generalizing V G with
  | h n ih =>
      rw [← n]
      by_cases hnsmall : Fintype.card V ≤ c
      · exact (twice_card_edgeFinset_le_complete G).trans
          (Nat.mul_le_mul_right (Fintype.card V - 1) hnsmall)
      have hcn : c < Fintype.card V := by omega
      have hnthree : 3 ≤ Fintype.card V := by omega
      by_cases hpre : G.Preconnected
      · by_cases hdelete : ∀ v, (E767EGApi.deleteVertex G v).Preconnected
        · obtain ⟨v, hv⟩ := hDirac G c hc hcn hpre hdelete hcycle
          let H := E767EGApi.deleteVertex G v
          have hcardH : Fintype.card ↑(({v} : Set V)ᶜ) < Fintype.card V := by
            rw [E767EGApi.card_deleteVertex_type]
            omega
          have hind : 2 * H.edgeFinset.card ≤
              c * (Fintype.card ↑(({v} : Set V)ᶜ) - 1) :=
            ih _ (by simpa only [n] using hcardH) H
              (cycleLengthAtMost_induce G c hcycle _) rfl
          have hedge := E767EGApi.card_edgeFinset_eq_deleteVertex_add_degree G v
          have hcard : Fintype.card ↑(({v} : Set V)ᶜ) = Fintype.card V - 1 :=
            E767EGApi.card_deleteVertex_type v
          rw [hcard] at hind
          calc
            2 * G.edgeFinset.card = 2 * H.edgeFinset.card + 2 * G.degree v := by
              change 2 * G.edgeFinset.card =
                2 * (E767EGApi.deleteVertex G v).edgeFinset.card + 2 * G.degree v
              rw [hedge]
              omega
            _ ≤ c * (Fintype.card V - 1 - 1) + c := Nat.add_le_add hind hv
            _ = c * (Fintype.card V - 1) := by
              have hn : Fintype.card V - 1 = (Fintype.card V - 1 - 1) + 1 := by
                omega
              rw [hn, Nat.mul_add]
              simp
        · push Not at hdelete
          obtain ⟨v, hvdelete⟩ := hdelete
          let H := E767EGApi.deleteVertex G v
          obtain ⟨C, hCnon, hCproper⟩ :=
            E767EGApi.exists_component_with_nonempty_proper_support H hvdelete
          let e : ↑(({v} : Set V)ᶜ) ↪ V := Function.Embedding.subtype _
          let D : Finset V := C.supp.toFinset.map e
          let A : Finset V := insert v D
          let B : Finset V := Dᶜ
          have hvD : v ∉ D := by simp [D, e]
          have hmemD (x : V) :
              x ∈ D ↔ ∃ hx : x ≠ v, (⟨x, hx⟩ : ↑(({v} : Set V)ᶜ)) ∈ C.supp := by
            simp only [D, Finset.mem_map, Set.mem_toFinset]
            constructor
            · rintro ⟨y, hy, rfl⟩
              refine ⟨y.2, ?_⟩
              simpa [e] using hy
            · rintro ⟨hx, hxC⟩
              refine ⟨⟨x, hx⟩, ?_, ?_⟩
              · simpa using hxC
              · rfl
          have hDclosed {x y : V} (hxy : G.Adj x y) (hx : x ≠ v) (hy : y ≠ v) :
              (x ∈ D ↔ y ∈ D) := by
            rw [hmemD x, hmemD y]
            have hadjH : H.Adj ⟨x, hx⟩ ⟨y, hy⟩ :=
              SimpleGraph.induce_adj.mpr hxy
            have hclose := E767EGApi.component_closed H C ⟨x, hx⟩ ⟨y, hy⟩ hadjH
            constructor
            · rintro ⟨hx', hxC⟩
              refine ⟨hy, ?_⟩
              apply hclose.mp
              simpa using hxC
            · rintro ⟨hy', hyC⟩
              refine ⟨hx, ?_⟩
              apply hclose.mpr
              simpa using hyC
          have hcover : ∀ x y, G.Adj x y →
              (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := by
            intro x y hxy
            by_cases hxv : x = v
            · subst x
              by_cases hyD : y ∈ D
              · exact Or.inl ⟨by simp [A], by simp [A, hyD]⟩
              · exact Or.inr ⟨by simp [B, hvD], by simp [B, hyD]⟩
            · by_cases hyv : y = v
              · subst y
                by_cases hxD : x ∈ D
                · exact Or.inl ⟨by simp [A, hxD], by simp [A]⟩
                · exact Or.inr ⟨by simp [B, hxD], by simp [B, hvD]⟩
              · have hiff := hDclosed hxy hxv hyv
                by_cases hxD : x ∈ D
                · have hyD : y ∈ D := hiff.mp hxD
                  exact Or.inl ⟨by simp [A, hxD], by simp [A, hyD]⟩
                · have hyD : y ∉ D := fun hyD ↦ hxD (hiff.mpr hyD)
                  exact Or.inr ⟨by simp [B, hxD], by simp [B, hyD]⟩
          have hunion : A ∪ B = Finset.univ := by
            ext x
            by_cases hxD : x ∈ D <;> simp [A, B]
          have hinterEq : A ∩ B = {v} := by
            ext x
            by_cases hxv : x = v
            · subst x
              simp [A, B, hvD]
            · by_cases hxD : x ∈ D <;> simp [A, B, hxv, hxD]
          have hinter : (A ∩ B).card ≤ 1 := by simp [hinterEq]
          have hAnon : A.Nonempty := ⟨v, by simp [A]⟩
          have hBnon : B.Nonempty := ⟨v, by simp [B, hvD]⟩
          have hAproper : A ≠ Finset.univ := by
            have hnotall : ¬ ∀ z, z ∈ C.supp := by
              intro hall
              apply hCproper
              exact Set.eq_univ_of_forall hall
            push Not at hnotall
            obtain ⟨z, hz⟩ := hnotall
            intro hA
            have hzA : (z : V) ∈ A := by simp [hA]
            have hzv : (z : V) ≠ v := z.2
            have hzD : (z : V) ∈ D := by simpa [A, hzv] using hzA
            exact hz ((hmemD z).mp hzD |>.2)
          have hBproper : B ≠ Finset.univ := by
            obtain ⟨z, hz⟩ := hCnon
            have hzD : (z : V) ∈ D := by
              apply (hmemD z).mpr
              exact ⟨z.2, by simpa using hz⟩
            intro hB
            have hzB : (z : V) ∈ B := by simp [hB]
            exact (Finset.mem_compl.mp hzB) hzD
          have hAcard : Fintype.card ↑A < Fintype.card V :=
            E767EGApi.card_coe_lt_card_of_ne_univ A hAproper
          have hBcard : Fintype.card ↑B < Fintype.card V :=
            E767EGApi.card_coe_lt_card_of_ne_univ B hBproper
          let GA := G.induce (A : Set V)
          let GB := G.induce (B : Set V)
          have ihA : 2 * GA.edgeFinset.card ≤ c * (Fintype.card ↑A - 1) :=
            ih _ (by simpa only [n] using hAcard) GA
              (cycleLengthAtMost_induce G c hcycle _) rfl
          have ihB : 2 * GB.edgeFinset.card ≤ c * (Fintype.card ↑B - 1) :=
            ih _ (by simpa only [n] using hBcard) GB
              (cycleLengthAtMost_induce G c hcycle _) rfl
          have hedge :=
            E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_of_separation
              G A B hcover hinter
          have hparts : (A.card - 1) + (B.card - 1) ≤ Fintype.card V - 1 :=
            E767EGApi.card_sub_one_add_card_sub_one_le_of_separation
              A B hunion hinter hAnon hBnon
          simp only [Fintype.card_coe] at ihA ihB
          calc
            2 * G.edgeFinset.card = 2 * GA.edgeFinset.card + 2 * GB.edgeFinset.card := by
              change 2 * G.edgeFinset.card =
                2 * (G.induce (A : Set V)).edgeFinset.card +
                  2 * (G.induce (B : Set V)).edgeFinset.card
              rw [hedge]
              omega
            _ ≤ c * (A.card - 1) + c * (B.card - 1) := Nat.add_le_add ihA ihB
            _ = c * ((A.card - 1) + (B.card - 1)) := by rw [Nat.mul_add]
            _ ≤ c * (Fintype.card V - 1) := Nat.mul_le_mul_left c hparts
      · obtain ⟨S, hSnon, hSCnon, hSproper, hSCproper, hclosed⟩ :=
          exists_disconnected_partition G hpre
        have hScard : Fintype.card ↑S < Fintype.card V :=
          E767EGApi.card_coe_lt_card_of_ne_univ S hSproper
        have hSCcard : Fintype.card ↑Sᶜ < Fintype.card V :=
          E767EGApi.card_coe_lt_card_of_ne_univ Sᶜ hSCproper
        let GS := G.induce (S : Set V)
        let GT := G.induce (↑(Sᶜ) : Set V)
        have hScard' : Fintype.card ↑(S : Set V) < Fintype.card V := by
          exact hScard
        have hSCcard' : Fintype.card ↑(↑(Sᶜ) : Set V) < Fintype.card V := by
          exact hSCcard
        have ihS := ih _ (by simpa only [n] using hScard') GS
          (cycleLengthAtMost_induce G c hcycle _) rfl
        have ihT := ih _ (by simpa only [n] using hSCcard') GT
          (cycleLengthAtMost_induce G c hcycle _) rfl
        dsimp [GS, GT] at ihS ihT
        simp only [Fintype.card_coe] at ihS ihT
        have hedge :=
          E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_compl G S hclosed
        exact combine_disconnected_bounds G c S hSnon hSCnon hedge ihS ihT

end

end E767EGConditional

-- END ErdosGallai

-- BEGIN Dirac
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Dirac's circumference theorem and the Erdős--Gallai edge bound

This is the public entry point for the graph-theoretic engine used in the
formalization of Erdős Problem 767.  The proof above it formalizes the
best-lollipop/aligned-fan argument, including both terminal-neighbor cases.
-/

open Finset Set
open scoped SimpleGraph

namespace Erdos767Dirac

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable


/-- The geometric principle consumed by the Erdős--Gallai induction,
derived from the best-lollipop relative low-degree theorem. -/
theorem diracCircumferencePrinciple :
    E767EGConditional.DiracCircumferencePrinciple.{u} := by
  intro W _ _ H _ c hc hcard hpre hdelete hcycle
  have hcard3 : 3 ≤ Fintype.card W := by omega
  let : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hconn : H.Connected := ⟨hpre⟩
  have hdelconn : ∀ w : W, (H.induce ({w}ᶜ : Set W)).Connected := by
    intro w
    let : Nonempty ({w}ᶜ : Set W) := Fintype.card_pos_iff.mp (by
      rw [Fintype.card_compl_set, Set.card_singleton]
      omega)
    exact ⟨hdelete w⟩
  have hTwo : Erdos58.TwoConnected H := ⟨hcard3, hconn, hdelconn⟩
  obtain ⟨B⟩ := BestLollipop.exists_bestLollipop hTwo
  have hcyclelen : B.cycle.length ≤ c :=
    hcycle B.cycleBase B.cycle B.cycle_isCycle
  have hnotspan : B.cycle.support.toFinset ≠ (Finset.univ : Finset W) := by
    intro hspan
    have hcarrier :=
      Erdos767LongestCycle.cycleCarrier_card B.cycle_isCycle
    rw [hspan, Finset.card_univ] at hcarrier
    omega
  have hpos := B.tail_length_pos_of_cycle_not_spanning hTwo hnotspan
  refine ⟨B.terminal, ?_⟩
  exact (B.relative_low_degree hTwo hpos).trans hcyclelen

/-- Erdős--Gallai's sharp edge bound for graphs of bounded circumference. -/
theorem erdosGallai_cycle
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ)
    (hc : 2 ≤ c) (hcycle : E767EGConditional.CycleLengthAtMost G c) :
    2 * G.edgeFinset.card ≤ c * (Fintype.card V - 1) :=
  E767EGConditional.erdosGallai_cycle_conditional
    diracCircumferencePrinciple G c hc hcycle

/-- A nonspanning longest cycle in a two-connected graph can be replaced by
a (possibly different) longest cycle with an exterior vertex whose doubled
degree is at most the common longest-cycle length. -/
theorem exists_nonspanning_longestCycle_lowDegree
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTwo : Erdos58.TwoConnected G)
    {z : V} {q : G.Walk z z}
    (hq : Erdos767LongestCycle.IsLongestCycle q)
    (hqlt : q.length < Fintype.card V) :
    ∃ (w : V) (r : G.Walk w w) (v : V),
      Erdos767LongestCycle.IsLongestCycle r ∧
        v ∉ r.support ∧ 2 * G.degree v ≤ r.length := by
  classical
  obtain ⟨B⟩ := BestLollipop.exists_bestLollipop hTwo
  have hlen : B.cycle.length = q.length := by
    apply Nat.le_antisymm
    · exact hq.2 B.cycle B.cycle_isCycle
    · exact B.cycle_maximal q hq.1
  have hnotspan : B.cycle.support.toFinset ≠ (Finset.univ : Finset V) := by
    intro hspan
    have hcarrier :=
      Erdos767LongestCycle.cycleCarrier_card B.cycle_isCycle
    rw [hspan, Finset.card_univ] at hcarrier
    omega
  have hpos := B.tail_length_pos_of_cycle_not_spanning hTwo hnotspan
  refine ⟨B.cycleBase, B.cycle, B.terminal, B.isLongestCycle, ?_,
    B.relative_low_degree hTwo hpos⟩
  exact B.toLollipop.terminal_not_mem_cycle hpos

/-- Dirac's circumference theorem in minimum-degree form. -/
theorem exists_cycle_length_ge_min_card_two_mul
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hTwo : Erdos58.TwoConnected G) (k : ℕ)
    (hdegree : ∀ v : V, k ≤ G.degree v) :
    ∃ (z : V) (C : G.Walk z z), C.IsCycle ∧
      min (Fintype.card V) (2 * k) ≤ C.length :=
  Erdos767Scratch.exists_cycle_length_ge_min_card_two_mul hTwo k hdegree

#print axioms diracCircumferencePrinciple
#print axioms erdosGallai_cycle
#print axioms exists_nonspanning_longestCycle_lowDegree
#print axioms exists_cycle_length_ge_min_card_two_mul

end

end Erdos767Dirac
-- END Dirac

-- BEGIN Erdos767
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 767.
https://www.erdosproblems.com/forum/thread/767

Informal authors:
- Tao Jiang

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos767.md
-/
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Erdős Problem 767

For positive `k`, Jiang proved that the maximum number of edges in an
`n`-vertex graph having no cycle with `k` distinct chords incident to one
cycle vertex is

`(k + 1) * n - (k + 1) ^ 2`

as soon as `3 * k + 3 ≤ n`.

The mathematical proof and a detailed map of the formalization are in
`tex/767.tex`.

Reference: T. Jiang, *A note on a conjecture about cycles with many incident
chords*, J. Graph Theory 46 (2004), 180--182.
-/

open Finset
open SimpleGraph
open scoped SimpleGraph

namespace Erdos767

noncomputable section

attribute [local instance] Classical.propDecidable


/-- A graph has the forbidden configuration for Problem 767 when a simple
cycle has at least `k` distinct chord edges which share a cycle vertex.

The embedding selects distinct opposite endpoints.  `Walk.IsChord` says that
the selected ambient edge joins two vertices of the cycle and is not a rim
edge of the cycle.  The explicit support condition on the common endpoint is
needed when `k = 0`. -/
def HasCycleWithKIncidentChords {V : Type u} (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

/-- The admissibility predicate in the definition of `g_k(n)`. -/
def AvoidsCycleWithKIncidentChords {V : Type u} (k : ℕ) (G : SimpleGraph V) : Prop :=
  ¬HasCycleWithKIncidentChords k G

/-- The extremal number from Problem 767, using labelled graphs on `Fin n`.
Every finite graph on `n` vertices is isomorphic to one of these graphs. -/
def chordCycleExtremalNumber (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) =>
    AvoidsCycleWithKIncidentChords k G).sup fun G => G.edgeFinset.card

lemma bot_avoids (k : ℕ) {V : Type u} :
    AvoidsCycleWithKIncidentChords k (⊥ : SimpleGraph V) := by
  rintro ⟨v, c, hc, f, hf, hchord⟩
  exact SimpleGraph.isAcyclic_bot c hc

lemma mem_admissibleGraphs_iff {k n : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ (Finset.univ.filter fun H : SimpleGraph (Fin n) =>
      AvoidsCycleWithKIncidentChords k H) ↔
      AvoidsCycleWithKIncidentChords k G := by
  simp

lemma card_edgeFinset_le_chordCycleExtremalNumber {k n : ℕ}
    {G : SimpleGraph (Fin n)} (hG : AvoidsCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤ chordCycleExtremalNumber k n := by
  unfold chordCycleExtremalNumber
  exact Finset.le_sup
    (s := Finset.univ.filter fun H : SimpleGraph (Fin n) =>
      AvoidsCycleWithKIncidentChords k H)
    (f := fun H : SimpleGraph (Fin n) => H.edgeFinset.card)
    (b := G) (mem_admissibleGraphs_iff.mpr hG)

lemma exists_extremizer (k n : ℕ) :
    ∃ G : SimpleGraph (Fin n),
      AvoidsCycleWithKIncidentChords k G ∧
        G.edgeFinset.card = chordCycleExtremalNumber k n := by
  let A := Finset.univ.filter fun G : SimpleGraph (Fin n) =>
    AvoidsCycleWithKIncidentChords k G
  have hA : A.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [A, bot_avoids]
  obtain ⟨G, hGA, hG⟩ :=
    Finset.exists_mem_eq_sup A hA (fun H : SimpleGraph (Fin n) => H.edgeFinset.card)
  exact ⟨G, (Finset.mem_filter.mp hGA).2, hG.symm⟩

/-! ## Transport and heredity -/

lemma isChord_map_embedding {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G ↪g H) {a b : V} {c : G.Walk a b}
    {e : Sym2 V} (he : c.IsChord e) :
    (c.map φ.toHom).IsChord (e.map φ) := by
  induction e using Sym2.ind with
  | _ x y =>
      rw [SimpleGraph.Walk.isChord_sym2Mk] at he
      change (c.map φ.toHom).IsChord s(φ x, φ y)
      rw [SimpleGraph.Walk.isChord_sym2Mk]
      rcases he with ⟨hxy, hnot, hx, hy⟩
      refine ⟨φ.toHom.map_adj hxy, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_map]
        intro hmem
        obtain ⟨e, hec, heq⟩ := List.mem_map.mp hmem
        have heeq : e = s(x, y) := (Sym2.map.injective φ.injective) heq
        exact hnot (heeq ▸ hec)
      · simp only [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨x, hx, rfl⟩
      · simp only [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨y, hy, rfl⟩

lemma hasCycleWithKIncidentChords_map_embedding {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ↪g H) {k : ℕ}
    (hG : HasCycleWithKIncidentChords k G) :
    HasCycleWithKIncidentChords k H := by
  rcases hG with ⟨v, c, hc, f, hf, hchord⟩
  let f' : Fin k → W := fun i ↦ φ (f i)
  refine ⟨φ v, c.map φ.toHom, hc.map φ.injective, f', ?_, ?_⟩
  · exact φ.injective.comp hf
  · intro i
    change (c.map φ.toHom).IsChord s(φ v, φ (f i))
    simpa only [Sym2.map_mk] using isChord_map_embedding φ (hchord i)

lemma avoids_of_embedding {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G ↪g H) {k : ℕ}
    (hH : AvoidsCycleWithKIncidentChords k H) :
    AvoidsCycleWithKIncidentChords k G :=
  fun hG ↦ hH (hasCycleWithKIncidentChords_map_embedding φ hG)

lemma avoids_induce {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G) (s : Set V) :
    AvoidsCycleWithKIncidentChords k (G.induce s) :=
  avoids_of_embedding (Embedding.induce s) hG

lemma avoids_iff_of_iso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G ≃g H) (k : ℕ) :
    AvoidsCycleWithKIncidentChords k G ↔
      AvoidsCycleWithKIncidentChords k H := by
  constructor
  · exact avoids_of_embedding φ.symm.toEmbedding
  · exact avoids_of_embedding φ.toEmbedding

/-! ## The complete-bipartite lower construction -/

private def IsLeft {L R : Type*} : L ⊕ R → Prop
  | .inl _ => True
  | .inr _ => False

private def IsRight {L R : Type*} : L ⊕ R → Prop
  | .inl _ => False
  | .inr _ => True

@[simp] private lemma isLeft_inl {L R : Type*} (x : L) :
    IsLeft (R := R) (.inl x) := trivial

@[simp] private lemma not_isLeft_inr {L R : Type*} (x : R) :
    ¬IsLeft (L := L) (.inr x) := by simp [IsLeft]

@[simp] private lemma not_isRight_inl {L R : Type*} (x : L) :
    ¬IsRight (R := R) (.inl x) := by simp [IsRight]

@[simp] private lemma isRight_inr {L R : Type*} (x : R) :
    IsRight (L := L) (.inr x) := trivial

private lemma sum_isLeft_iff {L R : Type*} (x : L ⊕ R) :
    x.isLeft = true ↔ IsLeft x := by
  cases x <;> simp [IsLeft]

private lemma sum_isRight_iff {L R : Type*} (x : L ⊕ R) :
    x.isRight = true ↔ IsRight x := by
  cases x <;> simp [IsRight]

private lemma adj_left_iff_right {L R : Type*} {x y : L ⊕ R}
    (h : (completeBipartiteGraph L R).Adj x y) :
    IsLeft x ↔ IsRight y := by
  cases x <;> cases y <;>
    simp_all [completeBipartiteGraph_adj, IsLeft, IsRight]

private lemma adj_right_iff_left {L R : Type*} {x y : L ⊕ R}
    (h : (completeBipartiteGraph L R).Adj x y) :
    IsRight x ↔ IsLeft y := by
  cases x <;> cases y <;>
    simp_all [completeBipartiteGraph_adj, IsLeft, IsRight]

private def leftCount {L R : Type*} (l : List (L ⊕ R)) : ℕ :=
  l.countP Sum.isLeft

private def rightCount {L R : Type*} (l : List (L ⊕ R)) : ℕ :=
  l.countP Sum.isRight

private lemma leftCount_dropLast_eq_rightCount_dropLast {L R : Type*}
    {z : L ⊕ R} (p : (completeBipartiteGraph L R).Walk z z) :
    leftCount p.support.dropLast = rightCount p.support.dropLast := by
  calc
    leftCount p.support.dropLast = leftCount (p.darts.map (·.fst)) := by
      rw [p.map_fst_darts]
    _ = rightCount (p.darts.map (·.snd)) := by
      simp only [leftCount, rightCount, List.countP_map]
      apply congrArg (fun q ↦ List.countP q p.darts)
      funext d
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply]
      rw [sum_isLeft_iff, sum_isRight_iff]
      exact adj_left_iff_right d.adj
    _ = rightCount p.support.tail := by rw [p.map_snd_darts]
    _ = rightCount p.support.dropLast :=
      p.tail_support_perm_dropLast_support.countP_eq _

section FiniteSides

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]

private def cycleVertices {z : L ⊕ R}
    (p : (completeBipartiteGraph L R).Walk z z) : Finset (L ⊕ R) :=
  p.support.dropLast.toFinset

private def leftCycleVertices {z : L ⊕ R}
    (p : (completeBipartiteGraph L R).Walk z z) : Finset (L ⊕ R) :=
  (cycleVertices p).filter fun x ↦ x.isLeft

private def rightCycleVertices {z : L ⊕ R}
    (p : (completeBipartiteGraph L R).Walk z z) : Finset (L ⊕ R) :=
  (cycleVertices p).filter fun x ↦ x.isRight

omit [Fintype L] [Fintype R] in
private lemma card_leftCycleVertices {z : L ⊕ R}
    {p : (completeBipartiteGraph L R).Walk z z} (hp : p.IsCycle) :
    (leftCycleVertices p).card = leftCount p.support.dropLast := by
  simpa [leftCycleVertices, cycleVertices, leftCount] using
    (hp.nodup_dropLast_support.card_eq_countP (P := fun x ↦ x.isLeft))

omit [Fintype L] [Fintype R] in
private lemma card_rightCycleVertices {z : L ⊕ R}
    {p : (completeBipartiteGraph L R).Walk z z} (hp : p.IsCycle) :
    (rightCycleVertices p).card = rightCount p.support.dropLast := by
  simpa [rightCycleVertices, cycleVertices, rightCount] using
    (hp.nodup_dropLast_support.card_eq_countP (P := fun x ↦ x.isRight))

omit [Fintype L] [Fintype R] in
private lemma card_leftCycleVertices_eq_right {z : L ⊕ R}
    {p : (completeBipartiteGraph L R).Walk z z} (hp : p.IsCycle) :
    (leftCycleVertices p).card = (rightCycleVertices p).card := by
  rw [card_leftCycleVertices hp, card_rightCycleVertices hp,
    leftCount_dropLast_eq_rightCount_dropLast]

omit [DecidableEq L] [DecidableEq R] in
private lemma card_filter_univ_isLeft :
    (Finset.univ.filter fun x : L ⊕ R ↦ x.isLeft).card = Fintype.card L := by
  let e : L ↪ L ⊕ R := ⟨Sum.inl, Sum.inl_injective⟩
  rw [show (Finset.univ.filter fun x : L ⊕ R ↦ x.isLeft) =
      Finset.univ.map e by
    ext x
    cases x <;> simp [e]]
  simp

omit [Fintype R] in
private lemma card_leftCycleVertices_le [Finite R] {z : L ⊕ R}
    (p : (completeBipartiteGraph L R).Walk z z) :
    (leftCycleVertices p).card ≤ Fintype.card L := by
  let := Fintype.ofFinite R
  rw [← card_filter_univ_isLeft (L := L) (R := R)]
  exact Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      (Finset.mem_filter.mp hx).2⟩)

omit [Fintype R] in
private lemma card_rightCycleVertices_le_left [Finite R] {z : L ⊕ R}
    {p : (completeBipartiteGraph L R).Walk z z} (hp : p.IsCycle) :
    (rightCycleVertices p).card ≤ Fintype.card L := by
  rw [← card_leftCycleVertices_eq_right hp]
  exact card_leftCycleVertices_le p

end FiniteSides

section SelectedVertices

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]
variable {z : L ⊕ R} {p : (completeBipartiteGraph L R).Walk z z}

private def selectedVertices {k : ℕ}
    (p : (completeBipartiteGraph L R).Walk z z) (f : Fin k → L ⊕ R) :
    Finset (L ⊕ R) :=
  {p.snd, p.penultimate} ∪ Finset.univ.image f

omit [Fintype L] [Fintype R] in
private lemma selected_pair_disjoint {k : ℕ} (hp : p.IsCycle)
    {f : Fin k → L ⊕ R} (hfchord : ∀ i, p.IsChord s(z, f i)) :
    Disjoint ({p.snd, p.penultimate} : Finset (L ⊕ R))
      (Finset.univ.image f) := by
  rw [Finset.disjoint_left]
  intro x hxpair hximage
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hximage
  have hnot := (SimpleGraph.Walk.isChord_sym2Mk.mp (hfchord i)).2.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
  rcases hxpair with h | h
  · exact hnot (by simpa only [h] using p.mk_start_snd_mem_edges hp.not_nil)
  · exact hnot (by
      simpa only [h, Sym2.eq_swap] using
        p.mk_penultimate_end_mem_edges hp.not_nil)

omit [Fintype L] [Fintype R] in
private lemma card_selectedVertices {k : ℕ} (hp : p.IsCycle)
    {f : Fin k → L ⊕ R} (hf : Function.Injective f)
    (hfchord : ∀ i, p.IsChord s(z, f i)) :
    (selectedVertices p f).card = k + 2 := by
  rw [selectedVertices,
    Finset.card_union_of_disjoint (selected_pair_disjoint hp hfchord)]
  have himage : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · exact hf.injOn
  rw [himage]
  simp [hp.snd_ne_penultimate]
  omega

omit [Fintype L] [Fintype R] in
private lemma snd_mem_cycleVertices (hp : p.IsCycle) :
    p.snd ∈ cycleVertices p := by
  rw [cycleVertices, List.mem_toFinset]
  exact p.tail_support_perm_dropLast_support.mem_iff.mp
    (p.snd_mem_tail_support hp.not_nil)

omit [Fintype L] [Fintype R] in
private lemma penultimate_mem_cycleVertices (hp : p.IsCycle) :
    p.penultimate ∈ cycleVertices p := by
  rw [cycleVertices, List.mem_toFinset]
  exact p.penultimate_mem_dropLast_support hp.not_nil

omit [Fintype L] [Fintype R] in
private lemma chord_endpoint_mem_cycleVertices {x : L ⊕ R}
    (hx : p.IsChord s(z, x)) : x ∈ cycleVertices p := by
  have h := SimpleGraph.Walk.isChord_sym2Mk.mp hx
  rw [cycleVertices, List.mem_toFinset]
  apply List.mem_dropLast_of_mem_of_ne_getLast h.2.2.2
  simpa only [p.getLast_support] using h.1.ne'

omit [Fintype L] [Fintype R] in
private lemma selected_subset_right_of_left {k : ℕ} (hp : p.IsCycle)
    (hz : IsLeft z) {f : Fin k → L ⊕ R}
    (hfchord : ∀ i, p.IsChord s(z, f i)) :
    selectedVertices p f ⊆ rightCycleVertices p := by
  intro x hx
  rw [selectedVertices, Finset.mem_union] at hx
  rw [rightCycleVertices, Finset.mem_filter]
  rcases hx with hxpair | hximage
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
    rcases hxpair with rfl | rfl
    · refine ⟨snd_mem_cycleVertices hp, ?_⟩
      exact (sum_isRight_iff _).mpr
        ((adj_left_iff_right (p.adj_snd hp.not_nil)).mp hz)
    · refine ⟨penultimate_mem_cycleVertices hp, ?_⟩
      exact (sum_isRight_iff _).mpr
        ((adj_left_iff_right (p.adj_penultimate hp.not_nil).symm).mp hz)
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hximage
    have hi := SimpleGraph.Walk.isChord_sym2Mk.mp (hfchord i)
    refine ⟨chord_endpoint_mem_cycleVertices (hfchord i), ?_⟩
    exact (sum_isRight_iff _).mpr ((adj_left_iff_right hi.1).mp hz)

omit [Fintype L] [Fintype R] in
private lemma selected_subset_left_of_right {k : ℕ} (hp : p.IsCycle)
    (hz : IsRight z) {f : Fin k → L ⊕ R}
    (hfchord : ∀ i, p.IsChord s(z, f i)) :
    selectedVertices p f ⊆ leftCycleVertices p := by
  intro x hx
  rw [selectedVertices, Finset.mem_union] at hx
  rw [leftCycleVertices, Finset.mem_filter]
  rcases hx with hxpair | hximage
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
    rcases hxpair with rfl | rfl
    · refine ⟨snd_mem_cycleVertices hp, ?_⟩
      exact (sum_isLeft_iff _).mpr
        ((adj_right_iff_left (p.adj_snd hp.not_nil)).mp hz)
    · refine ⟨penultimate_mem_cycleVertices hp, ?_⟩
      exact (sum_isLeft_iff _).mpr
        ((adj_right_iff_left (p.adj_penultimate hp.not_nil).symm).mp hz)
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hximage
    have hi := SimpleGraph.Walk.isChord_sym2Mk.mp (hfchord i)
    refine ⟨chord_endpoint_mem_cycleVertices (hfchord i), ?_⟩
    exact (sum_isLeft_iff _).mpr ((adj_right_iff_left hi.1).mp hz)

end SelectedVertices

lemma completeBipartite_avoids (k m : ℕ) :
    AvoidsCycleWithKIncidentChords k
      (completeBipartiteGraph (Fin (k + 1)) (Fin m)) := by
  rintro ⟨z, p, hp, f, hf, hfchord⟩
  have hcard : (selectedVertices p f).card = k + 2 :=
    card_selectedVertices hp hf hfchord
  cases z with
  | inl z =>
      have hsub := selected_subset_right_of_left hp (by simp) hfchord
      have hle := Finset.card_le_card hsub
      have hu := card_rightCycleVertices_le_left hp
      simp only [Fintype.card_fin] at hu
      rw [hcard] at hle
      omega
  | inr z =>
      have hsub := selected_subset_left_of_right hp (by simp) hfchord
      have hle := Finset.card_le_card hsub
      have hu := card_leftCycleVertices_le p
      simp only [Fintype.card_fin] at hu
      rw [hcard] at hle
      omega

private lemma card_edgeFinset_completeBipartiteFin (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).edgeFinset.card = a * b := by
  have h := encard_edgeSet_completeBipartiteGraph
    (W₁ := Fin a) (W₂ := Fin b)
  have h' := congrArg ENat.toNat h
  simpa [SimpleGraph.edgeFinset, Set.encard_eq_coe_toFinset_card] using h'

private abbrev LowerVertex (k n : ℕ) :=
  Fin (k + 1) ⊕ Fin (n - (k + 1))

private def lowerGraph (k n : ℕ) : SimpleGraph (LowerVertex k n) :=
  completeBipartiteGraph (Fin (k + 1)) (Fin (n - (k + 1)))

private lemma card_lowerVertex {k n : ℕ} (hkn : k + 1 ≤ n) :
    Fintype.card (LowerVertex k n) = n := by
  simp [LowerVertex]
  omega

private lemma lowerGraph_avoids (k n : ℕ) :
    AvoidsCycleWithKIncidentChords k (lowerGraph k n) :=
  completeBipartite_avoids k (n - (k + 1))

private lemma card_edgeFinset_lowerGraph (k n : ℕ) :
    (lowerGraph k n).edgeFinset.card =
      (k + 1) * n - (k + 1) ^ 2 := by
  rw [lowerGraph, card_edgeFinset_completeBipartiteFin]
  rw [Nat.mul_sub_left_distrib]
  simp [pow_two]

lemma lower_bound (k n : ℕ) (hkn : k + 1 ≤ n) :
    (k + 1) * n - (k + 1) ^ 2 ≤ chordCycleExtremalNumber k n := by
  let H := lowerGraph k n
  let Hn : SimpleGraph (Fin n) := H.overFin (card_lowerVertex hkn)
  have hfree : AvoidsCycleWithKIncidentChords k Hn := by
    rw [show Hn = H.overFin (card_lowerVertex hkn) by rfl]
    exact (avoids_iff_of_iso (H.overFinIso (card_lowerVertex hkn)) k).mp
      (lowerGraph_avoids k n)
  have hcard : Hn.edgeFinset.card =
      (k + 1) * n - (k + 1) ^ 2 := by
    rw [show Hn = H.overFin (card_lowerVertex hkn) by rfl]
    rw [← (H.overFinIso (card_lowerVertex hkn)).card_edgeFinset_eq]
    exact card_edgeFinset_lowerGraph k n
  rw [← hcard]
  exact card_edgeFinset_le_chordCycleExtremalNumber hfree

/-! ## The longest-path low-degree lemma -/

private lemma isChord_rotate_iff {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u v : V}
    (c : G.Walk u u) (hv : v ∈ c.support) (e : Sym2 V) :
    (c.rotate v hv).IsChord e ↔ c.IsChord e := by
  induction e using Sym2.ind with
  | _ x y =>
      simp only [SimpleGraph.Walk.isChord_sym2Mk,
        SimpleGraph.Walk.mem_support_rotate_iff]
      rw [(c.rotate_edges v hv).mem_iff]

lemma hasCycleWithKIncidentChords_of_isLongestPath_degree
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    {a b : V} {p : G.Walk a b}
    (hp : Erdos767LongestCycle.IsLongestPath p)
    (hdeg : k + 2 ≤ G.degree b) :
    HasCycleWithKIncidentChords k G := by
  classical
  let I : Finset ℕ := (Finset.range p.length).filter fun i ↦
    G.Adj b (p.getVert i)
  have htwo : 2 ≤ G.degree b := by omega
  have hplen : 2 ≤ p.length := htwo.trans hp.degree_end_le_length
  have hI : I.Nonempty := by
    refine ⟨p.length - 1, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    exact p.adj_penultimate (by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      omega) |>.symm
  let j : ℕ := I.min' hI
  have hjI : j ∈ I := Finset.min'_mem I hI
  have hjlt : j < p.length :=
    (Finset.mem_filter.mp hjI).1 |> Finset.mem_range.mp
  have hbj : G.Adj b (p.getVert j) := (Finset.mem_filter.mp hjI).2
  let r : G.Walk (p.getVert j) b := p.drop j
  have hrpath : r.IsPath := hp.1.drop j
  have hneighbor : G.neighborFinset b ⊆ r.support.toFinset.erase b := by
    intro x hx
    have hbx : G.Adj b x := (G.mem_neighborFinset b x).mp hx
    have hxP : x ∈ p.support := hp.end_neighbor_mem_support hbx
    obtain ⟨i, hi, hile⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxP
    have hilt : i < p.length := by
      rcases hile.lt_or_eq with hilt | rfl
      · exact hilt
      · rw [p.getVert_length] at hi
        exact (hbx.ne hi).elim
    have hiI : i ∈ I := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hilt, hi.symm ▸ hbx⟩
    have hji : j ≤ i := Finset.min'_le I i hiI
    have hxR : x ∈ r.support := by
      have hm : r.getVert (i - j) = x := by
        change (p.drop j).getVert (i - j) = x
        rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hji, hi]
      exact hm ▸ r.getVert_mem_support (i - j)
    exact Finset.mem_erase.mpr
      ⟨hbx.ne.symm, List.mem_toFinset.mpr hxR⟩
  have hdegree_le : G.degree b ≤ r.length := by
    rw [← G.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset b).card ≤ (r.support.toFinset.erase b).card :=
        Finset.card_le_card hneighbor
      _ = r.length := by
        rw [Finset.card_erase_of_mem
          (List.mem_toFinset.mpr r.end_mem_support)]
        rw [List.toFinset_card_of_nodup hrpath.support_nodup,
          r.length_support]
        omega
  have hrlen : 2 ≤ r.length := htwo.trans hdegree_le
  have hedge : s(p.getVert j, b) ∉ r.reverse.edges := by
    intro hedge
    have hedge' : s(p.getVert j, b) ∈ r.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using hedge
    have hone := hrpath.length_eq_one_of_mem_edges hedge'
    omega
  let c : G.Walk (p.getVert j) (p.getVert j) := r.reverse.cons hbj.symm
  have hc : c.IsCycle := by
    exact (SimpleGraph.Walk.cons_isCycle_iff r.reverse hbj.symm).mpr
      ⟨hrpath.reverse, hedge⟩
  have hbmem : b ∈ c.support := by
    simp only [c, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_reverse, List.mem_cons, List.mem_reverse]
    exact Or.inr r.end_mem_support
  let A : Finset V := G.neighborFinset b
  let B : Finset V := (c.toSubgraph.neighborSet b).toFinset
  have hBcard : B.card = 2 := by
    simpa [B] using hc.ncard_neighborSet_toSubgraph_eq_two hbmem
  have hBsub : B ⊆ A := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    exact (G.mem_neighborFinset b x).mpr (c.toSubgraph.adj_sub hx)
  let T : Finset V := A \ B
  have hTcard : k ≤ T.card := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset hBsub, hBcard]
    change k ≤ G.degree b - 2
    omega
  let g : Fin k ↪ T :=
    (Fin.castLEEmb hTcard).trans (Finset.equivFin T).symm.toEmbedding
  let f : Fin k → V := fun i ↦ (g i).1
  have hf : Function.Injective f := by
    intro i i' hii'
    apply g.injective
    exact Subtype.ext hii'
  let c' : G.Walk b b := c.rotate b hbmem
  have hc' : c'.IsCycle := by simpa [c'] using hc.rotate hbmem
  refine ⟨b, c', hc', f, hf, ?_⟩
  intro i
  have hxT : f i ∈ T := (g i).2
  have hxAB : f i ∈ A ∧ f i ∉ B := Finset.mem_sdiff.mp hxT
  have hbx : G.Adj b (f i) :=
    (G.mem_neighborFinset b (f i)).mp hxAB.1
  change (c.rotate b hbmem).IsChord s(b, f i)
  apply (isChord_rotate_iff c hbmem s(b, f i)).mpr
  rw [SimpleGraph.Walk.isChord_sym2Mk]
  refine ⟨hbx, ?_, hbmem, ?_⟩
  · intro he
    apply hxAB.2
    change f i ∈ (c.toSubgraph.neighborSet b).toFinset
    rw [Set.mem_toFinset, Subgraph.mem_neighborSet,
      SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    exact he
  · have hxR := hneighbor hxAB.1
    have hxRs : f i ∈ r.support :=
      List.mem_toFinset.mp (Finset.mem_of_mem_erase hxR)
    simp only [c, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_reverse, List.mem_cons, List.mem_reverse]
    exact Or.inr hxRs

lemma exists_degree_le_add_one
    {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G) :
    ∃ v : V, G.degree v ≤ k + 1 := by
  classical
  obtain ⟨a, b, p, hp⟩ :=
    Erdos767LongestCycle.exists_isLongestPath (G := G)
  refine ⟨b, ?_⟩
  by_contra h
  exact hG (hasCycleWithKIncidentChords_of_isLongestPath_degree hp (by omega))

/-! ## Induction above Jiang's base order -/

lemma edge_count_add_sq_le_of_base (k : ℕ)
    (hbase : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = 3 * (k + 1) →
        AvoidsCycleWithKIncidentChords k H →
        H.edgeFinset.card ≤ 2 * (k + 1) ^ 2) :
    ∀ (V : Type u) [Fintype V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      3 * (k + 1) ≤ Fintype.card V →
        AvoidsCycleWithKIncidentChords k G →
        G.edgeFinset.card + (k + 1) ^ 2 ≤
          (k + 1) * Fintype.card V := by
  classical
  intro V _ G _ hn hG
  generalize hcard : Fintype.card V = n at hn ⊢
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases heq : n = 3 * (k + 1)
      · have hb := hbase V G (hcard.trans heq) hG
        nlinarith
      · have hlt : 3 * (k + 1) < n :=
          lt_of_le_of_ne hn (Ne.symm heq)
        let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
        obtain ⟨v, hvdeg⟩ := exists_degree_le_add_one hG
        let W : Type u := {x : V // x ∈ ({v}ᶜ : Set V)}
        let H : SimpleGraph W := G.induce ({v}ᶜ : Set V)
        have hWcard : Fintype.card W = n - 1 := by
          dsimp [W]
          change Fintype.card {x : V // x ≠ v} = n - 1
          rw [Fintype.card_subtype_compl (fun x : V ↦ x = v)]
          simp [hcard]
        have hHfree : AvoidsCycleWithKIncidentChords k H :=
          avoids_induce hG ({v}ᶜ : Set V)
        have hIH := ih (n - 1) (by omega) W H hHfree hWcard (by omega)
        have hdegcard : G.degree v ≤ G.edgeFinset.card :=
          G.degree_le_card_edgeFinset v
        have hedge : H.edgeFinset.card + G.degree v = G.edgeFinset.card := by
          dsimp [H]
          rw [G.card_edgeFinset_induce_compl_singleton,
            G.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel hdegcard]
        have hnsub : n - 1 + 1 = n := by omega
        nlinarith

lemma edge_count_le_of_base (k : ℕ)
    (hbase : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = 3 * (k + 1) →
        AvoidsCycleWithKIncidentChords k H →
        H.edgeFinset.card ≤ 2 * (k + 1) ^ 2)
    (V : Type u) [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 * (k + 1) ≤ Fintype.card V)
    (hG : AvoidsCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤
      (k + 1) * Fintype.card V - (k + 1) ^ 2 := by
  classical
  exact Nat.le_sub_of_add_le
    (edge_count_add_sq_le_of_base k hbase V G hn hG)

/-! ## Jiang's sharp base case, reduced to Bondy's longest-cycle estimate -/

private lemma hasCycleWithKIncidentChords_of_hamiltonianCycle_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    {z : V} {c : G.Walk z z} (hc : c.IsHamiltonianCycle)
    (x : V) (hdeg : k + 2 ≤ G.degree x) :
    HasCycleWithKIncidentChords k G := by
  have hx : x ∈ c.support := hc.mem_support x
  let A : Finset V := G.neighborFinset x
  let B : Finset V := (c.toSubgraph.neighborSet x).toFinset
  have hBcard : B.card = 2 := by
    simpa [B] using hc.isCycle.ncard_neighborSet_toSubgraph_eq_two hx
  have hBsub : B ⊆ A := by
    intro y hy
    rw [Set.mem_toFinset] at hy
    exact (G.mem_neighborFinset x y).mpr (c.toSubgraph.adj_sub hy)
  let T : Finset V := A \ B
  have hTcard : k ≤ T.card := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset hBsub, hBcard]
    change k ≤ G.degree x - 2
    omega
  let g : Fin k ↪ T :=
    (Fin.castLEEmb hTcard).trans (Finset.equivFin T).symm.toEmbedding
  let f : Fin k → V := fun i ↦ (g i).1
  have hf : Function.Injective f := by
    intro i j hij
    apply g.injective
    exact Subtype.ext hij
  let c' : G.Walk x x := c.rotate x hx
  refine ⟨x, c', hc.isCycle.rotate hx, f, hf, ?_⟩
  intro i
  have hfi : f i ∈ T := (g i).2
  have hAB : f i ∈ A ∧ f i ∉ B := Finset.mem_sdiff.mp hfi
  have hadj : G.Adj x (f i) := (G.mem_neighborFinset x (f i)).mp hAB.1
  apply (isChord_rotate_iff c hx s(x, f i)).mpr
  rw [SimpleGraph.Walk.isChord_sym2Mk]
  refine ⟨hadj, ?_, hx, hc.mem_support (f i)⟩
  intro he
  apply hAB.2
  change f i ∈ (c.toSubgraph.neighborSet x).toFinset
  rw [Set.mem_toFinset, Subgraph.mem_neighborSet,
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  exact he

lemma degree_le_add_one_on_hamiltonianCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G)
    {z : V} {c : G.Walk z z} (hc : c.IsHamiltonianCycle)
    (x : V) : G.degree x ≤ k + 1 := by
  by_contra h
  exact hG (hasCycleWithKIncidentChords_of_hamiltonianCycle_degree hc x (by omega))

lemma two_mul_card_edges_le_of_hamiltonianCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G)
    {z : V} {c : G.Walk z z} (hc : c.IsHamiltonianCycle) :
    2 * G.edgeFinset.card ≤ (k + 1) * Fintype.card V := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  calc
    ∑ x, G.degree x ≤ ∑ _x : V, (k + 1) := by
      exact Finset.sum_le_sum fun x _hx ↦
        degree_le_add_one_on_hamiltonianCycle hG hc x
    _ = (k + 1) * Fintype.card V := by
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
      exact Nat.mul_comm _ _

private lemma avoids_zero_of_isAcyclic
    {V : Type u} {G : SimpleGraph V} (hG : G.IsAcyclic) :
    AvoidsCycleWithKIncidentChords 0 G := by
  rintro ⟨v, c, hc, f, hf, hchord⟩
  exact hG c hc

lemma card_edgeFinset_le_card_sub_one_of_isAcyclic
    {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V - 1 := by
  classical
  generalize hcard : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hn : n ≤ 1
      · have hedge := G.card_edgeFinset_le_card_choose_two
        rw [hcard] at hedge
        interval_cases n <;> simp_all
      · obtain ⟨v, hv⟩ := exists_degree_le_add_one
          (avoids_zero_of_isAcyclic hG)
        let W : Type u := {x : V // x ∈ ({v}ᶜ : Set V)}
        let H : SimpleGraph W := G.induce ({v}ᶜ : Set V)
        have hWcard : Fintype.card W = n - 1 := by
          dsimp [W]
          change Fintype.card {x : V // x ≠ v} = n - 1
          rw [Fintype.card_subtype_compl (fun x : V ↦ x = v)]
          simp [hcard]
        let : Nonempty W := Fintype.card_pos_iff.mp (by omega)
        have hHacyc : H.IsAcyclic := hG.induce ({v}ᶜ : Set V)
        have hIH := ih (n - 1) (by omega) (V := W) H hHacyc hWcard
        have hdegcard : G.degree v ≤ G.edgeFinset.card :=
          G.degree_le_card_edgeFinset v
        have hedge : H.edgeFinset.card + G.degree v = G.edgeFinset.card := by
          dsimp [H]
          rw [G.card_edgeFinset_induce_compl_singleton,
            G.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel hdegcard]
        omega

/-! ## Longest-cycle induction across cut vertices -/

/-- The local longest-cycle predicate used by the induction below. -/
private def InductionLongestCycle {V : Type u} {G : SimpleGraph V}
    {z : V} (q : G.Walk z z) : Prop :=
  q.IsCycle ∧ ∀ (w : V) (r : G.Walk w w), r.IsCycle → r.length ≤ q.length

private lemma isCycle_length_le_card
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    {z : V} {q : G.Walk z z} (hq : q.IsCycle) :
    q.length ≤ Fintype.card V := by
  classical
  rw [← Erdos767LongestCycle.cycleCarrier_card hq]
  exact Finset.card_le_univ _

private lemma card_setCoe_finset
    {V : Type u} (A : Finset V) :
    Fintype.card (↑A : Set V) = A.card := by
  classical
  simp

private lemma card_insert_add_card_compl
    {V : Type u} [Fintype V] [DecidableEq V]
    (c : V) (A : Finset V) (hcA : c ∉ A) :
    (insert c A).card + Aᶜ.card = Fintype.card V + 1 := by
  have hle : A.card ≤ Fintype.card V := by simpa using Finset.card_le_univ A
  rw [Finset.card_insert_of_notMem hcA, Finset.card_compl]
  omega

private lemma card_insert_lt_card_of_mem_compl_erase
    {V : Type u} [Fintype V] [DecidableEq V]
    (c : V) (A : Finset V) {y : V} (hy : y ∈ Aᶜ.erase c) :
    (insert c A).card < Fintype.card V := by
  have hyA : y ∉ A := Finset.mem_compl.mp (Finset.mem_erase.mp hy).2
  have hyc : y ≠ c := (Finset.mem_erase.mp hy).1
  have hsub : insert c A ⊆ Finset.univ.erase y := by
    intro z hz
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ z⟩
    intro hzy
    subst z
    simp only [Finset.mem_insert] at hz
    exact hz.elim (fun h ↦ hyc h) (fun h ↦ hyA h)
  have hle := Finset.card_le_card hsub
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  have herase : (Finset.univ.erase y).card = Fintype.card V - 1 := by simp
  rw [herase] at hle
  omega

private lemma card_compl_lt_card_of_mem
    {V : Type u} [Fintype V] [DecidableEq V]
    (A : Finset V) {x : V} (hx : x ∈ A) :
    Aᶜ.card < Fintype.card V := by
  rw [Finset.card_compl]
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hle : A.card ≤ Fintype.card V := by simpa using Finset.card_le_univ A
  omega

private lemma cut_edge_cover
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (A : Finset V) (_hcA : c ∉ A)
    (hcross : G.interedges A (Aᶜ.erase c) = ∅) :
    ∀ u v, G.Adj u v →
      (u ∈ insert c A ∧ v ∈ insert c A) ∨ (u ∈ Aᶜ ∧ v ∈ Aᶜ) := by
  intro u v huv
  by_cases huA : u ∈ A
  · by_cases hvA : v ∈ A
    · exact Or.inl ⟨by simp [huA], by simp [hvA]⟩
    · by_cases hvc : v = c
      · subst v
        exact Or.inl ⟨by simp [huA], by simp⟩
      · exfalso
        have he : (u, v) ∈ G.interedges A (Aᶜ.erase c) :=
          G.mk_mem_interedges_iff.mpr
            ⟨huA, Finset.mem_erase.mpr ⟨hvc, Finset.mem_compl.mpr hvA⟩, huv⟩
        simp [hcross] at he
  · by_cases hvA : v ∈ A
    · by_cases huc : u = c
      · subst u
        exact Or.inl ⟨by simp, by simp [hvA]⟩
      · exfalso
        have he : (v, u) ∈ G.interedges A (Aᶜ.erase c) :=
          G.mk_mem_interedges_iff.mpr
            ⟨hvA, Finset.mem_erase.mpr ⟨huc, Finset.mem_compl.mpr huA⟩, huv.symm⟩
        simp [hcross] at he
    · exact Or.inr ⟨Finset.mem_compl.mpr huA, Finset.mem_compl.mpr hvA⟩

private lemma cut_inter_card_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (c : V) (A : Finset V) (hcA : c ∉ A) :
    ((insert c A) ∩ Aᶜ).card ≤ 1 := by
  have hsub : insert c A ∩ Aᶜ ⊆ {c} := by
    intro x hx
    have hxL := (Finset.mem_inter.mp hx).1
    have hxR := (Finset.mem_inter.mp hx).2
    simp only [Finset.mem_insert] at hxL
    rcases hxL with rfl | hxA
    · simp
    · exact False.elim ((Finset.mem_compl.mp hxR) hxA)
  simpa using Finset.card_le_card hsub

private lemma card_edgeFinset_eq_add_induce_of_cut
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (A : Finset V) (hcA : c ∉ A)
    (hcross : G.interedges A (Aᶜ.erase c) = ∅) :
    G.edgeFinset.card =
      (G.induce (↑(insert c A) : Set V)).edgeFinset.card +
        (G.induce (↑(Aᶜ) : Set V)).edgeFinset.card := by
  exact E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_of_separation
    G (insert c A) Aᶜ (cut_edge_cover G c A hcA hcross)
      (cut_inter_card_le_one c A hcA)

private lemma reachable_induce_of_mem_support
    {V : Type u}
    {G : SimpleGraph V}
    {S : Set V} {u v x y : V} (p : G.Walk u v)
    (hS : ∀ z ∈ p.support, z ∈ S)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    (G.induce S).Reachable ⟨x, hS x hx⟩ ⟨y, hS y hy⟩ := by
  classical
  have hr := p.connected_induce_support.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  exact hr.map (G.induceHomOfLE hS).toHom

private lemma cycle_vertices_reachable_delete
    {V : Type u}
    {G : SimpleGraph V}
    {v c x y : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxc : x ≠ c) (hyc : y ≠ c) :
    (G.induce {z : V | z ≠ c}).Reachable ⟨x, hxc⟩ ⟨y, hyc⟩ := by
  classical
  by_cases hc : c ∈ p.support
  · let q : G.Walk c c := p.rotate c hc
    have hq : q.IsCycle := hp.rotate hc
    have hqtail : ¬ q.tail.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      have hlen := hq.three_le_length
      have ht := q.length_tail_add_one hq.not_nil
      omega
    let r := q.tail.dropLast
    have hrSupport : r.support = q.tail.support.dropLast :=
      q.tail.support_dropLast hqtail
    have hxq : x ∈ q.support := (p.mem_support_rotate_iff c hc).mpr hx
    have hyq : y ∈ q.support := (p.mem_support_rotate_iff c hc).mpr hy
    have hxt : x ∈ q.tail.support := by
      rw [q.support_tail_of_not_nil hq.not_nil]
      rw [← q.cons_tail_support] at hxq
      exact (List.mem_cons.mp hxq).resolve_left hxc
    have hyt : y ∈ q.tail.support := by
      rw [q.support_tail_of_not_nil hq.not_nil]
      rw [← q.cons_tail_support] at hyq
      exact (List.mem_cons.mp hyq).resolve_left hyc
    have hxdrop : x ∈ q.tail.support.dropLast := by
      apply List.mem_dropLast_of_mem_of_ne_getLast hxt
      simpa only [q.tail.getLast_support] using hxc
    have hydrop : y ∈ q.tail.support.dropLast := by
      apply List.mem_dropLast_of_mem_of_ne_getLast hyt
      simpa only [q.tail.getLast_support] using hyc
    have hcnot : c ∉ q.tail.support.dropLast := by
      have hdecomp := List.dropLast_append_getLast
        (l := q.tail.support) q.tail.support_ne_nil
      have hnodup := hq.isPath_tail.support_nodup
      rw [← hdecomp] at hnodup
      simp only [q.tail.getLast_support, List.nodup_append,
        List.nodup_singleton, true_and, List.mem_singleton, forall_eq] at hnodup
      exact fun hcMem ↦ (hnodup.2 c hcMem) rfl
    have hS : ∀ z ∈ r.support, z ∈ ({z : V | z ≠ c} : Set V) := by
      intro z hz hzc
      subst z
      apply hcnot
      rw [← hrSupport]
      exact hz
    have hxr : x ∈ r.support := by rwa [hrSupport]
    have hyr : y ∈ r.support := by rwa [hrSupport]
    simpa using reachable_induce_of_mem_support r hS hxr hyr
  · have hS : ∀ z ∈ p.support, z ∈ ({z : V | z ≠ c} : Set V) := by
      intro z hz hzc
      subst z
      exact hc hz
    simpa using reachable_induce_of_mem_support p hS hx hy

private noncomputable def cutComponent
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (x : {v : V // v ≠ c}) : Finset V :=
  (Finset.univ.filter fun y : {v : V // v ≠ c} ↦
    (G.induce {v : V | v ≠ c}).Reachable x y).map
      (Function.Embedding.subtype _)

@[simp] private lemma mem_cutComponent
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {c : V} {x : {v : V // v ≠ c}} {z : V} :
    z ∈ cutComponent G c x ↔
      ∃ hz : z ≠ c, (G.induce {v : V | v ≠ c}).Reachable x ⟨z, hz⟩ := by
  simp [cutComponent]

private lemma cutVertex_not_mem_cutComponent
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (x : {v : V // v ≠ c}) : c ∉ cutComponent G c x := by
  simp

private lemma interedges_cutComponent_compl_erase_eq_empty
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (x : {v : V // v ≠ c}) :
    G.interedges (cutComponent G c x) ((cutComponent G c x)ᶜ.erase c) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' :
      (e.1 ∈ cutComponent G c x ∧ e.2 ∈ (cutComponent G c x)ᶜ.erase c) ∧
        G.Adj e.1 e.2 := by
    simpa [SimpleGraph.interedges_def] using he
  obtain ⟨hu, hxu⟩ := mem_cutComponent.mp he'.1.1
  have hv : e.2 ≠ c := (Finset.mem_erase.mp he'.1.2).1
  have huv : (G.induce {v : V | v ≠ c}).Adj ⟨e.1, hu⟩ ⟨e.2, hv⟩ :=
    SimpleGraph.induce_adj.mpr he'.2
  have hxv := hxu.trans huv.reachable
  exact (Finset.mem_compl.mp (Finset.mem_erase.mp he'.1.2).2)
    (mem_cutComponent.mpr ⟨hv, hxv⟩)

private lemma cycle_support_subset_cut_side
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v c : V} {p : G.Walk v v} (hp : p.IsCycle)
    (x : {z : V // z ≠ c}) :
    (∀ z ∈ p.support, z ∈ insert c (cutComponent G c x)) ∨
      (∀ z ∈ p.support, z ∈ (cutComponent G c x)ᶜ) := by
  have hsnd : p.snd ∈ p.support :=
    List.mem_of_mem_tail (p.snd_mem_tail_support hp.not_nil)
  have hpen : p.penultimate ∈ p.support :=
    List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hp.not_nil)
  obtain ⟨w, hw, hwc⟩ : ∃ w, w ∈ p.support ∧ w ≠ c := by
    by_cases hsc : p.snd = c
    · exact ⟨p.penultimate, hpen,
        fun hpc ↦ hp.snd_ne_penultimate (hsc.trans hpc.symm)⟩
    · exact ⟨p.snd, hsnd, hsc⟩
  by_cases hwA : w ∈ cutComponent G c x
  · left
    intro z hz
    by_cases hzc : z = c
    · simp [hzc]
    · apply Finset.mem_insert.mpr
      right
      obtain ⟨_, hxw⟩ := mem_cutComponent.mp hwA
      have hwz := cycle_vertices_reachable_delete hp hw hz hwc hzc
      exact mem_cutComponent.mpr ⟨hzc, hxw.trans hwz⟩
  · right
    intro z hz
    apply Finset.mem_compl.mpr
    intro hzA
    by_cases hzc : z = c
    · subst z
      exact cutVertex_not_mem_cutComponent G c x hzA
    · obtain ⟨_, hxz⟩ := mem_cutComponent.mp hzA
      have hwz := cycle_vertices_reachable_delete hp hw hz hwc hzc
      apply hwA
      exact mem_cutComponent.mpr ⟨hwc, hxz.trans hwz.symm⟩

private lemma induce_isCycle
    {V : Type u}
    {G : SimpleGraph V}
    {S : Set V} {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hS : ∀ z ∈ p.support, z ∈ S) :
    (p.induce S hS).IsCycle := by
  classical
  have hm : ((p.induce S hS).map
      (SimpleGraph.Embedding.induce (G := G) S).toHom).IsCycle := by
    simpa using hp
  exact hm.of_map

private lemma length_induce_eq
    {V : Type u}
    {G : SimpleGraph V}
    {S : Set V} {x y : V} (p : G.Walk x y)
    (hS : ∀ z ∈ p.support, z ∈ S) :
    (p.induce S hS).length = p.length := by
  classical
  have hm := congrArg (fun r ↦ r.length) (SimpleGraph.Walk.map_induce p hS)
  simp only [SimpleGraph.Walk.length_map] at hm
  exact hm

private lemma induce_isLongestCycle
    {V : Type u}
    {G : SimpleGraph V}
    {S : Set V} {v : V} {p : G.Walk v v}
    (hp : InductionLongestCycle p)
    (hS : ∀ z ∈ p.support, z ∈ S) :
    InductionLongestCycle (p.induce S hS) := by
  classical
  refine ⟨induce_isCycle hp.1 hS, ?_⟩
  intro w q hq
  have hqG : (q.map (SimpleGraph.Embedding.induce (G := G) S).toHom).IsCycle :=
    hq.map (SimpleGraph.Embedding.induce (G := G) S).injective
  have hlen := hp.2 w.1
    (q.map (SimpleGraph.Embedding.induce (G := G) S).toHom) hqG
  rw [length_induce_eq p hS]
  exact (SimpleGraph.Walk.length_map _ q).symm ▸ hlen

private def componentFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : Finset V :=
  Finset.univ.filter fun z ↦ G.Reachable r z

@[simp] private lemma mem_componentFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r z : V} :
    z ∈ componentFinset G r ↔ G.Reachable r z := by
  simp [componentFinset]

private lemma root_mem_componentFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : r ∈ componentFinset G r := by simp

private lemma cycle_support_subset_component
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V} (p : G.Walk v v) :
    ∀ z ∈ p.support, z ∈ componentFinset G v := by
  intro z hz
  rw [mem_componentFinset]
  exact (p.takeUntil z hz).reachable

private lemma card_edgeFinset_eq_add_induce_component
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    G.edgeFinset.card =
      (G.induce (↑(componentFinset G r) : Set V)).edgeFinset.card +
        (G.induce (↑((componentFinset G r)ᶜ) : Set V)).edgeFinset.card := by
  apply E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_compl
  intro u v huv
  simp only [mem_componentFinset]
  constructor
  · exact fun hu ↦ hu.trans huv.reachable
  · exact fun hv ↦ hv.trans huv.symm.reachable

private lemma cyclic_cut_arithmetic {n nL nR c a eL eR : ℕ}
    (hcard : nL + nR = n + 1) (hcL : c ≤ nL) (hRpos : 0 < nR)
    (hL : 2 * eL ≤ a * c + c * (nL - c))
    (hR : 2 * eR ≤ c * (nR - 1)) :
    2 * (eL + eR) ≤ a * c + c * (n - c) := by
  have hparts : (nL - c) + (nR - 1) = n - c := by omega
  calc
    2 * (eL + eR) = 2 * eL + 2 * eR := by omega
    _ ≤ (a * c + c * (nL - c)) + c * (nR - 1) := Nat.add_le_add hL hR
    _ = a * c + c * ((nL - c) + (nR - 1)) := by rw [Nat.mul_add]; omega
    _ = a * c + c * (n - c) := by rw [hparts]

private lemma cyclic_disconnected_arithmetic {n nL nR c a eL eR : ℕ}
    (hcard : nL + nR = n) (hcL : c ≤ nL) (hRpos : 0 < nR)
    (hL : 2 * eL ≤ a * c + c * (nL - c))
    (hR : 2 * eR ≤ c * (nR - 1)) :
    2 * (eL + eR) ≤ a * c + c * (n - c) := by
  have hparts : (nL - c) + (nR - 1) ≤ n - c := by omega
  calc
    2 * (eL + eR) = 2 * eL + 2 * eR := by omega
    _ ≤ (a * c + c * (nL - c)) + c * (nR - 1) := Nat.add_le_add hL hR
    _ = a * c + c * ((nL - c) + (nR - 1)) := by rw [Nat.mul_add]; omega
    _ ≤ a * c + c * (n - c) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left c hparts) _

/-- Edges whose two endpoints lie on a fixed finite vertex carrier. -/
def cycleInsideEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ C

/-- Edges with at least one endpoint outside a fixed finite vertex carrier. -/
def cycleOutsideEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset \ cycleInsideEdges G C

lemma cycleInsideEdges_subset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    cycleInsideEdges G C ⊆ G.edgeFinset := by
  intro e he
  exact (Finset.mem_filter.mp he).1

lemma card_inside_add_outside {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    (cycleInsideEdges G C).card + (cycleOutsideEdges G C).card =
      G.edgeFinset.card := by
  rw [cycleOutsideEdges, Finset.card_sdiff_of_subset (cycleInsideEdges_subset G C)]
  exact Nat.add_sub_of_le (Finset.card_le_card (cycleInsideEdges_subset G C))

lemma card_cycleInsideEdges_eq_induce {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    (cycleInsideEdges G C).card = (G.induce (C : Set V)).edgeFinset.card := by
  exact G.card_filter_edgeFinset_toFinset_subset C

lemma two_mul_card_cycleInsideEdges_le
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hG : AvoidsCycleWithKIncidentChords k G)
    {z : V} {c : G.Walk z z} (hc : c.IsCycle) :
    2 * (cycleInsideEdges G c.support.toFinset).card ≤
      (k + 1) * c.length := by
  let C : Finset V := c.support.toFinset
  let hC : ∀ x ∈ c.support, x ∈ (C : Set V) := fun x hx ↦
    List.mem_toFinset.mpr hx
  let q : (G.induce (C : Set V)).Walk ⟨z, hC z c.start_mem_support⟩
      ⟨z, hC z c.end_mem_support⟩ := c.induce (C : Set V) hC
  have hq : q.IsHamiltonianCycle := by
    simpa [C, hC, q] using
      (Erdos767LongestCycle.induced_cycle_isHamiltonianCycle hc)
  have hfree : AvoidsCycleWithKIncidentChords k (G.induce (C : Set V)) :=
    avoids_induce hG (C : Set V)
  have hbound := two_mul_card_edges_le_of_hamiltonianCycle hfree hq
  rw [card_cycleInsideEdges_eq_induce]
  change 2 * (G.induce (C : Set V)).edgeFinset.card ≤ (k + 1) * c.length
  convert hbound using 1
  exact congrArg ((k + 1) * ·) <| ((Fintype.card_coe C).trans
    (Erdos767LongestCycle.cycleCarrier_card hc)).symm

/-- Strong cyclic estimate used in Jiang's base case.  The longest cycle is
allowed to change after a low-degree deletion; this is why the global
best-lollipop theorem suffices. -/
lemma cyclic_free_edge_bound
    (k : ℕ) :
    ∀ (W : Type u) [Fintype W]
      (H : SimpleGraph W) [DecidableRel H.Adj]
      (z : W) (q : H.Walk z z),
      AvoidsCycleWithKIncidentChords k H →
      InductionLongestCycle q →
      2 * H.edgeFinset.card ≤
        (k + 1) * q.length +
          q.length * (Fintype.card W - q.length) := by
  classical
  intro W _ H _ z q hfree hq
  generalize hn : Fintype.card W = n
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
    have hqcard : q.length ≤ Fintype.card W := isCycle_length_le_card hq.1
    have hqthree : 3 ≤ q.length := hq.1.three_le_length
    have hcycles (X : Type u) [Fintype X] [DecidableEq X]
        (K : SimpleGraph X) [DecidableRel K.Adj]
        (f : K ↪g H) :
        ∀ (w : X) (r : K.Walk w w), r.IsCycle → r.length ≤ q.length := by
      intro w r hr
      have ht := hq.2 (f w) (r.map f.toHom) (hr.map f.injective)
      calc
        r.length = (r.map f.toHom).length :=
          (SimpleGraph.Walk.length_map _ r).symm
        _ ≤ q.length := ht
    by_cases hpre : H.Preconnected
    · let : Nonempty W := ⟨z⟩
      have hconn : H.Connected := ⟨hpre⟩
      have hcard3 : 3 ≤ Fintype.card W := hqthree.trans hqcard
      by_cases hdel : ∀ c : W, (H.induce ({c}ᶜ : Set W)).Connected
      · have htwo : Erdos58.TwoConnected H := ⟨hcard3, hconn, hdel⟩
        by_cases hspan : Fintype.card W = q.length
        · have hham : q.IsHamiltonianCycle :=
            SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
              ⟨hq.1, hspan.symm⟩
          have hbase := two_mul_card_edges_le_of_hamiltonianCycle hfree hham
          rw [hspan] at hbase
          rw [← hn, hspan]
          simpa using hbase
        · have hnonspan : q.length < Fintype.card W :=
            lt_of_le_of_ne hqcard (Ne.symm hspan)
          have hqN : Erdos767LongestCycle.IsLongestCycle q := by
            refine ⟨hq.1, ?_⟩
            intro z' r hr
            exact hq.2 z' r hr
          obtain ⟨w, r, v, hrN, hv, hdeg⟩ :=
            Erdos767Dirac.exists_nonspanning_longestCycle_lowDegree
              H htwo hqN hnonspan
          have hr : InductionLongestCycle r :=
            ⟨hrN.1, fun _ r' hr' ↦ hrN.2 r' hr'⟩
          have hrq : r.length = q.length := by
            apply Nat.le_antisymm
            · exact hq.2 w r hr.1
            · exact hr.2 z q hq.1
          let S : Set W := {v}ᶜ
          have hrS : ∀ x ∈ r.support, x ∈ S := by
            intro x hx
            simp only [S, Set.mem_compl_iff, Set.mem_singleton_iff]
            intro hxv
            subst x
            exact hv hx
          let K : SimpleGraph S := H.induce S
          let p := r.induce S hrS
          have hp : InductionLongestCycle p := induce_isLongestCycle hr hrS
          have hfreeK : AvoidsCycleWithKIncidentChords k K :=
            avoids_induce hfree S
          have hScard : Fintype.card S = Fintype.card W - 1 := by
            dsimp [S]
            rw [Fintype.card_compl_set, Set.card_singleton]
          have hSlt : Fintype.card S < n := by omega
          have hind := ih (Fintype.card S) hSlt S K
            ⟨w, hrS w r.start_mem_support⟩ p hfreeK hp rfl
          rw [show p.length = r.length by exact length_induce_eq r hrS,
            hrq, hScard] at hind
          have hdegcard : H.degree v ≤ H.edgeFinset.card :=
            H.degree_le_card_edgeFinset v
          have hedge : K.edgeFinset.card + H.degree v = H.edgeFinset.card := by
            dsimp [K, S]
            rw [H.card_edgeFinset_induce_compl_singleton,
              H.card_edgeFinset_deleteIncidenceSet,
              Nat.sub_add_cancel hdegcard]
          calc
            2 * H.edgeFinset.card =
                2 * K.edgeFinset.card + 2 * H.degree v := by omega
            _ ≤ ((k + 1) * q.length +
                q.length * (Fintype.card W - 1 - q.length)) + q.length :=
              Nat.add_le_add hind (hrq ▸ hdeg)
            _ = (k + 1) * q.length + q.length * (n - q.length) := by
              rw [← hn, show Fintype.card W - q.length =
                (Fintype.card W - 1 - q.length) + 1 by omega, Nat.mul_add]
              omega
      · push Not at hdel
        obtain ⟨c, hc⟩ := hdel
        have hdelcard : 0 < Fintype.card ({c}ᶜ : Set W) := by
          rw [Fintype.card_compl_set, Set.card_singleton]
          omega
        let : Nonempty ({c}ᶜ : Set W) := Fintype.card_pos_iff.mp hdelcard
        have hnotpre : ¬ (H.induce ({c}ᶜ : Set W)).Preconnected := by
          intro hp
          exact hc ⟨hp⟩
        simp only [SimpleGraph.Preconnected] at hnotpre
        push Not at hnotpre
        obtain ⟨x, y, hxy⟩ := hnotpre
        let A := cutComponent H c x
        have hcA : c ∉ A := cutVertex_not_mem_cutComponent H c x
        have hxA : x.1 ∈ A := mem_cutComponent.mpr
          ⟨x.2, SimpleGraph.Reachable.rfl⟩
        have hyB : y.1 ∈ Aᶜ.erase c := by
          apply Finset.mem_erase.mpr
          refine ⟨y.2, Finset.mem_compl.mpr ?_⟩
          intro hyA
          exact hxy (mem_cutComponent.mp hyA).2
        have hcross := interedges_cutComponent_compl_erase_eq_empty H c x
        have hcardSplit := card_insert_add_card_compl c A hcA
        have hleftlt := card_insert_lt_card_of_mem_compl_erase c A hyB
        have hrightlt := card_compl_lt_card_of_mem A hxA
        rcases cycle_support_subset_cut_side H hq.1 x with hqL | hqR
        · let S := insert c A
          let pL := q.induce (↑S : Set W) hqL
          have hpL := induce_isLongestCycle hq hqL
          have hfreeL := avoids_induce hfree (↑S : Set W)
          have hIL := ih S.card (by simpa [S, hn] using hleftlt)
            (↑S : Set W) (H.induce (↑S : Set W))
            ⟨z, hqL z q.start_mem_support⟩ pL hfreeL hpL
            (by simp [Fintype.card_coe])
          rw [show pL.length = q.length by exact length_induce_eq q hqL] at hIL
          have hcyclesR := hcycles (↑(Aᶜ) : Set W)
            (H.induce (↑(Aᶜ) : Set W))
            (SimpleGraph.Embedding.induce (G := H) _)
          have hER := Erdos767Dirac.erdosGallai_cycle
            (H.induce (↑(Aᶜ) : Set W)) q.length (by omega) hcyclesR
          rw [card_setCoe_finset (Aᶜ)] at hER
          have hedge := card_edgeFinset_eq_add_induce_of_cut H c A hcA hcross
          rw [hedge]
          exact cyclic_cut_arithmetic
            (n := n) (nL := S.card) (nR := Aᶜ.card)
            (c := q.length) (a := k + 1)
            (by simpa [S, hn] using hcardSplit)
            (by
              rw [← length_induce_eq q hqL]
              have ht := isCycle_length_le_card hpL.1
              rw [card_setCoe_finset S] at ht
              exact ht)
            (Finset.card_pos.mpr ⟨y.1, (Finset.mem_erase.mp hyB).2⟩)
            hIL hER
        · let S := Aᶜ
          let pR := q.induce (↑S : Set W) hqR
          have hpR := induce_isLongestCycle hq hqR
          have hfreeR := avoids_induce hfree (↑S : Set W)
          have hIR := ih S.card (by simpa [S, hn] using hrightlt)
            (↑S : Set W) (H.induce (↑S : Set W))
            ⟨z, hqR z q.start_mem_support⟩ pR hfreeR hpR
            (by simp [Fintype.card_coe])
          rw [show pR.length = q.length by exact length_induce_eq q hqR] at hIR
          have hcyclesL := hcycles (↑(insert c A) : Set W)
            (H.induce (↑(insert c A) : Set W))
            (SimpleGraph.Embedding.induce (G := H) _)
          have hEL := Erdos767Dirac.erdosGallai_cycle
            (H.induce (↑(insert c A) : Set W)) q.length (by omega) hcyclesL
          rw [card_setCoe_finset (insert c A)] at hEL
          have hedge := card_edgeFinset_eq_add_induce_of_cut H c A hcA hcross
          rw [hedge, Nat.add_comm]
          exact cyclic_cut_arithmetic
            (n := n) (nL := S.card) (nR := (insert c A).card)
            (c := q.length) (a := k + 1)
            (by simpa [S, hn, Nat.add_comm] using hcardSplit)
            (by
              rw [← length_induce_eq q hqR]
              have ht := isCycle_length_le_card hpR.1
              rw [card_setCoe_finset S] at ht
              exact ht)
            (Finset.card_pos.mpr ⟨c, by simp⟩) hIR hEL
    · have hy : ∃ y : W, ¬ H.Reachable z y := by
        by_contra hall
        push Not at hall
        apply hpre
        intro x y
        exact (hall x).symm.trans (hall y)
      obtain ⟨y, hzy⟩ := hy
      let S := componentFinset H z
      have hzS : z ∈ S := root_mem_componentFinset H z
      have hySc : y ∈ Sᶜ := Finset.mem_compl.mpr (by simpa [S] using hzy)
      have hSlt : S.card < Fintype.card W := by
        rw [← Finset.card_univ]
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_univ _, fun heq ↦
            (Finset.mem_compl.mp hySc) (heq.symm ▸ Finset.mem_univ y)⟩)
      have hqS := cycle_support_subset_component q
      let pS := q.induce (↑S : Set W) hqS
      have hpS := induce_isLongestCycle hq hqS
      have hfreeS := avoids_induce hfree (↑S : Set W)
      have hIS := ih S.card (by simpa [hn] using hSlt)
        (↑S : Set W) (H.induce (↑S : Set W)) ⟨z, hzS⟩ pS hfreeS hpS
        (by simp [Fintype.card_coe])
      rw [show pS.length = q.length by exact length_induce_eq q hqS] at hIS
      have hcyclesC := hcycles (↑(Sᶜ) : Set W)
        (H.induce (↑(Sᶜ) : Set W))
        (SimpleGraph.Embedding.induce (G := H) _)
      have hEC := Erdos767Dirac.erdosGallai_cycle
        (H.induce (↑(Sᶜ) : Set W)) q.length (by omega) hcyclesC
      rw [card_setCoe_finset (Sᶜ)] at hEC
      have hedge := card_edgeFinset_eq_add_induce_component H z
      rw [hedge]
      exact cyclic_disconnected_arithmetic
        (n := n) (nL := S.card) (nR := Sᶜ.card)
        (c := q.length) (a := k + 1)
        (by rw [Finset.card_compl, hn]; omega)
        (by
          rw [← length_induce_eq q hqS]
          have ht := isCycle_length_le_card hpS.1
          rw [card_setCoe_finset S] at ht
          exact ht)
        (Finset.card_pos.mpr ⟨y, hySc⟩) hIS hEC

/-- Jiang's base case follows from the division-free form of Bondy's
longest-cycle external-edge estimate. -/
lemma jiang_base_of_bondy
    (hbondy : ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (z : V) (c : G.Walk z z), c.IsCycle →
        (∀ (w : V) (d : G.Walk w w), d.IsCycle → d.length ≤ c.length) →
        2 * (cycleOutsideEdges G c.support.toFinset).card ≤
          c.length * (Fintype.card V - c.length))
    (k : ℕ) (hk : 0 < k)
    (V : Type u) [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 3 * (k + 1))
    (hG : AvoidsCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤ 2 * (k + 1) ^ 2 := by
  classical
  by_cases hacyc : G.IsAcyclic
  · let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hforest := card_edgeFinset_le_card_sub_one_of_isAcyclic G hacyc
    rw [hcard] at hforest
    have hthree : 3 ≤ 2 * (k + 1) := by omega
    have hmul : 3 * (k + 1) ≤ 2 * (k + 1) ^ 2 := by
      calc
        3 * (k + 1) ≤ (2 * (k + 1)) * (k + 1) :=
          Nat.mul_le_mul_right (k + 1) hthree
        _ = 2 * (k + 1) ^ 2 := by ring
    omega
  · have hex : ∃ (z : V) (c : G.Walk z z), c.IsCycle := by
      simp only [SimpleGraph.IsAcyclic] at hacyc
      push Not at hacyc
      obtain ⟨z, c, hc⟩ := hacyc
      exact ⟨z, c, hc⟩
    obtain ⟨z₀, c₀, hc₀⟩ := hex
    have hnonempty : (Erdos767LongestCycle.cycleLengths G).Nonempty := by
      exact ⟨c₀.length,
        Erdos767LongestCycle.mem_cycleLengths_iff.mpr ⟨z₀, c₀, hc₀, rfl⟩⟩
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image
      (Erdos767LongestCycle.cycleLengths G) id hnonempty
    obtain ⟨z, c, hc, hcm⟩ :=
      Erdos767LongestCycle.mem_cycleLengths_iff.mp hm
    subst m
    have hlong : ∀ (w : V) (d : G.Walk w w),
        d.IsCycle → d.length ≤ c.length := by
      intro w d hd
      have hdmem := Erdos767LongestCycle.mem_cycleLengths_iff.mpr
        ⟨w, d, hd, rfl⟩
      simpa using hmax d.length hdmem
    have hin := two_mul_card_cycleInsideEdges_le hG hc
    have hout := hbondy V G z c hc hlong
    have hpartition := card_inside_add_outside G c.support.toFinset
    have hclen := Erdos767LongestCycle.isCycle_length_le_card hc
    rw [hcard] at hout hclen
    have hsum : c.length + ((k + 1) + (3 * (k + 1) - c.length)) =
        4 * (k + 1) := by omega
    have hamgm := four_mul_le_sq_add c.length
      ((k + 1) + (3 * (k + 1) - c.length))
    rw [hsum] at hamgm
    have hquad : c.length * ((k + 1) + (3 * (k + 1) - c.length)) ≤
        4 * (k + 1) ^ 2 := by
      nlinarith
    have htwo : 2 * G.edgeFinset.card ≤ 4 * (k + 1) ^ 2 := by
      calc
        2 * G.edgeFinset.card =
            2 * (cycleInsideEdges G c.support.toFinset).card +
              2 * (cycleOutsideEdges G c.support.toFinset).card := by omega
        _ ≤ (k + 1) * c.length +
              c.length * (3 * (k + 1) - c.length) := Nat.add_le_add hin hout
        _ = c.length * ((k + 1) + (3 * (k + 1) - c.length)) := by ring
        _ ≤ 4 * (k + 1) ^ 2 := hquad
    omega

/-- Jiang's sharp estimate at the threshold order `3 * (k + 1)`. -/
lemma jiang_base
    (k : ℕ) (hk : 0 < k)
    (V : Type u) [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 3 * (k + 1))
    (hG : AvoidsCycleWithKIncidentChords k G) :
    G.edgeFinset.card ≤ 2 * (k + 1) ^ 2 := by
  classical
  by_cases hacyc : G.IsAcyclic
  · let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hforest := card_edgeFinset_le_card_sub_one_of_isAcyclic G hacyc
    rw [hcard] at hforest
    have hthree : 3 ≤ 2 * (k + 1) := by omega
    have hmul : 3 * (k + 1) ≤ 2 * (k + 1) ^ 2 := by
      calc
        3 * (k + 1) ≤ (2 * (k + 1)) * (k + 1) :=
          Nat.mul_le_mul_right (k + 1) hthree
        _ = 2 * (k + 1) ^ 2 := by ring
    omega
  · have hex : ∃ (z : V) (c : G.Walk z z), c.IsCycle := by
      simp only [SimpleGraph.IsAcyclic] at hacyc
      push Not at hacyc
      obtain ⟨z, c, hc⟩ := hacyc
      exact ⟨z, c, hc⟩
    obtain ⟨z₀, c₀, hc₀⟩ := hex
    have hnonempty : (Erdos767LongestCycle.cycleLengths G).Nonempty := by
      exact ⟨c₀.length,
        Erdos767LongestCycle.mem_cycleLengths_iff.mpr ⟨z₀, c₀, hc₀, rfl⟩⟩
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image
      (Erdos767LongestCycle.cycleLengths G) id hnonempty
    obtain ⟨z, c, hc, hcm⟩ :=
      Erdos767LongestCycle.mem_cycleLengths_iff.mp hm
    subst m
    have hlong : ∀ (w : V) (d : G.Walk w w),
        d.IsCycle → d.length ≤ c.length := by
      intro w d hd
      have hdmem := Erdos767LongestCycle.mem_cycleLengths_iff.mpr
        ⟨w, d, hd, rfl⟩
      simpa using hmax d.length hdmem
    have hbound := cyclic_free_edge_bound k V G z c hG ⟨hc, hlong⟩
    have hclen := Erdos767LongestCycle.isCycle_length_le_card hc
    rw [hcard] at hbound hclen
    have hsum : c.length + ((k + 1) + (3 * (k + 1) - c.length)) =
        4 * (k + 1) := by omega
    have hamgm := four_mul_le_sq_add c.length
      ((k + 1) + (3 * (k + 1) - c.length))
    rw [hsum] at hamgm
    have hquad : c.length * ((k + 1) + (3 * (k + 1) - c.length)) ≤
        4 * (k + 1) ^ 2 := by
      nlinarith
    have htwo : 2 * G.edgeFinset.card ≤ 4 * (k + 1) ^ 2 := by
      calc
        2 * G.edgeFinset.card ≤ (k + 1) * c.length +
            c.length * (3 * (k + 1) - c.length) := hbound
        _ = c.length * ((k + 1) + (3 * (k + 1) - c.length)) := by ring
        _ ≤ 4 * (k + 1) ^ 2 := hquad
    omega

/-- Resolution of Erdős Problem 767: for positive `k` and
`n ≥ 3 * k + 3`, the complete-bipartite construction is extremal. -/
theorem erdos_767 (k n : ℕ) (hk : 0 < k) (hn : 3 * k + 3 ≤ n) :
    chordCycleExtremalNumber k n =
      (k + 1) * n - (k + 1) ^ 2 := by
  apply Nat.le_antisymm
  · obtain ⟨G, hG, hGcard⟩ := exists_extremizer k n
    rw [← hGcard]
    simpa using edge_count_le_of_base k
      (fun W _ _ H _ ↦ jiang_base k hk W H) (Fin n) G
      (by
        rw [Fintype.card_fin]
        omega) hG
  · exact lower_bound k n (by omega)

#print axioms Erdos767.erdos_767

end

end Erdos767
-- END Erdos767

def BondyHasCycleWithKIncidentChords {V : Type u} (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.edges.Nodup ∧ c.support.dropLast.Nodup ∧
    3 ≤ c.length ∧ ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

def BondyHasCycle {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.edges.Nodup ∧ c.support.dropLast.Nodup ∧ 3 ≤ c.length

lemma bondy_cycle_edge_bound_flat {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (h_avoid : ¬BondyHasCycleWithKIncidentChords k G)
    (h_cycle : BondyHasCycle G) :
    ∃ c : ℕ, c ≤ Fintype.card V ∧
      2 * G.edgeFinset.card ≤ c * (Fintype.card V - c) + c * (k + 1) := by
  classical
  let havoid' : ¬Erdos767.HasCycleWithKIncidentChords k G := by
    intro h
    rcases h with ⟨v, c, hc, f, hf, hch⟩
    apply h_avoid
    exact ⟨v, c, hc.edges_nodup, by
      exact (c.tail_support_perm_dropLast_support.nodup_iff).mp hc.support_nodup,
      hc.three_le_length, f, hf, hch⟩
  rcases h_cycle with ⟨v, c, he, hs, hl⟩
  have hc : c.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    have hn : ¬c.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      omega
    refine ⟨⟨?_, ?_⟩, hl⟩
    · rw [SimpleGraph.Walk.isTrail_def]
      simpa only [SimpleGraph.Walk.edges_tail] using he.tail
    · rw [c.support_tail_of_not_nil hn]
      exact (c.tail_support_perm_dropLast_support.nodup_iff).mpr hs
  letI : Nonempty V := ⟨v⟩
  have hnonempty : (Erdos767LongestCycle.cycleLengths G).Nonempty := by
    exact ⟨c.length, Erdos767LongestCycle.mem_cycleLengths_iff.mpr ⟨v, c, hc, rfl⟩⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image
    (Erdos767LongestCycle.cycleLengths G) id hnonempty
  obtain ⟨z, q, hq, hqm⟩ := Erdos767LongestCycle.mem_cycleLengths_iff.mp hm
  subst m
  have hlong : ∀ (w : V) (r : G.Walk w w), r.IsCycle → r.length ≤ q.length := by
    intro w r hr
    exact hmax r.length (Erdos767LongestCycle.mem_cycleLengths_iff.mpr ⟨w, r, hr, rfl⟩)
  have hbound := Erdos767.cyclic_free_edge_bound k V G z q havoid' ⟨hq, hlong⟩
  refine ⟨q.length, Erdos767LongestCycle.isCycle_length_le_card hq, ?_⟩
  have hbound' := hbound
  have hcard : Fintype.card G.edgeSet = G.edgeFinset.card := SimpleGraph.card_edgeSet
  simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbound

end JiangBaseCase

end JSP000628
