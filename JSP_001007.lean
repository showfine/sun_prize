import Mathlib.Tactic
-- Modular import: Mathlib propagates transitive dependencies, so this suffices.

open Finset

/-- Sieve counterexample configuration: 1000 consecutive strictly increasing odd primes
together with derived quantities (M, D, K, L) satisfying the paper's structural bounds. -/
structure SieveCounterexampleConfig where
  N : ℕ
  p : Fin 1000 → ℕ
  p_prime : ∀ i, (p i).Prime
  p_pos : ∀ i, 0 < p i
  p_odd : ∀ i, 2 < p i
  p_strict_mono : StrictMono p
  hp_le_max : ∀ i, p i ≤ p ⟨999, by decide⟩
  hp_ge_min : ∀ i, p ⟨0, by decide⟩ ≤ p i
  D : ℕ
  hD : p ⟨999, by decide⟩ - p ⟨0, by decide⟩ = D
  K : ℕ
  hK : K = N / (p ⟨0, by decide⟩)
  L : ℕ
  hL_pos : 0 < L
  hL_le : L ≤ p ⟨0, by decide⟩
  h_r_bound : L + K * D ≤ (p ⟨0, by decide⟩ + 1) / 2
  hKD : K * D ≤ (p ⟨0, by decide⟩) / 6
  hL_lower : (p ⟨0, by decide⟩) / 3 ≤ L
  hM_upper : (p ⟨0, by decide⟩) * 2 ≤ N

namespace SieveCounterexample

instance (cfg : SieveCounterexampleConfig) (i : Fin 1000) : NeZero (cfg.p i) :=
  ⟨Nat.ne_of_gt (cfg.p_pos i)⟩

/-- Reference modulus `M := p 0`, the smallest of the 1000 primes. -/
def M (cfg : SieveCounterexampleConfig) : ℕ := cfg.p ⟨0, by decide⟩

/-- Offset of the `i`-th prime relative to `M`: `d_i = p_i - M`. -/
def d (cfg : SieveCounterexampleConfig) (i : Fin 1000) : ℕ :=
  cfg.p i - M cfg

/-- Allowed residue classes modulo `p_i`:
`A_i = { -K*D + r (mod p_i) | 1 ≤ r ≤ (p_i + 1)/2 }`. -/
def allowedSet (cfg : SieveCounterexampleConfig) (i : Fin 1000) : Finset (ZMod (cfg.p i)) :=
  let half := (cfg.p i + 1) / 2
  (Finset.Icc 1 half).image fun (r : ℕ) =>
    -(cfg.K * cfg.D : ZMod (cfg.p i)) + (r : ZMod (cfg.p i))

/-- Forbidden (sieved-out) residue classes modulo `p_i`: `B_i = ZMod(p_i) \ A_i`. -/
def forbiddenSet (cfg : SieveCounterexampleConfig) (i : Fin 1000) : Finset (ZMod (cfg.p i)) :=
  Finset.univ \ (allowedSet cfg i)

/-- Exactly half of the residues modulo `p_i` are forbidden, i.e. `|B_i| = p_i / 2`. -/
theorem card_forbiddenSet (cfg : SieveCounterexampleConfig) (i : Fin 1000) :
    (forbiddenSet cfg i).card = cfg.p i / 2 := by
  rw [forbiddenSet]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have h_univ : (Finset.univ : Finset (ZMod (cfg.p i))).card = cfg.p i := by
    rw [Finset.card_univ, ZMod.card]
  have h_allowed : (allowedSet cfg i).card = (cfg.p i + 1) / 2 := by
    rw [allowedSet]
    rw [Finset.card_image_of_injOn]
    · simp
    · intro x hx y hy heq
      -- Strip the Set coercion `↑` and unfold the Icc interval.
      simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
      -- Expose the addition by stripping the anonymous lambda from the equation.
      dsimp only at heq
      -- Inject the reverse constant via ring to cancel the shared offset.
      have heq_zmod : (x : ZMod (cfg.p i)) = (y : ZMod (cfg.p i)) := by
        calc (x : ZMod (cfg.p i))
            = (cfg.K * cfg.D : ZMod (cfg.p i))
              + (-(cfg.K * cfg.D : ZMod (cfg.p i)) + (x : ZMod (cfg.p i))) := by ring
          _ = (cfg.K * cfg.D : ZMod (cfg.p i))
              + (-(cfg.K * cfg.D : ZMod (cfg.p i)) + (y : ZMod (cfg.p i))) := by rw [heq]
          _ = (y : ZMod (cfg.p i)) := by ring
      -- Lift the equality to natural numbers via ZMod.val.
      have heq_val := congrArg ZMod.val heq_zmod
      simp only [ZMod.val_natCast] at heq_val
      have hxp : x % cfg.p i = x := Nat.mod_eq_of_lt (by have := cfg.p_odd i; omega)
      have hyp : y % cfg.p i = y := Nat.mod_eq_of_lt (by have := cfg.p_odd i; omega)
      rw [hxp, hyp] at heq_val
      exact heq_val
  rw [h_univ, h_allowed]
  omega

/-- Candidate set `T = ⋃ k ∈ [0,K) { k*M + t | t ∈ [1, L] }`,
i.e. K equilong subintervals concatenated together. -/
def T (cfg : SieveCounterexampleConfig) : Finset ℕ :=
  (Finset.Ico 0 cfg.K).biUnion fun k =>
    (Finset.Icc 1 cfg.L).image fun t =>
      k * M cfg + t

/-- Every element of `T` lies inside the candidate window `[1, N]`. -/
theorem T_subset_interval (cfg : SieveCounterexampleConfig) :
    ∀ n ∈ T cfg, 1 ≤ n ∧ n ≤ cfg.N := by
  intro n hn
  simp only [T, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image, Finset.mem_Icc] at hn
  rcases hn with ⟨k, ⟨hk_zero, hk_lt_K⟩, t, ⟨ht_one, ht_le_L⟩, rfl⟩
  constructor
  · omega
  · have hM : M cfg = cfg.p ⟨0, by decide⟩ := rfl
    have hL_bound : cfg.L ≤ M cfg := by
      rw [hM]; exact cfg.hL_le
    have h_div : cfg.K * M cfg ≤ cfg.N := by
      rw [cfg.hK, hM]
      exact Nat.div_mul_le_self cfg.N (cfg.p ⟨0, by decide⟩)
    calc k * M cfg + t ≤ k * M cfg + cfg.L := Nat.add_le_add_left ht_le_L (k * M cfg)
      _ ≤ k * M cfg + M cfg := Nat.add_le_add_left hL_bound (k * M cfg)
      _ = (k + 1) * M cfg := by ring
      _ ≤ cfg.K * M cfg := Nat.mul_le_mul_right (M cfg) hk_lt_K
      _ ≤ cfg.N := h_div

/-- Central drift lemma: every element of `T` lands in the allowed class `A_i`
modulo `p_i`. The witness `r = t + K*D - k*d_i` is the preimage that demonstrates it. -/
theorem T_mod_in_allowed (cfg : SieveCounterexampleConfig) (n : ℕ) (hn : n ∈ T cfg) (i : Fin 1000) :
    (n : ZMod (cfg.p i)) ∈ allowedSet cfg i := by
  simp only [T, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image, Finset.mem_Icc] at hn
  rcases hn with ⟨k, ⟨hk_zero, hk_lt_K⟩, t, ⟨ht_one, ht_le_L⟩, rfl⟩
  have hd_le : d cfg i ≤ cfg.D := by
    have h1 := cfg.hp_le_max i
    have h2 := cfg.hD
    have hM : M cfg = cfg.p ⟨0, by decide⟩ := rfl
    have hd_def : d cfg i = cfg.p i - M cfg := rfl
    omega
  have hkd_le : k * d cfg i ≤ cfg.K * cfg.D :=
    Nat.mul_le_mul (le_of_lt hk_lt_K) hd_le
  -- Key construction: r = t + K*D - k*d_i; this lies in [1, (p_i+1)/2]
  -- and satisfies k*M + t ≡ -K*D + r (mod p_i).
  let r : ℕ := t + cfg.K * cfg.D - k * d cfg i
  rw [allowedSet, Finset.mem_image]
  use r
  constructor
  · rw [Finset.mem_Icc]
    constructor
    · omega
    · have hr_bound := cfg.h_r_bound
      have hp_min := cfg.hp_ge_min i
      omega
  · have h_pi_eq : cfg.p i = M cfg + d cfg i := by
      have hp_min := cfg.hp_ge_min i
      have hd_def : d cfg i = cfg.p i - M cfg := rfl
      have hM : M cfg = cfg.p ⟨0, by decide⟩ := rfl
      omega
    -- Modulo p_i: M ≡ -d_i, since p_i = M + d_i.
    have h_M_eq_neg_d : (M cfg : ZMod (cfg.p i)) = - (d cfg i : ZMod (cfg.p i)) := by
      apply eq_neg_of_add_eq_zero_left
      calc (M cfg : ZMod (cfg.p i)) + (d cfg i : ZMod (cfg.p i))
        _ = ↑(M cfg + d cfg i) := by push_cast; rfl
        _ = ↑(cfg.p i) := by rw [← h_pi_eq]
        _ = 0 := by simp
    have hr_val : (r : ZMod (cfg.p i))
        = (t : ZMod (cfg.p i))
          + (cfg.K * cfg.D : ZMod (cfg.p i))
          - (k * d cfg i : ZMod (cfg.p i)) := by
      have h_sub : k * d cfg i ≤ t + cfg.K * cfg.D := by omega
      rw [show r = t + cfg.K * cfg.D - k * d cfg i from rfl]
      rw [Nat.cast_sub h_sub]
      push_cast
      rfl
    -- Final algebraic collapse: k*M + t = (k*M + t + K*D) - K*D ≡ r - K*D
    -- and the witness r satisfies the allowed-class representation.
    push_cast
    rw [hr_val, h_M_eq_neg_d]
    ring

/-- Sieved set: integers in `[1, N]` that survive every prime's forbidden residues. -/
def S (cfg : SieveCounterexampleConfig) : Finset ℕ :=
  (Finset.Icc 1 cfg.N).filter fun n => ∀ i : Fin 1000, (n : ZMod (cfg.p i)) ∉ forbiddenSet cfg i

/-- Every candidate in `T` survives the sieve, so `T ⊆ S`. -/
theorem T_subset_S (cfg : SieveCounterexampleConfig) : T cfg ⊆ S cfg := by
  intro n hn
  rw [S, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rcases T_subset_interval cfg n hn with ⟨h1, h2⟩
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  · intro i
    have h_allowed := T_mod_in_allowed cfg n hn i
    rw [forbiddenSet, Finset.mem_sdiff]
    intro h_contra
    exact h_contra.2 h_allowed

/-- `|T| = K * L`: each of the K disjoint slabs contributes exactly L elements. -/
theorem card_T (cfg : SieveCounterexampleConfig) :
    (T cfg).card = cfg.K * cfg.L := by
  rw [T, Finset.card_biUnion]
  · -- Part one: every slab has cardinality exactly L.
    have h_card_eq : ∀ k ∈ Finset.Ico 0 cfg.K, (Finset.image (fun t => k * M cfg + t)
    (Finset.Icc 1 cfg.L)).card = cfg.L := by
      intro k _hk
      rw [Finset.card_image_of_injective]
      · simp
      · intro x y heq
        exact Nat.add_left_cancel heq
    rw [Finset.sum_congr rfl h_card_eq]
    simp
  · -- Part two: distinct slabs are pairwise disjoint.
    intro k1 _hk1 k2 _hk2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    rcases hx1 with ⟨t1, ht1, rfl⟩
    rcases hx2 with ⟨t2, ht2, heq⟩
    rw [Finset.mem_Icc] at ht1 ht2
    have hM : M cfg = cfg.p ⟨0, by decide⟩ := rfl
    have hL_bound : cfg.L ≤ M cfg := by rw [hM]; exact cfg.hL_le
    rcases lt_or_gt_of_ne hne with hk | hk
    · -- Case 1: k1 < k2
      have h1 : t1 ≤ M cfg := le_trans ht1.2 hL_bound
      have h2 : k1 * M cfg + t1 ≤ k1 * M cfg + M cfg := Nat.add_le_add_left h1 _
      have h3 : k1 * M cfg + M cfg = (k1 + 1) * M cfg := by ring
      have h4 : (k1 + 1) * M cfg ≤ k2 * M cfg := Nat.mul_le_mul_right (M cfg) hk
      have h5 : k2 * M cfg < k2 * M cfg + t2 := Nat.lt_add_of_pos_right ht2.1
      have contra : k1 * M cfg + t1 < k2 * M cfg + t2 := by
        calc k1 * M cfg + t1
          _ ≤ k1 * M cfg + M cfg := h2
          _ = (k1 + 1) * M cfg := h3
          _ ≤ k2 * M cfg := h4
          _ < k2 * M cfg + t2 := h5
      exact Nat.ne_of_lt contra heq.symm
    · -- Case 2: k2 < k1 (symmetric to case 1)
      have h1 : t2 ≤ M cfg := le_trans ht2.2 hL_bound
      have h2 : k2 * M cfg + t2 ≤ k2 * M cfg + M cfg := Nat.add_le_add_left h1 _
      have h3 : k2 * M cfg + M cfg = (k2 + 1) * M cfg := by ring
      have h4 : (k2 + 1) * M cfg ≤ k1 * M cfg := Nat.mul_le_mul_right (M cfg) hk
      have h5 : k1 * M cfg < k1 * M cfg + t1 := Nat.lt_add_of_pos_right ht1.1
      have contra : k2 * M cfg + t2 < k1 * M cfg + t1 := by
        calc k2 * M cfg + t2
          _ ≤ k2 * M cfg + M cfg := h2
          _ = (k2 + 1) * M cfg := h3
          _ ≤ k1 * M cfg := h4
          _ < k1 * M cfg + t1 := h5
      exact Nat.ne_of_lt contra heq

/-- Final sieve bound: `|S| > N / 10`, refuting any density bound of the form
`|S| ≤ N/10` and thus supplying the desired counterexample. -/
theorem counterexample_size_bound (cfg : SieveCounterexampleConfig) :
    (S cfg).card > cfg.N / 10 := by
  have h1 : (T cfg).card ≤ (S cfg).card := Finset.card_le_card (T_subset_S cfg)
  have h2 : (T cfg).card = cfg.K * cfg.L := card_T cfg
  have hM_pos : 0 < M cfg := cfg.p_pos ⟨0, by decide⟩
  have hM_eq : M cfg = cfg.p ⟨0, by decide⟩ := rfl
  have hK_eq : cfg.K = cfg.N / M cfg := by rw [cfg.hK, hM_eq]
  -- Step 1: N < K*M + M (Euclidean division, remainder bounded by M-1).
  have step1 : cfg.N < cfg.K * M cfg + M cfg := by
    have h_div : cfg.N = cfg.K * M cfg + cfg.N % M cfg := by
      have h := Nat.div_add_mod cfg.N (M cfg)
      rw [← hK_eq] at h
      calc cfg.N = M cfg * cfg.K + cfg.N % M cfg := h.symm
        _ = cfg.K * M cfg + cfg.N % M cfg := by ring
    have h_mod := Nat.mod_lt cfg.N hM_pos
    calc cfg.N = cfg.K * M cfg + cfg.N % M cfg := h_div
      _ < cfg.K * M cfg + M cfg := Nat.add_lt_add_left h_mod (cfg.K * M cfg)
  -- Step 2: M ≤ 3L + 2, the linear bound derived from M/3 ≤ L.
  have step2 : M cfg ≤ 3 * cfg.L + 2 := by
    have h_mod := Nat.mod_lt (M cfg) (by decide : 0 < 3)
    have h_div := Nat.div_add_mod (M cfg) 3
    have h_lower := cfg.hL_lower
    rw [← hM_eq] at h_lower
    omega
  -- Step 3: combine to obtain N < (K+1)(3L+2).
  have step3 : cfg.N < (cfg.K + 1) * (3 * cfg.L + 2) := by
    calc cfg.N < cfg.K * M cfg + M cfg := step1
      _ = (cfg.K + 1) * M cfg := by ring
      _ ≤ (cfg.K + 1) * (3 * cfg.L + 2) := Nat.mul_le_mul_left (cfg.K + 1) step2
  -- hK2: prove K ≥ 2 by contradiction; omega cannot handle the division bound directly.
  have hK2 : 2 ≤ cfg.K := by
    by_contra! h_contra
    have hK_le_1 : cfg.K ≤ 1 := by omega
    have h_div : cfg.N = cfg.K * M cfg + cfg.N % M cfg := by
      have h := Nat.div_add_mod cfg.N (M cfg)
      rw [← hK_eq] at h
      calc cfg.N = M cfg * cfg.K + cfg.N % M cfg := h.symm
        _ = cfg.K * M cfg + cfg.N % M cfg := by ring
    have h_mod := Nat.mod_lt cfg.N hM_pos
    have h_upper : 2 * M cfg ≤ cfg.N := by
      have h := cfg.hM_upper
      rw [← hM_eq] at h
      omega
    have h_contradiction : cfg.N < 2 * M cfg := by
      calc cfg.N = cfg.K * M cfg + cfg.N % M cfg := h_div
        _ ≤ 1 * M cfg + cfg.N % M cfg := Nat.add_le_add_right (Nat.mul_le_mul_right
        (M cfg) hK_le_1) _
        _ = M cfg + cfg.N % M cfg := by ring
        _ < M cfg + M cfg := Nat.add_lt_add_left h_mod (M cfg)
        _ = 2 * M cfg := by ring
    omega
  have hL1 : 1 ≤ cfg.L := cfg.hL_pos
  -- Helper bounds used to linearise the nonlinear term K*L before the final omega.
  have H1 : cfg.K ≤ cfg.K * cfg.L := by
    calc cfg.K = cfg.K * 1 := by ring
      _ ≤ cfg.K * cfg.L := Nat.mul_le_mul_left cfg.K hL1
  have H2 : cfg.L ≤ cfg.K * cfg.L := by
    calc cfg.L = 1 * cfg.L := by ring
      _ ≤ cfg.K * cfg.L := Nat.mul_le_mul_right cfg.L (by omega)
  have H3 : 1 ≤ cfg.K * cfg.L := by
    calc 1 = 1 * 1 := by ring
      _ ≤ cfg.K * 1 := Nat.mul_le_mul_right 1 (by omega)
      _ ≤ cfg.K * cfg.L := Nat.mul_le_mul_left cfg.K hL1
  -- Expand (K+1)(3L+2) into a sum that omega can dispatch together with the lower bounds.
  have step3_expanded : cfg.N < 3 * (cfg.K * cfg.L) + 2 * cfg.K + 3 * cfg.L + 2 := by
    calc cfg.N < (cfg.K + 1) * (3 * cfg.L + 2) := step3
      _ = 3 * (cfg.K * cfg.L) + 2 * cfg.K + 3 * cfg.L + 2 := by ring
  omega

end SieveCounterexample
