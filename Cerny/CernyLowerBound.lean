import Cerny.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Optimality of the Černý Automaton `C_n`: `rt(C_n) = (n - 1)^2`

This module defines the Černý automaton `cernyAut n hn` on `Fin n` (`2 ≤ n`)
and proves:
1. Uniqueness and preimage closure of cyclic intervals `cycInt n x k`.
2. A 1-Lipschitz potential `Phi` on cyclic intervals.
3. `cerny_lower_bound`: every synchronizing word of `cernyAut n hn` has length `≥ (n - 1)^2`.
4. `cerny_upper_bound`: an explicit synchronizing word of length `(n - 1)^2`.
-/

namespace CernyLowerBound

/-- The Černý automaton `C_n` on `Fin n` (`2 ≤ n`) with `false = a` (cyclic shift)
and `true = b` (maps `n - 1` to `0`, fixes all other states). -/
def cernyAut (n : ℕ) (hn : 2 ≤ n) : Aut (Fin n) Bool where
  step q σ :=
    match σ with
    | false => ⟨(q.1 + 1) % n, Nat.mod_lt _ (by omega)⟩
    | true => if q.1 = n - 1 then ⟨0, by omega⟩ else q

/-- Cyclic interval `{x, x+1, ..., x+k-1} mod n` in `Fin n`. -/
def cycInt (n : ℕ) (hn : 0 < n) (x k : ℕ) : Finset (Fin n) :=
  (Finset.range k).image (fun j => ⟨(x + j) % n, Nat.mod_lt _ hn⟩)

private lemma hn_pos {n : ℕ} (hn : 2 ≤ n) : 0 < n := by omega

section CycIntProps
variable {n : ℕ} (hn : 2 ≤ n)
include hn

lemma mem_cycInt_iff {x k : ℕ} (hx : x < n) (hk : k ≤ n) (q : Fin n) :
    q ∈ cycInt n (hn_pos hn) x k ↔ (q.1 + n - x) % n < k := by
  simp only [cycInt, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hq⟩
    have hq1 : q.1 = (x + j) % n := by rw [← hq]
    rw [hq1]
    have hjk : j < n := lt_of_lt_of_le hj hk
    have hmod : ((x + j) % n + n - x) % n = j := by
      by_cases h : x + j < n
      · rw [Nat.mod_eq_of_lt h]
        have : x + j + n - x = j + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hjk]
      · have hge : n ≤ x + j := by omega
        have hlt : x + j - n < n := by omega
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
        have : x + j - n + n - x = j := by omega
        rw [this, Nat.mod_eq_of_lt hjk]
    rw [hmod]
    exact hj
  · intro hlt
    let j := (q.1 + n - x) % n
    refine ⟨j, hlt, Fin.ext ?_⟩
    dsimp only [j]
    by_cases h : x ≤ q.1
    · have h1 : q.1 + n - x = (q.1 - x) + n := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : q.1 - x < n)]
      have h2 : x + (q.1 - x) = q.1 := by omega
      rw [h2, Nat.mod_eq_of_lt q.2]
    · have h1 : q.1 + n - x < n := by omega
      rw [Nat.mod_eq_of_lt h1]
      have h2 : x + (q.1 + n - x) = q.1 + n := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt q.2]

lemma card_cycInt {x k : ℕ} (hk : k ≤ n) :
    (cycInt n (hn_pos hn) x k).card = k := by
  rw [cycInt, Finset.card_image_of_injOn]
  · exact Finset.card_range k
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    have hval := congrArg Fin.val hab
    dsimp only at hval
    have h1 : (x + a) % n = (x + b) % n := hval
    have ha' : a < n := lt_of_lt_of_le ha hk
    have hb' : b < n := lt_of_lt_of_le hb hk
    have hsub : ((x + a) % n + n - x % n) % n = a := by
      have : (x + a) % n = (x % n + a) % n := (Nat.mod_add_mod x n a).symm
      rw [this]
      by_cases h : x % n + a < n
      · rw [Nat.mod_eq_of_lt h]
        have heq : x % n + a + n - x % n = a + n := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt ha']
      · have hge : n ≤ x % n + a := by omega
        have hlt : x % n + a - n < n := by have := Nat.mod_lt x (hn_pos hn); omega
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
        have heq : x % n + a - n + n - x % n = a := by omega
        rw [heq, Nat.mod_eq_of_lt ha']
    have hsub2 : ((x + b) % n + n - x % n) % n = b := by
      have : (x + b) % n = (x % n + b) % n := (Nat.mod_add_mod x n b).symm
      rw [this]
      by_cases h : x % n + b < n
      · rw [Nat.mod_eq_of_lt h]
        have heq : x % n + b + n - x % n = b + n := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hb']
      · have hge : n ≤ x % n + b := by omega
        have hlt : x % n + b - n < n := by have := Nat.mod_lt x (hn_pos hn); omega
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
        have heq : x % n + b - n + n - x % n = b := by omega
        rw [heq, Nat.mod_eq_of_lt hb']
    rw [← hsub, h1, hsub2]

lemma cycInt_univ (x : ℕ) : cycInt n (hn_pos hn) x n = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [card_cycInt hn le_rfl, Fintype.card_fin]

lemma cycInt_one (q : Fin n) : cycInt n (hn_pos hn) q.1 1 = {q} := by
  ext p
  simp [cycInt, Fin.ext_iff, Nat.mod_eq_of_lt q.2, eq_comm]

/-- Uniqueness of the left endpoint of a proper nonempty cyclic interval. -/
lemma cycInt_left_unique {x k : ℕ} (hx : x < n) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1)
    {q : Fin n} (hq : q ∈ cycInt n (hn_pos hn) x k)
    (hprev : (⟨(q.1 + n - 1) % n, Nat.mod_lt _ (hn_pos hn)⟩ : Fin n) ∉
      cycInt n (hn_pos hn) x k) :
    q.1 = x := by
  rw [mem_cycInt_iff hn hx (by omega) q] at hq
  rw [mem_cycInt_iff hn hx (by omega)] at hprev
  dsimp only at hprev
  by_contra hne
  have h1 : (q.1 + n - x) % n ≠ 0 := by
    intro h0
    have hq' : q.1 = x := by
      by_cases h : x ≤ q.1
      · have heq : q.1 + n - x = (q.1 - x) + n := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : q.1 - x < n)] at h0
        omega
      · have hlt : q.1 + n - x < n := by omega
        rw [Nat.mod_eq_of_lt hlt] at h0
        omega
    exact hne hq'
  have hpos : 1 ≤ (q.1 + n - x) % n := by omega
  have hlt_k : ((q.1 + n - 1) % n + n - x) % n < k := by
    have hmod_prev : ((q.1 + n - 1) % n + n - x) % n = (q.1 + n - x) % n - 1 := by
      by_cases hq0 : q.1 = 0
      · have hx_pos : 1 ≤ x := by omega
        have hlt_nx : n - x < n := by omega
        have hlt_nx1 : n - x - 1 < n := by omega
        rw [hq0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n), Nat.mod_eq_of_lt hlt_nx]
        have h2' : (n - 1 + n - x) % n = n - x - 1 := by
          have : n - 1 + n - x = (n - x - 1) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hlt_nx1]
        rw [h2']
      · have hq_pos : 1 ≤ q.1 := by omega
        have h1' : (q.1 + n - 1) % n = q.1 - 1 := by
          have : q.1 + n - 1 = (q.1 - 1) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1']
        by_cases hxq : x < q.1
        · have ha : q.1 - 1 + n - x = (q.1 - 1 - x) + n := by omega
          have hb : q.1 + n - x = (q.1 - x) + n := by omega
          rw [ha, hb, Nat.add_mod_right, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        · have hqx : q.1 ≤ x := by omega
          have ha : q.1 - 1 + n - x < n := by omega
          have hb : q.1 + n - x < n := by omega
          rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
          omega
    rw [hmod_prev]
    omega
  exact hprev hlt_k

lemma cycInt_inj {x y k k' : ℕ} (hx : x < n) (hy : y < n)
    (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) (hk'1 : 1 ≤ k') (hk'n : k' ≤ n - 1)
    (heq : cycInt n (hn_pos hn) x k = cycInt n (hn_pos hn) y k') :
    x = y ∧ k = k' := by
  have hk_eq : k = k' := by
    have := congrArg Finset.card heq
    rw [card_cycInt hn (by omega), card_cycInt hn (by omega)] at this
    exact this
  refine ⟨?_, hk_eq⟩
  have hx_mem : (⟨x, hx⟩ : Fin n) ∈ cycInt n (hn_pos hn) x k := by
    rw [mem_cycInt_iff hn hx (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.mod_self]
    exact hk1
  have hx_prev : (⟨(x + n - 1) % n, Nat.mod_lt _ (hn_pos hn)⟩ : Fin n) ∉
      cycInt n (hn_pos hn) x k := by
    rw [mem_cycInt_iff hn hx (by omega)]
    dsimp only
    have hmod : ((x + n - 1) % n + n - x) % n = n - 1 := by
      by_cases hx0 : x = 0
      · subst hx0
        simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      · have h1 : (x + n - 1) % n = x - 1 := by
          have : x + n - 1 = (x - 1) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1]
        have h2 : x - 1 + n - x = n - 1 := by omega
        rw [h2, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    omega
  rw [heq] at hx_mem hx_prev
  exact cycInt_left_unique hn hy hk'1 hk'n hx_mem hx_prev

/-- Predicate characterizing cyclic intervals (including `∅` and `Finset.univ`). -/
def IsCycInterval (S : Finset (Fin n)) : Prop :=
  S = ∅ ∨ ∃ x < n, ∃ k, 1 ≤ k ∧ k ≤ n ∧ S = cycInt n (hn_pos hn) x k

lemma isCycInterval_singleton (q : Fin n) : IsCycInterval hn {q} := by
  right
  exact ⟨q.1, q.2, 1, le_rfl, by omega, (cycInt_one hn q).symm⟩

lemma isCycInterval_univ : IsCycInterval hn Finset.univ := by
  right
  exact ⟨0, hn_pos hn, n, by omega, le_rfl, (cycInt_univ hn 0).symm⟩

lemma preimage_false_cycInt {x k : ℕ} (hx : x < n) (hk : k ≤ n) :
    (cernyAut n hn).preimage (cycInt n (hn_pos hn) x k) [false] =
      cycInt n (hn_pos hn) ((x + n - 1) % n) k := by
  let x' := (x + n - 1) % n
  have hx' : x' < n := Nat.mod_lt _ (hn_pos hn)
  ext q
  rw [Aut.mem_preimage, mem_cycInt_iff hn hx' hk q, mem_cycInt_iff hn hx hk]
  change (((q.1 + 1) % n + n - x) % n < k) ↔ ((q.1 + n - x') % n < k)
  have hmod : ((q.1 + 1) % n + n - x) % n = (q.1 + n - x') % n := by
    have hL : ((q.1 + 1) % n + n - x) % n = (q.1 + 1 + (n - x)) % n := by
      have : (q.1 + 1) % n + n - x = (q.1 + 1) % n + (n - x) := by omega
      rw [this, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hR : (q.1 + n - x') % n = (q.1 + (n - x')) % n := by
      have : q.1 + n - x' = q.1 + (n - x') := by omega
      rw [this]
    rw [hL, hR]
    by_cases hx0 : x = 0
    · subst hx0
      have hx'_eq : x' = n - 1 := by simp [x', Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      rw [hx'_eq]
      have : n - (n - 1) = 1 := by omega
      rw [this, Nat.sub_zero, Nat.add_mod_right]
    · have hx'_eq : x' = x - 1 := by
        have : x + n - 1 = (x - 1) + n := by omega
        simp [x', this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x - 1 < n)]
      rw [hx'_eq]
      have : n - (x - 1) = 1 + (n - x) := by omega
      rw [this, ← add_assoc]
  rw [hmod]

lemma zero_mem_cycInt_iff {x k : ℕ} (hx : x < n) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    (⟨0, hn_pos hn⟩ : Fin n) ∈ cycInt n (hn_pos hn) x k ↔ x = 0 ∨ n - k < x := by
  rw [mem_cycInt_iff hn hx (by omega)]
  dsimp only
  by_cases hx0 : x = 0
  · subst hx0
    rw [Nat.zero_add, Nat.sub_zero, Nat.mod_self]
    simp only [true_or, iff_true]
    omega
  · have : (0 + n - x) % n = n - x := by
      rw [zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [this]
    omega

lemma last_mem_cycInt_iff {x k : ℕ} (hx : x < n) (hkn : k ≤ n - 1) :
    (⟨n - 1, by omega⟩ : Fin n) ∈ cycInt n (hn_pos hn) x k ↔ n - k ≤ x := by
  rw [mem_cycInt_iff hn hx (by omega)]
  dsimp only
  by_cases hxn : x = n - 1
  · subst hxn
    have : n - 1 + n - (n - 1) = n := by omega
    rw [this, Nat.mod_self]
    omega
  · have h1 : n - 1 + n - x = (n - 1 - x) + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : n - 1 - x < n)]
    omega

lemma preimage_true_cycInt_x0 {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    (cernyAut n hn).preimage (cycInt n (hn_pos hn) 0 k) [true] =
      cycInt n (hn_pos hn) (n - 1) (k + 1) := by
  ext q
  rw [Aut.mem_preimage, mem_cycInt_iff hn (by omega : n - 1 < n) (by omega : k + 1 ≤ n) q]
  change (cernyAut n hn).step q true ∈ cycInt n (hn_pos hn) 0 k ↔ _
  dsimp only [cernyAut]
  split_ifs with hq
  · rw [mem_cycInt_iff hn (hn_pos hn) (by omega)]
    dsimp only
    rw [hq]
    have hL : (0 + n - 0) % n = 0 := by simp
    have hR : (n - 1 + n - (n - 1)) % n = 0 := by
      have : n - 1 + n - (n - 1) = n := by omega
      rw [this, Nat.mod_self]
    rw [hL, hR]
    omega
  · rw [mem_cycInt_iff hn (hn_pos hn) (by omega)]
    have hL : (q.1 + n - 0) % n = q.1 := by simp [Nat.mod_eq_of_lt q.2]
    have hR : (q.1 + n - (n - 1)) % n = q.1 + 1 := by
      have : q.1 + n - (n - 1) = q.1 + 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega : q.1 + 1 < n)]
    rw [hL, hR]
    omega

lemma preimage_true_cycInt_xnk {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    (cernyAut n hn).preimage (cycInt n (hn_pos hn) (n - k) k) [true] =
      if k = 1 then ∅ else cycInt n (hn_pos hn) (n - k) (k - 1) := by
  split_ifs with hk
  · subst hk
    ext q
    simp only [Aut.mem_preimage, Finset.notMem_empty, iff_false]
    rw [mem_cycInt_iff hn (by omega : n - 1 < n) (by omega)]
    simp only [Aut.eval_singleton, cernyAut]
    split_ifs with hq
    · have : (0 + n - (n - 1)) % n = 1 := by
        have h : 0 + n - (n - 1) = 1 := by omega
        rw [h, Nat.mod_eq_of_lt (by omega : 1 < n)]
      rw [this]
      omega
    · have : (q.1 + n - (n - 1)) % n = q.1 + 1 := by
        have h : q.1 + n - (n - 1) = q.1 + 1 := by omega
        rw [h, Nat.mod_eq_of_lt (by omega : q.1 + 1 < n)]
      rw [this]
      omega
  · ext q
    rw [Aut.mem_preimage, mem_cycInt_iff hn (by omega : n - k < n) (by omega)]
    simp only [Aut.eval_singleton, cernyAut]
    split_ifs with hq
    · rw [mem_cycInt_iff hn (by omega : n - k < n) (by omega)]
      dsimp only
      rw [hq]
      have hL : (0 + n - (n - k)) % n = k := by
        have : 0 + n - (n - k) = k := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      have hR : (n - 1 + n - (n - k)) % n = k - 1 := by
        have : n - 1 + n - (n - k) = (k - 1) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hL, hR]
      omega
    · rw [mem_cycInt_iff hn (by omega : n - k < n) (by omega)]
      have hne : q.1 ≠ n - 1 := hq
      by_cases hle : n - k ≤ q.1
      · have h1 : (q.1 + n - (n - k)) % n = q.1 - (n - k) := by
          have : q.1 + n - (n - k) = (q.1 - (n - k)) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1]
        omega
      · have h1 : (q.1 + n - (n - k)) % n = q.1 + k := by
          have : q.1 + n - (n - k) = q.1 + k := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
        rw [h1]
        omega

lemma preimage_true_cycInt_other {x k : ℕ} (hx : x < n) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1)
    (hx0 : x ≠ 0) (hxnk : x ≠ n - k) :
    (cernyAut n hn).preimage (cycInt n (hn_pos hn) x k) [true] =
      cycInt n (hn_pos hn) x k := by
  have hz := zero_mem_cycInt_iff hn hx hk1 hkn
  have hl := last_mem_cycInt_iff hn hx hkn
  ext q
  rw [Aut.mem_preimage]
  change (cernyAut n hn).step q true ∈ cycInt n (hn_pos hn) x k ↔ _
  dsimp only [cernyAut]
  split_ifs with hq
  · have hq_eq : q = ⟨n - 1, by omega⟩ := Fin.ext hq
    rw [hq_eq]
    constructor <;> intro hmem
    · have h0 : (⟨0, hn_pos hn⟩ : Fin n) ∈ cycInt n (hn_pos hn) x k := hmem
      rw [hz] at h0
      rw [hl]
      omega
    · rw [hl] at hmem
      rw [hz]
      omega
  · rfl

lemma isCycInterval_preimage {S : Finset (Fin n)} (hS : IsCycInterval hn S) (σ : Bool) :
    IsCycInterval hn ((cernyAut n hn).preimage S [σ]) := by
  rcases hS with rfl | ⟨x, hx, k, hk1, hkn, rfl⟩
  · left; simp
  · cases σ with
    | false =>
      right
      refine ⟨(x + n - 1) % n, Nat.mod_lt _ (hn_pos hn), k, hk1, hkn, ?_⟩
      exact preimage_false_cycInt hn hx hkn
    | true =>
      by_cases hkn_eq : k = n
      · subst hkn_eq
        rw [cycInt_univ hn, Aut.preimage_univ]
        exact isCycInterval_univ hn
      · have hkn' : k ≤ n - 1 := by omega
        by_cases hx0 : x = 0
        · subst hx0
          right
          refine ⟨n - 1, by omega, k + 1, by omega, by omega, ?_⟩
          exact preimage_true_cycInt_x0 hn hk1 hkn'
        · by_cases hxnk : x = n - k
          · subst hxnk
            rw [preimage_true_cycInt_xnk hn hk1 hkn']
            split_ifs with hk
            · left; rfl
            · right
              exact ⟨n - k, by omega, k - 1, by omega, by omega, rfl⟩
          · right
            refine ⟨x, hx, k, hk1, hkn, ?_⟩
            exact preimage_true_cycInt_other hn hx hk1 hkn' hx0 hxnk

end CycIntProps

section Potential
variable {n : ℕ} (hn : 2 ≤ n)
include hn

/-- 1-Lipschitz potential `Phi` on cyclic intervals of `Fin n`. -/
noncomputable def Phi (S : Finset (Fin n)) : ℕ :=
  open scoped Classical in
  if S = Finset.univ then (n - 1) ^ 2
  else if h : ∃ x < n, ∃ k, 1 ≤ k ∧ k ≤ n - 1 ∧ S = cycInt n (hn_pos hn) x k then
    let x := Classical.choose h
    let k := Classical.choose (Classical.choose_spec h).2
    if k ≤ 1 then 0 else (k - 1) * n - x
  else 0

lemma Phi_univ : Phi hn (Finset.univ : Finset (Fin n)) = (n - 1) ^ 2 := by
  simp [Phi]

lemma Phi_empty : Phi hn (∅ : Finset (Fin n)) = 0 := by
  have hne : (∅ : Finset (Fin n)) ≠ Finset.univ := by
    intro h
    have : (0 : ℕ) = n := by
      simpa using congrArg Finset.card h
    omega
  have hno : ¬ ∃ x < n, ∃ k, 1 ≤ k ∧ k ≤ n - 1 ∧ (∅ : Finset (Fin n)) = cycInt n (hn_pos hn) x k := by
    rintro ⟨x, hx, k, hk1, hkn, heq⟩
    have := congrArg Finset.card heq
    rw [Finset.card_empty, card_cycInt hn (by omega)] at this
    omega
  simp [Phi, hne, hno]

lemma Phi_cycInt {x k : ℕ} (hx : x < n) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    Phi hn (cycInt n (hn_pos hn) x k) = if k ≤ 1 then 0 else (k - 1) * n - x := by
  have hne : cycInt n (hn_pos hn) x k ≠ Finset.univ := by
    intro h
    have := congrArg Finset.card h
    rw [card_cycInt hn (by omega), Finset.card_univ, Fintype.card_fin] at this
    omega
  have hex : ∃ x' < n, ∃ k', 1 ≤ k' ∧ k' ≤ n - 1 ∧
      cycInt n (hn_pos hn) x k = cycInt n (hn_pos hn) x' k' :=
    ⟨x, hx, k, hk1, hkn, rfl⟩
  simp only [Phi, hne, ↓reduceIte, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec hex
  have hspec2 := Classical.choose_spec hspec.2
  obtain ⟨hx_eq, hk_eq⟩ := cycInt_inj hn hx hspec.1 hk1 hkn hspec2.1 hspec2.2.1 hspec2.2.2
  rw [← hk_eq, ← hx_eq]

lemma Phi_singleton (q : Fin n) : Phi hn ({q} : Finset (Fin n)) = 0 := by
  rw [← cycInt_one hn q, Phi_cycInt hn q.2 le_rfl (by omega)]
  simp

lemma Phi_preimage_le {S : Finset (Fin n)} (hS : IsCycInterval hn S) (σ : Bool) :
    Phi hn ((cernyAut n hn).preimage S [σ]) ≤ Phi hn S + 1 := by
  rcases hS with rfl | ⟨x, hx, k, hk1, hkn, rfl⟩
  · simp [Phi_empty]
  · by_cases hkn_eq : k = n
    · subst hkn_eq
      rw [cycInt_univ hn, Aut.preimage_univ]
      omega
    · have hkn' : k ≤ n - 1 := by omega
      rw [Phi_cycInt hn hx hk1 hkn']
      cases σ with
      | false =>
        rw [preimage_false_cycInt hn hx (by omega)]
        have hx' : (x + n - 1) % n < n := Nat.mod_lt _ (hn_pos hn)
        rw [Phi_cycInt hn hx' hk1 hkn']
        split_ifs with hk
        · omega
        · have hle : x ≤ (x + n - 1) % n + 1 := by
            by_cases hx0 : x = 0
            · omega
            · have : (x + n - 1) % n = x - 1 := by
                have h1 : x + n - 1 = (x - 1) + n := by omega
                rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [this]
              omega
          omega
      | true =>
        by_cases hx0 : x = 0
        · subst hx0
          rw [preimage_true_cycInt_x0 hn hk1 hkn']
          by_cases hk_last : k = n - 1
          · subst hk_last
            have heq : n - 1 + 1 = n := by omega
            rw [heq, cycInt_univ hn, Phi_univ]
            by_cases hn2 : n = 2
            · subst hn2; simp
            · have hnot : ¬ (n - 1 ≤ 1) := by omega
              simp only [hnot, ↓reduceIte, Nat.sub_zero]
              have : (n - 1) ^ 2 = (n - 1 - 1) * n + 1 := by
                have hsub1 : (n - 1 - 1) + 2 = n := by omega
                have hsub2 : (n - 1) + 1 = n := by omega
                nlinarith
              omega
          · have hk1' : k + 1 ≤ n - 1 := by omega
            rw [Phi_cycInt hn (by omega : n - 1 < n) (by omega) hk1']
            have hnot : ¬ (k + 1 ≤ 1) := by omega
            simp only [hnot, ↓reduceIte, Nat.add_sub_cancel, Nat.sub_zero]
            split_ifs with hk
            · have hk_eq : k = 1 := by omega
              subst hk_eq
              simp
              omega
            · have : k * n - (n - 1) = (k - 1) * n + 1 := by
                have hk2 : 2 ≤ k := by omega
                have hle : n - 1 ≤ k * n := by
                  have := Nat.mul_le_mul_right n hk1
                  omega
                have hk2' : (k - 1) + 1 = k := by omega
                have hle2 : (k * n - (n - 1)) + (n - 1) = k * n := by omega
                have hn1 : (n - 1) + 1 = n := by omega
                nlinarith
              omega
        · by_cases hxnk : x = n - k
          · subst hxnk
            rw [preimage_true_cycInt_xnk hn hk1 hkn']
            by_cases hk : k = 1
            · simp [hk, Phi_empty]
            · simp only [hk, ↓reduceIte]
              rw [Phi_cycInt hn (by omega : n - k < n) (by omega) (by omega)]
              have hk2 : ¬ (k ≤ 1) := by omega
              simp only [hk2, ↓reduceIte]
              split_ifs with hk'
              · omega
              · have hle : (k - 1 - 1) * n - (n - k) ≤ (k - 1) * n - (n - k) := by
                  apply Nat.sub_le_sub_right
                  exact Nat.mul_le_mul_right n (by omega)
                omega
          · rw [preimage_true_cycInt_other hn hx hk1 hkn' hx0 hxnk,
              Phi_cycInt hn hx hk1 hkn']
            omega

end Potential

section MainTheorems
variable {n : ℕ} (hn : 2 ≤ n)
include hn

/-- Lower bound: every synchronizing word of `cernyAut n hn` has length at least `(n - 1)^2`. -/
theorem cerny_lower_bound {w : List Bool} (hw : (cernyAut n hn).IsSyncWord w) :
    (n - 1) ^ 2 ≤ w.length := by
  haveI : NeZero n := ⟨by omega⟩
  rw [Aut.isSyncWord_iff_preimage_univ] at hw
  obtain ⟨q₀, hq₀⟩ := hw
  have hinv : ∀ u : List Bool,
      IsCycInterval hn ((cernyAut n hn).preimage {q₀} u) ∧
      Phi hn ((cernyAut n hn).preimage {q₀} u) ≤ u.length := by
    intro u
    induction u with
    | nil =>
      simp only [Aut.preimage_nil, List.length_nil]
      exact ⟨isCycInterval_singleton hn q₀, by rw [Phi_singleton]⟩
    | cons σ u ih =>
      have hcons : σ :: u = [σ] ++ u := rfl
      rw [hcons, ← Aut.preimage_append]
      refine ⟨isCycInterval_preimage hn ih.1 σ, ?_⟩
      calc Phi hn ((cernyAut n hn).preimage ((cernyAut n hn).preimage {q₀} u) [σ])
          ≤ Phi hn ((cernyAut n hn).preimage {q₀} u) + 1 := Phi_preimage_le hn ih.1 σ
        _ ≤ u.length + 1 := Nat.add_le_add_right ih.2 1
        _ = ([σ] ++ u).length := by simp
  have h := (hinv w).2
  rw [hq₀, Phi_univ] at h
  exact h

end MainTheorems

/-- Explicit Černý synchronizing word of length `(n - 1)^2`. -/
def cernyWord (n : ℕ) : List Bool :=
  (List.replicate (n - 2) (true :: List.replicate (n - 1) false)).flatten ++ [true]

lemma cernyWord_length {n : ℕ} (hn : 2 ≤ n) : (cernyWord n).length = (n - 1) ^ 2 := by
  simp only [cernyWord, List.length_append, List.length_flatten, List.map_replicate,
    List.sum_replicate, smul_eq_mul, List.length_cons, List.length_nil, List.length_replicate]
  nlinarith [Nat.sub_add_cancel hn, Nat.sub_add_cancel (by omega : 1 ≤ n)]

section UpperBound
variable {n : ℕ} (hn : 2 ≤ n)
include hn

private lemma preimage_false_replicate (x k m : ℕ) (hx : x < n) (hk : k ≤ n) :
    (cernyAut n hn).preimage (cycInt n (hn_pos hn) x k) (List.replicate m false) =
      cycInt n (hn_pos hn) ((x + m * (n - 1)) % n) k := by
  induction m generalizing x with
  | zero =>
    simp [Nat.mod_eq_of_lt hx]
  | succ m ih =>
    rw [List.replicate_succ', ← Aut.preimage_append, preimage_false_cycInt hn hx hk,
      ih ((x + n - 1) % n) (Nat.mod_lt _ (hn_pos hn))]
    congr 1
    have h1 : ((x + n - 1) % n + m * (n - 1)) % n = (x + n - 1 + m * (n - 1)) % n := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [h1]
    have h2 : x + n - 1 + m * (n - 1) = x + (m + 1) * (n - 1) := by
      have : (m + 1) * (n - 1) = (n - 1) + m * (n - 1) := by ring
      omega
    rw [h2]

private lemma preimage_block (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    (cernyAut n hn).preimage (cycInt n (hn_pos hn) (n - 1) k)
      (true :: List.replicate (n - 1) false) =
      cycInt n (hn_pos hn) (n - 1) (k + 1) := by
  have hsplit : true :: List.replicate (n - 1) false = [true] ++ List.replicate (n - 1) false := rfl
  rw [hsplit, ← Aut.preimage_append, preimage_false_replicate hn (n - 1) k (n - 1) (by omega) (by omega)]
  have hmod : (n - 1 + (n - 1) * (n - 1)) % n = 0 := by
    have h1 : n - 1 + (n - 1) * (n - 1) = n * (n - 1) := by
      zify [show 1 ≤ n by omega]; ring
    rw [h1, Nat.mul_mod_right]
  rw [hmod]
  exact preimage_true_cycInt_x0 hn hk1 hkn

/-- Upper bound: `cernyWord n` is a synchronizing word for `cernyAut n hn` of length `(n - 1)^2`. -/
theorem cerny_upper_bound :
    (cernyAut n hn).IsSyncWord (cernyWord n) ∧ (cernyWord n).length = (n - 1) ^ 2 := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨?_, cernyWord_length hn⟩
  rw [Aut.isSyncWord_iff_preimage_univ]
  refine ⟨⟨0, hn_pos hn⟩, ?_⟩
  rw [cernyWord, ← Aut.preimage_append]
  have h0 : (cernyAut n hn).preimage {⟨0, hn_pos hn⟩} [true] =
      cycInt n (hn_pos hn) (n - 1) 2 := by
    rw [← cycInt_one hn ⟨0, hn_pos hn⟩]
    exact preimage_true_cycInt_x0 hn le_rfl (by omega)
  rw [h0]
  have hloop : ∀ t ≤ n - 2,
      (cernyAut n hn).preimage (cycInt n (hn_pos hn) (n - 1) 2)
        (List.replicate t (true :: List.replicate (n - 1) false)).flatten =
        cycInt n (hn_pos hn) (n - 1) (2 + t) := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      rw [List.replicate_succ, List.flatten_cons, ← Aut.preimage_append, ih (by omega)]
      have hb := preimage_block hn (2 + t) (by omega) (by omega)
      rw [hb]
      ring_nf
  rw [hloop (n - 2) le_rfl]
  have h2n : 2 + (n - 2) = n := by omega
  rw [h2n, cycInt_univ hn]

end UpperBound

end CernyLowerBound
