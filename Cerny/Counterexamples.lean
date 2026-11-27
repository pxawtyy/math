import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Cerny.Defs

open Finset

namespace Cerny.Counterexamples

/-! ### 1. Bitmask Certificate Engine -/

/-- Preimage of a subset represented by bitmask `m : ℕ` under `g : Fin n → Fin n`. -/
def preMask (n : ℕ) (g : Fin n → Fin n) (m : ℕ) : ℕ :=
  (List.finRange n).foldl
    (fun acc x => if (m >>> (g x).val) &&& 1 == 1 then acc ||| (1 <<< x.val) else acc) 0

/-- Popcount on the first `n` bits intersected with `maskC`. -/
def popMask (n : ℕ) (maskC m : ℕ) : ℕ :=
  (List.finRange n).foldl
    (fun acc x => if ((m &&& maskC) >>> x.val) &&& 1 == 1 then acc + 1 else acc) 0

/-- Bitmask of a `Finset (Fin n)` via `foldl` + `|||`. -/
def toMask {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  (List.finRange n).foldl (fun acc x => if x ∈ S then acc ||| (1 <<< x.val) else acc) 0

lemma testBit_foldl_or {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (L : List (Fin n)) :
    ∀ (acc k : ℕ),
      (L.foldl (fun a x => if P x then a ||| (1 <<< x.val) else a) acc).testBit k =
        (acc.testBit k || decide (∃ x ∈ L, P x ∧ x.val = k)) := by
  induction L with
  | nil => intro acc k; simp
  | cons y ys ih =>
    intro acc k
    simp only [List.foldl_cons, ih]
    by_cases hPy : P y
    · simp only [hPy, ↓reduceIte, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hky : k = y.val
      · subst hky; simp [hPy]
      · have hbit : ((1 : ℕ).testBit (k - y.val) && decide (y.val ≤ k)) = false := by
          by_cases hle : y.val ≤ k
          · have hpos : 0 < k - y.val := by omega
            rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨d, hd⟩
            have h1_lt : 1 < 2 ^ d.succ := Nat.one_lt_two_pow (Nat.succ_ne_zero d)
            have hbit1 : (1 : ℕ).testBit d.succ = false := by
              rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h1_lt]
              rfl
            rw [hd, hbit1]
            simp
          · simp [hle]
        simp only [Bool.and_comm (decide (y.val ≤ k)), hbit, Bool.or_false]
        congr 1; apply decide_eq_decide.mpr
        constructor
        · rintro ⟨x, hx, hPx, rfl⟩; exact ⟨x, List.mem_cons_of_mem y hx, hPx, rfl⟩
        · rintro ⟨x, hx, hPx, rfl⟩
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact (hky rfl).elim
          · exact ⟨x, hmem, hPx, rfl⟩
    · simp only [hPy, ↓reduceIte]
      congr 1; apply decide_eq_decide.mpr
      constructor
      · rintro ⟨x, hx, hPx, rfl⟩; exact ⟨x, List.mem_cons_of_mem y hx, hPx, rfl⟩
      · rintro ⟨x, hx, hPx, rfl⟩
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact (hPy hPx).elim
        · exact ⟨x, hmem, hPx, rfl⟩

lemma testBit_toMask {n : ℕ} (S : Finset (Fin n)) (x : Fin n) :
    (toMask S).testBit x.val = decide (x ∈ S) := by
  dsimp [toMask]
  rw [testBit_foldl_or]
  simp only [Nat.zero_testBit, Bool.false_or]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨y, _, hyS, hyx⟩; exact (Fin.ext hyx) ▸ hyS
  · intro hxS; exact ⟨x, List.mem_finRange x, hxS, rfl⟩

lemma toMask_lt_two_pow {n : ℕ} (S : Finset (Fin n)) : toMask S < 2 ^ n := by
  dsimp [toMask]
  have hgen : ∀ (L : List (Fin n)) (acc : ℕ), acc < 2 ^ n →
      L.foldl (fun a x => if x ∈ S then a ||| (1 <<< x.val) else a) acc < 2 ^ n := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons y ys ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih
      by_cases hy : y ∈ S
      · simp only [hy, ↓reduceIte]
        refine Nat.or_lt_two_pow hacc ?_
        rw [Nat.shiftLeft_eq, one_mul]
        exact Nat.pow_lt_pow_right (by decide : 1 < 2) y.isLt
      · simp [hy, hacc]
  exact hgen _ 0 (Nat.two_pow_pos n)

lemma nat_shiftRight_and_one_beq_one (m k : ℕ) :
    (((m >>> k) &&& 1) == 1) = m.testBit k := by
  have hmod : (m >>> k) &&& 1 = (m >>> k) % 2 := Nat.and_one_is_mod (m >>> k)
  rw [Nat.testBit, hmod]
  cases Nat.mod_two_eq_zero_or_one (m >>> k) with
  | inl h => simp [h]
  | inr h => simp [h]

lemma toMask_preimage {n : ℕ} (A : Aut (Fin n) Bool) (S : Finset (Fin n)) (σ : Bool) :
    toMask (A.preimage S [σ]) = preMask n (fun q => A.step q σ) (toMask S) := by
  dsimp [toMask, preMask]
  congr 1; funext acc x
  have hbit : (((toMask S) >>> (A.step x σ).val) &&& 1 == 1) =
      decide (x ∈ A.preimage S [σ]) := by
    rw [nat_shiftRight_and_one_beq_one, testBit_toMask]
    exact decide_eq_decide.mpr (by rw [Aut.mem_preimage]; simp [Aut.eval])
  dsimp [toMask] at hbit
  rw [hbit]
  by_cases hx : x ∈ A.preimage S [σ] <;> simp [hx]

lemma popMask_toMask {n : ℕ} (S C : Finset (Fin n)) :
    popMask n (toMask C) (toMask S) = (S ∩ C).card := by
  dsimp [popMask]
  have hfold : ∀ (L : List (Fin n)) (acc : ℕ),
      L.foldl (fun a x => if ((toMask S &&& toMask C) >>> x.val) &&& 1 == 1 then a + 1 else a) acc =
        acc + L.countP (fun x => decide (x ∈ S ∩ C)) := by
    intro L
    induction L with
    | nil => intro acc; simp
    | cons y ys ih =>
      intro acc
      simp only [List.foldl_cons, List.countP_cons]
      have hbit : (((toMask S &&& toMask C) >>> y.val) &&& 1 == 1) = decide (y ∈ S ∩ C) := by
        rw [nat_shiftRight_and_one_beq_one, Nat.testBit_and, testBit_toMask, testBit_toMask]
        by_cases hyS : y ∈ S <;> by_cases hyC : y ∈ C <;> simp [hyS, hyC]
      rw [hbit, ih]
      by_cases hy : y ∈ S ∩ C <;> simp [hy] <;> omega
  rw [hfold, Nat.zero_add, List.countP_eq_length_filter]
  have hnodup : ((List.finRange n).filter (fun x => decide (x ∈ S ∩ C))).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  congr 1
  ext x
  simp [List.mem_filter, List.mem_finRange]

/-- Distance certificate theorem: if `dist` satisfies the step, popcount, and start conditions,
then every word `w` of length `≤ d` keeps `popMask n maskC (toMask (A.preimage T₀ w)) ≤ k`. -/
theorem cert_bound_bang {n d k : ℕ} (A : Aut (Fin n) Bool) (maskC : ℕ)
    (dist : Array ℕ)
    (hstep : ∀ m : Fin (2 ^ n), ∀ σ : Bool,
      dist[m.val]! ≤ dist[(preMask n (fun q => A.step q σ) m.val) % (2 ^ n)]! + 1)
    (hpop : ∀ m : Fin (2 ^ n), 0 < dist[m.val]! → popMask n maskC m.val ≤ k)
    (T₀ : Finset (Fin n))
    (hstart : d + 1 ≤ dist[toMask T₀]!) :
    ∀ w : List Bool, w.length ≤ d → popMask n maskC (toMask (A.preimage T₀ w)) ≤ k := by
  have hind : ∀ (w : List Bool) (S : Finset (Fin n)),
      dist[toMask S]! ≤ dist[toMask (A.preimage S w)]! + w.length := by
    intro w
    induction w with
    | nil =>
      intro S
      have hnil : A.preimage S [] = S := by
        ext q; rw [Aut.mem_preimage]; simp [Aut.eval]
      rw [hnil]
      exact Nat.le_add_right _ _
    | cons σ rest ih =>
      intro S
      have h1 := ih S
      have h2 := hstep ⟨toMask (A.preimage S rest), toMask_lt_two_pow _⟩ σ
      dsimp only at h2
      rw [show A.preimage S (σ :: rest) = A.preimage (A.preimage S rest) [σ] from
            (Aut.preimage_append A S rest [σ]).symm,
          toMask_preimage A (A.preimage S rest) σ]
      have hlt' : preMask n (fun q => A.step q σ) (toMask (A.preimage S rest)) < 2 ^ n := by
        rw [← toMask_preimage]; exact toMask_lt_two_pow _
      rw [Nat.mod_eq_of_lt hlt'] at h2
      simp only [List.length_cons]
      omega
  intro w hw
  have hle := hind w T₀
  have hpos : 0 < dist[toMask (A.preimage T₀ w)]! := by omega
  exact hpop ⟨toMask (A.preimage T₀ w), toMask_lt_two_pow _⟩ hpos

/-! ### 2. The 5 Explicit Counterexamples with Precomputed Distance Certificates -/

/-- Helper to build `Aut (Fin n) Bool` from two transition functions (`false ↦ a`, `true ↦ b`). -/
def mkAut (n : ℕ) (a b : Fin n → Fin n) : Aut (Fin n) Bool :=
  ⟨fun q σ => if σ then b q else a q⟩

-- Counterexample 1: Unbalanced two-cluster (3, 4), n = 7, minimum extension = 13 = 2n - 1
def ex1_aut : Aut (Fin 7) Bool :=
  mkAut 7 ![1, 2, 0, 4, 5, 6, 3] ![0, 1, 4, 2, 2, 0, 1]

def ex1_syncWord : List Bool :=
  [true, false, true, false, false, false, false, false, false,
   true, false, true, false, false, false, false, false, true]

def ex1_dist : Array ℕ :=
  #[13, 10, 11, 3, 12, 4, 4, 1, 13, 6, 7, 3, 11, 4, 4, 1, 13, 3, 4, 1, 8, 1, 1, 1, 13, 3, 4, 1, 8, 1, 1, 0,
    13, 9, 4, 2, 5, 2, 2, 1, 13, 6, 4, 2, 5, 2, 2, 0, 13, 3, 4, 1, 5, 1, 1, 0, 13, 3, 4, 0, 5, 0, 0, 0,
    13, 6, 10, 3, 5, 3, 3, 1, 13, 6, 7, 3, 5, 3, 3, 0, 13, 3, 4, 1, 5, 1, 1, 0, 13, 3, 4, 0, 5, 0, 0, 0,
    13, 6, 4, 2, 5, 2, 2, 0, 13, 6, 4, 0, 5, 0, 0, 0, 13, 3, 4, 0, 5, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 4096 in
lemma ex1_sync : ex1_aut.IsSyncWord ex1_syncWord := by
  rw [Aut.isSyncWord_iff_exists_eval_eq]
  exact ⟨ex1_aut.eval 0 ex1_syncWord, by decide⟩
set_option maxRecDepth 4096 in
lemma ex1_cert_step : ∀ m : Fin 128, ∀ σ : Bool,
    ex1_dist[m.val]! ≤ ex1_dist[(preMask 7 (fun q => ex1_aut.step q σ) m.val) % 128]! + 1 := by decide
set_option maxRecDepth 4096 in
lemma ex1_cert_pop : ∀ m : Fin 128, 0 < ex1_dist[m.val]! → popMask 7 127 m.val ≤ 4 := by decide
set_option maxRecDepth 4096 in
lemma ex1_cert_start : ex1_dist[120]! = 13 := by decide

theorem two_cluster_34_counterexample :
    ex1_aut.IsSync ∧
      ∀ w : List Bool, w.length ≤ 12 →
        (ex1_aut.preimage ({3, 4, 5, 6} : Finset (Fin 7)) w).card ≤ 4 := by
  refine ⟨⟨ex1_syncWord, ex1_sync⟩, fun w hw => ?_⟩
  have hmaskU : toMask (Finset.univ : Finset (Fin 7)) = 127 := by decide
  have hmaskT : toMask ({3, 4, 5, 6} : Finset (Fin 7)) = 120 := by decide
  have h := cert_bound_bang ex1_aut 127 ex1_dist ex1_cert_step ex1_cert_pop
    ({3, 4, 5, 6} : Finset (Fin 7)) (by rw [hmaskT, ex1_cert_start]) w hw
  rw [← hmaskU, popMask_toMask, Finset.inter_univ] at h
  exact h

-- Counterexample 2: Balanced (1, 2, 4), n = 7, minimum extension = 8
def ex2_aut : Aut (Fin 7) Bool :=
  mkAut 7 ![0, 2, 1, 4, 5, 6, 3] ![4, 1, 6, 5, 2, 5, 0]

def ex2_syncWord : List Bool :=
  [true, false, true, false, false, false, true, false, true, false,
   true, false, true, true, false, true, false, true, false, true]

def ex2_dist : Array ℕ :=
  #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 5, 8, 6, 7, 3,
    8, 8, 8, 7, 8, 8, 8, 7, 8, 8, 8, 7, 8, 8, 8, 7, 8, 5, 8, 3, 6, 4, 4, 1, 8, 5, 8, 3, 6, 4, 4, 0,
    8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 8, 5, 8, 4, 6, 2, 8, 8, 8, 8, 8, 8, 8, 8, 8, 5, 8, 3, 7, 3, 3, 0,
    8, 6, 7, 3, 7, 4, 5, 1, 8, 4, 6, 2, 7, 2, 2, 0, 8, 3, 7, 1, 5, 1, 1, 0, 8, 3, 6, 0, 5, 0, 0, 0]

lemma ex2_sync : ex2_aut.IsSyncWord ex2_syncWord := by
  rw [Aut.isSyncWord_iff_exists_eval_eq]
  exact ⟨ex2_aut.eval 0 ex2_syncWord, by decide⟩
set_option maxRecDepth 4096 in
lemma ex2_cert_step : ∀ m : Fin 128, ∀ σ : Bool,
    ex2_dist[m.val]! ≤ ex2_dist[(preMask 7 (fun q => ex2_aut.step q σ) m.val) % 128]! + 1 := by decide
set_option maxRecDepth 4096 in
lemma ex2_cert_pop : ∀ m : Fin 128, 0 < ex2_dist[m.val]! → popMask 7 127 m.val ≤ 5 := by decide
set_option maxRecDepth 4096 in
lemma ex2_cert_start : ex2_dist[87]! = 8 := by decide

theorem balanced_124_counterexample :
    ex2_aut.IsSync ∧
      (ex2_aut.preimage ({0} : Finset (Fin 7)) [true]).card = 1 ∧
      (ex2_aut.preimage ({1, 2} : Finset (Fin 7)) [true]).card = 2 ∧
      (ex2_aut.preimage ({3, 4, 5, 6} : Finset (Fin 7)) [true]).card = 4 ∧
      ∀ w : List Bool, w.length ≤ 7 →
        (ex2_aut.preimage ({0, 1, 2, 4, 6} : Finset (Fin 7)) w).card ≤ 5 := by
  refine ⟨⟨ex2_syncWord, ex2_sync⟩, by decide, by decide, by decide, fun w hw => ?_⟩
  have hmaskU : toMask (Finset.univ : Finset (Fin 7)) = 127 := by decide
  have hmaskT : toMask ({0, 1, 2, 4, 6} : Finset (Fin 7)) = 87 := by decide
  have h := cert_bound_bang ex2_aut 127 ex2_dist ex2_cert_step ex2_cert_pop
    ({0, 1, 2, 4, 6} : Finset (Fin 7)) (by rw [hmaskT, ex2_cert_start]) w hw
  rw [← hmaskU, popMask_toMask, Finset.inter_univ] at h
  exact h

-- Counterexample 3: Balanced (1, 6) pure in Φ_6, n = 7, minimum extension = 8
def ex3_aut : Aut (Fin 7) Bool :=
  mkAut 7 ![0, 2, 3, 4, 5, 6, 1] ![6, 2, 1, 3, 2, 1, 0]

def ex3_syncWord : List Bool :=
  [true, false, true, false, false, false, false, true, false, false,
   true, false, false, false, false, true, false, true, false, true]

def ex3_dist : Array ℕ :=
  #[8, 8, 8, 8, 8, 8, 8, 6, 8, 8, 8, 8, 8, 7, 3, 1, 8, 8, 8, 8, 8, 8, 8, 6, 8, 8, 8, 8, 4, 2, 2, 1,
    8, 8, 8, 8, 8, 8, 8, 6, 8, 8, 8, 8, 8, 7, 3, 1, 8, 8, 8, 8, 8, 8, 8, 6, 5, 3, 5, 3, 3, 2, 2, 0,
    8, 8, 8, 8, 8, 8, 7, 1, 8, 8, 8, 8, 8, 7, 1, 1, 8, 8, 8, 8, 8, 8, 7, 1, 8, 8, 8, 8, 4, 2, 1, 0,
    8, 8, 7, 5, 8, 8, 6, 1, 8, 8, 7, 5, 8, 7, 1, 0, 6, 4, 5, 4, 6, 4, 5, 0, 4, 3, 4, 0, 3, 0, 0, 0]

lemma ex3_sync : ex3_aut.IsSyncWord ex3_syncWord := by
  rw [Aut.isSyncWord_iff_exists_eval_eq]
  exact ⟨ex3_aut.eval 0 ex3_syncWord, by decide⟩
set_option maxRecDepth 4096 in
lemma ex3_cert_step : ∀ m : Fin 128, ∀ σ : Bool,
    ex3_dist[m.val]! ≤ ex3_dist[(preMask 7 (fun q => ex3_aut.step q σ) m.val) % 128]! + 1 := by decide
set_option maxRecDepth 4096 in
lemma ex3_cert_pop : ∀ m : Fin 128, 0 < ex3_dist[m.val]! → popMask 7 127 m.val ≤ 5 := by decide
set_option maxRecDepth 4096 in
lemma ex3_cert_start : ex3_dist[91]! = 8 := by decide

theorem balanced_16_counterexample :
    ex3_aut.IsSync ∧ ex3_syncWord.length = 20 ∧
      (ex3_aut.preimage ({0} : Finset (Fin 7)) [true]).card = 1 ∧
      (ex3_aut.preimage ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) [true]).card = 6 ∧
      ∀ w : List Bool, w.length ≤ 7 →
        (ex3_aut.preimage ({0, 1, 3, 4, 6} : Finset (Fin 7)) w).card ≤ 5 := by
  refine ⟨⟨ex3_syncWord, ex3_sync⟩, rfl, by decide, by decide, fun w hw => ?_⟩
  have hmaskU : toMask (Finset.univ : Finset (Fin 7)) = 127 := by decide
  have hmaskT : toMask ({0, 1, 3, 4, 6} : Finset (Fin 7)) = 91 := by decide
  have h := cert_bound_bang ex3_aut 127 ex3_dist ex3_cert_step ex3_cert_pop
    ({0, 1, 3, 4, 6} : Finset (Fin 7)) (by rw [hmaskT, ex3_cert_start]) w hw
  rw [← hmaskU, popMask_toMask, Finset.inter_univ] at h
  exact h

-- Counterexample 4: Rank n - 1, (1, 6), step s = 2, n = 7, minimum extension = 8
def ex4_aut : Aut (Fin 7) Bool :=
  mkAut 7 ![0, 2, 3, 4, 5, 6, 1] ![6, 1, 2, 1, 4, 5, 0]

def ex4_syncWord : List Bool :=
  [true, false, true, false, false, true, false, false, false,
   true, false, false, true, false, true, false, true]

def ex4_dist : Array ℕ :=
  #[8, 8, 8, 8, 8, 8, 5, 3, 8, 8, 8, 8, 6, 4, 4, 2, 8, 8, 6, 4, 8, 8, 4, 1, 7, 5, 5, 3, 5, 3, 3, 0,
    8, 8, 8, 7, 7, 5, 3, 1, 8, 8, 8, 7, 5, 2, 2, 0, 8, 6, 5, 1, 6, 4, 1, 0, 6, 4, 4, 0, 4, 0, 0, 0,
    8, 8, 8, 4, 8, 8, 3, 1, 8, 6, 7, 3, 4, 2, 2, 0, 8, 8, 4, 1, 8, 8, 1, 0, 6, 3, 3, 0, 3, 0, 0, 0,
    8, 7, 8, 1, 6, 2, 1, 0, 7, 5, 6, 0, 2, 0, 0, 0, 7, 5, 1, 0, 5, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0]

lemma ex4_sync : ex4_aut.IsSyncWord ex4_syncWord := by
  rw [Aut.isSyncWord_iff_exists_eval_eq]
  exact ⟨ex4_aut.eval 0 ex4_syncWord, by decide⟩
set_option maxRecDepth 4096 in
lemma ex4_cert_step : ∀ m : Fin 128, ∀ σ : Bool,
    ex4_dist[m.val]! ≤ ex4_dist[(preMask 7 (fun q => ex4_aut.step q σ) m.val) % 128]! + 1 := by decide
set_option maxRecDepth 4096 in
lemma ex4_cert_pop : ∀ m : Fin 128, 0 < ex4_dist[m.val]! → popMask 7 127 m.val ≤ 4 := by decide
set_option maxRecDepth 4096 in
lemma ex4_cert_start : ex4_dist[85]! = 8 := by decide

theorem balanced_16_step2_counterexample :
    ex4_aut.IsSync ∧ (ex4_aut.image Finset.univ [true]).card = 6 ∧
      (ex4_aut.preimage ({0} : Finset (Fin 7)) [true]).card = 1 ∧
      (ex4_aut.preimage ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) [true]).card = 6 ∧
      ∀ w : List Bool, w.length ≤ 7 →
        (ex4_aut.preimage ({0, 2, 4, 6} : Finset (Fin 7)) w).card ≤ 4 := by
  refine ⟨⟨ex4_syncWord, ex4_sync⟩, by decide, by decide, by decide, fun w hw => ?_⟩
  have hmaskU : toMask (Finset.univ : Finset (Fin 7)) = 127 := by decide
  have hmaskT : toMask ({0, 2, 4, 6} : Finset (Fin 7)) = 85 := by decide
  have h := cert_bound_bang ex4_aut 127 ex4_dist ex4_cert_step ex4_cert_pop
    ({0, 2, 4, 6} : Finset (Fin 7)) (by rw [hmaskT, ex4_cert_start]) w hw
  rw [← hmaskU, popMask_toMask, Finset.inter_univ] at h
  exact h

-- Counterexample 5: Multi-cluster balanced with trees (2, 2), ℓ = 2, n = 6, relative extension = 8
def ex5_aut : Aut (Fin 6) Bool :=
  mkAut 6 ![1, 0, 3, 2, 0, 4] ![5, 3, 1, 2, 5, 5]

def ex5_syncWord : List Bool :=
  [true, false, true, false, true, true, false, true]

def ex5_dist : Array ℕ :=
  #[8, 5, 6, 0, 8, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
    3, 3, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

lemma ex5_sync : ex5_aut.IsSyncWord ex5_syncWord := by
  rw [Aut.isSyncWord_iff_exists_eval_eq]
  exact ⟨ex5_aut.eval 0 ex5_syncWord, by decide⟩
lemma ex5_cert_step : ∀ m : Fin 64, ∀ σ : Bool,
    ex5_dist[m.val]! ≤ ex5_dist[(preMask 6 (fun q => ex5_aut.step q σ) m.val) % 64]! + 1 := by decide
lemma ex5_cert_pop : ∀ m : Fin 64, 0 < ex5_dist[m.val]! → popMask 6 15 m.val ≤ 1 := by decide
lemma ex5_cert_start : ex5_dist[4]! = 8 := by decide

theorem multi_cluster_trees_counterexample :
    ex5_aut.IsSync ∧
      (ex5_aut.preimage ({0, 1, 4, 5} : Finset (Fin 6)) [true] ∩ ({0, 1, 2, 3} : Finset (Fin 6))).card = 2 ∧
      (ex5_aut.preimage ({2, 3} : Finset (Fin 6)) [true] ∩ ({0, 1, 2, 3} : Finset (Fin 6))).card = 2 ∧
      ∀ w : List Bool, w.length ≤ 7 →
        (ex5_aut.preimage ({2} : Finset (Fin 6)) (w ++ [false, false]) ∩
          ({0, 1, 2, 3} : Finset (Fin 6))).card ≤ 1 := by
  refine ⟨⟨ex5_syncWord, ex5_sync⟩, by decide, by decide, fun w hw => ?_⟩
  have hmaskC : toMask ({0, 1, 2, 3} : Finset (Fin 6)) = 15 := by decide
  have hmaskT : toMask ({2} : Finset (Fin 6)) = 4 := by decide
  have hpre2 : ex5_aut.preimage ({2} : Finset (Fin 6)) [false, false] = {2} := by decide
  have h := cert_bound_bang ex5_aut 15 ex5_dist ex5_cert_step ex5_cert_pop
    ({2} : Finset (Fin 6)) (by rw [hmaskT, ex5_cert_start]) w hw
  rw [← hmaskC, popMask_toMask] at h
  rw [← Aut.preimage_append, hpre2]
  exact h

end Cerny.Counterexamples
