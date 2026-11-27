import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic
import Cerny.Defs

open Finset
open scoped BigOperators

namespace Cerny.CircularDubuc

variable {𝕜 : Type*} [Field 𝕜]

/-! ### 1. Annular Cancellation Identity by Pure Induction (No Polynomials / No Lagrange) -/

/-- Divided-difference / Vandermonde sum `D(t, x, k) = ∑ u, (x u)^k / ∏_{v ≠ u} (x u - x v)`. -/
noncomputable def divDiffSum (t : ℕ) (x : Fin (t + 1) → 𝕜) (k : ℕ) : 𝕜 :=
  ∑ u : Fin (t + 1), (x u) ^ k / ∏ v ∈ Finset.univ.erase u, (x u - x v)

/-- Recursive complete homogeneous sum `hSum t x N`. -/
noncomputable def hSum : (t : ℕ) → (Fin (t + 1) → 𝕜) → ℕ → 𝕜
  | 0, x, N => (x 0) ^ N
  | t + 1, x, N =>
      ∑ j ∈ Finset.range (N + 1), (x (Fin.last (t + 1))) ^ j * hSum t (Fin.init x) (N - j)

lemma hSum_zero (t : ℕ) (x : Fin (t + 1) → 𝕜) : hSum t x 0 = 1 := by
  induction t with
  | zero => simp [hSum]
  | succ t ih => simp [hSum, ih]

lemma hSum_succ_N (t : ℕ) (x : Fin (t + 2) → 𝕜) (N : ℕ) :
    hSum (t + 1) x (N + 1) =
      x (Fin.last (t + 1)) * hSum (t + 1) x N + hSum t (Fin.init x) (N + 1) := by
  conv_lhs =>
    unfold hSum
    rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero]
  congr 1
  have hrhs : hSum (t + 1) x N =
      ∑ j ∈ Finset.range (N + 1), (x (Fin.last (t + 1))) ^ j * hSum t (Fin.init x) (N - j) := rfl
  rw [hrhs, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_succ', mul_assoc, Nat.succ_sub_succ]

/-- Recurrence 1 (`k → k + 1`):
`D(t + 1, x, k + 1) - x(last) * D(t + 1, x, k) = D(t, Fin.init x, k)`. -/
lemma divDiffSum_succ_k (t : ℕ) (x : Fin (t + 2) → 𝕜) (hx : Function.Injective x) (k : ℕ) :
    divDiffSum (t + 1) x (k + 1) - x (Fin.last (t + 1)) * divDiffSum (t + 1) x k =
      divDiffSum t (Fin.init x) k := by
  dsimp [divDiffSum]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
  have hlast : (x (Fin.last (t + 1))) ^ (k + 1) /
      ∏ v ∈ Finset.univ.erase (Fin.last (t + 1)), (x (Fin.last (t + 1)) - x v) -
      x (Fin.last (t + 1)) * ((x (Fin.last (t + 1))) ^ k /
      ∏ v ∈ Finset.univ.erase (Fin.last (t + 1)), (x (Fin.last (t + 1)) - x v)) = 0 := by
    rw [pow_succ']; ring
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hne_last : i.castSucc ≠ Fin.last (t + 1) := Fin.castSucc_ne_last i
  have hmem_last : Fin.last (t + 1) ∈ Finset.univ.erase i.castSucc :=
    Finset.mem_erase.mpr ⟨hne_last.symm, Finset.mem_univ _⟩
  have hprod : ∏ v ∈ Finset.univ.erase i.castSucc, (x i.castSucc - x v) =
      (x i.castSucc - x (Fin.last (t + 1))) *
        ∏ j ∈ Finset.univ.erase i, (Fin.init x i - Fin.init x j) := by
    rw [← Finset.mul_prod_erase _ _ hmem_last]
    congr 1
    symm
    refine Finset.prod_bij (fun (j : Fin (t + 1)) _ => j.castSucc) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
      exact ⟨Fin.castSucc_ne_last j, fun h => hj (Fin.castSucc_injective (t + 1) h)⟩
    · intro j₁ _ j₂ _ h; exact Fin.castSucc_injective (t + 1) h
    · intro v hv
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv
      obtain ⟨j, hj_eq⟩ := Fin.exists_castSucc_eq.mpr hv.1
      refine ⟨j, Finset.mem_erase.mpr ⟨fun h => hv.2 ?_, Finset.mem_univ _⟩, hj_eq⟩
      rw [← hj_eq, h]
    · intro j _; rfl
  have hdiff_ne : x i.castSucc - x (Fin.last (t + 1)) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne_last (hx h))
  rw [hprod]
  dsimp [Fin.init]
  have hnum : (x i.castSucc) ^ (k + 1) - x (Fin.last (t + 1)) * (x i.castSucc) ^ k =
      (x i.castSucc - x (Fin.last (t + 1))) * (x i.castSucc) ^ k := by
    rw [pow_succ']; ring
  rw [← mul_div_assoc, ← sub_div, hnum, mul_div_mul_left _ _ hdiff_ne]

/-- Recurrence 2 (`k = 0`):
`(x 0 - x last) * D(t + 1, x, 0) = D(t, Fin.init x, 0) - D(t, Fin.tail x, 0)`. -/
lemma divDiffSum_zero_recurrence (t : ℕ) (x : Fin (t + 2) → 𝕜) (hx : Function.Injective x) :
    (x 0 - x (Fin.last (t + 1))) * divDiffSum (t + 1) x 0 =
      divDiffSum t (Fin.init x) 0 - divDiffSum t (Fin.tail x) 0 := by
  dsimp [divDiffSum]
  simp only [pow_zero]
  rw [Finset.mul_sum]
  let y := x (Fin.last (t + 1))
  let z := x 0
  have h0ne : (0 : Fin (t + 2)) ≠ Fin.last (t + 1) := Fin.ext_iff.ne.mpr (by simp)
  let A : Fin (t + 2) → 𝕜 := fun u =>
    if h : u = Fin.last (t + 1) then 0
    else 1 / ∏ v ∈ (Finset.univ.erase u).erase (Fin.last (t + 1)), (x u - x v)
  let B : Fin (t + 2) → 𝕜 := fun u =>
    if h : u = 0 then 0
    else 1 / ∏ v ∈ (Finset.univ.erase u).erase 0, (x u - x v)
  have hterm : ∀ u : Fin (t + 2),
      (z - y) * (1 / ∏ v ∈ Finset.univ.erase u, (x u - x v)) = A u - B u := by
    intro u
    by_cases hu0 : u = 0
    · subst hu0
      have hmem : Fin.last (t + 1) ∈ Finset.univ.erase (0 : Fin (t + 2)) :=
        Finset.mem_erase.mpr ⟨h0ne.symm, Finset.mem_univ _⟩
      have hne : z - y ≠ 0 := sub_ne_zero.mpr (fun h => h0ne (hx h))
      dsimp only [A, B]
      rw [dif_neg h0ne, dif_pos rfl, sub_zero, ← Finset.mul_prod_erase _ _ hmem]
      dsimp [z, y] at hne ⊢
      field_simp [hne]
    · by_cases hul : u = Fin.last (t + 1)
      · subst hul
        have hmem : (0 : Fin (t + 2)) ∈ Finset.univ.erase (Fin.last (t + 1)) :=
          Finset.mem_erase.mpr ⟨h0ne, Finset.mem_univ _⟩
        have hne : y - z ≠ 0 := sub_ne_zero.mpr (fun h => h0ne.symm (hx h))
        dsimp only [A, B]
        rw [dif_pos rfl, dif_neg h0ne.symm, zero_sub]
        rw [← Finset.mul_prod_erase _ _ hmem]
        have hneg : z - y = -(y - z) := by ring
        dsimp [z, y] at hne hneg ⊢
        rw [hneg]
        field_simp [hne]
      · simp only [A, B, hu0, hul, ↓reduceDIte]
        have hmem0 : (0 : Fin (t + 2)) ∈ Finset.univ.erase u :=
          Finset.mem_erase.mpr ⟨Ne.symm hu0, Finset.mem_univ _⟩
        have hmeml : Fin.last (t + 1) ∈ Finset.univ.erase u :=
          Finset.mem_erase.mpr ⟨Ne.symm hul, Finset.mem_univ _⟩
        have hmem0' : (0 : Fin (t + 2)) ∈ (Finset.univ.erase u).erase (Fin.last (t + 1)) :=
          Finset.mem_erase.mpr ⟨h0ne, hmem0⟩
        have hmeml' : Fin.last (t + 1) ∈ (Finset.univ.erase u).erase 0 :=
          Finset.mem_erase.mpr ⟨h0ne.symm, hmeml⟩
        have hP0 : ∏ v ∈ Finset.univ.erase u, (x u - x v) =
            (x u - y) * ((x u - z) *
              ∏ v ∈ ((Finset.univ.erase u).erase (Fin.last (t + 1))).erase 0, (x u - x v)) := by
          rw [← Finset.mul_prod_erase _ _ hmeml, ← Finset.mul_prod_erase _ _ hmem0']
        have hPA : ∏ v ∈ (Finset.univ.erase u).erase (Fin.last (t + 1)), (x u - x v) =
            (x u - z) *
              ∏ v ∈ ((Finset.univ.erase u).erase (Fin.last (t + 1))).erase 0, (x u - x v) :=
          (Finset.mul_prod_erase _ _ hmem0').symm
        have hPB : ∏ v ∈ (Finset.univ.erase u).erase 0, (x u - x v) =
            (x u - y) *
              ∏ v ∈ ((Finset.univ.erase u).erase (Fin.last (t + 1))).erase 0, (x u - x v) := by
          rw [← Finset.mul_prod_erase _ _ hmeml', Finset.erase_right_comm]
        have hz_ne : x u - z ≠ 0 := sub_ne_zero.mpr (fun h => hu0 (hx h))
        have hy_ne : x u - y ≠ 0 := sub_ne_zero.mpr (fun h => hul (hx h))
        rw [hP0, hPA, hPB]
        set P := ∏ v ∈ ((Finset.univ.erase u).erase (Fin.last (t + 1))).erase 0, (x u - x v)
        have hP_ne : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v hv => by
          have hv' : v ≠ u :=
            (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2).1
          exact sub_ne_zero.mpr (fun h => hv' (hx h.symm))
        field_simp [hz_ne, hy_ne, hP_ne]; ring
  calc ∑ u : Fin (t + 2), (z - y) * (1 / ∏ v ∈ Finset.univ.erase u, (x u - x v))
      = ∑ u : Fin (t + 2), (A u - B u) := Finset.sum_congr rfl (fun u _ => hterm u)
    _ = (∑ u : Fin (t + 2), A u) - (∑ u : Fin (t + 2), B u) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i : Fin (t + 1), 1 / ∏ j ∈ Finset.univ.erase i, (Fin.init x i - Fin.init x j)) -
        (∑ i : Fin (t + 1), 1 / ∏ j ∈ Finset.univ.erase i, (Fin.tail x i - Fin.tail x j)) := by
          congr 1
          · rw [Fin.sum_univ_castSucc]; simp only [A, ↓reduceDIte, add_zero]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp only [Fin.castSucc_ne_last, ↓reduceDIte]
            congr 1
            symm
            refine Finset.prod_bij (fun (j : Fin (t + 1)) _ => j.castSucc) ?_ ?_ ?_ ?_
            · intro j hj; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
              exact ⟨Fin.castSucc_ne_last j, fun h => hj (Fin.castSucc_injective (t + 1) h)⟩
            · intro j₁ _ j₂ _ h; exact Fin.castSucc_injective (t + 1) h
            · intro v hv; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv
              obtain ⟨j, hj_eq⟩ := Fin.exists_castSucc_eq.mpr hv.1
              refine ⟨j, Finset.mem_erase.mpr ⟨fun h => hv.2 ?_, Finset.mem_univ _⟩, hj_eq⟩
              rw [← hj_eq, h]
            · intro j _; rfl
          · rw [Fin.sum_univ_succ]; simp only [B, ↓reduceDIte, zero_add]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp only [Fin.succ_ne_zero, ↓reduceDIte]
            congr 1
            symm
            refine Finset.prod_bij (fun (j : Fin (t + 1)) _ => j.succ) ?_ ?_ ?_ ?_
            · intro j hj; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
              exact ⟨Fin.succ_ne_zero j, fun h => hj (Fin.succ_injective (t + 1) h)⟩
            · intro j₁ _ j₂ _ h; exact Fin.succ_injective (t + 1) h
            · intro v hv; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv
              obtain ⟨j, hj_eq⟩ := Fin.eq_succ_of_ne_zero hv.1
              refine ⟨j, Finset.mem_erase.mpr ⟨fun h => hv.2 ?_, Finset.mem_univ _⟩, hj_eq.symm⟩
              rw [hj_eq, h]
            · intro j _; rfl

/-- Polynomial-free Lagrange vanishing: `D(t, x, k) = 0` for `k < t`, and `= 1` for `k = t`. -/
lemma divDiffSum_lt_and_eq :
    ∀ (t : ℕ) (x : Fin (t + 1) → 𝕜), Function.Injective x →
      (∀ k < t, divDiffSum t x k = 0) ∧ divDiffSum t x t = 1 := by
  intro t
  induction t with
  | zero =>
    intro x _; exact ⟨fun k hk => by omega, by simp [divDiffSum]⟩
  | succ t ih =>
    intro x hx
    have hinit : Function.Injective (Fin.init x) := fun i j h => Fin.castSucc_injective _ (hx h)
    have htail : Function.Injective (Fin.tail x) := fun i j h => Fin.succ_injective _ (hx h)
    have hD0 : divDiffSum (t + 1) x 0 = 0 := by
      have hrec := divDiffSum_zero_recurrence t x hx
      have hne : x 0 - x (Fin.last (t + 1)) ≠ 0 :=
        sub_ne_zero.mpr (fun h => (Fin.ext_iff.ne.mpr (by simp) :
          (0 : Fin (t + 2)) ≠ Fin.last (t + 1)) (hx h))
      have hRHS : divDiffSum t (Fin.init x) 0 - divDiffSum t (Fin.tail x) 0 = 0 := by
        cases t with
        | zero => rw [(ih _ hinit).2, (ih _ htail).2, sub_self]
        | succ t' => rw [(ih _ hinit).1 0 (by omega), (ih _ htail).1 0 (by omega), sub_self]
      rw [hRHS] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left hne
    have hlt : ∀ k < t + 1, divDiffSum (t + 1) x k = 0 := by
      intro k
      induction k with
      | zero => intro _; exact hD0
      | succ k ihk =>
        intro hk
        have hrec := divDiffSum_succ_k t x hx k
        rw [ihk (by omega), mul_zero, sub_zero, (ih _ hinit).1 k (by omega)] at hrec
        exact hrec
    refine ⟨hlt, ?_⟩
    have hrec := divDiffSum_succ_k t x hx t
    rw [hlt t (by omega), mul_zero, sub_zero, (ih _ hinit).2] at hrec
    exact hrec

/-- `hSum t x N = divDiffSum t x (t + N)` for any injective family `x`. -/
lemma hSum_eq_divDiffSum :
    ∀ (t : ℕ) (x : Fin (t + 1) → 𝕜), Function.Injective x →
      ∀ N : ℕ, hSum t x N = divDiffSum t x (t + N) := by
  intro t
  induction t with
  | zero =>
    intro x _ N; simp [hSum, divDiffSum]
  | succ t ih =>
    intro x hx N
    have hinit : Function.Injective (Fin.init x) := fun i j h => Fin.castSucc_injective _ (hx h)
    induction N with
    | zero =>
      rw [hSum_zero (t + 1) x]
      exact (divDiffSum_lt_and_eq (t + 1) x hx).2.symm
    | succ N ihN =>
      have hrec := divDiffSum_succ_k t x hx (t + 1 + N)
      have h1 : t + 1 + (N + 1) = (t + 1 + N) + 1 := by omega
      have h2 : t + (N + 1) = t + 1 + N := by omega
      calc hSum (t + 1) x (N + 1)
          = x (Fin.last (t + 1)) * hSum (t + 1) x N + hSum t (Fin.init x) (N + 1) :=
            hSum_succ_N t x N
        _ = x (Fin.last (t + 1)) * divDiffSum (t + 1) x (t + 1 + N) +
              divDiffSum t (Fin.init x) (t + 1 + N) := by
            rw [ihN, ih (Fin.init x) hinit (N + 1), h2]
        _ = divDiffSum (t + 1) x (t + 1 + (N + 1)) := by
            rw [← hrec, h1]; ring

/-- Simplex of exponent tuples `∑ r, i r ≤ N`. -/
def simplexSet (t N : ℕ) : Finset (Fin t → ℕ) :=
  (Fintype.piFinset fun _ : Fin t => Finset.range (N + 1)).filter (fun i => ∑ r : Fin t, i r ≤ N)

noncomputable def simplexSum (t : ℕ) (lam : Fin t → 𝕜) (N : ℕ) : 𝕜 :=
  ∑ i ∈ simplexSet t N, ∏ r : Fin t, (lam r) ^ (i r)

/-- Connection between `simplexSum` and `hSum` (with `x = Fin.cons 1 lam`). -/
lemma simplexSum_eq_hSum :
    ∀ (t : ℕ) (lam : Fin t → 𝕜) (N : ℕ),
      simplexSum t lam N = hSum t (Fin.cons 1 lam) N := by
  intro t
  induction t with
  | zero =>
    intro lam N
    dsimp [simplexSum, simplexSet, hSum]
    have hsub : (Fintype.piFinset fun _ : Fin 0 => Finset.range (N + 1)).filter
        (fun i => ∑ r : Fin 0, i r ≤ N) = Finset.univ := by
      ext i; simp
    rw [hsub]; simp
  | succ t ih =>
    intro lam N
    have hmaps : ∀ i ∈ simplexSet (t + 1) N, i (Fin.last t) ∈ Finset.range (N + 1) := by
      intro i hi
      rw [Finset.mem_range]
      have hle := (Finset.mem_filter.mp hi).2
      have h1 : i (Fin.last t) ≤ ∑ r : Fin (t + 1), i r :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      omega
    rw [simplexSum, ← Finset.sum_fiberwise_of_maps_to hmaps]
    have hlast_eq : (Fin.cons (1 : 𝕜) lam : Fin (t + 2) → 𝕜) (Fin.last (t + 1)) = lam (Fin.last t) :=
      (congrArg (Fin.cons (1 : 𝕜) lam)
        (Fin.ext (by simp) : Fin.last (t + 1) = (Fin.last t).succ)).trans
        (@Fin.cons_succ _ (fun _ => 𝕜) (1 : 𝕜) lam (Fin.last t))
    have hinit_eq :
        Fin.init (Fin.cons (α := fun _ => 𝕜) (1 : 𝕜) lam) =
          Fin.cons (α := fun _ => 𝕜) (1 : 𝕜) (Fin.init lam) := by
      ext r; refine Fin.cases ?_ ?_ r
      · simp [Fin.init, Fin.cons]
      · intro k; simp [Fin.init, Fin.cons]
    rw [hSum, hlast_eq, hinit_eq]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← ih (Fin.init lam) (N - j), simplexSum, Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun k _ => Fin.snoc k j) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, simplexSet, Fintype.mem_piFinset, Finset.mem_range] at hk hj ⊢
      refine ⟨⟨fun r => ?_, ?_⟩, by simp [Fin.snoc]⟩
      · refine Fin.lastCases ?_ ?_ r
        · simp [Fin.snoc, hj]
        · intro r'; simp only [Fin.snoc_castSucc]; have := hk.1 r'; omega
      · rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; omega
    · intro k₁ _ k₂ _ hEq
      ext r; have := congrFun hEq r.castSucc; simpa [Fin.snoc_castSucc] using this
    · intro i hi
      simp only [Finset.mem_filter, simplexSet, Fintype.mem_piFinset, Finset.mem_range] at hi hj ⊢
      refine ⟨Fin.init i, ⟨fun r => ?_, ?_⟩, ?_⟩
      · have hle : i r.castSucc ≤ ∑ s : Fin t, i s.castSucc :=
          Finset.single_le_sum (f := fun s : Fin t => i s.castSucc)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
        have htot := hi.1.2
        rw [Fin.sum_univ_castSucc, hi.2] at htot
        dsimp [Fin.init]; omega
      · have htot := hi.1.2
        rw [Fin.sum_univ_castSucc, hi.2] at htot
        dsimp [Fin.init]; omega
      · ext r; refine Fin.lastCases ?_ ?_ r
        · simp [Fin.snoc, hi.2]
        · intro r'; simp [Fin.snoc_castSucc, Fin.init]
    · intro k _
      rw [Fin.prod_univ_castSucc, mul_comm]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.init]

/-- Annulus of exponent tuples `M - m < ∑ r, i r ≤ M`. -/
def annulusSet (t m M : ℕ) : Finset (Fin t → ℕ) :=
  (simplexSet t M).filter (fun i => M < m + ∑ r : Fin t, i r)

/-- **Annular Cancellation**: for `m ≥ 2`, `t ≥ 1`, pairwise distinct `lam : Fin t → 𝕜`
in `μ_m \ {1}`, and any `M` with `m ≤ M + t`, the sum over `annulusSet t m M` is `0`. -/
theorem annular_cancellation {m t M : ℕ} (ht : 1 ≤ t) (hM : m ≤ M + t)
    (lam : Fin t → 𝕜) (hinj : Function.Injective lam)
    (hpow : ∀ r, (lam r) ^ m = 1) (hne1 : ∀ r, lam r ≠ 1) :
    ∑ i ∈ annulusSet t m M, ∏ r : Fin t, (lam r) ^ (i r) = 0 := by
  let x : Fin (t + 1) → 𝕜 := Fin.cons 1 lam
  have hx_inj : Function.Injective x := by
    intro u v huv
    rcases Fin.eq_zero_or_eq_succ u with rfl | ⟨u', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨v', rfl⟩
    · rfl
    · dsimp only [x] at huv; rw [Fin.cons_zero, Fin.cons_succ] at huv
      exact (hne1 v' huv.symm).elim
    · dsimp only [x] at huv; rw [Fin.cons_zero, Fin.cons_succ] at huv
      exact (hne1 u' huv).elim
    · dsimp only [x] at huv; rw [Fin.cons_succ, Fin.cons_succ] at huv
      exact congrArg Fin.succ (hinj huv)
  have hx_pow : ∀ u : Fin (t + 1), (x u) ^ m = 1 :=
    Fin.cases (by simp [x]) (fun r => by simpa [x] using hpow r)
  by_cases hMm : m ≤ M
  · have hsub : simplexSet t (M - m) ⊆ simplexSet t M := by
      intro i hi
      simp only [simplexSet, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hi ⊢
      exact ⟨fun r => by have := hi.1 r; omega, by omega⟩
    have hann : annulusSet t m M = simplexSet t M \ simplexSet t (M - m) := by
      ext i
      simp only [annulusSet, simplexSet, Finset.mem_filter, Finset.mem_sdiff, Fintype.mem_piFinset,
                 Finset.mem_range]
      constructor
      · rintro ⟨⟨hr, hle⟩, hgt⟩
        exact ⟨⟨hr, hle⟩, fun h => by omega⟩
      · rintro ⟨⟨hr, hle⟩, hnot⟩
        refine ⟨⟨hr, hle⟩, ?_⟩
        by_contra hle2; push_neg at hle2
        refine hnot ⟨fun r => ?_, by omega⟩
        have h1 : i r ≤ ∑ s : Fin t, i s :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
        omega
    rw [hann, Finset.sum_sdiff_eq_sub hsub]
    change simplexSum t lam M - simplexSum t lam (M - m) = 0
    rw [simplexSum_eq_hSum, simplexSum_eq_hSum, hSum_eq_divDiffSum t x hx_inj M,
        hSum_eq_divDiffSum t x hx_inj (M - m)]
    dsimp [divDiffSum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero (fun u _ => ?_)
    have hpow_eq : (x u) ^ (t + M) = (x u) ^ (t + (M - m)) := by
      have hadd : t + M = (t + (M - m)) + m := by omega
      rw [hadd, pow_add, hx_pow u, mul_one]
    rw [hpow_eq, sub_self]
  · have hann : annulusSet t m M = simplexSet t M := by
      ext i; simp only [annulusSet, Finset.mem_filter, and_iff_left_iff_imp]; intro _; omega
    rw [hann]
    change simplexSum t lam M = 0
    rw [simplexSum_eq_hSum, hSum_eq_divDiffSum t x hx_inj M]
    let d := t + M - m
    have hd_lt : d < t := by omega
    have hEq : divDiffSum t x (t + M) = divDiffSum t x d := by
      dsimp [divDiffSum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      have hadd : t + M = d + m := by omega
      rw [hadd, pow_add, hx_pow u, mul_one]
    rw [hEq]
    exact (divDiffSum_lt_and_eq t x hx_inj).1 d hd_lt

/-- Corollary (Simplex Cancellation for Dubuc): case `M = m - t`. -/
theorem simplex_cancellation {m t : ℕ} (ht : 1 ≤ t) (htm : t < m)
    (lam : Fin t → 𝕜) (hinj : Function.Injective lam)
    (hpow : ∀ r, (lam r) ^ m = 1) (hne1 : ∀ r, lam r ≠ 1) :
    simplexSum t lam (m - t) = 0 := by
  have hM : m ≤ (m - t) + t := by omega
  have hann : annulusSet t m (m - t) = simplexSet t (m - t) := by
    ext i; simp only [annulusSet, Finset.mem_filter, and_iff_left_iff_imp]; intro _; omega
  rw [simplexSum, ← hann]
  exact annular_cancellation ht hM lam hinj hpow hne1

/-! ### 2. Two Universal `finrank` Lemmas (Replacing Cayley–Hamilton, Quotients, and `minpoly`) -/

/-- Quotient-free Cayley–Hamilton substitute on `B / A`:
if `A ≤ B` are `T`-invariant, every orbit `(T^[k]) x` (`x ∈ B`) lies in
`A ⊔ span {T^j x | j < finrank B - finrank A}`. -/
lemma span_orbit_mod_subspace {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (T : V →ₗ[𝕜] V) (A B : Submodule 𝕜 V) (hAB : A ≤ B)
    (hTA : ∀ x ∈ A, T x ∈ A) (hTB : ∀ x ∈ B, T x ∈ B)
    (x : V) (hx : x ∈ B) (k : ℕ) :
    (T^[k]) x ∈
      A ⊔ Submodule.span 𝕜 {y | ∃ j < Module.finrank 𝕜 B - Module.finrank 𝕜 A, y = (T^[j]) x} := by
  let d := Module.finrank 𝕜 B - Module.finrank 𝕜 A
  let S : ℕ → Submodule 𝕜 V := fun t =>
    A ⊔ Submodule.span 𝕜 {y | ∃ j < t, y = (T^[j]) x}
  have hS0 : S 0 = A := by simp [S]
  have hSmono : ∀ t, S t ≤ S (t + 1) := fun t =>
    sup_le_sup_left (Submodule.span_mono (by rintro _ ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩)) A
  have hSB : ∀ t, S t ≤ B := by
    intro t
    refine sup_le hAB (Submodule.span_le.mpr ?_)
    rintro _ ⟨j, hj_lt, rfl⟩
    clear hj_lt
    induction j with
    | zero => exact hx
    | succ j ihj => rw [Function.iterate_succ_apply']; exact hTB _ ihj
  have hTstep : ∀ t (v : V), v ∈ S t → T v ∈ S (t + 1) := by
    intro t v hv
    rcases Submodule.mem_sup.mp hv with ⟨a, ha, b, hb, rfl⟩
    clear hv
    rw [map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hTA a ha)) (Submodule.mem_sup_right ?_)
    induction hb using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨j, hj, rfl⟩
      rw [← Function.iterate_succ_apply' T j x]
      exact Submodule.subset_span ⟨j + 1, by omega, rfl⟩
    | zero => simp
    | add _ _ _ _ ih1 ih2 => rw [map_add]; exact Submodule.add_mem _ ih1 ih2
    | smul c _ _ ih => rw [map_smul]; exact Submodule.smul_mem _ c ih
  by_cases hstab : ∃ t < d, S t = S (t + 1)
  · obtain ⟨t, htd, hEq⟩ := hstab
    have hinv : ∀ v ∈ S t, T v ∈ S t := fun v hv => hEq ▸ hTstep t v hv
    have hx_in : x ∈ S t := by
      have hx1 : x ∈ S (t + 1) :=
        Submodule.mem_sup_right (Submodule.subset_span ⟨0, Nat.zero_lt_succ t, rfl⟩)
      exact hEq ▸ hx1
    have hle : S t ≤ S d := by
      have hrec : ∀ m, t ≤ m → S t ≤ S m := by
        intro m hm
        induction m with
        | zero =>
          have ht0 : t = 0 := by omega
          rw [ht0]
        | succ m ihm =>
          rcases eq_or_lt_of_le hm with rfl | hlt
          · exact le_rfl
          · exact le_trans (ihm (by omega)) (hSmono m)
      exact hrec d (le_of_lt htd)
    apply hle
    induction k with
    | zero => exact hx_in
    | succ k ihk => rw [Function.iterate_succ_apply']; exact hinv _ ihk
  · push_neg at hstab
    have hgrow : ∀ m ≤ d, Module.finrank 𝕜 A + m ≤ Module.finrank 𝕜 (S m) := by
      intro m hm
      induction m with
      | zero => rw [hS0, Nat.add_zero]
      | succ m ihm =>
        have hlt : S m < S (m + 1) := lt_of_le_of_ne (hSmono m) (hstab m (by omega))
        have hf := Submodule.finrank_lt_finrank_of_lt hlt
        have := ihm (by omega)
        omega
    have hfin_ge := hgrow d le_rfl
    have hfin_le := Submodule.finrank_mono (hSB d)
    have hAB_fin := Submodule.finrank_mono hAB
    have hSd_eq_B : S d = B :=
      Submodule.eq_of_le_of_finrank_eq (hSB d) (by omega)
    have hkB : (T^[k]) x ∈ B := by
      induction k with
      | zero => exact hx
      | succ k ihk => rw [Function.iterate_succ_apply']; exact hTB _ ihk
    have hkSd : (T^[k]) x ∈ S d := by rw [hSd_eq_B]; exact hkB
    exact hkSd

/-- `minpoly`-free nilpotency bound on quotients `B / A`:
if `A ≤ B` are `T`-invariant and `T^[ℓ](B) ≤ A`, then `T^[i](B) ≤ A` for all `i ≥ finrank B - finrank A`. -/
lemma nilpotent_step_mod_subspace {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (T : V →ₗ[𝕜] V) (A B : Submodule 𝕜 V) (hAB : A ≤ B)
    (hTA : ∀ x ∈ A, T x ∈ A) (hTB : ∀ x ∈ B, T x ∈ B)
    (ℓ : ℕ) (hNil : ∀ x ∈ B, (T^[ℓ]) x ∈ A)
    (x : V) (hx : x ∈ B) (i : ℕ) (hi : Module.finrank 𝕜 B - Module.finrank 𝕜 A ≤ i) :
    (T^[i]) x ∈ A := by
  classical
  let d := Module.finrank 𝕜 B - Module.finrank 𝕜 A
  suffices hd : (T^[d]) x ∈ A by
    have hshift : i = (i - d) + d := by omega
    rw [hshift, Function.iterate_add_apply]
    generalize i - d = s
    induction s with
    | zero => exact hd
    | succ s ihs => rw [Function.iterate_succ_apply']; exact hTA _ ihs
  by_contra hnotA
  have hex : ∃ r, r < ℓ ∧ (T^[r]) x ∉ A ∧ ∀ j, r < j → (T^[j]) x ∈ A := by
    have hS : ((Finset.range ℓ).filter (fun r => (T^[r]) x ∉ A)).Nonempty := by
      refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hnotA⟩⟩
      by_contra hge; push_neg at hge
      have hshift : d = (d - ℓ) + ℓ := by omega
      have hA : (T^[d]) x ∈ A := by
        rw [hshift, Function.iterate_add_apply]
        generalize d - ℓ = s
        induction s with
        | zero => exact hNil x hx
        | succ s ihs => rw [Function.iterate_succ_apply']; exact hTA _ ihs
      exact hnotA hA
    let r := ((Finset.range ℓ).filter (fun r => (T^[r]) x ∉ A)).max' hS
    have hr_mem := Finset.max'_mem _ hS
    have hr_lt : r < ℓ := Finset.mem_range.mp (Finset.mem_filter.mp hr_mem).1
    have hr_not : (T^[r]) x ∉ A := (Finset.mem_filter.mp hr_mem).2
    refine ⟨r, hr_lt, hr_not, fun j hj => ?_⟩
    by_cases hjl : j < ℓ
    · by_contra hjnot
      have hj_le := Finset.le_max' ((Finset.range ℓ).filter (fun r => (T^[r]) x ∉ A)) j
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjl, hjnot⟩)
      omega
    · have hshift : j = (j - ℓ) + ℓ := by omega
      rw [hshift, Function.iterate_add_apply]
      generalize j - ℓ = s
      induction s with
      | zero => exact hNil x hx
      | succ s ihs => rw [Function.iterate_succ_apply']; exact hTA _ ihs
  obtain ⟨r, _, hr_not, hr_max⟩ := hex
  have hdr : d ≤ r := by
    by_contra hlt; push_neg at hlt
    exact hnotA (hr_max d hlt)
  let W : ℕ → Submodule 𝕜 V := fun k =>
    A ⊔ Submodule.span 𝕜 {y | ∃ j, 1 ≤ j ∧ j ≤ k ∧ y = (T^[r + 1 - j]) x}
  have hW0 : W 0 = A := by
    dsimp [W]; convert sup_bot_eq A
    rw [Submodule.span_eq_bot]; rintro _ ⟨j, hj1, hj0, _⟩; omega
  have hWmono : ∀ k, W k ≤ W (k + 1) := fun k =>
    sup_le_sup_left (Submodule.span_mono (by rintro _ ⟨j, h1, h2, rfl⟩; exact ⟨j, h1, by omega, rfl⟩)) A
  have hWB : ∀ k, W k ≤ B := by
    intro k
    refine sup_le hAB (Submodule.span_le.mpr ?_)
    rintro _ ⟨j, _, _, rfl⟩
    generalize r + 1 - j = m
    induction m with
    | zero => exact hx
    | succ m ihm => rw [Function.iterate_succ_apply']; exact hTB _ ihm
  have hWstrict : ∀ k ≤ r, W k < W (k + 1) := by
    intro k hk
    refine lt_of_le_of_ne (hWmono k) ?_
    intro hEq
    have hmem : (T^[r - k]) x ∈ W k := by
      rw [hEq]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨k + 1, by omega, le_rfl, by congr 1; omega⟩)
    rcases Submodule.mem_sup.mp hmem with ⟨a, ha, b, hb, hab⟩
    have hTkA : ∀ (m : ℕ) (v : V), v ∈ A → (T^[m]) v ∈ A := by
      intro m v hv
      induction m with
      | zero => exact hv
      | succ m ihm => rw [Function.iterate_succ_apply']; exact hTA _ ihm
    have hTk_linear : ∀ (m : ℕ) (u v : V), (T^[m]) (u + v) = (T^[m]) u + (T^[m]) v := by
      intro m u v
      induction m with
      | zero => rfl
      | succ m ihm => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
                          Function.iterate_succ_apply', ihm, map_add]
    have hTk_smul : ∀ (m : ℕ) (c : 𝕜) (v : V), (T^[m]) (c • v) = c • (T^[m]) v := by
      intro m c v
      induction m with
      | zero => rfl
      | succ m ihm => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihm, map_smul]
    have hTkb : (T^[k]) b ∈ A := by
      clear hab
      induction hb using Submodule.span_induction with
      | mem y hy =>
        rcases hy with ⟨j, hj1, hjk, rfl⟩
        rw [← Function.iterate_add_apply]
        exact hr_max (k + (r + 1 - j)) (by omega)
      | zero =>
        have h0 : ∀ m, (T^[m]) (0 : V) = 0 := fun m => by
          induction m with
          | zero => rfl
          | succ m ihm => rw [Function.iterate_succ_apply', ihm, map_zero]
        rw [h0]; exact Submodule.zero_mem A
      | add _ _ _ _ ih1 ih2 => rw [hTk_linear]; exact Submodule.add_mem A ih1 ih2
      | smul c _ _ ih => rw [hTk_smul]; exact Submodule.smul_mem A c ih
    have hTr : (T^[r]) x = (T^[k]) a + (T^[k]) b := by
      have hadd : r = k + (r - k) := by omega
      rw [hadd, Function.iterate_add_apply, ← hab, hTk_linear]
    exact hr_not (hTr ▸ Submodule.add_mem A (hTkA k a ha) hTkb)
  have hgrow : ∀ k ≤ r + 1, Module.finrank 𝕜 A + k ≤ Module.finrank 𝕜 (W k) := by
    intro k hk
    induction k with
    | zero => rw [hW0, Nat.add_zero]
    | succ k ihk =>
      have := Submodule.finrank_lt_finrank_of_lt (hWstrict k (by omega))
      have := ihk (by omega)
      omega
  have h1 := hgrow (r + 1) le_rfl
  have h2 := Submodule.finrank_mono (hWB (r + 1))
  omega

end Cerny.CircularDubuc
