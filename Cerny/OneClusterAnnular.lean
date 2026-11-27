import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic
import Cerny.Defs
import Cerny.WeightedPrimeCycle
import Cerny.CircularDubuc

/-!
# Module 10: One-Cluster Annular Spectral Descent and Černý Bound

This module proves the full quadratic Černý bound `(n - 1)^2` for synchronizing
one-cluster automata (`one_cluster_cerny_bound`) and deduces Dubuc's theorem for
general circular automata (`dubuc_circular_bound`) as an immediate corollary
(`ℓ = 0, C = Finset.univ`).

The spectral decomposition avoids `Module.End`, `minpoly`, `charpoly`, and
`Submodule.Quotient`, working directly with explicit linear operators
`rowAct A w`, projections `projC`/`projN`, Fitting spectral projections
`eigProj`, and the `finrank` + `annular_cancellation` lemmas from
`Cerny.CircularDubuc`.
-/

open Finset
open scoped BigOperators

namespace Cerny.OneClusterAnnular

section FittingAndOperators

variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- Row-action (pushforward) operator on `Q → ℂ` induced by a word `w`. -/
noncomputable def rowAct (A : Aut Q α) (w : List α) : (Q → ℂ) →ₗ[ℂ] (Q → ℂ) where
  toFun f q := ∑ p : Q, if A.eval p w = q then f p else 0
  map_add' f g := by
    ext q; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  map_smul' c f := by
    ext q; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp

lemma rowAct_nil (A : Aut Q α) (f : Q → ℂ) : rowAct A [] f = f := by
  ext q
  simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk]
  change (∑ p : Q, if p = q then f p else 0) = f q
  rw [Finset.sum_ite_eq']
  simp

lemma rowAct_append (A : Aut Q α) (u v : List α) (f : Q → ℂ) :
    rowAct A (u ++ v) f = rowAct A v (rowAct A u f) := by
  ext q
  simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk, Aut.eval_append]
  symm
  trans ∑ x : Q, ∑ p : Q, if A.eval p u = x ∧ A.eval x v = q then f p else 0
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs with hx
    · refine Finset.sum_congr rfl (fun p _ => by simp [hx])
    · simp [hx]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_eq_single (A.eval p u)]
    · simp
    · intro x _ hxne
      simp [hxne.symm]
    · intro habs; exact absurd (Finset.mem_univ _) habs

lemma rowAct_replicate_succ (A : Aut Q α) (a : α) (k : ℕ) (f : Q → ℂ) :
    rowAct A (List.replicate (k + 1) a) f =
      rowAct A [a] (rowAct A (List.replicate k a) f) := by
  rw [List.replicate_succ', rowAct_append]

lemma rowAct_eq_iterate (A : Aut Q α) (a : α) (k : ℕ) (f : Q → ℂ) :
    rowAct A (List.replicate k a) f = ((rowAct A [a])^[k]) f := by
  induction k with
  | zero => simp [rowAct_nil]
  | succ k ih => rw [rowAct_replicate_succ, Function.iterate_succ_apply', ih]

/-- Standard bilinear pairing on `Q → ℂ`. -/
noncomputable def dotC (f g : Q → ℂ) : ℂ := ∑ q : Q, f q * g q

/-- Indicator vector of a subset `S : Finset Q` in `Q → ℂ`. -/
noncomputable def indC (S : Finset Q) : Q → ℂ := fun q => if q ∈ S then 1 else 0

lemma dotC_rowAct_indC (A : Aut Q α) (w : List α) (f : Q → ℂ) (S : Finset Q) :
    dotC (rowAct A w f) (indC S) = dotC f (indC (A.preimage S w)) := by
  simp only [dotC, rowAct, LinearMap.coe_mk, AddHom.coe_mk, indC]
  trans ∑ q : Q, ∑ p : Q, (if A.eval p w = q then f p else 0) * (if q ∈ S then (1 : ℂ) else 0)
  · refine Finset.sum_congr rfl (fun q _ => by rw [Finset.sum_mul])
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [Aut.mem_preimage, Finset.sum_ite_eq']

lemma sum_rowAct (A : Aut Q α) (w : List α) (f : Q → ℂ) :
    ∑ q : Q, rowAct A w f q = ∑ p : Q, f p := by
  have h := dotC_rowAct_indC A w f Finset.univ
  simp only [dotC, indC, Finset.mem_univ, ↓reduceIte, mul_one, Aut.preimage_univ] at h
  exact h

/-- Primitive `m`-th root of unity `exp(2πi/m)`. -/
noncomputable def primRoot (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))

lemma primRoot_pow_eq_one {m : ℕ} (hm : 1 ≤ m) : (primRoot m) ^ m = 1 := by
  dsimp [primRoot]
  rw [← Complex.exp_nat_mul]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have harg : (m : ℂ) * (2 * ↑Real.pi * Complex.I / (m : ℂ)) = 2 * ↑Real.pi * Complex.I := by
    field_simp
  rw [harg, Complex.exp_two_pi_mul_I]

lemma primRoot_pow_injOn {m : ℕ} (hm : 1 ≤ m) :
    Set.InjOn (fun r : ℕ => (primRoot m) ^ r) (Finset.range m : Set ℕ) := by
  intro r hr s hs hEq
  simp only [Finset.coe_range, Set.mem_Iio] at hr hs
  dsimp only at hEq
  wlog hrs : r ≤ s generalizing r s
  · exact (this (r := s) (s := r) hEq.symm hs hr (le_of_not_ge hrs)).symm
  rcases eq_or_lt_of_le hrs with rfl | hlt
  · rfl
  exfalso
  have hdiff : (primRoot m) ^ (s - r) = 1 := by
    have hpow0 : (primRoot m) ^ r ≠ 0 := pow_ne_zero r (Complex.exp_ne_zero _)
    have hadd : (primRoot m) ^ s = (primRoot m) ^ r * (primRoot m) ^ (s - r) := by
      rw [← pow_add, Nat.add_sub_of_le hrs]
    rw [hadd] at hEq
    exact mul_left_cancel₀ hpow0 (by simpa using hEq.symm)
  dsimp [primRoot] at hdiff
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at hdiff
  obtain ⟨k, hk⟩ := hdiff
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2piI : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hdiv : ((s - r : ℕ) : ℂ) / (m : ℂ) = (k : ℂ) := by
    apply mul_right_cancel₀ h2piI
    calc
      (((s - r : ℕ) : ℂ) / (m : ℂ)) * (2 * ↑Real.pi * Complex.I)
          = ((s - r : ℕ) : ℂ) * (2 * ↑Real.pi * Complex.I / (m : ℂ)) := by ring
      _ = k * (2 * ↑Real.pi * Complex.I) := hk
  have hre := congrArg Complex.re hdiv
  have hre' : ((s - r : ℕ) : ℝ) / (m : ℝ) = (k : ℝ) := by
    simpa [Complex.div_ofReal_re] using hre
  have hlt1 : (0 : ℝ) < ((s - r : ℕ) : ℝ) / (m : ℝ) := by
    have : (0 : ℝ) < (s - r : ℕ) := Nat.cast_pos.mpr (by omega)
    have : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    positivity
  have hlt2 : ((s - r : ℕ) : ℝ) / (m : ℝ) < 1 := by
    rw [div_lt_one (Nat.cast_pos.mpr hm)]
    exact_mod_cast (by omega : s - r < m)
  rw [hre'] at hlt1 hlt2
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hlt1
  have hk1 : k < (1 : ℤ) := by exact_mod_cast hlt2
  omega

/-- Projection onto the cycle subspace `C`: keeps coordinates in `C`, zeroes outside `C`. -/
noncomputable def projC (C : Finset Q) : (Q → ℂ) →ₗ[ℂ] (Q → ℂ) where
  toFun f q := if q ∈ C then f q else 0
  map_add' f g := by ext q; by_cases h : q ∈ C <;> simp [h]
  map_smul' c f := by ext q; by_cases h : q ∈ C <;> simp [h]

/-- Complementary projection onto `Q \ C`. -/
noncomputable def projN (C : Finset Q) : (Q → ℂ) →ₗ[ℂ] (Q → ℂ) :=
  LinearMap.id - projC C

lemma projC_add_projN (C : Finset Q) (f : Q → ℂ) :
    projC C f + projN C f = f := by
  ext q; simp [projN]

lemma projC_comp_projC (C : Finset Q) (f : Q → ℂ) :
    projC C (projC C f) = projC C f := by
  ext q; by_cases h : q ∈ C <;> simp [projC, h]

/-- Nilpotency of `rowAct A (replicate ℓ a)` on `projN`: it maps every `f` into `range (projC C)`. -/
lemma nilpotent_projN (A : Aut Q α) (a : α) (C : Finset Q) (ℓ : ℕ)
    (hreach : ∀ q : Q, A.eval q (List.replicate ℓ a) ∈ C) (f : Q → ℂ) :
    projN C (rowAct A (List.replicate ℓ a) f) = 0 := by
  ext q
  simp only [projN, LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, Pi.zero_apply,
    sub_eq_zero]
  by_cases hq : q ∈ C
  · simp [projC, hq]
  · simp only [projC, LinearMap.coe_mk, AddHom.coe_mk, hq, ↓reduceIte,
      rowAct]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    split_ifs with heq
    · exact absurd (heq ▸ hreach p) hq
    · rfl

/-- Spectral Fitting projection onto the `(primRoot C.card)^r`-eigenspace of `rowAct A [a]`,
composed with `rowAct A (replicate ℓ a)`. -/
noncomputable def eigProj (A : Aut Q α) (a : α) (C : Finset Q) (ℓ : ℕ) (r : Fin C.card) :
    (Q → ℂ) →ₗ[ℂ] (Q → ℂ) :=
  ((1 : ℂ) / (C.card : ℂ)) •
    ∑ j : Fin C.card,
      ((primRoot C.card) ^ (C.card - j.1)) ^ r.1 •
        rowAct A (List.replicate (ℓ + j.1) a)

lemma sum_eigProj_eq_projC (A : Aut Q α) (a : α) (C : Finset Q) (ℓ : ℕ)
    (hC : 1 ≤ C.card) (f : Q → ℂ) :
    ∑ r : Fin C.card, eigProj A a C ℓ r f = rowAct A (List.replicate ℓ a) f := by
  let m := C.card
  let ζ := primRoot m
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hζm : ζ ^ m = 1 := primRoot_pow_eq_one hC
  simp only [eigProj, LinearMap.smul_apply, LinearMap.sum_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hinner : ∀ j : Fin m,
      ∑ r : Fin m, (ζ ^ (m - j.1)) ^ r.1 • rowAct A (List.replicate (ℓ + j.1) a) f =
        (if j.1 = 0 then (m : ℂ) else 0) • rowAct A (List.replicate (ℓ + j.1) a) f := by
    intro j
    rw [← Finset.sum_smul]
    congr 1
    by_cases hj0 : j.1 = 0
    · simp only [hj0, Nat.sub_zero, hζm, one_pow, ↓reduceIte, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    · simp only [hj0, ↓reduceIte]
      have hne1 : ζ ^ (m - j.1) ≠ 1 := by
        intro hEq
        have hinj := primRoot_pow_injOn hC
        have h1 : m - j.1 ∈ (Finset.range m : Set ℕ) := by
          simp only [Finset.coe_range, Set.mem_Iio]; omega
        have h0 : 0 ∈ (Finset.range m : Set ℕ) := by
          simp only [Finset.coe_range, Set.mem_Iio]; omega
        have := hinj h1 h0 (by simpa using hEq)
        omega
      have hgeom : (∑ r : Fin m, (ζ ^ (m - j.1)) ^ r.1) * (ζ ^ (m - j.1) - 1) = 0 := by
        rw [Fin.sum_univ_eq_sum_range (fun k => (ζ ^ (m - j.1)) ^ k)]
        rw [geom_sum_mul (ζ ^ (m - j.1)) m]
        have hpow : (ζ ^ (m - j.1)) ^ m = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hζm, one_pow]
        rw [hpow, sub_self]
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne1)
  trans ((1 : ℂ) / (m : ℂ)) •
      ∑ j : Fin m, (if j.1 = 0 then (m : ℂ) else 0) • rowAct A (List.replicate (ℓ + j.1) a) f
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => hinner j)
  · have hj0_ex : (⟨0, hC⟩ : Fin m) ∈ Finset.univ := Finset.mem_univ _
    rw [Finset.sum_eq_single ⟨0, hC⟩]
    · simp only [↓reduceIte, add_zero, smul_smul, one_div, inv_mul_cancel₀ hm0, one_smul]
    · intro j _ hjne
      have : j.1 ≠ 0 := fun h => hjne (Fin.ext h)
      simp [this]
    · intro habs; exact absurd hj0_ex habs

lemma rowAct_comp_eigProj (A : Aut Q α) (a : α) (C : Finset Q) (ℓ : ℕ)
    (hC : 1 ≤ C.card)
    (hper : ∀ f : Q → ℂ, rowAct A (List.replicate (ℓ + C.card) a) f =
      rowAct A (List.replicate ℓ a) f)
    (r : Fin C.card) (f : Q → ℂ) :
    rowAct A [a] (eigProj A a C ℓ r f) = ((primRoot C.card) ^ r.1) • eigProj A a C ℓ r f := by
  let m := C.card
  let ζ := primRoot m
  have hζm : ζ ^ m = 1 := primRoot_pow_eq_one hC
  simp only [eigProj, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rw [smul_comm]
  congr 1
  have hstep : ∀ j : Fin m,
      rowAct A [a] (rowAct A (List.replicate (ℓ + j.1) a) f) =
        rowAct A (List.replicate (ℓ + (j.1 + 1)) a) f := by
    intro j
    rw [← rowAct_append]
    congr 1
    rw [show ℓ + (j.1 + 1) = (ℓ + j.1) + 1 by omega, List.replicate_succ']
  have hsum_l :
      ∑ j : Fin m, ((ζ ^ (m - j.1)) ^ r.1) •
        rowAct A [a] (rowAct A (List.replicate (ℓ + j.1) a) f) =
      ∑ j : Fin m, ((ζ ^ (m - j.1)) ^ r.1) •
        rowAct A (List.replicate (ℓ + (j.1 + 1)) a) f :=
    Finset.sum_congr rfl (fun j _ => congrArg (((ζ ^ (m - j.1)) ^ r.1) • ·) (hstep j))
  change (∑ j : Fin m, ((ζ ^ (m - j.1)) ^ r.1) •
        rowAct A [a] (rowAct A (List.replicate (ℓ + j.1) a) f)) =
      (ζ ^ r.1) • ∑ j : Fin m, ((ζ ^ (m - j.1)) ^ r.1) •
        rowAct A (List.replicate (ℓ + j.1) a) f
  rw [hsum_l, Finset.smul_sum]
  -- Reindex the RHS sum by `j ↦ (j + 1) mod m`
  let e : Fin m ≃ Fin m :=
    { toFun := fun j => ⟨(j.1 + 1) % m, Nat.mod_lt _ hC⟩
      invFun := fun j => ⟨(j.1 + (m - 1)) % m, Nat.mod_lt _ hC⟩
      left_inv := fun j => Fin.ext (by
        dsimp
        rw [Nat.mod_add_mod, show j.1 + 1 + (m - 1) = j.1 + m by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt j.2])
      right_inv := fun j => Fin.ext (by
        dsimp
        rw [Nat.mod_add_mod, show j.1 + (m - 1) + 1 = j.1 + m by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt j.2]) }
  refine Fintype.sum_equiv e _ _ (fun j => ?_)
  have hj : j.1 < m := j.2
  rw [smul_smul]
  by_cases hjlast : j.1 + 1 = m
  · have he_eq : (e j).1 = 0 := by simp [e, hjlast]
    rw [he_eq, Nat.sub_zero, hjlast, hper, add_zero]
    congr 1
    have hmj : m - j.1 = 1 := by omega
    rw [hmj, pow_one, hζm, one_pow, mul_one]
  · have he_eq : (e j).1 = j.1 + 1 := by
      simp [e, Nat.mod_eq_of_lt (by omega : j.1 + 1 < m)]
    rw [he_eq]
    congr 1
    have hmj : m - j.1 = (m - (j.1 + 1)) + 1 := by omega
    rw [hmj, pow_succ', mul_pow]

end FittingAndOperators

section OneClusterHelpers

open WeightedPrimeCycle

variable {Q α : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]

lemma step_a_bijOn_cycleStates (A : Aut Q α) (a : α) :
    Set.BijOn (fun q => A.step q a) (cycleStates A a : Set Q) (cycleStates A a : Set Q) := by
  have himg := image_cycleStates_a A a
  have hmaps : Set.MapsTo (fun q => A.step q a) (cycleStates A a : Set Q) (cycleStates A a : Set Q) :=
    fun q hq => step_a_mem_cycleStates A a hq
  have hsurj : Set.SurjOn (fun q => A.step q a) (cycleStates A a : Set Q) (cycleStates A a : Set Q) := by
    intro y hy
    rw [← himg] at hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
    exact ⟨x, hx, by simpa [Aut.eval] using hxy⟩
  have hinj : Set.InjOn (fun q => A.step q a) (cycleStates A a : Set Q) := by
    let f : cycleStates A a → cycleStates A a :=
      fun q => ⟨A.step q.1 a, step_a_mem_cycleStates A a q.2⟩
    have hf_surj : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := hsurj hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hf_inj : Function.Injective f := (Finite.injective_iff_surjective).mpr hf_surj
    intro x hx y hy hxy
    exact congrArg Subtype.val (hf_inj (Subtype.ext hxy : f ⟨x, hx⟩ = f ⟨y, hy⟩))
  exact ⟨hmaps, hinj, hsurj⟩

lemma rowAct_a_indC (A : Aut Q α) (a : α) :
    rowAct A [a] (indC (cycleStates A a)) = indC (cycleStates A a) := by
  have hbij := step_a_bijOn_cycleStates A a
  ext q
  simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk, indC, Aut.eval, List.foldl_cons,
    List.foldl_nil]
  by_cases hq : q ∈ cycleStates A a
  · simp only [hq, ↓reduceIte]
    obtain ⟨p₀, hp₀C, hp₀eq⟩ := hbij.surjOn hq
    have hp₀C' : p₀ ∈ cycleStates A a := hp₀C
    rw [Finset.sum_eq_single p₀]
    · simp [hp₀eq, hp₀C']
    · intro p _ hpne
      split_ifs with heq
      · by_cases hpC : p ∈ cycleStates A a
        · exact absurd (hbij.injOn hpC hp₀C (heq.trans hp₀eq.symm)) hpne
        · simp [hpC]
      · simp [heq]
    · intro habs; exact absurd (Finset.mem_univ p₀) habs
  · simp only [hq, ↓reduceIte]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    split_ifs with heq
    · by_cases hpC : p ∈ cycleStates A a
      · exact absurd (heq ▸ step_a_mem_cycleStates A a hpC) hq
      · simp [hpC]
    · simp [heq]

lemma rowAct_replicate_indC (A : Aut Q α) (a : α) (k : ℕ) :
    rowAct A (List.replicate k a) (indC (cycleStates A a)) = indC (cycleStates A a) := by
  induction k with
  | zero => simp [rowAct_nil]
  | succ k ih => rw [rowAct_replicate_succ, ih, rowAct_a_indC]

lemma eval_replicate_mem_cycleStates_of_mem (A : Aut Q α) (a : α)
    {c : Q} (hc : c ∈ cycleStates A a) (k : ℕ) :
    A.eval c (List.replicate k a) ∈ cycleStates A a := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [List.replicate_succ', Aut.eval_append]
    exact step_a_mem_cycleStates A a ih

lemma eval_replicate_injOn_cycleStates (A : Aut Q α) (a : α) (k : ℕ) :
    Set.InjOn (fun c => A.eval c (List.replicate k a)) (cycleStates A a : Set Q) := by
  have h1 := (step_a_bijOn_cycleStates A a).injOn
  induction k with
  | zero =>
    intro x _ y _ hxy
    simpa [Aut.eval] using hxy
  | succ k ih =>
    intro x hx y hy hxy
    dsimp only at hxy
    rw [List.replicate_succ', Aut.eval_append, Aut.eval_append] at hxy
    have hx' := eval_replicate_mem_cycleStates_of_mem A a hx k
    have hy' := eval_replicate_mem_cycleStates_of_mem A a hy k
    exact ih hx hy (h1 hx' hy' hxy)

lemma eval_replicate_card_eq_self (A : Aut Q α) (a : α)
    (h1c : IsOneCluster A a) {c : Q} (hc : c ∈ cycleStates A a) :
    A.eval c (List.replicate (cycleStates A a).card a) = c := by
  let C := cycleStates A a
  let m := C.card
  have hm_pos : 1 ≤ m := (cycleStates_nonempty A a).card_pos
  have hbij := one_cluster_cycle_bij A a h1c hc
  have hm_mem : A.eval c (List.replicate m a) ∈ C :=
    eval_replicate_mem_cycleStates_of_mem A a hc m
  obtain ⟨j, hj, hjeq⟩ := hbij.surjOn hm_mem
  rw [Finset.coe_range, Set.mem_Iio] at hj
  dsimp only at hjeq
  by_cases hj0 : j = 0
  · subst hj0; simpa [Aut.eval] using hjeq.symm
  · exfalso
    have hcomm : A.eval c (List.replicate m a) =
        A.eval (A.eval c (List.replicate (m - j) a)) (List.replicate j a) := by
      rw [← Aut.eval_append, ← List.replicate_add, Nat.sub_add_cancel (le_of_lt hj)]
    rw [hcomm] at hjeq
    have hinj := eval_replicate_injOn_cycleStates A a j
    have hmj_mem : A.eval c (List.replicate (m - j) a) ∈ C :=
      eval_replicate_mem_cycleStates_of_mem A a hc (m - j)
    have hmj_eq : A.eval c (List.replicate (m - j) a) = A.eval c (List.replicate 0 a) := by
      simpa [Aut.eval] using hinj hmj_mem hc hjeq.symm
    have h0_mem : 0 ∈ (Finset.range m : Set ℕ) := by
      simp only [Finset.coe_range, Set.mem_Iio]; exact hm_pos
    have hmj_range : m - j ∈ (Finset.range m : Set ℕ) := by
      simp only [Finset.coe_range, Set.mem_Iio]
      dsimp only [m] at hj ⊢; omega
    have := hbij.injOn hmj_range h0_mem hmj_eq
    dsimp only [m] at this
    exact absurd this (Nat.sub_ne_zero_of_lt hj)

lemma rowAct_replicate_period (A : Aut Q α) (a : α) (h1c : IsOneCluster A a) (f : Q → ℂ) :
    rowAct A (List.replicate (cycleLevel A a + (cycleStates A a).card) a) f =
      rowAct A (List.replicate (cycleLevel A a) a) f := by
  ext q
  simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hmem : A.eval p (List.replicate (cycleLevel A a) a) ∈ cycleStates A a :=
    eval_replicate_mem_cycleStates A a p 0
  have heq : A.eval p (List.replicate (cycleLevel A a + (cycleStates A a).card) a) =
      A.eval p (List.replicate (cycleLevel A a) a) := by
    rw [List.replicate_add, Aut.eval_append, eval_replicate_card_eq_self A a h1c hmem]
  rw [heq]

theorem one_cluster_m_eq_one_bound (A : Aut Q α) (a : α)
    (hm1 : (cycleStates A a).card = 1) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp hm1
  refine ⟨List.replicate (cycleLevel A a) a, ?_, ?_⟩
  · rw [Aut.isSyncWord_iff_exists_eval_eq]
    refine ⟨c₀, fun q => ?_⟩
    have hmem : A.eval q (List.replicate (cycleLevel A a) a) ∈ cycleStates A a :=
      eval_replicate_mem_cycleStates A a q 0
    rwa [hc₀, Finset.mem_singleton] at hmem
  · have hℓ := cycleLevel_le A a
    rw [hm1] at hℓ
    have hn : 1 ≤ Fintype.card Q := Fintype.card_pos
    have hsq : Fintype.card Q - 1 ≤ (Fintype.card Q - 1) ^ 2 := by nlinarith
    simp only [List.length_replicate]
    omega

lemma rowAct_replicate_period_of_mem (A : Aut Q α) (a : α) (h1c : IsOneCluster A a)
    {f : Q → ℂ} (hf : f ∈ LinearMap.range (projC (cycleStates A a))) :
    rowAct A (List.replicate (cycleStates A a).card a) f = f := by
  rcases hf with ⟨g, rfl⟩
  ext q
  simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk, projC]
  by_cases hq : q ∈ cycleStates A a
  · simp only [hq, ↓reduceIte]
    rw [Finset.sum_eq_single q]
    · simp [hq, eval_replicate_card_eq_self A a h1c hq]
    · intro p _ hpne
      split_ifs with heq hpC
      · have h1 := eval_replicate_card_eq_self A a h1c hpC
        rw [h1] at heq
        exact absurd heq hpne
      · rfl
      · rfl
    · intro habs; exact absurd (Finset.mem_univ q) habs
  · simp only [hq, ↓reduceIte]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    split_ifs with heq hpC
    · have h1 := eval_replicate_card_eq_self A a h1c hpC
      rw [h1] at heq
      exact absurd (heq ▸ hpC) hq
    · rfl
    · rfl

lemma rowAct_a_mem_projC (A : Aut Q α) (a : α)
    {f : Q → ℂ} (hf : f ∈ LinearMap.range (projC (cycleStates A a))) :
    rowAct A [a] f ∈ LinearMap.range (projC (cycleStates A a)) := by
  refine ⟨rowAct A [a] f, ?_⟩
  rcases hf with ⟨g, rfl⟩
  ext q
  simp only [projC, LinearMap.coe_mk, AddHom.coe_mk, rowAct, Aut.eval, List.foldl_cons,
    List.foldl_nil]
  by_cases hq : q ∈ cycleStates A a
  · simp [hq]
  · simp only [hq, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero (fun p _ => ?_)
    split_ifs with heq
    · by_cases hpC : p ∈ cycleStates A a
      · exact absurd (heq ▸ step_a_mem_cycleStates A a hpC) hq
      · simp [hpC]
    · simp [heq]

lemma finrank_range_projC (C : Finset Q) :
    Module.finrank ℂ (LinearMap.range (projC C)) = C.card := by
  let e : LinearMap.range (projC C) ≃ₗ[ℂ] (C → ℂ) :=
    { toFun := fun ⟨f, _⟩ q => f q.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun h => ⟨fun q => if hq : q ∈ C then h ⟨q, hq⟩ else 0,
        ⟨fun q => if hq : q ∈ C then h ⟨q, hq⟩ else 0, by
          ext q; by_cases hq : q ∈ C <;> simp [projC, hq]⟩⟩
      left_inv := by
        rintro ⟨f, g, rfl⟩
        ext q
        by_cases hq : q ∈ C <;> simp [projC, hq]
      right_inv := by
        intro h; ext ⟨q, hq⟩; simp [hq] }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

lemma eigProj_zero_mem_span (A : Aut Q α) (a : α) (h1c : IsOneCluster A a) (f : Q → ℂ) :
    eigProj A a (cycleStates A a) (cycleLevel A a)
      ⟨0, (cycleStates_nonempty A a).card_pos⟩ f =
      ((∑ p : Q, f p) / ((cycleStates A a).card : ℂ)) • indC (cycleStates A a) := by
  let C := cycleStates A a
  let m := C.card
  let ℓ := cycleLevel A a
  have hm_pos : 1 ≤ m := (cycleStates_nonempty A a).card_pos
  ext q
  simp only [eigProj, LinearMap.smul_apply, LinearMap.sum_apply, pow_zero,
    one_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, indC]
  change (1 / (m : ℂ)) * ∑ j : Fin m, (rowAct A (List.replicate (ℓ + j.1) a) f) q =
    ((∑ p : Q, f p) / (m : ℂ)) * (if q ∈ C then 1 else 0)
  by_cases hq : q ∈ C
  · simp only [hq, ↓reduceIte, mul_one, one_div, div_eq_inv_mul]
    congr 1
    simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hp_mem : A.eval p (List.replicate ℓ a) ∈ C :=
      eval_replicate_mem_cycleStates A a p 0
    have hbij := one_cluster_cycle_bij A a h1c hp_mem
    obtain ⟨j₀, hj₀, hj₀_eq⟩ := hbij.surjOn hq
    rw [Finset.coe_range, Set.mem_Iio] at hj₀
    dsimp only at hj₀_eq
    rw [Finset.sum_eq_single ⟨j₀, hj₀⟩]
    · have heq : A.eval p (List.replicate (ℓ + j₀) a) = q := by
        rw [List.replicate_add, Aut.eval_append, hj₀_eq]
      simp [heq]
    · intro j _ hjne
      split_ifs with heq
      · have heq' : A.eval (A.eval p (List.replicate ℓ a)) (List.replicate j.1 a) =
            A.eval (A.eval p (List.replicate ℓ a)) (List.replicate j₀ a) := by
          rw [← Aut.eval_append, ← List.replicate_add, heq, hj₀_eq]
        have hj_mem : j.1 ∈ (Finset.range m : Set ℕ) := by simp [j.2]
        have hj₀_mem : j₀ ∈ (Finset.range m : Set ℕ) := by
          simp only [Finset.coe_range, Set.mem_Iio]; exact hj₀
        exact absurd (Fin.ext (hbij.injOn hj_mem hj₀_mem heq')) hjne
      · rfl
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · simp only [hq, ↓reduceIte, mul_zero, mul_eq_zero]
    right
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    split_ifs with heq
    · have hp_mem : A.eval p (List.replicate (ℓ + j.1) a) ∈ C :=
        eval_replicate_mem_cycleStates A a p j.1
      exact absurd (heq ▸ hp_mem) hq
    · simp [heq]

end OneClusterHelpers

section AnnularProof

open WeightedPrimeCycle CircularDubuc

variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

lemma primRoot_pow_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (fun r : Fin m => (primRoot m) ^ r.val) := by
  intro r₁ r₂ hEq
  have hinj := primRoot_pow_injOn hm
  have h1 : r₁.val ∈ (Finset.range m : Set ℕ) := by simp [r₁.isLt]
  have h2 : r₂.val ∈ (Finset.range m : Set ℕ) := by simp [r₂.isLt]
  exact Fin.ext (hinj h1 h2 hEq)

lemma rowAct_comp_eigProj_iter (A : Aut Q α) (a : α) (C : Finset Q) (ℓ : ℕ)
    (hC : 1 ≤ C.card)
    (hper : ∀ f : Q → ℂ, rowAct A (List.replicate (ℓ + C.card) a) f =
      rowAct A (List.replicate ℓ a) f)
    (r : Fin C.card) (k : ℕ) (f : Q → ℂ) :
    rowAct A (List.replicate k a) (eigProj A a C ℓ r f) =
      ((primRoot C.card) ^ r.val) ^ k • eigProj A a C ℓ r f := by
  rw [rowAct_eq_iterate]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, rowAct_comp_eigProj A a C ℓ hC hper r f,
        smul_smul, mul_comm, ← pow_succ']

/-- Word chain `b 0 · a^(i 0) · ... · b (p-1) · a^(i (p-1))`. -/
def wordChain (a : α) : (p : ℕ) → (Fin p → α) → (Fin p → ℕ) → List α
  | 0, _, _ => []
  | p + 1, b, i =>
      wordChain a p (Fin.init b) (Fin.init i) ++
        (b (Fin.last p) :: List.replicate (i (Fin.last p)) a)

lemma wordChain_length (a : α) :
    ∀ (p : ℕ) (b : Fin p → α) (i : Fin p → ℕ),
      (wordChain a p b i).length = p + ∑ r : Fin p, i r := by
  intro p
  induction p with
  | zero => intro _ _; simp [wordChain]
  | succ p ih =>
    intro b i
    simp only [wordChain, List.length_append, List.length_cons, List.length_replicate,
               ih (Fin.init b) (Fin.init i), Fin.sum_univ_castSucc]
    dsimp [Fin.init]
    omega

lemma wordChain_countP_ne [DecidableEq α] (a : α) :
    ∀ (p : ℕ) (b : Fin p → α) (i : Fin p → ℕ),
      (wordChain a p b i).countP (fun x => decide (x ≠ a)) ≤ p := by
  intro p
  induction p with
  | zero => intro _ _; simp [wordChain]
  | succ p ih =>
    intro b i
    simp only [wordChain, List.countP_append, List.countP_cons, List.countP_replicate]
    have hrep : (if decide (a ≠ a) then i (Fin.last p) else 0) = 0 := by simp
    rw [hrep, zero_add]
    have h1 := ih (Fin.init b) (Fin.init i)
    by_cases hba : b (Fin.last p) = a
    · simp [hba, ne_eq] at h1 ⊢; exact Nat.le_succ_of_le h1
    · simp [hba, ne_eq] at h1 ⊢; omega

lemma rowAct_wordChain_succ (A : Aut Q α) (a : α) (p : ℕ)
    (b : Fin (p + 1) → α) (i : Fin (p + 1) → ℕ) (x : Q → ℂ) :
    rowAct A (wordChain a (p + 1) b i) x =
      ((rowAct A [a])^[i (Fin.last p)])
        (rowAct A [b (Fin.last p)] (rowAct A (wordChain a p (Fin.init b) (Fin.init i)) x)) := by
  have hcons : b (Fin.last p) :: List.replicate (i (Fin.last p)) a =
      [b (Fin.last p)] ++ List.replicate (i (Fin.last p)) a := rfl
  rw [wordChain, hcons, rowAct_append, rowAct_append, rowAct_eq_iterate]

/-- Fitting projection onto `V_C` along `V_N`, using `ℓ' = (ℓ / m + 1) * m ≥ ℓ`. -/
noncomputable def fitProjC (A : Aut Q α) (a : α) (ℓ' : ℕ) : (Q → ℂ) →ₗ[ℂ] (Q → ℂ) :=
  rowAct A (List.replicate ℓ' a)

/-- Fitting projection onto `V_N` along `V_C`. -/
noncomputable def fitProjN (A : Aut Q α) (a : α) (ℓ' : ℕ) : (Q → ℂ) →ₗ[ℂ] (Q → ℂ) :=
  LinearMap.id - fitProjC A a ℓ'

/-- Operators of the Fitting resolution of identity indexed by `Option (Fin C.card)`:
`none ↦ fitProjN`, `some r ↦ eigProj r`. -/
noncomputable def optProj (A : Aut Q α) (a : α) (C : Finset Q) (ℓ' : ℕ) :
    Option (Fin C.card) → (Q → ℂ) →ₗ[ℂ] (Q → ℂ)
  | none => fitProjN A a ℓ'
  | some r => eigProj A a C ℓ' r

lemma sum_optProj_eq_id (A : Aut Q α) (a : α) (C : Finset Q) (ℓ' : ℕ) (hm : 1 ≤ C.card) :
    ∑ o : Option (Fin C.card), optProj A a C ℓ' o = LinearMap.id := by
  rw [Fintype.sum_option]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.add_apply, LinearMap.sum_apply, optProj, fitProjN, fitProjC,
    LinearMap.sub_apply, LinearMap.id_apply]
  rw [sum_eigProj_eq_projC A a C ℓ' hm f, sub_add_cancel]

/-- Partial branch vector for spectral path `σ : Fin p → Option (Fin C.card)`. -/
noncomputable def branchVec (A : Aut Q α) (a : α) (C : Finset Q) (ℓ' : ℕ) :
    (p : ℕ) → (Fin p → α) → (Fin p → ℕ) → (Fin p → Option (Fin C.card)) → (Q → ℂ) → (Q → ℂ)
  | 0, _, _, _, v => v
  | p + 1, b, i, σ, v =>
      ((rowAct A [a])^[i (Fin.last p)])
        (optProj A a C ℓ' (σ (Fin.last p))
          (rowAct A [b (Fin.last p)]
            (branchVec A a C ℓ' p (Fin.init b) (Fin.init i) (Fin.init σ) v)))

/-- Complete expansion of `rowAct A (wordChain a p b i) v` into spectral branches. -/
lemma rowAct_wordChain_eq_sum_branch (A : Aut Q α) (a : α) (C : Finset Q) (ℓ' : ℕ)
    (hm : 1 ≤ C.card) :
    ∀ (p : ℕ) (b : Fin p → α) (i : Fin p → ℕ) (v : Q → ℂ),
      rowAct A (wordChain a p b i) v =
        ∑ σ : Fin p → Option (Fin C.card), branchVec A a C ℓ' p b i σ v := by
  intro p
  induction p with
  | zero =>
    intro b i v
    simp [wordChain, rowAct_nil, branchVec]
  | succ p ih =>
    intro b i v
    rw [rowAct_wordChain_succ, ih (Fin.init b) (Fin.init i) v]
    have hsplit : ∀ (f : (Fin (p + 1) → Option (Fin C.card)) → (Q → ℂ)),
        ∑ σ : Fin (p + 1) → Option (Fin C.card), f σ =
        ∑ σ' : Fin p → Option (Fin C.card), ∑ o : Option (Fin C.card), f (Fin.snoc σ' o) := by
      intro f
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv
        { toFun := fun σ => (Fin.init σ, σ (Fin.last p))
          invFun := fun p' => Fin.snoc p'.1 p'.2
          left_inv := fun σ => Fin.snoc_init_self σ
          right_inv := fun ⟨σ', o⟩ => by ext <;> simp [Fin.init, Fin.snoc] } _ _ ?_
      intro σ; simp [Fin.snoc_init_self]
    rw [hsplit]
    have hlin_it : ∀ (k : ℕ) (x : Q → ℂ),
        ((rowAct A [a])^[k]) x = rowAct A (List.replicate k a) x :=
      fun k x => (rowAct_eq_iterate A a k x).symm
    simp only [branchVec, Fin.init_snoc, Fin.snoc_last, hlin_it]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun σ' _ => ?_)
    rw [← map_sum]
    congr 1
    have hsum_o := congrArg (fun L : (Q → ℂ) →ₗ[ℂ] (Q → ℂ) =>
      L (rowAct A [b (Fin.last p)] (branchVec A a C ℓ' p (Fin.init b) (Fin.init i) σ' v)))
      (sum_optProj_eq_id A a C ℓ' hm)
    simpa [LinearMap.coe_sum, Finset.sum_apply] using hsum_o.symm

/-- One-dimensionality of `LinearMap.range (eigProj A a C ℓ' r)` when `a` acts transitively
as a single `m`-cycle on `C`. -/
lemma eigProj_range_le_of_mem_ne_zero [Nonempty Q] (A : Aut Q α) (a : α)
    (h1c : IsOneCluster A a) (ℓ' : ℕ) (hℓ' : cycleLevel A a ≤ ℓ')
    (r : Fin (cycleStates A a).card) (W : Submodule ℂ (Q → ℂ))
    {x₀ : Q → ℂ} (hx₀_rng : x₀ ∈ LinearMap.range (eigProj A a (cycleStates A a) ℓ' r))
    (hx₀_ne : x₀ ≠ 0) (hx₀_W : x₀ ∈ W) :
    LinearMap.range (eigProj A a (cycleStates A a) ℓ' r) ≤ W := by
  let C := cycleStates A a
  let m := C.card
  let ℓ := cycleLevel A a
  have hm : 1 ≤ m := (cycleStates_nonempty A a).card_pos
  have hper : ∀ f : Q → ℂ, rowAct A (List.replicate (ℓ' + m) a) f =
      rowAct A (List.replicate ℓ' a) f := by
    intro f
    have hsp1 : ℓ' + m = (ℓ' - ℓ) + (ℓ + m) := by omega
    have hsp2 : ℓ' = (ℓ' - ℓ) + ℓ := by omega
    rw [hsp1, List.replicate_add, rowAct_append,
        rowAct_replicate_period A a h1c, ← rowAct_append, ← List.replicate_add, ← hsp2]
  obtain ⟨c₀, hc₀C⟩ : C.Nonempty := cycleStates_nonempty A a
  have hchar : ∀ y ∈ LinearMap.range (eigProj A a C ℓ' r),
      (∀ q ∉ C, y q = 0) ∧
      (∀ j : ℕ, y (A.eval c₀ (List.replicate j a)) =
        ((primRoot m) ^ r.val)⁻¹ ^ j * y c₀) := by
    rintro y ⟨u, rfl⟩
    have hsupp : ∀ q ∉ C, eigProj A a C ℓ' r u q = 0 := by
      intro q hq
      simp only [eigProj, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      suffices h0 : ∀ j : Fin m, (rowAct A (List.replicate (ℓ' + j.1) a) u) q = 0 by
        rw [Finset.sum_eq_zero (fun j _ => by rw [h0 j, mul_zero]), mul_zero]
      intro j
      simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk]
      refine Finset.sum_eq_zero (fun p _ => ?_)
      split_ifs with heq
      · have hsplit : ℓ' + j.1 = ℓ + ((ℓ' - ℓ) + j.1) := by omega
        have hinC : A.eval p (List.replicate (ℓ' + j.1) a) ∈ C := by
          rw [hsplit]
          exact eval_replicate_mem_cycleStates A a p ((ℓ' - ℓ) + j.1)
        exact absurd (heq ▸ hinC) hq
      · rfl
    refine ⟨hsupp, fun j => ?_⟩
    have hact := congrArg (fun f : Q → ℂ => f (A.eval c₀ (List.replicate j a)))
      (rowAct_comp_eigProj_iter A a C ℓ' hm hper r j u)
    simp only [Pi.smul_apply, smul_eq_mul] at hact
    have hbij_j := eval_replicate_injOn_cycleStates A a j
    have hrow_eq : rowAct A (List.replicate j a) (eigProj A a C ℓ' r u)
        (A.eval c₀ (List.replicate j a)) = eigProj A a C ℓ' r u c₀ := by
      simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single c₀]
      · simp
      · intro p _ hpne
        split_ifs with heq
        · by_cases hpC : p ∈ C
          · exact absurd (hbij_j hpC hc₀C heq) hpne
          · exact hsupp p hpC
        · rfl
      · intro habs; exact absurd (Finset.mem_univ c₀) habs
    rw [hrow_eq] at hact
    have hroot_ne : ((primRoot m) ^ r.val) ^ j ≠ 0 := by
      refine pow_ne_zero j (pow_ne_zero r.val ?_)
      intro h0
      have := primRoot_pow_eq_one hm
      rw [h0, zero_pow (by omega)] at this
      exact zero_ne_one this
    rw [inv_pow]
    apply mul_left_cancel₀ hroot_ne
    rw [← mul_assoc, mul_inv_cancel₀ hroot_ne, one_mul, hact]
  have hx₀_c0 : x₀ c₀ ≠ 0 := by
    intro h0
    apply hx₀_ne
    ext q
    by_cases hqC : q ∈ C
    · have hbij := one_cluster_cycle_bij A a h1c hc₀C
      obtain ⟨j, _, rfl⟩ := hbij.surjOn hqC
      dsimp only
      rw [(hchar x₀ hx₀_rng).2 j, h0, mul_zero]; rfl
    · exact (hchar x₀ hx₀_rng).1 q hqC
  intro y hy
  have hy_eq : y = (y c₀ / x₀ c₀) • x₀ := by
    ext q
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hqC : q ∈ C
    · have hbij := one_cluster_cycle_bij A a h1c hc₀C
      obtain ⟨j, _, rfl⟩ := hbij.surjOn hqC
      dsimp only
      rw [(hchar y hy).2 j, (hchar x₀ hx₀_rng).2 j]
      field_simp [hx₀_c0]
    · rw [(hchar y hy).1 q hqC, (hchar x₀ hx₀_rng).1 q hqC, mul_zero]
  rw [hy_eq]
  exact Submodule.smul_mem W _ hx₀_W

/-- Per-branch annular cancellation lemma for fixed `σ : Fin p → Option (Fin C.card)`. -/
lemma branch_annular_sum_eq_zero [Nonempty Q] (A : Aut Q α) (a : α)
    (h1c : IsOneCluster A a) (ℓ' p : ℕ) (hℓ' : cycleLevel A a ≤ ℓ')
    (hm : 2 ≤ (cycleStates A a).card) (hp1 : 1 ≤ p) (hp_lt : p < Fintype.card Q)
    (U : ℕ → Submodule ℂ (Q → ℂ))
    (hU0 : U 0 = Submodule.span ℂ {indC (cycleStates A a)})
    (hU_mono : ∀ r, U r ≤ U (r + 1))
    (hU_T : ∀ r x, x ∈ U r → rowAct A [a] x ∈ U r)
    (hU_step : ∀ r (b_let : α) x, x ∈ U r → rowAct A [b_let] x ∈ U (r + 1))
    (ψ : (Q → ℂ) →ₗ[ℂ] ℂ)
    (hψ_kill : ∀ x ∈ U (p - 1), ψ x = 0)
    (hψ_N : ∀ x ∈ LinearMap.range (fitProjN A a ℓ'), ψ x = 0)
    (hVN_dim : Module.finrank ℂ (LinearMap.range (fitProjN A a ℓ')) =
      Fintype.card Q - (cycleStates A a).card)
    (hfit_idem : ∀ u : Q → ℂ, fitProjC A a ℓ' (fitProjC A a ℓ' u) = fitProjC A a ℓ' u)
    (hE0_U0 : ∀ x, eigProj A a (cycleStates A a) ℓ' ⟨0, by omega⟩ x ∈ U 0)
    (b : Fin p → α) (σ : Fin p → Option (Fin (cycleStates A a).card)) :
    ∑ i ∈ CircularDubuc.annulusSet p (cycleStates A a).card (Fintype.card Q - p),
      ψ (branchVec A a (cycleStates A a) ℓ' p b i σ (indC (cycleStates A a))) = 0 := by
  classical
  let C := cycleStates A a
  let m := C.card
  let ℓ := cycleLevel A a
  let n := Fintype.card Q
  let D := n - p
  let T := rowAct A [a]
  let VN := LinearMap.range (fitProjN A a ℓ')
  let UN : ℕ → Submodule ℂ (Q → ℂ) := fun r => U r ⊓ VN
  have hper : ∀ f : Q → ℂ, rowAct A (List.replicate (ℓ' + m) a) f =
      rowAct A (List.replicate ℓ' a) f := by
    intro f
    have hsp1 : ℓ' + m = (ℓ' - ℓ) + (ℓ + m) := by omega
    have hsp2 : ℓ' = (ℓ' - ℓ) + ℓ := by omega
    rw [hsp1, List.replicate_add, rowAct_append,
        rowAct_replicate_period A a h1c, ← rowAct_append, ← List.replicate_add, ← hsp2]
  have hU_Tk : ∀ r k x, x ∈ U r → (T^[k]) x ∈ U r := by
    intro r k x hx
    induction k with
    | zero => exact hx
    | succ k ihk => rw [Function.iterate_succ_apply']; exact hU_T r _ ihk
  have hU_opt : ∀ r o x, x ∈ U r → optProj A a C ℓ' o x ∈ U r := by
    intro r o x hx
    cases o with
    | none =>
      simp only [optProj, fitProjN, fitProjC, LinearMap.sub_apply, LinearMap.id_apply,
        rowAct_eq_iterate]
      exact Submodule.sub_mem _ hx (hU_Tk r _ x hx)
    | some idx =>
      simp only [optProj, eigProj, LinearMap.smul_apply, LinearMap.sum_apply]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => ?_)
      simp only [LinearMap.smul_apply, rowAct_eq_iterate]
      exact Submodule.smul_mem _ _ (hU_Tk r _ x hx)
  have hU_le : ∀ {r₁ r₂}, r₁ ≤ r₂ → U r₁ ≤ U r₂ := by
    intro r₁ r₂ hle
    induction r₂ with
    | zero =>
      have : r₁ = 0 := by omega
      subst this; exact le_rfl
    | succ r₂ ih =>
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (by omega)) (hU_mono r₂)
  let prefVec : (s : ℕ) → (hs : s ≤ p) → (Fin p → ℕ) → (Q → ℂ) :=
    fun s hs i =>
      branchVec A a C ℓ' s
        (fun k => b ⟨k.val, by omega⟩)
        (fun k => i ⟨k.val, by omega⟩)
        (fun k => σ ⟨k.val, by omega⟩)
        (indC C)
  have hpref_mem : ∀ s (hs : s ≤ p) i, prefVec s hs i ∈ U s := by
    intro s hs i
    induction s with
    | zero =>
      dsimp [prefVec, branchVec]; rw [hU0]; exact Submodule.subset_span (Set.mem_singleton _)
    | succ s ih =>
      dsimp [prefVec, branchVec]
      exact hU_Tk (s + 1) _ _ (hU_opt (s + 1) _ _ (hU_step s _ _ (ih (by omega))))
  have hdrop_kills : ∀ s (hs : 1 ≤ s) (hsp : s ≤ p) (i : Fin p → ℕ),
      prefVec s hsp i ∈ U (s - 1) → ψ (branchVec A a C ℓ' p b i σ (indC C)) = 0 := by
    intro s hs hsp i hmem
    have hprop : ∀ k (hsk : s ≤ k) (hkp : k ≤ p), prefVec k hkp i ∈ U (k - 1) := by
      intro k hsk hkp
      induction k with
      | zero => omega
      | succ k ihk =>
        rcases eq_or_lt_of_le hsk with rfl | hlt
        · exact hmem
        · dsimp [prefVec, branchVec]
          have hprev : prefVec k (by omega) i ∈ U (k - 1) := ihk (by omega) (by omega)
          have hstep1 := hU_step (k - 1) (b ⟨k, by omega⟩) _ hprev
          have heq : k - 1 + 1 = k := by omega
          rw [heq] at hstep1
          exact hU_Tk k _ _ (hU_opt k _ _ hstep1)
    have hfin := hprop p hsp le_rfl
    have heq_p : prefVec p le_rfl i = branchVec A a C ℓ' p b i σ (indC C) := by
      dsimp [prefVec]
    rw [← heq_p]
    exact hψ_kill _ hfin
  -- Case 1: last position `σ ⟨p - 1, _⟩ = none`
  by_cases hlastN : σ ⟨p - 1, by omega⟩ = none
  · refine Finset.sum_eq_zero (fun i _ => ?_)
    apply hψ_N
    have hVN_T : ∀ k x, x ∈ VN → (T^[k]) x ∈ VN := by
      intro k x ⟨u, hu⟩
      subst hu
      refine ⟨(T^[k]) u, ?_⟩
      change fitProjN A a ℓ' ((T^[k]) u) = (T^[k]) (fitProjN A a ℓ' u)
      dsimp [fitProjN, fitProjC, T]
      rw [← rowAct_eq_iterate, ← rowAct_eq_iterate, map_sub, ← rowAct_append, ← rowAct_append,
          ← List.replicate_add, ← List.replicate_add, add_comm k ℓ']
    have hmemVN : prefVec p le_rfl i ∈ VN := by
      have hp_eq : p = (p - 1) + 1 := by omega
      have hdecomp : prefVec p le_rfl i =
          (T^[i ⟨p - 1, by omega⟩])
            (optProj A a C ℓ' (σ ⟨p - 1, by omega⟩)
              (rowAct A [b ⟨p - 1, by omega⟩] (prefVec (p - 1) (by omega) i))) := by
        cases p with
        | zero => omega
        | succ q => rfl
      rw [hdecomp, hlastN]
      exact hVN_T _ _ ⟨_, rfl⟩
    have heq_p : prefVec p le_rfl i = branchVec A a C ℓ' p b i σ (indC C) := by
      dsimp [prefVec]
    rw [← heq_p]; exact hmemVN
  -- Case 2: some `s` has `σ s = some 0`
  by_cases hhit0 : ∃ s : Fin p, σ s = some ⟨0, by omega⟩
  · obtain ⟨s, hs0⟩ := hhit0
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine hdrop_kills (s.val + 1) (by omega) (by omega) i ?_
    dsimp [prefVec, branchVec]
    have h0 : optProj A a C ℓ' (σ s) (rowAct A [b s] (prefVec s.val (by omega) i)) ∈ U 0 := by
      rw [hs0]; exact hE0_U0 _
    exact hU_Tk s.val _ _ (hU_le (Nat.zero_le s.val) h0)
  push Not at hhit0
  -- Case 3: repeated eigenvalue `σ s₁ = σ s₂ = some r`
  by_cases hrep : ∃ s₁ s₂ : Fin p, s₁ < s₂ ∧ σ s₁ = σ s₂ ∧ σ s₁ ≠ none
  · obtain ⟨s₁, s₂, hlt, heqσ, hneN⟩ := hrep
    cases hσ1 : σ s₁ with
    | none => exact (hneN hσ1).elim
    | some r =>
      have hσ2 : σ s₂ = some r := heqσ.symm.trans hσ1
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_cases hz : optProj A a C ℓ' (σ s₁) (rowAct A [b s₁] (prefVec s₁.val (by omega) i)) = 0
      · refine hdrop_kills (s₁.val + 1) (by omega) (by omega) i ?_
        change (T^[i s₁]) (optProj A a C ℓ' (σ s₁)
          (rowAct A [b s₁] (prefVec s₁.val (by omega) i))) ∈ U s₁.val
        have h0' : (T^[i s₁]) 0 = 0 := by rw [← rowAct_eq_iterate, map_zero]
        rw [hz, h0']; exact Submodule.zero_mem _
      · have hle_rng : LinearMap.range (eigProj A a C ℓ' r) ≤ U (s₁.val + 1) := by
          refine eigProj_range_le_of_mem_ne_zero A a h1c ℓ' hℓ' r (U (s₁.val + 1)) ?_ hz ?_
          · rw [hσ1]; exact ⟨_, rfl⟩
          · exact hU_opt (s₁.val + 1) _ _ (hU_step s₁.val _ _ (hpref_mem s₁.val (by omega) i))
        refine hdrop_kills (s₂.val + 1) (by omega) (by omega) i ?_
        dsimp [prefVec, branchVec]
        have hin : optProj A a C ℓ' (σ s₂) (rowAct A [b s₂] (prefVec s₂.val (by omega) i)) ∈
            U s₂.val := by
          rw [hσ2]
          exact hU_le (by omega : s₁.val + 1 ≤ s₂.val) (hle_rng ⟨_, rfl⟩)
        exact hU_Tk s₂.val _ _ hin
  push Not at hrep
  -- Case 4: surviving injective branch
  let J : Finset (Fin p) := Finset.univ.filter (fun s => σ s = none)
  let K : Finset (Fin p) := Finset.univ.filter (fun s => σ s ≠ none)
  let t := K.card
  let sJ := J.card
  have hJK_sum : sJ + t = p := by
    dsimp [sJ, t, J, K]
    rw [Finset.card_filter_add_card_filter_not (fun s => σ s = none), Finset.card_fin]
  have ht1 : 1 ≤ t := by
    have hne : K.Nonempty := ⟨⟨p - 1, Nat.sub_lt hp1 Nat.zero_lt_one⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlastN⟩⟩
    exact Finset.card_pos.mpr hne
  have hm1 : 1 ≤ m := by dsimp [m, C]; omega
  let eK : Fin t ≃ K := (K.orderIsoOfFin rfl).toEquiv
  let rootAt : Fin t → Fin m := fun u =>
    match σ (eK u).1 with
    | none => ⟨0, hm1⟩
    | some r => r
  have hroot_spec : ∀ u : Fin t, σ (eK u).1 = some (rootAt u) := by
    intro u
    have hne : σ (eK u).1 ≠ none := (Finset.mem_filter.mp (eK u).2).2
    cases h : σ (eK u).1 with
    | none => exact (hne h).elim
    | some r => simp [rootAt, h]
  let lam : Fin t → ℂ := fun u => (primRoot m) ^ (rootAt u).val
  have hlam_inj : Function.Injective lam := by
    intro u₁ u₂ hEq
    have hr_eq : rootAt u₁ = rootAt u₂ := primRoot_pow_injective hm1 hEq
    have hσ_eq : σ (eK u₁).1 = σ (eK u₂).1 := by rw [hroot_spec, hroot_spec, hr_eq]
    by_contra hne
    have hne' : (eK u₁).1 ≠ (eK u₂).1 := fun h => hne (eK.injective (Subtype.ext h))
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have h0 := hrep (eK u₁).1 (eK u₂).1 hlt hσ_eq
      rw [hroot_spec] at h0; simp at h0
    · have h0 := hrep (eK u₂).1 (eK u₁).1 hgt hσ_eq.symm
      rw [hroot_spec] at h0; simp at h0
  have hlam_pow : ∀ u, (lam u) ^ m = 1 := fun u => by
    dsimp [lam]
    rw [← pow_mul, mul_comm, pow_mul, primRoot_pow_eq_one hm1, one_pow]
  have hlam_ne1 : ∀ u, lam u ≠ 1 := by
    intro u h1
    have h0 : (primRoot m) ^ (rootAt u).val =
        (primRoot m) ^ (⟨0, hm1⟩ : Fin m).val := by
      simpa [lam] using h1
    have hr0 : rootAt u = ⟨0, hm1⟩ := primRoot_pow_injective hm1 h0
    exact hhit0 (eK u).1 (by rw [hroot_spec, hr0])
  let zeroOnK : (Fin p → ℕ) → (Fin p → ℕ) := fun i s => if σ s = none then i s else 0
  have hfactor : ∀ i : Fin p → ℕ,
      branchVec A a C ℓ' p b i σ (indC C) =
        (∏ u : Fin t, (lam u) ^ (i (eK u).1)) •
          branchVec A a C ℓ' p b (zeroOnK i) σ (indC C) := by
    intro i
    have hrec : ∀ s (hs : s ≤ p),
        prefVec s hs i =
          (∏ k ∈ Finset.univ.filter (fun k : Fin p => k.val < s ∧ σ k ≠ none),
            (match σ k with
              | none => (1 : ℂ)
              | some r => ((primRoot m) ^ r.val) ^ (i k))) •
          branchVec A a C ℓ' s (fun k => b ⟨k.val, by omega⟩)
            (fun k => zeroOnK i ⟨k.val, by omega⟩) (fun k => σ ⟨k.val, by omega⟩) (indC C) := by
      intro s hs
      induction s with
      | zero => simp [prefVec, branchVec]
      | succ s ih =>
        change (T^[i ⟨s, by omega⟩]) ((optProj A a C ℓ' (σ ⟨s, by omega⟩))
          ((rowAct A [b ⟨s, by omega⟩]) (prefVec s (by omega) i))) = _
        rw [ih (by omega), map_smul, map_smul, ← rowAct_eq_iterate, map_smul]
        let idx : Fin p := ⟨s, by omega⟩
        have hflt : Finset.univ.filter (fun k : Fin p => k.val < s + 1 ∧ σ k ≠ none) =
            if σ idx ≠ none then
              insert idx (Finset.univ.filter (fun k : Fin p => k.val < s ∧ σ k ≠ none))
            else
              Finset.univ.filter (fun k : Fin p => k.val < s ∧ σ k ≠ none) := by
          by_cases hne : σ idx ≠ none
          · rw [if_pos hne]
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Fin.ext_iff, idx]
            constructor
            · rintro ⟨hlt, hσ⟩
              by_cases hk : k.val = s
              · exact Or.inl hk
              · exact Or.inr ⟨by omega, hσ⟩
            · rintro (rfl | ⟨hlt, hσ⟩)
              · exact ⟨by omega, hne⟩
              · exact ⟨by omega, hσ⟩
          · rw [if_neg hne]
            push Not at hne
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, hσ⟩
              refine ⟨?_, hσ⟩
              by_contra hge
              have hks : k = idx := Fin.ext (by dsimp [idx]; omega)
              rw [hks] at hσ; exact hσ hne
            · rintro ⟨hlt, hσ⟩; exact ⟨by omega, hσ⟩
        rw [hflt]
        cases hσs : σ idx with
        | none =>
          simp only [ne_eq, not_true_eq_false, ↓reduceIte, zeroOnK, idx, hσs, rowAct_eq_iterate,
            one_smul]
          congr 1
          dsimp [branchVec, Fin.init, Fin.last]
          rw [hσs]
          simp only [optProj, zeroOnK, hσs, ↓reduceIte]
          rfl
        | some r =>
          have hne : σ idx ≠ none := by rw [hσs]; simp
          have hnotmem : idx ∉ Finset.univ.filter (fun k : Fin p => k.val < s ∧ σ k ≠ none) := by
            simp [idx]
          simp only [hne, ↓reduceIte, Finset.prod_insert hnotmem, hσs, zeroOnK,
            show (some r = none) = False by simp, ↓reduceIte]
          have hact := rowAct_comp_eigProj_iter A a C ℓ' hm1 hper r (i idx)
            (rowAct A [b idx] (branchVec A a C ℓ' s (fun k => b ⟨k.val, by omega⟩)
              (fun k => zeroOnK i ⟨k.val, by omega⟩) (fun k => σ ⟨k.val, by omega⟩) (indC C)))
          dsimp [branchVec, Fin.init, Fin.last, optProj]
          rw [hσs]
          dsimp only
          have hact' : (rowAct A (List.replicate (i ⟨s, by omega⟩) a))
              ((eigProj A a C ℓ' r) ((rowAct A [b ⟨s, by omega⟩])
                (branchVec A a C ℓ' s (fun k => b ⟨k.val, by omega⟩)
                  (fun k => if σ ⟨k.val, by omega⟩ = none then i ⟨k.val, by omega⟩ else 0)
                  (fun k => σ ⟨k.val, by omega⟩) (indC C)))) =
              (primRoot m ^ r.val) ^ i ⟨s, by omega⟩ •
                (eigProj A a C ℓ' r) ((rowAct A [b ⟨s, by omega⟩])
                  (branchVec A a C ℓ' s (fun k => b ⟨k.val, by omega⟩)
                    (fun k => if σ ⟨k.val, by omega⟩ = none then i ⟨k.val, by omega⟩ else 0)
                    (fun k => σ ⟨k.val, by omega⟩) (indC C))) := by
            simpa [zeroOnK] using hact
          rw [hact', smul_smul, Finset.prod_insert hnotmem, hσs]
          dsimp only
          rw [mul_comm ((primRoot m ^ r.val) ^ i idx)]
          simp only [ne_eq, show (some r = none) = False by simp, ↓reduceIte,
            Function.iterate_zero_apply]
          rfl
    have hfull := hrec p le_rfl
    have heq_p : prefVec p le_rfl i = branchVec A a C ℓ' p b i σ (indC C) := by
      dsimp [prefVec]
    have heq_z : branchVec A a C ℓ' p (fun k => b ⟨k.val, k.isLt⟩)
        (fun k => zeroOnK i ⟨k.val, k.isLt⟩) (fun k => σ ⟨k.val, k.isLt⟩) (indC C) =
        branchVec A a C ℓ' p b (zeroOnK i) σ (indC C) := rfl
    rw [heq_p, heq_z] at hfull
    rw [hfull]
    congr 1
    have hfiltK : Finset.univ.filter (fun k : Fin p => k.val < p ∧ σ k ≠ none) = K := by
      ext k; simp [K, k.isLt]
    rw [hfiltK]
    symm
    refine Finset.prod_bij (fun u _ => (eK u).1) ?_ ?_ ?_ ?_
    · intro u _; exact (eK u).2
    · intro u₁ _ u₂ _ h; exact eK.injective (Subtype.ext h)
    · intro k hk; exact ⟨eK.symm ⟨k, hk⟩, Finset.mem_univ _, by simp⟩
    · intro u _; simp only [hroot_spec u, lam]
  let fibers : Finset (Fin p → ℕ) := (CircularDubuc.annulusSet p m D).image zeroOnK
  rw [← Finset.sum_fiberwise_of_maps_to (g := zeroOnK) (t := fibers)
        (fun i hi => Finset.mem_image_of_mem _ hi)]
  refine Finset.sum_eq_zero (fun iJ hiJ => ?_)
  have hfib_rew : ∑ i ∈ (CircularDubuc.annulusSet p m D).filter (fun i => zeroOnK i = iJ),
      ψ (branchVec A a C ℓ' p b i σ (indC C)) =
      (∑ i ∈ (CircularDubuc.annulusSet p m D).filter (fun i => zeroOnK i = iJ),
        ∏ u : Fin t, (lam u) ^ (i (eK u).1)) *
      ψ (branchVec A a C ℓ' p b iJ σ (indC C)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hEq := (Finset.mem_filter.mp hi).2
    rw [hfactor i, map_smul, smul_eq_mul, hEq]
  rw [hfib_rew]
  by_cases hbig : ∃ s ∈ J,
      Module.finrank ℂ (UN (s.val + 1)) - Module.finrank ℂ (UN s.val) ≤ iJ s
  · obtain ⟨s, hsJ, hge⟩ := hbig
    have hcoeff0 : ψ (branchVec A a C ℓ' p b iJ σ (indC C)) = 0 := by
      refine hdrop_kills (s.val + 1) (by omega) (by omega) iJ ?_
      dsimp [prefVec, branchVec]
      have hσs : σ s = none := (Finset.mem_filter.mp hsJ).2
      have hxs : optProj A a C ℓ' (σ s) (rowAct A [b s] (prefVec s.val (by omega) iJ)) ∈
          UN (s.val + 1) := by
        refine ⟨hU_opt (s.val + 1) _ _ (hU_step s.val _ _ (hpref_mem s.val (by omega) iJ)), ?_⟩
        rw [hσs]; exact ⟨_, rfl⟩
      have hUN_sub : UN s.val ≤ UN (s.val + 1) := inf_le_inf_right VN (hU_mono s.val)
      have hUN_T : ∀ r x, x ∈ UN r → T x ∈ UN r := by
        intro r x ⟨hxU, hxV⟩
        refine ⟨hU_T r x hxU, ?_⟩
        rcases hxV with ⟨u, rfl⟩
        refine ⟨T u, ?_⟩
        change fitProjN A a ℓ' (T u) = T (fitProjN A a ℓ' u)
        dsimp [fitProjN, fitProjC, T]
        rw [map_sub, ← rowAct_append, ← rowAct_append,
            show List.replicate ℓ' a ++ [a] = [a] ++ List.replicate ℓ' a by
              rw [← List.replicate_succ', List.replicate_succ]; rfl]
      have hNil : ∀ x ∈ UN (s.val + 1), (T^[ℓ']) x ∈ UN s.val := by
        intro x hx
        rcases hx with ⟨_, u, rfl⟩
        have h0 : (T^[ℓ']) (fitProjN A a ℓ' u) = 0 := by
          dsimp [T]; rw [← rowAct_eq_iterate]
          change fitProjC A a ℓ' (fitProjN A a ℓ' u) = 0
          dsimp [fitProjN]
          rw [map_sub, hfit_idem, sub_self]
        rw [h0]; exact Submodule.zero_mem _
      have hinUN := CircularDubuc.nilpotent_step_mod_subspace T (UN s.val) (UN (s.val + 1))
        hUN_sub (hUN_T s.val) (hUN_T (s.val + 1)) ℓ' hNil _ hxs (iJ s) hge
      exact hinUN.1
    rw [hcoeff0, mul_zero]
  · push Not at hbig
    obtain ⟨i₀, _, hi₀_eq⟩ := Finset.mem_image.mp hiJ
    let LJ : ℕ := ∑ s ∈ J, iJ s
    have hUN0 : Module.finrank ℂ (UN 0) = 0 := by
      have hbot : UN 0 = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxU, hxV⟩
        rw [SetLike.mem_coe, hU0, Submodule.mem_span_singleton] at hxU
        obtain ⟨c', rfl⟩ := hxU
        rcases hxV with ⟨u, hu⟩
        have h0 : fitProjC A a ℓ' (c' • indC C) = 0 := by
          rw [← hu]
          dsimp [fitProjN]
          rw [map_sub, hfit_idem, sub_self]
        rw [map_smul] at h0
        change c' • rowAct A (List.replicate ℓ' a) (indC C) = 0 at h0
        rw [rowAct_replicate_indC] at h0
        rw [Submodule.mem_bot]; exact h0
      rw [hbot, finrank_bot]
    have hLJ_bound : LJ + sJ ≤ n - m := by
      have h1 : LJ + sJ = ∑ s ∈ J, (iJ s + 1) := by
        dsimp [LJ, sJ]; rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      have h2 : ∑ s ∈ J, (iJ s + 1) ≤
          ∑ s ∈ J, (Module.finrank ℂ (UN (s.val + 1)) - Module.finrank ℂ (UN s.val)) :=
        Finset.sum_le_sum (fun s hs => by have := hbig s hs; omega)
      have h3 : ∑ s ∈ J, (Module.finrank ℂ (UN (s.val + 1)) - Module.finrank ℂ (UN s.val)) ≤
          ∑ s : Fin p, (Module.finrank ℂ (UN (s.val + 1)) - Module.finrank ℂ (UN s.val)) :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      have htel_k : ∀ k : ℕ,
          ∑ s ∈ Finset.range k, (Module.finrank ℂ (UN (s + 1)) - Module.finrank ℂ (UN s)) =
            Module.finrank ℂ (UN k) - Module.finrank ℂ (UN 0) := by
        intro k
        induction k with
        | zero => simp
        | succ q ihq =>
          rw [Finset.sum_range_succ, ihq]
          have hle1 : Module.finrank ℂ (UN 0) ≤ Module.finrank ℂ (UN q) :=
            Submodule.finrank_mono (inf_le_inf_right VN (hU_le (Nat.zero_le q)))
          have hle2 : Module.finrank ℂ (UN q) ≤ Module.finrank ℂ (UN (q + 1)) :=
            Submodule.finrank_mono (inf_le_inf_right VN (hU_mono q))
          omega
      have htel : ∑ s : Fin p, (Module.finrank ℂ (UN (s.val + 1)) - Module.finrank ℂ (UN s.val)) =
          Module.finrank ℂ (UN p) - Module.finrank ℂ (UN 0) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun k => Module.finrank ℂ (UN (k + 1)) - Module.finrank ℂ (UN k))]
        exact htel_k p
      have hUNp : Module.finrank ℂ (UN p) ≤ n - m := by
        dsimp only [n, m, C] at hVN_dim ⊢
        rw [← hVN_dim]; exact Submodule.finrank_mono inf_le_right
      omega
    have ht_lt_m : t < m := by
      have hinj_r : Function.Injective rootAt := fun u₁ u₂ h =>
        hlam_inj (by dsimp [lam]; rw [h])
      have hsub : (Finset.univ.image rootAt) ⊆ Finset.univ.erase ⟨0, hm1⟩ := by
        intro x hx
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_erase.mpr ⟨fun h0 => hhit0 (eK u).1 (by rw [hroot_spec, h0]),
          Finset.mem_univ _⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hinj_r, Finset.card_fin,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin] at hc
      dsimp only [m] at hc ⊢; omega
    have hLJ_le_D : LJ ≤ D := by
      dsimp only [D, n, m, LJ, sJ, t, C] at hLJ_bound hJK_sum ht_lt_m ⊢; omega
    have hM_ge : m ≤ (D - LJ) + t := by
      have hm_le_n : m ≤ n := Finset.card_le_univ C
      dsimp only [D, n, m, LJ, sJ, t, C] at hLJ_bound hJK_sum ht_lt_m hm_le_n ⊢; omega
    have hsum_ann : ∑ i ∈ (CircularDubuc.annulusSet p m D).filter (fun i => zeroOnK i = iJ),
        ∏ u : Fin t, (lam u) ^ (i (eK u).1) =
        ∑ iK ∈ CircularDubuc.annulusSet t m (D - LJ), ∏ u : Fin t, (lam u) ^ (iK u) := by
      refine Finset.sum_bij (fun i _ u => i (eK u).1) ?_ ?_ ?_ ?_
      · intro i hi
        obtain ⟨hiA, hzi⟩ := Finset.mem_filter.mp hi
        have hsum_split : ∑ s : Fin p, i s = LJ + ∑ u : Fin t, i (eK u).1 := by
          have hpart : Finset.univ = J ∪ K := by
            ext s; simp only [J, K, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            tauto
          have hdisj : Disjoint J K := by
            rw [Finset.disjoint_left]; intro s h1 h2
            exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          rw [hpart, Finset.sum_union hdisj]
          congr 1
          · refine Finset.sum_congr rfl (fun s hs => ?_)
            have hEq := congrFun hzi s
            have hsN := (Finset.mem_filter.mp hs).2
            simpa [zeroOnK, hsN] using hEq
          · symm
            refine Finset.sum_bij (fun u _ => (eK u).1) (fun u _ => (eK u).2)
              (fun _ _ _ _ h => eK.injective (Subtype.ext h))
              (fun k hk => ⟨eK.symm ⟨k, hk⟩, Finset.mem_univ _, by simp⟩) (fun _ _ => rfl)
        simp only [CircularDubuc.annulusSet, CircularDubuc.simplexSet, Finset.mem_filter,
          Fintype.mem_piFinset, Finset.mem_range] at hiA ⊢
        refine ⟨⟨fun u => ?_, by omega⟩, by omega⟩
        have hle1 : i (eK u).1 ≤ ∑ v : Fin t, i (eK v).1 :=
          Finset.single_le_sum (f := fun v : Fin t => i (eK v).1)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
        omega
      · intro i₁ hi₁ i₂ hi₂ hEq
        have hz1 := (Finset.mem_filter.mp hi₁).2
        have hz2 := (Finset.mem_filter.mp hi₂).2
        ext s
        by_cases hs : σ s = none
        · have h1 := congrFun hz1 s; have h2 := congrFun hz2 s
          simp only [zeroOnK, hs, ↓reduceIte] at h1 h2; rw [h1, h2]
        · have hsK : s ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
          have := congrFun hEq (eK.symm ⟨s, hsK⟩)
          simpa using this
      · intro iK hiK
        let i : Fin p → ℕ := fun s =>
          if hs : σ s = none then iJ s
          else iK (eK.symm ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩)
        refine ⟨i, ?_, ?_⟩
        · have hsum_split : ∑ s : Fin p, i s = LJ + ∑ u : Fin t, iK u := by
            have hpart : Finset.univ = J ∪ K := by
              ext s; simp only [J, K, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              tauto
            have hdisj : Disjoint J K := by
              rw [Finset.disjoint_left]; intro s h1 h2
              exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
            rw [hpart, Finset.sum_union hdisj]
            congr 1
            · refine Finset.sum_congr rfl (fun s hs => ?_)
              simp [i, (Finset.mem_filter.mp hs).2]
            · symm
              refine Finset.sum_bij (fun u _ => (eK u).1) (fun u _ => (eK u).2)
                (fun _ _ _ _ h => eK.injective (Subtype.ext h))
                (fun k hk => ⟨eK.symm ⟨k, hk⟩, Finset.mem_univ _, by simp⟩) (fun u _ => ?_)
              have hne : σ (eK u).1 ≠ none := (Finset.mem_filter.mp (eK u).2).2
              simp [i, hne]
          simp only [CircularDubuc.annulusSet, CircularDubuc.simplexSet, Finset.mem_filter,
            Fintype.mem_piFinset, Finset.mem_range] at hiK ⊢
          refine ⟨⟨⟨fun s => ?_, by omega⟩, by omega⟩, ?_⟩
          · have hle1 : i s ≤ ∑ r : Fin p, i r :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
            omega
          · ext s
            by_cases hs : σ s = none
            · simp [zeroOnK, i, hs]
            · have h0 := congrFun hi₀_eq s; simp [zeroOnK, hs] at h0 ⊢; exact h0
        · ext u
          have hne : σ (eK u).1 ≠ none := (Finset.mem_filter.mp (eK u).2).2
          simp [i, hne]
      · intro _ _; rfl
    rw [hsum_ann, CircularDubuc.annular_cancellation ht1 hM_ge lam hlam_inj hlam_pow hlam_ne1,
        zero_mul]

end AnnularProof

section MainBounds

open WeightedPrimeCycle CircularDubuc

variable {Q α : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]

/-- **One-Cluster Annular Extension**: if `1 ≤ |S ∩ C| < |C|`, there exists a word `w`
of length `≤ n + ℓ` strictly increasing `|(A.preimage S w) ∩ C|`. -/
theorem one_cluster_annular_extension
    (A : Aut Q α) (hsync : A.IsSync) (a : α) (h1c : IsOneCluster A a)
    (hm2 : 2 ≤ (cycleStates A a).card)
    {S : Finset Q} (hS_pos : 1 ≤ (S ∩ cycleStates A a).card)
    (hS_lt : (S ∩ cycleStates A a).card < (cycleStates A a).card) :
    ∃ w : List α,
      w.length ≤ Fintype.card Q + cycleLevel A a ∧
      (S ∩ cycleStates A a).card < (A.preimage S w ∩ cycleStates A a).card := by
  classical
  let C := cycleStates A a
  let m := C.card
  let ℓ := cycleLevel A a
  let n := Fintype.card Q
  let c := (S ∩ C).card
  have hm_pos : 1 ≤ m := by dsimp [m, C]; omega
  have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by dsimp [m, C]; omega)
  let T : (Q → ℂ) →ₗ[ℂ] (Q → ℂ) := rowAct A [a]
  let vC : Q → ℂ := indC C
  have hvC_fix : T vC = vC := rowAct_a_indC A a
  have hvC_iter : ∀ k : ℕ, (T^[k]) vC = vC := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hvC_fix]
  have hvC_sum : ∑ q : Q, vC q = (m : ℂ) := by
    simp [vC, indC, Finset.sum_ite, m, C]
  let φ : (Q → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => dotC f (indC S) - ((c : ℂ) / (m : ℂ)) * (∑ q : Q, f q)
      map_add' := fun f g => by
        simp only [dotC, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun k f => by
        simp only [dotC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
          ← Finset.mul_sum]
        ring }
  let ψ : (Q → ℂ) →ₗ[ℂ] ℂ := φ.comp (rowAct A (List.replicate ℓ a))
  have hψ_word : ∀ w : List α,
      ψ (rowAct A w vC) = ((A.preimage S (w ++ List.replicate ℓ a) ∩ C).card : ℂ) - (c : ℂ) := by
    intro w
    dsimp only [ψ, LinearMap.comp_apply, φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← rowAct_append, dotC_rowAct_indC, sum_rowAct, hvC_sum]
    have hdot : dotC vC (indC (A.preimage S (w ++ List.replicate ℓ a))) =
        ((A.preimage S (w ++ List.replicate ℓ a) ∩ C).card : ℂ) := by
      simp only [dotC, vC, indC]
      trans ∑ q : Q, if q ∈ A.preimage S (w ++ List.replicate ℓ a) ∩ C then (1 : ℂ) else 0
      · refine Finset.sum_congr rfl (fun q _ => ?_)
        by_cases h1 : q ∈ C <;> by_cases h2 : q ∈ A.preimage S (w ++ List.replicate ℓ a) <;>
          simp [h1, h2]
      · simp only [Finset.sum_boole, Nat.cast_inj]
        congr 1; ext q; simp [Finset.mem_inter]
    rw [hdot]
    congr 1
    field_simp
  by_contra hno
  push Not at hno
  have hψ_le : ∀ w : List α, w.length ≤ n →
      (ψ (rowAct A w vC)).re ≤ 0 ∧ (ψ (rowAct A w vC)).im = 0 := by
    intro w hw
    have hlen : (w ++ List.replicate ℓ a).length ≤ n + ℓ := by
      simp only [List.length_append, List.length_replicate]; omega
    have hle := hno (w ++ List.replicate ℓ a) hlen
    rw [hψ_word]
    have hleC : ((A.preimage S (w ++ List.replicate ℓ a) ∩ C).card : ℝ) ≤ (c : ℝ) :=
      Nat.cast_le.mpr hle
    simp only [Complex.sub_re, Complex.natCast_re, Complex.sub_im, Complex.natCast_im, sub_zero]
    exact ⟨by linarith, by simp⟩
  let ℓ' := (ℓ / m + 1) * m
  have hℓ'_ge : ℓ ≤ ℓ' := by
    have : ℓ < m * (ℓ / m + 1) := Nat.lt_mul_div_succ ℓ hm_pos
    dsimp only [ℓ']; rw [mul_comm]; omega
  have hfit_idem : ∀ u : Q → ℂ, fitProjC A a ℓ' (fitProjC A a ℓ' u) = fitProjC A a ℓ' u := by
    intro u
    dsimp [fitProjC]
    rw [← rowAct_append, ← List.replicate_add]
    have hpow : ∀ t : ℕ, rowAct A (List.replicate (ℓ' + t * m) a) u =
        rowAct A (List.replicate ℓ' a) u := by
      intro t
      induction t with
      | zero => simp
      | succ t iht =>
        have h1 : ℓ' + (t + 1) * m = ((ℓ' + t * m) - ℓ) + (ℓ + m) := by
          have hmul : (t + 1) * m = t * m + m := by ring
          dsimp only [ℓ', m, ℓ] at hℓ'_ge hmul ⊢; omega
        have h2 : ℓ' + t * m = ((ℓ' + t * m) - ℓ) + ℓ := by
          dsimp only [ℓ', m, ℓ] at hℓ'_ge ⊢; omega
        rw [h1, List.replicate_add, rowAct_append, rowAct_replicate_period A a h1c,
            ← rowAct_append, ← List.replicate_add, ← h2, iht]
    rw [show ℓ' + ℓ' = ℓ' + (ℓ / m + 1) * m from rfl, hpow (ℓ / m + 1)]
  have hφ_vC : φ vC = 0 := by
    dsimp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    have hdot : dotC vC (indC S) = (c : ℂ) := by
      simp only [dotC, vC, indC]
      trans ∑ q : Q, if q ∈ S ∩ C then (1 : ℂ) else 0
      · refine Finset.sum_congr rfl (fun q _ => ?_)
        by_cases h1 : q ∈ C <;> by_cases h2 : q ∈ S <;> simp [h1, h2]
      · simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, c]
    rw [hdot, hvC_sum]
    field_simp
    ring
  have hT_add : ∀ (k : ℕ) (x y : Q → ℂ), (T^[k]) (x + y) = (T^[k]) x + (T^[k]) y := by
    intro k x y
    induction k generalizing x y with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply, map_add, ih]
  have hT_smul : ∀ (k : ℕ) (c' : ℂ) (x : Q → ℂ), (T^[k]) (c' • x) = c' • (T^[k]) x := by
    intro k c' x
    induction k generalizing x with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply, map_smul, ih]
  let M_tail : Submodule ℂ (Q → ℂ) :=
    { carrier := { x | ∀ k : ℕ, ψ ((T^[k]) x) = 0 }
      zero_mem' := fun k => by
        rw [Function.iterate_fixed (map_zero T) k, map_zero]
      add_mem' := fun {x y} hx hy k => by
        rw [hT_add, map_add, hx k, hy k, add_zero]
      smul_mem' := fun c' {x} hx k => by
        rw [hT_smul, map_smul, hx k, smul_zero] }
  have hvC_mem_Mtail : vC ∈ M_tail := by
    intro k
    rw [hvC_iter k]
    change φ (rowAct A (List.replicate ℓ a) vC) = 0
    rw [rowAct_replicate_indC, hφ_vC]
  have hT_Mtail : ∀ x ∈ M_tail, T x ∈ M_tail := by
    intro x hx k
    rw [← Function.iterate_succ_apply T k x]
    exact hx (k + 1)
  let U : ℕ → Submodule ℂ (Q → ℂ) := fun r =>
    Submodule.span ℂ { y | ∃ w : List α,
      w.countP (fun b => decide (b ≠ a)) ≤ r ∧ ∃ j : ℕ, y = (T^[j]) (rowAct A w vC) }
  have hU0 : U 0 = Submodule.span ℂ {vC} := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, j, rfl⟩
      have hw0 : w.countP (fun b => decide (b ≠ a)) = 0 := by omega
      have hw_rep : w = List.replicate w.length a := by
        rw [List.countP_eq_zero] at hw0
        refine List.ext_get (by simp) (fun i hi1 _ => ?_)
        have hmem := hw0 w[i] (List.getElem_mem hi1)
        simp only [decide_eq_true_eq, not_not] at hmem
        simp [hmem]
      rw [hw_rep, rowAct_replicate_indC, hvC_iter j]
      exact Submodule.subset_span (Set.mem_singleton vC)
    · refine Submodule.span_le.mpr ?_
      rintro y rfl
      exact Submodule.subset_span ⟨[], by simp, 0, by simp [rowAct_nil]⟩
  have hU_mono : ∀ r, U r ≤ U (r + 1) := fun r =>
    Submodule.span_mono (by rintro y ⟨w, hw, j, rfl⟩; exact ⟨w, by omega, j, rfl⟩)
  have hU_T : ∀ r x, x ∈ U r → T x ∈ U r := by
    intro r x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨w, hw, j, rfl⟩
      exact Submodule.subset_span ⟨w, hw, j + 1, by rw [Function.iterate_succ_apply']⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact (U r).add_mem hx hy
    | smul c' x _ hx => rw [map_smul]; exact (U r).smul_mem c' hx
  have hU_step : ∀ r (b_let : α) x, x ∈ U r → rowAct A [b_let] x ∈ U (r + 1) := by
    intro r b_let x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨w, hw, j, rfl⟩
      refine Submodule.subset_span ⟨w ++ List.replicate j a ++ [b_let], ?_, 0, ?_⟩
      · rw [List.countP_append, List.countP_append, List.countP_replicate,
            List.countP_cons, List.countP_nil]
        by_cases hba : b_let = a
        · have : (w.countP (fun b => decide (b ≠ a))) ≤ r := hw
          simp [hba] at *; omega
        · have : (w.countP (fun b => decide (b ≠ a))) ≤ r := hw
          simp [hba] at *; omega
      · dsimp only [T]; simp [rowAct_append, rowAct_eq_iterate]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact (U (r + 1)).add_mem hx hy
    | smul c' x _ hx => rw [map_smul]; exact (U (r + 1)).smul_mem c' hx
  have hU_le_trans : ∀ a b : ℕ, a ≤ b → U a ≤ U b := by
    intro a' b' hab
    induction hab with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hU_mono _)
  have hU0_le : U 0 ≤ M_tail := by
    rw [hU0]; refine Submodule.span_le.mpr ?_; rintro y rfl; exact hvC_mem_Mtail
  have hex_escape : ∃ r : ℕ, ¬ (U r ≤ M_tail) := by
    by_contra hall
    push Not at hall
    have hstab : ∃ r : ℕ, U r = U (r + 1) := by
      by_contra hnostab
      push Not at hnostab
      have hgrow : ∀ r, r + 1 ≤ Module.finrank ℂ (U r) := by
        intro r
        induction r with
        | zero =>
          have hv0 : vC ∈ U 0 := by rw [hU0]; exact Submodule.subset_span (Set.mem_singleton _)
          have hv_ne : vC ≠ 0 := by
            intro h0
            have := congrArg (fun f => ∑ q : Q, f q) h0
            rw [hvC_sum] at this
            simp only [Pi.zero_apply, Finset.sum_const_zero] at this
            exact hm_ne this
          have hbot : (⊥ : Submodule ℂ (Q → ℂ)) < U 0 :=
            lt_of_le_of_ne bot_le (fun hEq => hv_ne (by simpa [← hEq] using hv0))
          have := Submodule.finrank_lt_finrank_of_lt hbot
          rw [finrank_bot] at this
          omega
        | succ r ihr =>
          have hlt : U r < U (r + 1) := lt_of_le_of_ne (hU_mono r) (hnostab r)
          have := Submodule.finrank_lt_finrank_of_lt hlt
          omega
      have hle_n : Module.finrank ℂ (U n) ≤ n := by
        have := Submodule.finrank_le (U n)
        rwa [Module.finrank_fintype_fun_eq_card] at this
      have := hgrow n
      omega
    obtain ⟨r₀, hr₀⟩ := hstab
    have hinv_letter : ∀ (b : α) (x : Q → ℂ), x ∈ U r₀ → rowAct A [b] x ∈ U r₀ := by
      intro b x hx; rw [hr₀]; exact hU_step r₀ b x hx
    have hall_words : ∀ w : List α, rowAct A w vC ∈ U r₀ := by
      intro w
      induction w using List.reverseRecOn with
      | nil =>
        rw [rowAct_nil]
        exact hU_le_trans 0 r₀ (Nat.zero_le r₀) (by rw [hU0]; exact Submodule.subset_span (Set.mem_singleton _))
      | append_singleton w b ih => rw [rowAct_append]; exact hinv_letter b _ ih
    obtain ⟨u₀, hu₀⟩ := hsync
    rw [Aut.isSyncWord_iff_exists_eval_eq] at hu₀
    obtain ⟨q₀, hq₀⟩ := hu₀
    obtain ⟨s₀, hs₀⟩ := Finset.card_pos.mp hS_pos
    rw [Finset.mem_inter] at hs₀
    have hq₁_mem : A.eval q₀ (List.replicate ℓ a) ∈ C :=
      eval_replicate_mem_cycleStates A a q₀ 0
    obtain ⟨s₁, hs₁_mem, hs₁_eq⟩ := (eval_cycleLevel_bijOn A a).surjOn hs₀.2
    obtain ⟨j₁, _, hj₁_eq⟩ := h1c _ hq₁_mem s₁ hs₁_mem
    let u' := u₀ ++ List.replicate (ℓ + j₁) a
    have hu'_eval : ∀ q : Q, A.eval q u' = s₁ := by
      intro q; dsimp only [u']
      rw [Aut.eval_append, hq₀ q, List.replicate_add, Aut.eval_append, hj₁_eq]
    have hu'_mem := hall r₀ (hall_words u') 0
    rw [Function.iterate_zero_apply, hψ_word] at hu'_mem
    have hpre_eq : A.preimage S (u' ++ List.replicate ℓ a) ∩ C = C := by
      ext q
      simp only [Finset.mem_inter, Aut.mem_preimage, and_iff_right_iff_imp]
      intro _
      dsimp only at hs₁_eq
      dsimp only [ℓ]
      rw [Aut.eval_append, hu'_eval q, hs₁_eq]
      exact hs₀.1
    rw [hpre_eq] at hu'_mem
    rw [sub_eq_zero] at hu'_mem
    have : m = c := Nat.cast_injective hu'_mem
    dsimp only [m, c, C] at hS_lt this
    omega
  let p := Nat.find hex_escape
  have hp_not : ¬ (U p ≤ M_tail) := Nat.find_spec hex_escape
  have hp_pos : 1 ≤ p := by
    by_contra h0
    have hp0 : p = 0 := by omega
    rw [hp0] at hp_not
    exact hp_not hU0_le
  have hp_prev : U (p - 1) ≤ M_tail := by
    by_contra hnot; exact Nat.find_min hex_escape (by omega : p - 1 < p) hnot
  have hp_lt_n : p < n := by
    have hgrow : ∀ r ≤ p - 1, r + 1 ≤ Module.finrank ℂ (U r) := by
      intro r hr
      induction r with
      | zero =>
        have hv0 : vC ∈ U 0 := by rw [hU0]; exact Submodule.subset_span (Set.mem_singleton _)
        have hv_ne : vC ≠ 0 := by
          intro h0; have := congrArg (fun f => ∑ q : Q, f q) h0
          rw [hvC_sum] at this; simp only [Pi.zero_apply, Finset.sum_const_zero] at this; exact hm_ne this
        have hbot : (⊥ : Submodule ℂ (Q → ℂ)) < U 0 :=
          lt_of_le_of_ne bot_le (fun hEq => hv_ne (by simpa [← hEq] using hv0))
        have := Submodule.finrank_lt_finrank_of_lt hbot
        rw [finrank_bot] at this; omega
      | succ r ihr =>
        have hne : U r ≠ U (r + 1) := by
          intro hEq
          have hinv_letter : ∀ (b : α) (x : Q → ℂ), x ∈ U r → rowAct A [b] x ∈ U r := by
            intro b x hx; rw [hEq]; exact hU_step r b x hx
          have hall_words : ∀ w : List α, rowAct A w vC ∈ U r := by
            intro w
            induction w using List.reverseRecOn with
            | nil =>
              rw [rowAct_nil]
              exact hU_le_trans 0 r (Nat.zero_le r) (by rw [hU0]; exact Submodule.subset_span (Set.mem_singleton _))
            | append_singleton w b ih => rw [rowAct_append]; exact hinv_letter b _ ih
          have hle_Mt : U r ≤ M_tail := (hU_le_trans r (p - 1) (by omega)).trans hp_prev
          have hUp_le : U p ≤ U r := by
            refine Submodule.span_le.mpr ?_
            rintro y ⟨w, _, j, rfl⟩
            have hw := hall_words w
            clear hEq hr ihr
            induction j with
            | zero => exact hw
            | succ j ihj => rw [Function.iterate_succ_apply']; exact hU_T r _ ihj
          exact hp_not (hUp_le.trans hle_Mt)
        have hlt : U r < U (r + 1) := lt_of_le_of_ne (hU_mono r) hne
        have := Submodule.finrank_lt_finrank_of_lt hlt
        have := ihr (by omega)
        omega
    have hM_lt_top : M_tail < ⊤ := by
      refine lt_of_le_of_ne le_top (fun hEq => ?_)
      exact hp_not (by rw [hEq]; exact le_top)
    have hfin_Mt : Module.finrank ℂ M_tail < n := by
      have := Submodule.finrank_lt_finrank_of_lt hM_lt_top
      rw [finrank_top, Module.finrank_fintype_fun_eq_card] at this
      exact this
    have hfin_prev : p ≤ Module.finrank ℂ (U (p - 1)) := by
      have := hgrow (p - 1) le_rfl; omega
    have hfin_le := Submodule.finrank_mono hp_prev
    omega
  -- Telescoping `BoundSpan` via `span_orbit_mod_subspace`
  let BoundSpan : ℕ → Submodule ℂ (Q → ℂ) := fun k =>
    Submodule.span ℂ { y | ∃ (q : ℕ) (b : Fin q → α) (i : Fin q → ℕ),
      q ≤ k ∧ q + ∑ s : Fin q, i s ≤ Module.finrank ℂ (U k) - 1 ∧
      y = rowAct A (wordChain a q b i) vC }
  have hU_le_Bound : ∀ k ≤ p, U k ≤ BoundSpan k := by
    intro k hk
    induction k with
    | zero =>
      rw [hU0]; refine Submodule.span_le.mpr ?_; rintro y rfl
      refine Submodule.subset_span ⟨0, Fin.elim0, Fin.elim0, le_rfl, ?_, by simp [wordChain, rowAct_nil]⟩
      simp
    | succ k ihk =>
      have hk_le : U k ≤ BoundSpan k := ihk (by omega)
      have hBS_mono : BoundSpan k ≤ BoundSpan (k + 1) := by
        refine Submodule.span_le.mpr ?_
        rintro y ⟨q, b, i, hqk, hlen, rfl⟩
        have hfin_mono := Submodule.finrank_mono (hU_mono k)
        exact Submodule.subset_span ⟨q, b, i, by omega, by omega, rfl⟩
      have hUk_le : U k ≤ BoundSpan (k + 1) := hk_le.trans hBS_mono
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, j, rfl⟩
      by_cases hwk : w.countP (fun b => decide (b ≠ a)) ≤ k
      · exact hUk_le (Submodule.subset_span ⟨w, hwk, j, rfl⟩)
      · have hweq : w.countP (fun b => decide (b ≠ a)) = k + 1 := by omega
        -- Split `w` at the last non-`a` letter
        have hsplit_w : ∃ (w₀ : List α) (b_last : α) (j_tail : ℕ),
            w₀.countP (fun b => decide (b ≠ a)) = k ∧
            w = w₀ ++ [b_last] ++ List.replicate j_tail a := by
          clear hw hwk hk_le hBS_mono hUk_le ihk hk
          induction w using List.reverseRecOn with
          | nil => simp at hweq
          | append_singleton w' x ihw =>
            by_cases hxa : x = a
            · rw [hxa] at hweq
              rw [List.countP_append, List.countP_singleton] at hweq
              simp at hweq
              obtain ⟨w₀, bl, jt, hw₀, rfl⟩ := ihw hweq
              refine ⟨w₀, bl, jt + 1, hw₀, ?_⟩
              simp [hxa, List.replicate_succ', List.append_assoc]
            · rw [List.countP_append, List.countP_singleton] at hweq
              simp [hxa] at hweq
              exact ⟨w', x, 0, hweq, by simp⟩
        obtain ⟨w₀, b_last, j_tail, hw₀, rfl⟩ := hsplit_w
        have hw₀_in : rowAct A w₀ vC ∈ BoundSpan k :=
          hk_le (Submodule.subset_span ⟨w₀, le_of_eq hw₀, 0, by simp⟩)
        have hstep_in : rowAct A [b_last] (rowAct A w₀ vC) ∈
            U k ⊔ Submodule.span ℂ { z | ∃ (b : Fin (k + 1) → α) (i : Fin (k + 1) → ℕ),
              (k + 1) + ∑ s : Fin (k + 1), i s ≤ Module.finrank ℂ (U k) ∧
              z = rowAct A (wordChain a (k + 1) b i) vC } := by
          generalize rowAct A w₀ vC = z₀ at hw₀_in ⊢
          induction hw₀_in using Submodule.span_induction with
          | mem z hz =>
            rcases hz with ⟨q, b, i, hqk, hlen, rfl⟩
            by_cases hq_lt : q < k
            · refine Submodule.mem_sup_left ?_
              have hstep_z := hU_step q b_last (rowAct A (wordChain a q b i) vC)
                (Submodule.subset_span ⟨wordChain a q b i, wordChain_countP_ne a q b i, 0, by simp⟩)
              exact hU_le_trans (q + 1) k (by omega) hstep_z
            · have hqk_eq : q = k := Nat.le_antisymm hqk (Nat.le_of_not_lt hq_lt)
              subst hqk_eq
              have hfin_pos : 1 ≤ Module.finrank ℂ (U q) := by
                have hv0 : vC ∈ U q :=
                  hU_le_trans 0 q (Nat.zero_le q) (by rw [hU0]; exact Submodule.subset_span (Set.mem_singleton _))
                have hv_ne : vC ≠ 0 := by
                  intro h0; have := congrArg (fun f => ∑ s : Q, f s) h0
                  rw [hvC_sum] at this; simp only [Pi.zero_apply, Finset.sum_const_zero] at this; exact hm_ne this
                have hbot : (⊥ : Submodule ℂ (Q → ℂ)) < U q :=
                  lt_of_le_of_ne bot_le (fun hEq => hv_ne (by simpa [← hEq] using hv0))
                have := Submodule.finrank_lt_finrank_of_lt hbot
                rw [finrank_bot] at this; omega
              refine Submodule.mem_sup_right (Submodule.subset_span ⟨Fin.snoc b b_last,
                Fin.snoc i 0, ?_, ?_⟩)
              · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, add_zero]
                omega
              · simp only [wordChain, Fin.init_snoc, Fin.snoc_last, List.replicate_zero,
                  rowAct_append]
          | zero => simp
          | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
          | smul c' x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
        -- Apply `T^[j + j_tail]` and `span_orbit_mod_subspace`!
        have hcomp_eq : (T^[j]) (rowAct A (w₀ ++ [b_last] ++ List.replicate j_tail a) vC) =
            (T^[j + j_tail]) (rowAct A [b_last] (rowAct A w₀ vC)) := by
          dsimp only [T]
          simp only [List.append_assoc, rowAct_append, rowAct_eq_iterate,
            ← Function.iterate_add_apply]
        rw [hcomp_eq]
        rcases Submodule.mem_sup.mp hstep_in with ⟨u₁, hu₁, u₂, hu₂, hsum⟩
        rw [← hsum]
        dsimp only [T]
        rw [← rowAct_eq_iterate, map_add, rowAct_eq_iterate, rowAct_eq_iterate]
        refine Submodule.add_mem _ (hUk_le ?_) ?_
        · clear hsum hu₂
          generalize j + j_tail = s
          induction s with
          | zero => exact hu₁
          | succ s ihs => rw [Function.iterate_succ_apply']; exact hU_T k _ ihs
        · clear hsum hu₁
          induction hu₂ using Submodule.span_induction with
          | mem z hz =>
            rcases hz with ⟨b, i, hlen, rfl⟩
            have hz_in : rowAct A (wordChain a (k + 1) b i) vC ∈ U (k + 1) :=
              Submodule.subset_span ⟨wordChain a (k + 1) b i, wordChain_countP_ne a (k + 1) b i,
                0, by simp⟩
            have hsp := CircularDubuc.span_orbit_mod_subspace T (U k) (U (k + 1)) (hU_mono k)
              (hU_T k) (hU_T (k + 1)) _ hz_in (j + j_tail)
            refine (sup_le hUk_le (Submodule.span_le.mpr ?_)) hsp
            rintro _ ⟨j', hj', rfl⟩
            refine Submodule.subset_span ⟨k + 1, b,
              Fin.snoc (Fin.init i) (i (Fin.last k) + j'), le_rfl, ?_, ?_⟩
            · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
              have hi_sum : ∑ s : Fin k, (Fin.init i) s + i (Fin.last k) =
                  ∑ s : Fin (k + 1), i s := by
                rw [Fin.sum_univ_castSucc]; rfl
              have hfin_pos : 1 ≤ Module.finrank ℂ (U k) := by
                have hv0 : vC ∈ U k :=
                  hU_le_trans 0 k (Nat.zero_le k) (by rw [hU0]; exact Submodule.subset_span (Set.mem_singleton _))
                have hv_ne : vC ≠ 0 := by
                  intro h0; have := congrArg (fun f => ∑ q : Q, f q) h0
                  rw [hvC_sum] at this; simp only [Pi.zero_apply, Finset.sum_const_zero] at this; exact hm_ne this
                have hbot : (⊥ : Submodule ℂ (Q → ℂ)) < U k :=
                  lt_of_le_of_ne bot_le (fun hEq => hv_ne (by simpa [← hEq] using hv0))
                have := Submodule.finrank_lt_finrank_of_lt hbot
                rw [finrank_bot] at this; omega
              omega
            · simp only [wordChain, Fin.init_snoc, Fin.snoc_last, List.cons_append,
                rowAct_append]
              dsimp only [T]
              rw [← rowAct_eq_iterate, List.replicate_add, ← List.cons_append, rowAct_append]
          | zero => rw [← rowAct_eq_iterate, map_zero]; exact Submodule.zero_mem _
          | add x y _ _ hx hy =>
            rw [← rowAct_eq_iterate, map_add, rowAct_eq_iterate, rowAct_eq_iterate]
            exact Submodule.add_mem _ hx hy
          | smul c' x _ hx =>
            rw [← rowAct_eq_iterate, map_smul, rowAct_eq_iterate]
            exact Submodule.smul_mem _ _ hx
  -- Extract witness `(b, i_star)` from `U p ⊈ M_tail` and `U p ≤ BoundSpan p`
  have hex_witness : ∃ (b : Fin p → α) (i_star : Fin p → ℕ),
      ∑ r : Fin p, i_star r ≤ n - p ∧ ψ (rowAct A (wordChain a p b i_star) vC) ≠ 0 := by
    have hnot_ker : ∃ x ∈ U p, ψ x ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hp_not
      intro x hx k
      exact hall _ (by
        clear hall
        induction k with
        | zero => exact hx
        | succ k ihk => rw [Function.iterate_succ_apply']; exact hU_T p _ ihk)
    obtain ⟨x, hxUp, hxψ⟩ := hnot_ker
    have hxBS := hU_le_Bound p le_rfl hxUp
    have hex_gen : ∃ (q : ℕ) (b : Fin q → α) (i : Fin q → ℕ),
        q ≤ p ∧ q + ∑ s : Fin q, i s ≤ Module.finrank ℂ (U p) - 1 ∧
        ψ (rowAct A (wordChain a q b i) vC) ≠ 0 := by
      by_contra hall
      push Not at hall
      have hψ_all : ∀ y ∈ BoundSpan p, ψ y = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem z hz => rcases hz with ⟨q, b, i, hqp, hlen, rfl⟩; exact hall q b i hqp hlen
        | zero => simp
        | add _ _ _ _ hx hy => rw [map_add, hx, hy, add_zero]
        | smul _ _ _ hx => rw [map_smul, hx, smul_zero]
      exact hxψ (hψ_all x hxBS)
    rcases hex_gen with ⟨q, b, i, hqp, hlen, hψne⟩
    have hqp_eq : q = p := by
      by_contra hne
      have hle : q ≤ p - 1 := by omega
      have hmem : rowAct A (wordChain a q b i) vC ∈ U (p - 1) := by
        refine Submodule.subset_span ⟨wordChain a q b i, ?_, 0, by simp⟩
        exact (wordChain_countP_ne a q b i).trans hle
      exact hψne (hp_prev hmem 0)
    subst hqp_eq
    have hfin_le : Module.finrank ℂ (U p) ≤ n := by
      have := Submodule.finrank_le (U p)
      rwa [Module.finrank_fintype_fun_eq_card] at this
    exact ⟨b, i, by omega, hψne⟩
  rcases hex_witness with ⟨b, i_star, hS_le, hψ_ne⟩
  -- Shift last exponent by `q_sh * m` so `i'` lands in `annulusSet p m (n - p)`
  let D := n - p
  let S_star := ∑ r : Fin p, i_star r
  let q_sh := (D - S_star) / m
  let last_r : Fin p := ⟨p - 1, by omega⟩
  let i' : Fin p → ℕ := Function.update i_star last_r (i_star last_r + q_sh * m)
  have hi'_sum : ∑ r : Fin p, i' r = S_star + q_sh * m := by
    have h1 := Finset.add_sum_erase (Finset.univ : Finset (Fin p)) i' (Finset.mem_univ last_r)
    have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin p)) i_star (Finset.mem_univ last_r)
    have her : ∑ r ∈ Finset.univ.erase last_r, i' r =
        ∑ r ∈ Finset.univ.erase last_r, i_star r := by
      refine Finset.sum_congr rfl (fun r hr => ?_)
      simp [i', Function.update_of_ne (Finset.ne_of_mem_erase hr)]
    rw [← h1, her, show i' last_r = i_star last_r + q_sh * m by simp [i'], add_assoc,
        add_comm (q_sh * m), ← add_assoc, h2]
  have hi'_mem : i' ∈ CircularDubuc.annulusSet p m D := by
    have hqm_le : q_sh * m ≤ D - S_star := Nat.div_mul_le_self (D - S_star) m
    have hqm_gt : D - S_star < q_sh * m + m := by
      have hdiv := Nat.div_add_mod (D - S_star) m
      have hmod := Nat.mod_lt (D - S_star) hm_pos
      dsimp only [D, S_star, q_sh] at hdiv hmod ⊢
      linarith
    simp only [CircularDubuc.annulusSet, CircularDubuc.simplexSet, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨⟨fun r => ?_, ?_⟩, ?_⟩
    · have hle1 : i' r ≤ ∑ s : Fin p, i' s :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
      omega
    · omega
    · omega
  have hψ_i' : ψ (rowAct A (wordChain a p b i') vC) = ψ (rowAct A (wordChain a p b i_star) vC) := by
    -- Replacing `i_star last_r` by `i_star last_r + q_sh * m` adds `q_sh * m` copies of `a` before `ℓ`
    have hwc_eq_gen : ∀ (q : ℕ) (hq : 1 ≤ q) (b' : Fin q → α) (j : Fin q → ℕ),
        wordChain a q b' j =
          wordChain a (q - 1) (fun r => b' ⟨r.1, by omega⟩) (fun r => j ⟨r.1, by omega⟩) ++
            (b' ⟨q - 1, by omega⟩ :: List.replicate (j ⟨q - 1, by omega⟩) a) := by
      intro q hq b' j
      cases q with
      | zero => omega
      | succ q' => rfl
    rw [hwc_eq_gen p hp_pos b i', hwc_eq_gen p hp_pos b i_star]
    have hinit_eq : (fun r : Fin (p - 1) => i' ⟨r.1, by omega⟩) =
        (fun r : Fin (p - 1) => i_star ⟨r.1, by omega⟩) := by
      ext r
      have hne : (⟨r.1, by omega⟩ : Fin p) ≠ last_r := by
        intro h; have := congrArg Fin.val h; dsimp [last_r] at this; omega
      simp only [i', Function.update_of_ne hne]
    rw [hinit_eq]
    have hfuse : ∀ (k : ℕ) (x : Q → ℂ),
        rowAct A (List.replicate ℓ a) (rowAct A (List.replicate k a) x) =
          rowAct A (List.replicate (k + ℓ) a) x := by
      intro k x
      rw [← rowAct_append, ← List.replicate_add]
    dsimp only [ψ, LinearMap.comp_apply]
    rw [show b last_r :: List.replicate (i' last_r) a =
          [b last_r] ++ List.replicate (i' last_r) a from rfl,
        show b last_r :: List.replicate (i_star last_r) a =
          [b last_r] ++ List.replicate (i_star last_r) a from rfl]
    simp only [rowAct_append, LinearMap.comp_apply]
    rw [hfuse, hfuse]
    have hi'_last : i' last_r = i_star last_r + q_sh * m := by simp [i']
    rw [hi'_last, add_assoc, add_comm (q_sh * m) ℓ, ← add_assoc]
    have hper_q : ∀ (t : ℕ) (f : Q → ℂ),
        rowAct A (List.replicate (i_star last_r + ℓ + t * m) a) f =
          rowAct A (List.replicate (i_star last_r + ℓ) a) f := by
      intro t f
      induction t with
      | zero => simp
      | succ t iht =>
        have hmul : (t + 1) * m = t * m + m := by ring
        have h1 : i_star last_r + ℓ + (t + 1) * m = (i_star last_r + t * m) + (ℓ + m) := by omega
        have h2 : i_star last_r + ℓ + t * m = (i_star last_r + t * m) + ℓ := by omega
        rw [h1, List.replicate_add, rowAct_append, rowAct_replicate_period A a h1c,
            ← rowAct_append, ← List.replicate_add, ← h2, iht]
    rw [hper_q q_sh]
  -- Sum over `annulusSet p m D` is `0` by `rowAct_wordChain_eq_sum_branch` + `branch_annular_sum_eq_zero`!
  have hVN_dim : Module.finrank ℂ (LinearMap.range (fitProjN A a ℓ')) = n - m := by
    have hdisj : LinearMap.range (projC C) ⊓ LinearMap.range (fitProjN A a ℓ') = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxC, u, rfl⟩
      have h0 : fitProjC A a ℓ' (fitProjN A a ℓ' u) = 0 := by
        dsimp [fitProjN]; rw [map_sub, hfit_idem, sub_self]
      have hid : fitProjC A a ℓ' (fitProjN A a ℓ' u) = fitProjN A a ℓ' u := by
        have hpow : ∀ t : ℕ, ∀ y ∈ LinearMap.range (projC C),
            rowAct A (List.replicate (t * m) a) y = y := by
          intro t y hy
          induction t with
          | zero => simp [rowAct_nil]
          | succ t iht =>
            rw [Nat.succ_mul, List.replicate_add, rowAct_append, iht]
            exact rowAct_replicate_period_of_mem A a h1c hy
        exact hpow (ℓ / m + 1) _ hxC
      rw [← hid, h0, Submodule.mem_bot]
    have hsup : LinearMap.range (projC C) ⊔ LinearMap.range (fitProjN A a ℓ') = ⊤ := by
      rw [eq_top_iff]
      intro f _
      have hPC_in : fitProjC A a ℓ' f ∈ LinearMap.range (projC C) := by
        have hsp : ℓ' = (ℓ' - ℓ) + ℓ := by omega
        dsimp [fitProjC]; rw [hsp, List.replicate_add, rowAct_append]
        have h0 := nilpotent_projN A a C ℓ (fun q => eval_replicate_mem_cycleStates A a q 0)
          (rowAct A (List.replicate (ℓ' - ℓ) a) f)
        have hsub := projC_add_projN C (rowAct A (List.replicate ℓ a)
          (rowAct A (List.replicate (ℓ' - ℓ) a) f))
        rw [h0, add_zero] at hsub
        exact ⟨_, hsub⟩
      rw [show f = fitProjC A a ℓ' f + fitProjN A a ℓ' f by simp [fitProjN]]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hPC_in)
        (Submodule.mem_sup_right ⟨f, rfl⟩)
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (projC C)) (LinearMap.range (fitProjN A a ℓ'))
    rw [hsup, hdisj, finrank_top, finrank_bot, Module.finrank_fintype_fun_eq_card,
        finrank_range_projC] at hsum
    dsimp only [n, m, C] at hsum ⊢; omega
  have hE0_U0 : ∀ x, eigProj A a C ℓ' ⟨0, by omega⟩ x ∈ U 0 := by
    intro x
    have hsp : eigProj A a C ℓ' ⟨0, by omega⟩ x =
        eigProj A a C ℓ ⟨0, by omega⟩ (rowAct A (List.replicate (ℓ' - ℓ) a) x) := by
      simp only [eigProj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.smul_apply]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      rw [← rowAct_append, ← List.replicate_add]
      rw [show ℓ' - ℓ + (ℓ + j.val) = ℓ' + j.val by dsimp only [ℓ', ℓ] at hℓ'_ge ⊢; omega]
    rw [hsp, eigProj_zero_mem_span A a h1c, hU0]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hsum_zero : ∑ i ∈ CircularDubuc.annulusSet p m D, ψ (rowAct A (wordChain a p b i) vC) = 0 := by
    have hrew : ∀ i, ψ (rowAct A (wordChain a p b i) vC) =
        ∑ σ : Fin p → Option (Fin m), ψ (branchVec A a C ℓ' p b i σ vC) := by
      intro i
      rw [rowAct_wordChain_eq_sum_branch A a C ℓ' hm_pos p b i vC, map_sum]
    simp_rw [hrew]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    exact branch_annular_sum_eq_zero A a h1c ℓ' p hℓ'_ge hm2 hp_pos hp_lt_n U hU0 hU_mono
      hU_T hU_step ψ (fun x hx => hp_prev hx 0) (fun x ⟨u, hu⟩ => by
        subst hu
        dsimp [ψ, LinearMap.comp_apply, fitProjN, fitProjC]
        have h0 : rowAct A (List.replicate ℓ a) (u - rowAct A (List.replicate ℓ' a) u) = 0 := by
          rw [map_sub]
          have hcomp : (rowAct A (List.replicate ℓ a)) ((rowAct A (List.replicate ℓ' a)) u) =
              rowAct A (List.replicate ℓ' a) (rowAct A (List.replicate ℓ a) u) := by
            rw [← rowAct_append, ← List.replicate_add, add_comm ℓ' ℓ, List.replicate_add, rowAct_append]
          rw [hcomp]
          have hTℓ : rowAct A (List.replicate ℓ a) u ∈ LinearMap.range (projC C) := by
            have h0' := nilpotent_projN A a C ℓ (fun q => eval_replicate_mem_cycleStates A a q 0) u
            have hsub := projC_add_projN C (rowAct A (List.replicate ℓ a) u)
            rw [h0', add_zero] at hsub
            exact ⟨_, hsub⟩
          have hpow : ∀ t : ℕ, ∀ y ∈ LinearMap.range (projC C),
              rowAct A (List.replicate (t * m) a) y = y := by
            intro t y hy
            induction t with
            | zero => simp [rowAct_nil]
            | succ t iht =>
              rw [Nat.succ_mul, List.replicate_add, rowAct_append, iht]
              exact rowAct_replicate_period_of_mem A a h1c hy
          rw [hpow (ℓ / m + 1) _ hTℓ, sub_self]
        rw [h0, map_zero]) hVN_dim hfit_idem hE0_U0 b σ
  -- Contradiction: `∑ i, (ψ (wordChain i)).re = 0`, every term is `≤ 0`, yet `i'` has `≠ 0`!
  have hsum_re : ∑ i ∈ CircularDubuc.annulusSet p m D,
      (ψ (rowAct A (wordChain a p b i) vC)).re = 0 := by
    have := congrArg Complex.re hsum_zero
    simpa [Complex.zero_re] using this
  have hle_all : ∀ i ∈ CircularDubuc.annulusSet p m D,
      (ψ (rowAct A (wordChain a p b i) vC)).re ≤ 0 := by
    intro i hi
    have hi_sum : ∑ r : Fin p, i r ≤ D :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hlen : (wordChain a p b i).length ≤ n := by
      rw [wordChain_length]; omega
    exact (hψ_le (wordChain a p b i) hlen).1
  have h_all0 : ∀ i ∈ CircularDubuc.annulusSet p m D,
      (ψ (rowAct A (wordChain a p b i) vC)).re = 0 := by
    have hle_sum : ∑ i ∈ CircularDubuc.annulusSet p m D,
        (ψ (rowAct A (wordChain a p b i) vC)).re ≤ 0 :=
      Finset.sum_nonpos hle_all
    intro i hi
    by_contra hne
    have hlt : (ψ (rowAct A (wordChain a p b i) vC)).re < 0 :=
      lt_of_le_of_ne (hle_all i hi) hne
    have hsp := Finset.add_sum_erase (CircularDubuc.annulusSet p m D)
      (fun k => (ψ (rowAct A (wordChain a p b k) vC)).re) hi
    have hrest : ∑ k ∈ (CircularDubuc.annulusSet p m D).erase i,
        (ψ (rowAct A (wordChain a p b k) vC)).re ≤ 0 :=
      Finset.sum_nonpos (fun k hk => hle_all k (Finset.mem_of_mem_erase hk))
    linarith
  have hi'_re0 := h_all0 i' hi'_mem
  have hi'_im0 : (ψ (rowAct A (wordChain a p b i') vC)).im = 0 := by
    have hi_sum : ∑ r : Fin p, i' r ≤ D :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi'_mem).1).2
    have hlen : (wordChain a p b i').length ≤ n := by rw [wordChain_length]; omega
    exact (hψ_le (wordChain a p b i') hlen).2
  have hi'_zero : ψ (rowAct A (wordChain a p b i') vC) = 0 :=
    Complex.ext hi'_re0 hi'_im0
  rw [hψ_i'] at hi'_zero
  exact hψ_ne hi'_zero

/-- **Full One-Cluster Černý Bound**:
Every synchronizing automaton with a one-cluster letter `a` has a synchronizing word
of length at most `(n - 1) ^ 2` (including `n = 1` where `[]` synchronizes in length `0`). -/
theorem one_cluster_cerny_bound
    (A : Aut Q α) (hsync : A.IsSync) (a : α) (h1c : IsOneCluster A a) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  let C := cycleStates A a
  let m := C.card
  let ℓ := cycleLevel A a
  let n := Fintype.card Q
  have hm_pos : 1 ≤ m := (cycleStates_nonempty A a).card_pos
  have hℓ_le : ℓ ≤ n - m := cycleLevel_le A a
  have hm_le_n : m ≤ n := Finset.card_le_univ C
  by_cases hm1 : m = 1
  · exact one_cluster_m_eq_one_bound A a hm1
  · have hm2 : 2 ≤ m := by omega
    have hbound_le : (n - m + 1 + ℓ) + (m - 2) * (n + ℓ) + ℓ ≤ (n - 1) ^ 2 := by
      have h1 : (m - 2) * (n + ℓ) ≤ (m - 2) * (n + (n - m)) :=
        Nat.mul_le_mul_left (m - 2) (Nat.add_le_add_left hℓ_le n)
      let d := n - m
      let k := m - 2
      have hn_d : n = d + k + 2 := by dsimp only [d, k, m, n] at hm_le_n hm2 ⊢; omega
      have hm_k : m = k + 2 := by dsimp only [k, m] at hm2 ⊢; omega
      have h_alg : d + 1 + (n - m) + k * (n + (n - m)) + (n - m) ≤ (n - 1) ^ 2 := by
        have h_n1 : n - 1 = d + k + 1 := by omega
        have h_2n : n + (n - m) = 2 * d + k + 2 := by omega
        have hdd : d ≤ d * d := Nat.le_mul_self d
        rw [h_n1, h_2n]
        change d + 1 + d + k * (2 * d + k + 2) + d ≤ (d + k + 1) ^ 2
        nlinarith
      dsimp only [d, k, m, n, ℓ] at hℓ_le h1 h_alg ⊢
      omega
    obtain ⟨c₀, _, w₁, hw₁_len, hw₁_card⟩ := multi_cluster_initial_step A hsync a hm2
    let u₀ := w₁ ++ List.replicate ℓ a
    let S₁ := A.preimage {c₀} u₀
    have hu₀_len : u₀.length ≤ n - m + 1 + ℓ := by
      simp only [u₀, List.length_append, List.length_replicate]
      dsimp only [m, n, ℓ, C] at hw₁_len ⊢; omega
    have hgrow : ∀ d : ℕ, ∀ S : Finset Q, ∀ u : List α,
        (S ∩ C).card + d = m → 2 ≤ (S ∩ C).card →
        S ⊆ A.preimage {c₀} u → u.length ≤ (n - m + 1 + ℓ) + ((S ∩ C).card - 2) * (n + ℓ) →
        ∃ v : List α, C ⊆ A.preimage {c₀} v ∧
          v.length ≤ (n - m + 1 + ℓ) + (m - 2) * (n + ℓ) := by
      intro d
      induction d using Nat.strong_induction_on with
      | ind d ih =>
        intro S u hd hS2 hSu hulen
        by_cases hd0 : d = 0
        · subst hd0
          have hSC_eq : S ∩ C = C :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
          refine ⟨u, ?_, ?_⟩
          · rw [← hSC_eq]; exact Finset.inter_subset_left.trans hSu
          · rw [show (S ∩ C).card = m by omega] at hulen; exact hulen
        · have hS_lt : (S ∩ C).card < m := by omega
          obtain ⟨w, hw_len, hw_gt⟩ :=
            one_cluster_annular_extension A hsync a h1c hm2 (Nat.le_trans (by decide : 1 ≤ 2) hS2)
              (by dsimp only [m, C] at hS_lt ⊢; exact hS_lt)
          let S' := A.preimage S w
          have hS'_le : (S' ∩ C).card ≤ m := Finset.card_le_card Finset.inter_subset_right
          have hS'_pre : S' ⊆ A.preimage {c₀} (w ++ u) := by
            rw [← Aut.preimage_append]; exact A.preimage_mono hSu _
          have hlen' : (w ++ u).length ≤ (n - m + 1 + ℓ) + ((S' ∩ C).card - 2) * (n + ℓ) := by
            simp only [List.length_append]
            have hmul : ((S ∩ C).card - 2) * (n + ℓ) + (n + ℓ) ≤
                ((S' ∩ C).card - 2) * (n + ℓ) := by
              rw [← Nat.succ_mul]
              exact Nat.mul_le_mul_right (n + ℓ) (by dsimp only [S', C] at hS2 hw_gt ⊢; omega)
            dsimp only [S', m, n, ℓ, C] at hw_len hw_gt hulen hmul ⊢
            omega
          exact ih (m - (S' ∩ C).card) (by dsimp only [S', m, C] at *; omega) S' (w ++ u)
            (by dsimp only [S', m, C] at *; omega) (by dsimp only [S', C] at *; omega) hS'_pre hlen'
    obtain ⟨v, hvC, hv_len⟩ := hgrow (m - (S₁ ∩ C).card) S₁ u₀
      (by have := Finset.card_le_card (Finset.inter_subset_right : S₁ ∩ C ⊆ C); omega)
      hw₁_card (Finset.Subset.refl _) (hu₀_len.trans (Nat.le_add_right _ _))
    refine ⟨List.replicate ℓ a ++ v, ?_, ?_⟩
    · rw [Aut.isSyncWord_iff_preimage_univ]
      refine ⟨c₀, Finset.eq_univ_iff_forall.mpr (fun q => ?_)⟩
      rw [← Aut.preimage_append, Aut.mem_preimage]
      exact hvC (eval_replicate_mem_cycleStates A a q 0)
    · simp only [List.length_append, List.length_replicate]
      dsimp only [m, n, ℓ] at hv_len hbound_le ⊢; omega

/-- **Dubuc's Circular Theorem**: every synchronizing automaton with a circular letter `a`
(`a` is a single `n`-cycle on `Q`) has a synchronizing word of length at most `(n - 1) ^ 2`. -/
theorem dubuc_circular_bound
    (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (hcyc : ∀ p q : Q, ∃ k : ℕ, A.eval p (List.replicate k a) = q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have heval_bij : ∀ k : ℕ, Function.Bijective (fun q => A.eval q (List.replicate k a)) := by
    intro k
    induction k with
    | zero => simpa [Aut.eval] using Function.bijective_id
    | succ k ih =>
      have : (fun q => A.eval q (List.replicate (k + 1) a)) =
          (fun q => A.step q a) ∘ (fun q => A.eval q (List.replicate k a)) := by
        ext q; rw [List.replicate_succ', Aut.eval_append]; rfl
      rw [this]
      exact hbij.comp ih
  have h1c : IsOneCluster A a := by
    intro p hp q hq
    have hk_ex := hcyc p q
    let k := Nat.find hk_ex
    have hk_eq : A.eval p (List.replicate k a) = q := Nat.find_spec hk_ex
    have hk_lt : k < (cycleStates A a).card := by
      have hcard_pos : 0 < (cycleStates A a).card := (cycleStates_nonempty A a).card_pos
      have hk_lt_n : k < Fintype.card Q := by
        by_contra hge
        have hnotinj : ¬ Function.Injective
            (fun i : Fin (k + 1) => A.eval p (List.replicate i.1 a)) := by
          intro hinj
          have := Fintype.card_le_of_injective _ hinj
          rw [Fintype.card_fin] at this
          omega
        rw [Function.Injective] at hnotinj
        push Not at hnotinj
        obtain ⟨i₁, i₂, hEq, hne⟩ := hnotinj
        wlog hlt : i₁ < i₂ generalizing i₁ i₂
        · exact this i₂ i₁ hEq.symm hne.symm (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
        have hdiff : i₂.1 = i₁.1 + (i₂.1 - i₁.1) := by omega
        have hEq' : A.eval p (List.replicate (i₂.1 - i₁.1) a) = p := by
          apply (heval_bij i₁.1).injective
          dsimp only
          rw [← Aut.eval_append, ← List.replicate_add, add_comm, ← hdiff]
          exact hEq.symm
        have hk_eq' : A.eval p (List.replicate (k - (i₂.1 - i₁.1)) a) = q := by
          have hk_split : k = (i₂.1 - i₁.1) + (k - (i₂.1 - i₁.1)) := by omega
          conv_lhs => rw [← hEq']
          rw [← Aut.eval_append, ← List.replicate_add, ← hk_split, hk_eq]
        have hmin := Nat.find_min hk_ex (by omega : k - (i₂.1 - i₁.1) < k)
        exact hmin hk_eq'
      have hC_univ : cycleStates A a = Finset.univ := by
        refine Finset.eq_univ_iff_forall.mpr (fun x => ?_)
        have hmem := eval_replicate_mem_cycleStates A a
          ((heval_bij (cycleLevel A a)).surjective x).choose 0
        have hspec := ((heval_bij (cycleLevel A a)).surjective x).choose_spec
        simpa [hspec] using hmem
      rw [hC_univ, Finset.card_univ]
      exact hk_lt_n
    exact ⟨k, hk_lt, hk_eq⟩
  exact one_cluster_cerny_bound A hsync a h1c

end MainBounds

end Cerny.OneClusterAnnular