import Cerny.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Unified Linear Operators on State Functions

This module defines, once and for all, the two linear operators induced by a word:

- `pullbackLin 𝕜 A w f p = f (A.eval p w)` (precomposition), and
- `rowAct 𝕜 A w f q = ∑ p, if A.eval p w = q then f p else 0` (pushforward / row action),

together with the duality `dot (rowAct w f) g = dot f (pullbackLin w g)`.

Specializations to `ℚ` and `ℂ` in the other modules are thin aliases of these
definitions, so the algebraic and spectral arguments share one implementation.
-/

namespace Cerny.Linear

variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- Pullback operator `f ↦ f ∘ eval(·, w)` on `Q → 𝕜`. -/
def pullbackLin (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (w : List α) :
    (Q → 𝕜) →ₗ[𝕜] (Q → 𝕜) where
  toFun f p := f (A.eval p w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pushforward (row-action) operator on `Q → 𝕜`. -/
def rowAct (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (w : List α) :
    (Q → 𝕜) →ₗ[𝕜] (Q → 𝕜) where
  toFun f q := ∑ p : Q, if A.eval p w = q then f p else 0
  map_add' f g := by
    ext q
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  map_smul' c f := by
    ext q
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp

@[simp] lemma pullbackLin_apply (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (w : List α)
    (f : Q → 𝕜) (p : Q) : pullbackLin 𝕜 A w f p = f (A.eval p w) := rfl

@[simp] lemma rowAct_apply (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (w : List α)
    (f : Q → 𝕜) (q : Q) :
    rowAct 𝕜 A w f q = ∑ p : Q, if A.eval p w = q then f p else 0 := rfl

/-- Standard bilinear pairing `∑ q, f q * g q` on `Q → 𝕜`. -/
def dot (𝕜 : Type*) [CommSemiring 𝕜] (f g : Q → 𝕜) : 𝕜 :=
  ∑ q : Q, f q * g q

/-! ### Pullback lemmas -/

lemma pullbackLin_nil (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) :
    pullbackLin 𝕜 A [] = LinearMap.id := by
  ext f p
  rfl

lemma pullbackLin_append (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (u v : List α) :
    pullbackLin 𝕜 A (u ++ v) = (pullbackLin 𝕜 A u) ∘ₗ (pullbackLin 𝕜 A v) := by
  ext f p
  simp [pullbackLin, Aut.eval_append]

lemma pullbackLin_cons (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (a : α) (w : List α) :
    pullbackLin 𝕜 A (a :: w) = (pullbackLin 𝕜 A [a]) ∘ₗ (pullbackLin 𝕜 A w) :=
  pullbackLin_append 𝕜 A [a] w

/-! ### Pushforward lemmas -/

lemma rowAct_nil (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (f : Q → 𝕜) :
    rowAct 𝕜 A [] f = f := by
  ext q
  simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk]
  change (∑ p : Q, if p = q then f p else 0) = f q
  rw [Finset.sum_ite_eq']
  simp

lemma rowAct_append (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (u v : List α) (f : Q → 𝕜) :
    rowAct 𝕜 A (u ++ v) f = rowAct 𝕜 A v (rowAct 𝕜 A u f) := by
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

lemma rowAct_cons (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (a : α) (w : List α)
    (f : Q → 𝕜) :
    rowAct 𝕜 A (a :: w) f = rowAct 𝕜 A w (rowAct 𝕜 A [a] f) := by
  rw [← List.singleton_append, rowAct_append]

lemma rowAct_replicate_succ (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (a : α) (k : ℕ)
    (f : Q → 𝕜) :
    rowAct 𝕜 A (List.replicate (k + 1) a) f =
      rowAct 𝕜 A [a] (rowAct 𝕜 A (List.replicate k a) f) := by
  rw [List.replicate_succ', rowAct_append]

lemma rowAct_eq_iterate (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (a : α) (k : ℕ)
    (f : Q → 𝕜) :
    rowAct 𝕜 A (List.replicate k a) f = ((rowAct 𝕜 A [a])^[k]) f := by
  induction k with
  | zero => simp [rowAct_nil]
  | succ k ih => rw [rowAct_replicate_succ, Function.iterate_succ_apply', ih]

lemma rowAct_one_apply (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (w : List α) (q : Q) :
    (rowAct 𝕜 A w (fun _ => (1 : 𝕜))) q = ((A.preimage {q} w).card : 𝕜) := by
  simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk]
  have hset : Finset.univ.filter (fun p : Q => A.eval p w = q) = A.preimage {q} w := by
    ext p
    simp [Aut.mem_preimage]
  rw [← Finset.sum_filter, hset]
  simp

lemma rowAct_ones_eq_ones_of_bij (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) :
    rowAct 𝕜 A [a] (fun _ => (1 : 𝕜)) = (fun _ => 1) := by
  ext q
  rw [rowAct_one_apply]
  obtain ⟨p₀, hp₀⟩ := hbij.surjective q
  have hsing : A.preimage {q} [a] = {p₀} := by
    ext p
    simp only [Aut.mem_preimage, Finset.mem_singleton, Aut.eval_singleton]
    exact ⟨fun h => hbij.injective (h.trans hp₀.symm), fun h => h.symm ▸ hp₀⟩
  rw [hsing, Finset.card_singleton, Nat.cast_one]

lemma sum_rowAct (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (w : List α) (f : Q → 𝕜) :
    ∑ q : Q, (rowAct 𝕜 A w f) q = ∑ p : Q, f p := by
  simp only [rowAct, LinearMap.coe_mk, AddHom.coe_mk]
  calc
    ∑ q : Q, ∑ p : Q, (if A.eval p w = q then f p else 0)
        = ∑ p : Q, ∑ q : Q, (if A.eval p w = q then f p else 0) := Finset.sum_comm
    _ = ∑ p : Q, f p := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_eq_single (A.eval p w)]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro h
        exact absurd (Finset.mem_univ _) h

/-! ### Duality -/

lemma dot_rowAct_pullbackLin (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (w : List α)
    (f g : Q → 𝕜) :
    dot 𝕜 (rowAct 𝕜 A w f) g = dot 𝕜 f (pullbackLin 𝕜 A w g) := by
  simp only [dot, rowAct, pullbackLin, LinearMap.coe_mk, AddHom.coe_mk]
  trans ∑ q : Q, ∑ p : Q, (if A.eval p w = q then f p else 0) * g q
  · refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_eq_single (A.eval p w)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · intro h
      exact absurd (Finset.mem_univ _) h

lemma dot_rowAct_indicator (𝕜 : Type*) [CommSemiring 𝕜] (A : Aut Q α) (w : List α)
    (f : Q → 𝕜) (S : Finset Q) :
    dot 𝕜 (rowAct 𝕜 A w f) (fun q => if q ∈ S then 1 else 0) =
      dot 𝕜 f (fun q => if q ∈ A.preimage S w then 1 else 0) := by
  rw [dot_rowAct_pullbackLin]
  congr 2
  ext q
  simp [pullbackLin, Aut.mem_preimage]

end Cerny.Linear
