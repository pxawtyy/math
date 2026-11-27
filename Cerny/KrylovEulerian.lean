import Cerny.Defs
import Cerny.Linear
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Universal Krylov Lemma and Kari's Theorem for Eulerian Automata

This module proves:
1. `krylov_nonconstant_preimage`: for any synchronizing automaton (without assuming
   strong connectivity!) and any nonempty proper subset `S ⊂ Q`, there exists a word
   `w` of length `≤ n - 1` such that `|(A.preimage S w)| ≠ |S|`.
2. `kari_eulerian_bound`: every synchronizing Eulerian automaton on `n ≥ 1` states
   has a synchronizing word of length at most `(n - 1)^2`.
-/

namespace KrylovEulerian

section Krylov
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

/-- Pullback linear operator `T w f p = f (A.eval p w)` on `Q → ℚ`.
This is the specialization of `Cerny.Linear.pullbackLin` to `ℚ`. -/
abbrev pullbackLin (w : List α) : (Q → ℚ) →ₗ[ℚ] (Q → ℚ) :=
  Cerny.Linear.pullbackLin ℚ A w

lemma pullbackLin_nil : pullbackLin A [] = LinearMap.id :=
  Cerny.Linear.pullbackLin_nil ℚ A

lemma pullbackLin_append (u v : List α) :
    pullbackLin A (u ++ v) = (pullbackLin A u) ∘ₗ (pullbackLin A v) :=
  Cerny.Linear.pullbackLin_append ℚ A u v

lemma pullbackLin_cons (a : α) (w : List α) :
    pullbackLin A (a :: w) = (pullbackLin A [a]) ∘ₗ (pullbackLin A w) :=
  Cerny.Linear.pullbackLin_cons ℚ A a w

/-- Sum functional `σ f = ∑ q, f q` on `Q → ℚ`. -/
def sumLin (Q : Type*) [Fintype Q] : (Q → ℚ) →ₗ[ℚ] ℚ where
  toFun f := ∑ q : Q, f q
  map_add' f g := Finset.sum_add_distrib
  map_smul' c f := by simp [Finset.mul_sum]

lemma finrank_ker_sumLin [Nonempty Q] :
    Module.finrank ℚ (LinearMap.ker (sumLin Q)) = Fintype.card Q - 1 := by
  have hsurj : LinearMap.range (sumLin Q) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    refine ⟨fun _ => y / (Fintype.card Q : ℚ), ?_⟩
    simp only [sumLin, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hcard : (Fintype.card Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  have hrk := LinearMap.finrank_range_add_finrank_ker (sumLin Q)
  rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card] at hrk
  have h1 : Module.finrank ℚ ℚ = 1 := Module.finrank_self ℚ
  rw [h1] at hrk
  omega

/-- Universal Krylov lemma (without strong connectivity): for any synchronizing
automaton and any `1 ≤ |S| < n`, there exists `w` of length `≤ n - 1` with
`|(A.preimage S w)| ≠ |S|`. -/
theorem krylov_nonconstant_preimage [Nonempty Q] (hsync : A.IsSync)
    {S : Finset Q} (hS_pos : 1 ≤ S.card) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α, w.length ≤ Fintype.card Q - 1 ∧ (A.preimage S w).card ≠ S.card := by
  classical
  by_contra hconst
  push_neg at hconst
  let n := Fintype.card Q
  let H := LinearMap.ker (sumLin Q)
  let indS : Q → ℚ := fun q => if q ∈ S then 1 else 0
  let ones : Q → ℚ := fun _ => 1
  let v₀ : Q → ℚ := indS - ((S.card : ℚ) / (n : ℚ)) • ones
  have hn_pos : (0 : ℚ) < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn_ne : (n : ℚ) ≠ 0 := ne_of_gt hn_pos
  have hv₀_mem : v₀ ∈ H := by
    simp only [H, LinearMap.mem_ker, v₀, map_sub, map_smul, sumLin, LinearMap.coe_mk,
      AddHom.coe_mk, indS, ones, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
    field_simp
    ring
  have hv₀_ne : v₀ ≠ 0 := by
    intro h0
    obtain ⟨q₀, hq₀⟩ := Finset.card_pos.mp hS_pos
    have hval := congrFun h0 q₀
    simp only [v₀, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, indS, ones, if_pos hq₀, mul_one,
      Pi.zero_apply] at hval
    have hlt_q : (S.card : ℚ) < (n : ℚ) := by exact_mod_cast hS_lt
    field_simp at hval
    linarith
  have hsum_pull : ∀ w : List α,
      sumLin Q (pullbackLin A w v₀) = ((A.preimage S w).card : ℚ) - (S.card : ℚ) := by
    intro w
    simp only [sumLin, pullbackLin, Cerny.Linear.pullbackLin_apply, LinearMap.coe_mk,
      AddHom.coe_mk, v₀, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, indS, ones, mul_one, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hpre : ∑ q : Q, (if A.eval q w ∈ S then (1 : ℚ) else 0) =
        ((A.preimage S w).card : ℚ) := by
      simp [Aut.preimage, Finset.sum_boole]
    rw [hpre]
    have hnq : (Fintype.card Q : ℚ) = (n : ℚ) := rfl
    rw [hnq]
    field_simp
  -- Define Krylov chain U t ⊆ Q → ℚ
  let U : ℕ → Submodule ℚ (Q → ℚ) := fun t =>
    Submodule.span ℚ {f | ∃ w : List α, w.length ≤ t ∧ f = pullbackLin A w v₀}
  have hU_mono : ∀ t, U t ≤ U (t + 1) := by
    intro t
    apply Submodule.span_mono
    rintro f ⟨w, hw, rfl⟩
    exact ⟨w, by omega, rfl⟩
  have hU_le_H : ∀ t ≤ n - 1, U t ≤ H := by
    intro t ht
    rw [Submodule.span_le]
    rintro f ⟨w, hw, rfl⟩
    change pullbackLin A w v₀ ∈ H
    rw [LinearMap.mem_ker, hsum_pull w, hconst w (by omega), sub_self]
  have hU0_pos : 1 ≤ Module.finrank ℚ (U 0) := by
    have hv₀_in_U0 : v₀ ∈ U 0 := by
      apply Submodule.subset_span
      exact ⟨[], by simp, by simp [pullbackLin_nil]⟩
    have hbot : (⊥ : Submodule ℚ (Q → ℚ)) < U 0 := by
      rw [bot_lt_iff_ne_bot]
      intro h0
      rw [h0, Submodule.mem_bot] at hv₀_in_U0
      exact hv₀_ne hv₀_in_U0
    have hlt := Submodule.finrank_lt_finrank_of_lt hbot
    rw [finrank_bot] at hlt
    omega
  have hstab : ∃ t < n - 1, U t = U (t + 1) := by
    by_contra hno
    push_neg at hno
    have hinc : ∀ t ≤ n - 1, t + 1 ≤ Module.finrank ℚ (U t) := by
      intro t ht
      induction t with
      | zero => exact hU0_pos
      | succ t ih =>
        have hlt_sub : U t < U (t + 1) := lt_of_le_of_ne (hU_mono t) (hno t (by omega))
        have hlt_rk := Submodule.finrank_lt_finrank_of_lt hlt_sub
        have ih' := ih (by omega)
        omega
    have htop := hinc (n - 1) le_rfl
    have hle_H : Module.finrank ℚ (U (n - 1)) ≤ Module.finrank ℚ H :=
      Submodule.finrank_mono (hU_le_H (n - 1) le_rfl)
    rw [finrank_ker_sumLin] at hle_H
    have hn2 : 2 ≤ n := by omega
    omega
  obtain ⟨t, ht_lt, ht_eq⟩ := hstab
  have hinv : ∀ a : α, ∀ f ∈ U t, pullbackLin A [a] f ∈ U t := by
    intro a f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨w, hw, rfl⟩
      rw [ht_eq]
      apply Submodule.subset_span
      refine ⟨a :: w, by simp; omega, ?_⟩
      rw [pullbackLin_cons]
      rfl
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (U t).add_mem hx hy
    | smul c x _ hx =>
      rw [map_smul]
      exact (U t).smul_mem c hx
  have hall_in_Ut : ∀ w : List α, pullbackLin A w v₀ ∈ U t := by
    intro w
    induction w with
    | nil =>
      rw [pullbackLin_nil]
      apply Submodule.span_mono (s := {f | ∃ u : List α, u.length ≤ 0 ∧ f = pullbackLin A u v₀})
      · rintro f ⟨u, hu, rfl⟩
        exact ⟨u, by omega, rfl⟩
      · exact Submodule.subset_span ⟨[], le_rfl, rfl⟩
    | cons a w ih =>
      rw [pullbackLin_cons]
      exact hinv a _ ih
  -- Contradict with synchronizing word u₀
  obtain ⟨u₀, hu₀⟩ := hsync
  rw [Aut.isSyncWord_iff_exists_eval_eq] at hu₀
  obtain ⟨c_star, hc_star⟩ := hu₀
  have hu₀_in_H : pullbackLin A u₀ v₀ ∈ H := hU_le_H t (by omega) (hall_in_Ut u₀)
  rw [LinearMap.mem_ker, hsum_pull u₀] at hu₀_in_H
  by_cases hc : c_star ∈ S
  · have hpre : A.preimage S u₀ = Finset.univ := by
      ext q; simp [hc_star q, hc]
    rw [hpre, Finset.card_univ] at hu₀_in_H
    have : (n : ℚ) = (S.card : ℚ) := by linarith
    have : n = S.card := Nat.cast_injective this
    omega
  · have hpre : A.preimage S u₀ = ∅ := by
      ext q; simp [hc_star q, hc]
    rw [hpre, Finset.card_empty] at hu₀_in_H
    simp only [Nat.cast_zero, zero_sub, neg_eq_zero, Nat.cast_eq_zero] at hu₀_in_H
    omega

end Krylov

section Eulerian
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] [Fintype α] [DecidableEq α] (A : Aut Q α)

/-- An automaton is Eulerian if every state has in-degree equal to `|α|`. -/
def IsEulerian : Prop :=
  ∀ q : Q, (Finset.univ.filter (fun pa : Q × α => A.step pa.1 pa.2 = q)).card = Fintype.card α

lemma eulerian_preimage_avg (heul : IsEulerian A) (S : Finset Q) (w : List α) :
    ∑ a : α, (A.preimage S (a :: w)).card = Fintype.card α * (A.preimage S w).card := by
  let S' := A.preimage S w
  have hrewrite : ∀ a : α, (A.preimage S (a :: w)).card =
      ∑ p : Q, if A.step p a ∈ S' then 1 else 0 := by
    intro a
    rw [← Finset.card_filter]
    congr 1
    ext p
    simp [S', Aut.eval_cons]
  simp_rw [hrewrite]
  rw [Finset.sum_comm]
  have hpair : ∑ p : Q, ∑ a : α, (if A.step p a ∈ S' then 1 else 0) =
      ∑ pa : Q × α, if A.step pa.1 pa.2 ∈ S' then 1 else 0 :=
    (Fintype.sum_prod_type (fun pa : Q × α => if A.step pa.1 pa.2 ∈ S' then 1 else 0)).symm
  rw [hpair]
  have hsplit : ∑ pa : Q × α, (if A.step pa.1 pa.2 ∈ S' then 1 else 0) =
      ∑ q ∈ S', ∑ pa : Q × α, if A.step pa.1 pa.2 = q then 1 else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun pa _ => ?_
    by_cases h : A.step pa.1 pa.2 ∈ S'
    · simp [h, Finset.sum_ite_eq]
    · simp [h, Finset.sum_ite_eq]
  rw [hsplit]
  have hconst : ∀ q ∈ S', ∑ pa : Q × α, (if A.step pa.1 pa.2 = q then 1 else 0) = Fintype.card α := by
    intro q _
    rw [← Finset.card_filter]
    exact heul q
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]

/-- Kari's theorem: every synchronizing Eulerian automaton on `n ≥ 1` states
has a synchronizing word of length at most `(n - 1)^2`. -/
theorem kari_eulerian_bound [Nonempty Q] (heul : IsEulerian A) (hsync : A.IsSync) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  let n := Fintype.card Q
  by_cases hn1 : n ≤ 1
  · have h1 : Fintype.card Q = 1 := by have := Fintype.card_pos (α := Q); omega
    obtain ⟨w, hw⟩ := A.isSync_of_card_eq_one h1
    by_cases hw0 : A.IsSyncWord []
    · exact ⟨[], hw0, by simp⟩
    · have : A.IsSyncWord [] := by
        haveI : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        exact A.isSyncWord_nil_of_subsingleton
      exact ⟨[], this, by simp⟩
  · have hn2 : 2 ≤ n := by omega
    have hα_pos : 0 < Fintype.card α := by
      by_contra h0
      have hα0 : Fintype.card α = 0 := by omega
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hα0
      obtain ⟨w, hw⟩ := hsync
      cases w with
      | nil =>
        simp only [Aut.IsSyncWord, Aut.image_nil, Finset.card_univ] at hw
        omega
      | cons a _ => exact IsEmpty.false a
    have hstep : ∀ S : Finset Q, 1 ≤ S.card → S.card < n →
        ∃ w : List α, w.length ≤ n - 1 ∧ S.card < (A.preimage S w).card := by
      intro S hS1 hSn
      by_contra hno
      push_neg at hno
      have heq_len : ∀ k ≤ n - 1, ∀ w : List α, w.length = k → (A.preimage S w).card = S.card := by
        intro k
        induction k with
        | zero =>
          intro _ w hw
          rw [List.length_eq_zero_iff] at hw
          subst hw
          simp
        | succ k ih =>
          intro hk w hw
          cases w with
          | nil => simp at hw
          | cons a u =>
            simp only [List.length_cons] at hw
            have hu_eq : (A.preimage S u).card = S.card := ih (by omega) u (by omega)
            have havg := eulerian_preimage_avg A heul S u
            rw [hu_eq] at havg
            have hle_all : ∀ b ∈ (Finset.univ : Finset α), (A.preimage S (b :: u)).card ≤ S.card := by
              intro b _
              exact hno (b :: u) (by simp; omega)
            have hsum_le : ∑ b : α, (A.preimage S (b :: u)).card ≤ ∑ _b : α, S.card :=
              Finset.sum_le_sum hle_all
            have hsum_eq : ∑ b : α, (A.preimage S (b :: u)).card = ∑ _b : α, S.card := by
              rw [havg]
              simp [Finset.sum_const, smul_eq_mul]
            have hall_eq := (Finset.sum_eq_sum_iff_of_le hle_all).mp hsum_eq
            exact hall_eq a (Finset.mem_univ a)
      obtain ⟨w, hw_len, hw_ne⟩ := krylov_nonconstant_preimage A hsync hS1 hSn
      exact hw_ne (heq_len w.length hw_len w rfl)
    -- Backward expansion from {q₀} to Finset.univ
    obtain ⟨q₀⟩ := ‹Nonempty Q›
    have hgrow : ∀ d : ℕ, ∀ u : List α, (A.preimage {q₀} u).card + d = n →
        1 ≤ (A.preimage {q₀} u).card → u.length ≤ ((A.preimage {q₀} u).card - 1) * (n - 1) →
        ∃ w : List α, A.preimage {q₀} w = Finset.univ ∧ w.length ≤ (n - 1) ^ 2 := by
      intro d
      induction d using Nat.strong_induction_on with
      | ind d ih =>
        intro u hd hpos hlen
        set S := A.preimage {q₀} u
        by_cases hd0 : d = 0
        · subst hd0
          have hS_univ : S = Finset.univ := Finset.eq_univ_of_card S (by omega)
          refine ⟨u, hS_univ, ?_⟩
          have hcard : S.card = n := by omega
          rw [hcard] at hlen
          calc u.length ≤ (n - 1) * (n - 1) := hlen
            _ = (n - 1) ^ 2 := (sq (n - 1)).symm
        · have hS_lt : S.card < n := by omega
          obtain ⟨v, hv_len, hv_gt⟩ := hstep S hpos hS_lt
          set S' := A.preimage S v
          have hS'_eq : S' = A.preimage {q₀} (v ++ u) := Aut.preimage_append A {q₀} u v
          have hd' : S'.card + (n - S'.card) = n := by
            have := Finset.card_le_univ S'
            omega
          have hd'_lt : n - S'.card < d := by omega
          have hS'_pos : 1 ≤ S'.card := by omega
          have hlen' : (v ++ u).length ≤ (S'.card - 1) * (n - 1) := by
            rw [List.length_append]
            have h1 : (S.card - 1) * (n - 1) + (n - 1) = S.card * (n - 1) := by
              calc (S.card - 1) * (n - 1) + (n - 1) = (S.card - 1 + 1) * (n - 1) := by ring
                _ = S.card * (n - 1) := by rw [Nat.sub_add_cancel hpos]
            have h2 : S.card * (n - 1) ≤ (S'.card - 1) * (n - 1) :=
              Nat.mul_le_mul_right (n - 1) (by omega)
            omega
          exact ih (n - S'.card) hd'_lt (v ++ u) (by rw [← hS'_eq]; exact hd')
            (by rw [← hS'_eq]; exact hS'_pos) (by rw [← hS'_eq]; exact hlen')
    obtain ⟨w, hw_univ, hw_len⟩ := hgrow (n - 1) [] (by simp [n]; omega) (by simp) (by simp)
    refine ⟨w, ?_, hw_len⟩
    rw [Aut.isSyncWord_iff_preimage_univ]
    exact ⟨q₀, hw_univ⟩

end Eulerian

end KrylovEulerian
