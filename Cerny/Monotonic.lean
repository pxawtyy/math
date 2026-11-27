import Cerny.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# Monotonic Automata: `rt(A) ≤ n - 1`

This module proves that any synchronizing monotonic automaton on `Fin n` (`n ≥ 1`)
admits a synchronizing word of length at most `n - 1`.
-/

namespace Monotonic

section Basics
variable {n : ℕ} {α : Type*} (A : Aut (Fin n) α)

/-- An automaton on `Fin n` is monotonic if every letter preserves the order `≤`. -/
def IsMonotonic : Prop :=
  ∀ (p q : Fin n) (a : α), p ≤ q → A.step p a ≤ A.step q a

lemma eval_mono (hm : IsMonotonic A) {p q : Fin n} (hpq : p ≤ q) (w : List α) :
    A.eval p w ≤ A.eval q w := by
  induction w generalizing p q with
  | nil => exact hpq
  | cons a w ih => exact ih (hm p q a hpq)

/-- Prefix `{0, ..., k - 1}` in `Fin n`. -/
def pref (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun q => q.1 < k)

@[simp]
lemma mem_pref {k : ℕ} {q : Fin n} : q ∈ pref n k ↔ q.1 < k := by
  simp [pref]

lemma pref_zero : pref n 0 = ∅ := by
  ext q; simp

lemma pref_self : pref n n = Finset.univ := by
  ext q; simp [q.2]

lemma card_pref {k : ℕ} (hk : k ≤ n) : (pref n k).card = k := by
  have himg : pref n k = (Finset.range k).attach.image (fun j => ⟨j.1, lt_of_lt_of_le (Finset.mem_range.mp j.2) hk⟩) := by
    ext q
    simp only [mem_pref, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
      Finset.mem_range, Fin.ext_iff]
    constructor
    · intro hq; exact ⟨q.1, hq, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact hj
  rw [himg, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact Subtype.ext (congrArg Fin.val hab)

lemma downward_eq_pref (S : Finset (Fin n))
    (hdown : ∀ p q : Fin n, q ∈ S → p ≤ q → p ∈ S) :
    S = pref n S.card := by
  have hsub : S ⊆ pref n S.card := by
    intro q hq
    rw [mem_pref]
    have hpref_sub : pref n (q.1 + 1) ⊆ S := by
      intro p hp
      rw [mem_pref] at hp
      exact hdown p q hq (Fin.le_iff_val_le_val.mpr (by omega))
    have hcard : q.1 + 1 ≤ S.card := by
      calc q.1 + 1 = (pref n (q.1 + 1)).card := (card_pref (by omega : q.1 + 1 ≤ n)).symm
        _ ≤ S.card := Finset.card_le_card hpref_sub
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [card_pref (Finset.card_le_univ S |>.trans_eq (Fintype.card_fin n))]

/-- Induced action `τ A w k := |(pref n k) · w⁻¹|` on `{0, ..., n}`. -/
def tau (w : List α) (k : ℕ) : ℕ :=
  (A.preimage (pref n k) w).card

lemma tau_le (w : List α) (k : ℕ) : tau A w k ≤ n := by
  unfold tau
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

lemma preimage_pref (hm : IsMonotonic A) (w : List α) (k : ℕ) :
    A.preimage (pref n k) w = pref n (tau A w k) := by
  apply downward_eq_pref
  intro p q hq hpq
  rw [Aut.mem_preimage, mem_pref] at hq ⊢
  have hle : (A.eval p w).1 ≤ (A.eval q w).1 := eval_mono A hm hpq w
  omega

@[simp]
lemma tau_nil {k : ℕ} (hk : k ≤ n) : tau A [] k = k := by
  simp [tau, card_pref hk]

@[simp]
lemma tau_zero (w : List α) : tau A w 0 = 0 := by
  simp [tau, pref_zero]

@[simp]
lemma tau_self (w : List α) : tau A w n = n := by
  simp [tau, pref_self]

lemma tau_mono {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (w : List α) :
    tau A w k₁ ≤ tau A w k₂ := by
  apply Finset.card_le_card
  apply Aut.preimage_mono
  intro q hq
  rw [mem_pref] at hq ⊢
  omega

lemma tau_append (hm : IsMonotonic A) (v u : List α) (k : ℕ) :
    tau A (v ++ u) k = tau A v (tau A u k) := by
  simp only [tau, ← Aut.preimage_append]
  rw [preimage_pref A hm u k, card_pref (tau_le A u k)]

end Basics

section Main
variable {n : ℕ} {α : Type*} (A : Aut (Fin n) α)

/-- Any synchronizing monotonic automaton on `Fin n` (`n ≥ 1`) has a synchronizing word
of length at most `n - 1`. -/
theorem monotonic_cerny_bound (hn : 1 ≤ n) (hm : IsMonotonic A) (hsync : A.IsSync) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ n - 1 := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hU_ne : ∃ k, k ≤ n ∧ ∃ w : List α, tau A w k = n :=
    ⟨n, le_rfl, [], tau_self A []⟩
  let k_star : ℕ := Nat.find hU_ne
  have hk_spec := Nat.find_spec hU_ne
  have hk_le : k_star ≤ n := hk_spec.1
  have hk_pos : 1 ≤ k_star := by
    by_contra h0
    have hkz : k_star = 0 := by omega
    obtain ⟨w, hw⟩ := hk_spec.2
    change tau A w k_star = n at hw
    rw [hkz, tau_zero] at hw
    omega
  -- Closure of {0, ..., k_star - 1} under tau
  have hbelow_closed : ∀ (w : List α) {k : ℕ}, k < k_star → tau A w k < k_star := by
    intro w k hk
    by_contra hge
    have hk_le_tau : k_star ≤ tau A w k := by omega
    obtain ⟨u, hu⟩ := hk_spec.2
    have htau_n : tau A (u ++ w) k = n := by
      rw [tau_append A hm]
      have h1 : n = tau A u k_star := hu.symm
      have h2 : tau A u k_star ≤ tau A u (tau A w k) := tau_mono A hk_le_tau u
      have h3 : tau A u (tau A w k) ≤ n := tau_le A u _
      omega
    have hmin := Nat.find_min' hU_ne ⟨(by omega : k ≤ n), u ++ w, htau_n⟩
    change k_star ≤ k at hmin
    omega
  -- Shortest word u with tau A u k_star = n has length ≤ n - k_star
  have hu_len_ex : ∃ m : ℕ, ∃ u : List α, u.length = m ∧ tau A u k_star = n := by
    obtain ⟨u, hu⟩ := hk_spec.2
    exact ⟨u.length, u, rfl, hu⟩
  let m_u := Nat.find hu_len_ex
  obtain ⟨u, hu_len, hu_tau⟩ := Nat.find_spec hu_len_ex
  have hu_bound : u.length ≤ n - k_star := by
    let s : ℕ → ℕ := fun i => tau A (u.drop i) k_star
    have hs_mem : ∀ i ≤ u.length, s i ∈ Finset.Icc k_star n := by
      intro i hi
      rw [Finset.mem_Icc]
      refine ⟨?_, tau_le A _ _⟩
      by_contra hlt
      have h1 : s i < k_star := by omega
      have h2 : tau A (u.take i) (s i) < k_star := hbelow_closed (u.take i) h1
      have h3 : tau A (u.take i) (s i) = n := by
        dsimp only [s]
        rw [← tau_append A hm, List.take_append_drop]
        exact hu_tau
      omega
    have hs_inj : Set.InjOn s (Finset.range (u.length + 1)) := by
      have hcontra : ∀ a b, a < b → b < u.length + 1 → s a = s b → False := by
        intro a b hab hb heq
        let u' := u.take a ++ u.drop b
        have hu'_len : u'.length < m_u := by
          simp only [u', List.length_append, List.length_take, List.length_drop]
          omega
        have hu'_tau : tau A u' k_star = n := by
          dsimp only [u']
          rw [tau_append A hm]
          change tau A (u.take a) (s b) = n
          rw [← heq]
          dsimp only [s]
          rw [← tau_append A hm, List.take_append_drop]
          exact hu_tau
        have hmin := Nat.find_min' hu_len_ex ⟨u', rfl, hu'_tau⟩
        omega
      intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exact absurd hij (fun h => hcontra i j hlt hj h)
      · rfl
      · exact absurd hij.symm (fun h => hcontra j i hgt hi h)
    have hcard := Finset.card_le_card_of_injOn s (fun i hi => hs_mem i (by simp at hi; omega)) hs_inj
    rw [Finset.card_range, Nat.card_Icc] at hcard
    omega
  -- From a sync word w₀ with image {c}, deduce tau A w₀ (k_star - 1) = 0
  have hv_ex : ∃ w : List α, tau A w (k_star - 1) = 0 := by
    obtain ⟨w₀, hw₀⟩ := hsync
    rw [Aut.isSyncWord_iff_exists_eval_eq] at hw₀
    obtain ⟨c, hc⟩ := hw₀
    have hc_top : tau A w₀ (c.1 + 1) = n := by
      unfold tau
      have : A.preimage (pref n (c.1 + 1)) w₀ = Finset.univ := by
        ext q
        simp [hc q]
      rw [this, Finset.card_univ, Fintype.card_fin]
    have hk_le_c : k_star ≤ c.1 + 1 := by
      apply Nat.find_min' hU_ne
      exact ⟨by omega, w₀, hc_top⟩
    have hc_bot : tau A w₀ c.1 = 0 := by
      unfold tau
      have : A.preimage (pref n c.1) w₀ = ∅ := by
        ext q
        simp [hc q]
      rw [this, Finset.card_empty]
    have hle := tau_mono A (by omega : k_star - 1 ≤ c.1) w₀
    rw [hc_bot] at hle
    exact ⟨w₀, by omega⟩
  -- Shortest word v with tau A v (k_star - 1) = 0 has length ≤ k_star - 1
  have hv_len_ex : ∃ m : ℕ, ∃ v : List α, v.length = m ∧ tau A v (k_star - 1) = 0 := by
    obtain ⟨v, hv⟩ := hv_ex
    exact ⟨v.length, v, rfl, hv⟩
  let m_v := Nat.find hv_len_ex
  obtain ⟨v, hv_len, hv_tau⟩ := Nat.find_spec hv_len_ex
  have hv_bound : v.length ≤ k_star - 1 := by
    let t : ℕ → ℕ := fun i => tau A (v.drop i) (k_star - 1)
    have ht_mem : ∀ i ≤ v.length, t i ∈ Finset.range k_star := by
      intro i _
      rw [Finset.mem_range]
      exact hbelow_closed (v.drop i) (by omega)
    have ht_inj : Set.InjOn t (Finset.range (v.length + 1)) := by
      have hcontra : ∀ a b, a < b → b < v.length + 1 → t a = t b → False := by
        intro a b hab hb heq
        let v' := v.take a ++ v.drop b
        have hv'_len : v'.length < m_v := by
          simp only [v', List.length_append, List.length_take, List.length_drop]
          omega
        have hv'_tau : tau A v' (k_star - 1) = 0 := by
          dsimp only [v']
          rw [tau_append A hm]
          change tau A (v.take a) (t b) = 0
          rw [← heq]
          dsimp only [t]
          rw [← tau_append A hm, List.take_append_drop]
          exact hv_tau
        have hmin := Nat.find_min' hv_len_ex ⟨v', rfl, hv'_tau⟩
        omega
      intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exact absurd hij (fun h => hcontra i j hlt hj h)
      · rfl
      · exact absurd hij.symm (fun h => hcontra j i hgt hi h)
    have hcard := Finset.card_le_card_of_injOn t (fun i hi => ht_mem i (by simp at hi; omega)) ht_inj
    rw [Finset.card_range, Finset.card_range] at hcard
    omega
  -- Combine w := v ++ u
  refine ⟨v ++ u, ?_, ?_⟩
  · rw [Aut.isSyncWord_iff_exists_eval_eq]
    refine ⟨⟨k_star - 1, by omega⟩, fun q => Fin.ext ?_⟩
    have htop : tau A (v ++ u) k_star = n := by
      rw [tau_append A hm, hu_tau, tau_self]
    have hbot : tau A (v ++ u) (k_star - 1) = 0 := by
      rw [tau_append A hm]
      have h1 : tau A u (k_star - 1) < k_star := hbelow_closed u (by omega)
      have h2 := tau_mono A (by omega : tau A u (k_star - 1) ≤ k_star - 1) v
      rw [hv_tau] at h2
      omega
    have hpre_univ : A.preimage (pref n k_star) (v ++ u) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin]
      exact htop
    have hpre_empty : A.preimage (pref n (k_star - 1)) (v ++ u) = ∅ := by
      rw [← Finset.card_eq_zero]
      exact hbot
    have hq_in : q ∈ A.preimage (pref n k_star) (v ++ u) := by
      rw [hpre_univ]; exact Finset.mem_univ q
    have hq_out : q ∉ A.preimage (pref n (k_star - 1)) (v ++ u) := by
      rw [hpre_empty]; exact Finset.notMem_empty q
    rw [Aut.mem_preimage, mem_pref] at hq_in hq_out
    dsimp only
    omega
  · rw [List.length_append]
    omega

end Main

end Monotonic
