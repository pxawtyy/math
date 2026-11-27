import Cerny.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Pin–Frankl Cubic Upper Bound: `rt(A) ≤ (n^3 - n) / 6`

This module proves Frankl's skew-two intersection theorem (`frankl_skew_two`)
using univariate polynomials over `ℚ` (avoiding exterior algebra and Vandermonde
determinants), and deduces the Pin–Frankl cubic upper bound `pin_frankl_bound`.
-/

namespace PinFrankl

section SkewTwo

/-- Upper triangular index set `{(a, b) | a ≤ b ≤ r}`. -/
def triSet (r : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (r + 1)) ×ˢ (Finset.range (r + 1))).filter (fun p => p.1 ≤ p.2)

lemma mem_triSet {r : ℕ} {p : ℕ × ℕ} :
    p ∈ triSet r ↔ p.1 ≤ p.2 ∧ p.2 ≤ r := by
  simp only [triSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

lemma card_triSet (r : ℕ) : (triSet r).card = (r + 1) * (r + 2) / 2 := by
  induction r with
  | zero =>
    decide
  | succ r ih =>
    have hsplit : triSet (r + 1) =
        triSet r ∪ (Finset.range (r + 2)).image (fun a => (a, r + 1)) := by
      ext p
      simp only [mem_triSet, Finset.mem_union, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hp : p.2 = r + 1
        · right; exact ⟨p.1, by omega, Prod.ext rfl hp.symm⟩
        · left; exact ⟨h1, by omega⟩
      · rintro (⟨h1, h2⟩ | ⟨a, ha, rfl⟩)
        · exact ⟨h1, by omega⟩
        · exact ⟨by omega, le_rfl⟩
    have hdisj : Disjoint (triSet r) ((Finset.range (r + 2)).image (fun a => (a, r + 1))) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [mem_triSet] at hp1
      rw [Finset.mem_image] at hp2
      rcases hp2 with ⟨a, _, rfl⟩
      omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih, Finset.card_image_of_injective]
    · rw [Finset.card_range]
      have heven : 2 ∣ (r + 1) * (r + 2) := by
        rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact ⟨(2 * k + 1) * (k + 1), by ring⟩
        · exact ⟨(k + 1) * (2 * k + 3), by ring⟩
      have heven2 : 2 ∣ (r + 2) * (r + 3) := by
        rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact ⟨(k + 1) * (2 * k + 3), by ring⟩
        · exact ⟨(2 * k + 3) * (k + 2), by ring⟩
      have hdiv := Nat.div_mul_cancel heven
      have hdiv2 := Nat.div_mul_cancel heven2
      have hmul : (r + 1) * (r + 2) + 2 * (r + 2) = (r + 2) * (r + 3) := by ring
      have hmul2 : (r + 1 + 1) * (r + 1 + 2) = (r + 2) * (r + 3) := by ring
      omega
    · intro a b hab
      exact congrArg Prod.fst hab

/-- Frankl's skew-two theorem via univariate polynomials over `ℚ`. -/
theorem frankl_skew_two {Q : Type*} [Fintype Q] [DecidableEq Q]
    {m r : ℕ} (A B : Fin m → Finset Q)
    (hA : ∀ i, (A i).card = 2)
    (hB : ∀ i, (B i).card ≤ r)
    (hdisj : ∀ i, Disjoint (A i) (B i))
    (hskew : ∀ i j : Fin m, j < i → (A i ∩ B j).Nonempty) :
    m ≤ (r + 1) * (r + 2) / 2 := by
  classical
  let ι : Q ↪ ℚ :=
    (Fintype.equivFin Q).toEmbedding.trans
      ⟨fun k => (k.1 : ℚ), fun a b h => Fin.ext (Nat.cast_injective h)⟩
  let P : Fin m → Polynomial ℚ := fun j =>
    ∏ s ∈ B j, (Polynomial.X - Polynomial.C (ι s))
  have hdeg : ∀ j, (P j).natDegree ≤ r := fun j => by
    have hle : ∀ S : Finset Q, (∏ s ∈ S, (Polynomial.X - Polynomial.C (ι s))).natDegree ≤ S.card := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih =>
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
        calc ((Polynomial.X - Polynomial.C (ι a)) *
              ∏ s ∈ S, (Polynomial.X - Polynomial.C (ι s))).natDegree
            ≤ (Polynomial.X - Polynomial.C (ι a)).natDegree +
              (∏ s ∈ S, (Polynomial.X - Polynomial.C (ι s))).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 1 + S.card := by rw [Polynomial.natDegree_X_sub_C]; omega
          _ = S.card + 1 := add_comm _ _
    exact (hle (B j)).trans (hB j)
  have hP_eval : ∀ j (x : ℚ), (P j).eval x = ∑ a ∈ Finset.range (r + 1), (P j).coeff a * x ^ a := by
    intro j x
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg j))]
  have hP_zero_iff : ∀ j (q : Q), (P j).eval (ι q) = 0 ↔ q ∈ B j := by
    intro j q
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Finset.prod_eq_zero_iff, sub_eq_zero]
    constructor
    · rintro ⟨s, hs, hsq⟩
      rw [ι.injective hsq]
      exact hs
    · intro hq
      exact ⟨q, hq, rfl⟩
  let v : Fin m → (↥(triSet r) → ℚ) := fun j p =>
    (P j).coeff p.1.1 * (P j).coeff p.1.2
  have hpair : ∀ i : Fin m, ∃ p q : Q, A i = {p, q} := fun i => by
    obtain ⟨p, q, _, hAi⟩ := Finset.card_eq_two.mp (hA i)
    exact ⟨p, q, hAi⟩
  let p_of : Fin m → Q := fun i => Classical.choose (hpair i)
  let q_of : Fin m → Q := fun i => Classical.choose (Classical.choose_spec (hpair i))
  have hpq_eq : ∀ i, A i = {p_of i, q_of i} := fun i =>
    Classical.choose_spec (Classical.choose_spec (hpair i))
  let φ : Fin m → (↥(triSet r) → ℚ) →ₗ[ℚ] ℚ := fun i =>
    { toFun := fun f =>
        ∑ p : ↥(triSet r), f p *
          if p.1.1 = p.1.2 then (ι (p_of i)) ^ p.1.1 * (ι (q_of i)) ^ p.1.1
          else (ι (p_of i)) ^ p.1.1 * (ι (q_of i)) ^ p.1.2 +
               (ι (p_of i)) ^ p.1.2 * (ι (q_of i)) ^ p.1.1
      map_add' := fun f g => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum] }
  have hφ_eval : ∀ i j : Fin m,
      φ i (v j) = (P j).eval (ι (p_of i)) * (P j).eval (ι (q_of i)) := by
    intro i j
    rw [hP_eval j (ι (p_of i)), hP_eval j (ι (q_of i)), Finset.sum_mul_sum]
    rw [← Finset.sum_product']
    let S := Finset.range (r + 1) ×ˢ Finset.range (r + 1)
    let S_eq := S.filter (fun p => p.1 = p.2)
    let S_lt := S.filter (fun p => p.1 < p.2)
    let S_gt := S.filter (fun p => p.2 < p.1)
    let term : ℕ × ℕ → ℚ := fun p =>
      (P j).coeff p.1 * (ι (p_of i)) ^ p.1 * ((P j).coeff p.2 * (ι (q_of i)) ^ p.2)
    have hS_part : ∑ p ∈ S, term p =
        ∑ p ∈ S_eq, term p + ∑ p ∈ S_lt, term p + ∑ p ∈ S_gt, term p := by
      have h1 : S = S_eq ∪ (S_lt ∪ S_gt) := by
        ext p; simp only [S_eq, S_lt, S_gt, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hp
          rcases lt_trichotomy p.1 p.2 with h | h | h
          · right; left; exact ⟨hp, h⟩
          · left; exact ⟨hp, h⟩
          · right; right; exact ⟨hp, h⟩
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
      have hd1 : Disjoint S_eq (S_lt ∪ S_gt) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [S_eq, S_lt, S_gt, Finset.mem_filter, Finset.mem_union] at hp1 hp2
        rcases hp2 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
      have hd2 : Disjoint S_lt S_gt := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [S_lt, S_gt, Finset.mem_filter] at hp1 hp2
        omega
      rw [h1, Finset.sum_union hd1, Finset.sum_union hd2, add_assoc]
    have hS_gt_eq : ∑ p ∈ S_gt, term p =
        ∑ p ∈ S_lt, (P j).coeff p.1 * (P j).coeff p.2 *
          ((ι (p_of i)) ^ p.2 * (ι (q_of i)) ^ p.1) := by
      refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [S_gt, S_lt, S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro a _ b _ hab
        exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
      · intro b hb
        refine ⟨(b.2, b.1), ?_, rfl⟩
        simp only [S_gt, S_lt, S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb ⊢
        exact ⟨⟨hb.1.2, hb.1.1⟩, hb.2⟩
      · intro p _
        dsimp only [term]
        ring
    have hT_part : ∑ p ∈ triSet r,
        (P j).coeff p.1 * (P j).coeff p.2 *
          (if p.1 = p.2 then (ι (p_of i)) ^ p.1 * (ι (q_of i)) ^ p.1
           else (ι (p_of i)) ^ p.1 * (ι (q_of i)) ^ p.2 +
                (ι (p_of i)) ^ p.2 * (ι (q_of i)) ^ p.1) =
        ∑ p ∈ S_eq, term p + ∑ p ∈ S_lt, term p + ∑ p ∈ S_gt, term p := by
      have hT_split : triSet r = S_eq ∪ S_lt := by
        ext p
        simp only [triSet, S_eq, S_lt, S, Finset.mem_union, Finset.mem_filter,
          Finset.mem_product, Finset.mem_range]
        omega
      have hT_disj : Disjoint S_eq S_lt := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [S_eq, S_lt, Finset.mem_filter] at hp1 hp2
        omega
      rw [hT_split, Finset.sum_union hT_disj, hS_gt_eq, add_assoc]
      congr 1
      · refine Finset.sum_congr rfl fun p hp => ?_
        simp only [S_eq, Finset.mem_filter] at hp
        simp only [hp.2, ↓reduceIte, term]
        ring
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p hp => ?_
        simp only [S_lt, Finset.mem_filter] at hp
        have hne : p.1 ≠ p.2 := by omega
        simp only [hne, ↓reduceIte, term]
        ring
    dsimp only [φ, v, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Finset.sum_coe_sort (triSet r)] at hT_part
    rw [hT_part, ← hS_part]
  have hφ_zero : ∀ i j : Fin m, φ i (v j) = 0 ↔ (A i ∩ B j).Nonempty := by
    intro i j
    rw [hφ_eval i j, mul_eq_zero, hP_zero_iff, hP_zero_iff, hpq_eq i]
    constructor
    · rintro (hp | hq)
      · exact ⟨p_of i, Finset.mem_inter.mpr ⟨by simp, hp⟩⟩
      · exact ⟨q_of i, Finset.mem_inter.mpr ⟨by simp, hq⟩⟩
    · rintro ⟨x, hx⟩
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx.1 with rfl | rfl
      · left; exact hx.2
      · right; exact hx.2
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    by_contra hci
    let S : Finset (Fin m) := Finset.univ.filter (fun j => c j ≠ 0)
    have hS_ne : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hci⟩⟩
    let k := S.max' hS_ne
    have hk_mem : k ∈ S := S.max'_mem hS_ne
    have hck : c k ≠ 0 := (Finset.mem_filter.mp hk_mem).2
    have hzero : φ k (∑ j : Fin m, c j • v j) = 0 := by rw [hc, map_zero]
    rw [map_sum] at hzero
    have hsum : ∑ j : Fin m, φ k (c j • v j) = c k * φ k (v k) := by
      rw [Finset.sum_eq_single k]
      · simp [smul_eq_mul]
      · intro j _ hjk
        rw [map_smul, smul_eq_mul]
        by_cases hj : c j = 0
        · simp [hj]
        · have hj_mem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
          have hj_le : j ≤ k := S.le_max' j hj_mem
          have hj_lt : j < k := lt_of_le_of_ne hj_le hjk
          have hφ0 : φ k (v j) = 0 := (hφ_zero k j).mpr (hskew k j hj_lt)
          simp [hφ0]
      · intro hk_abs
        exact absurd (Finset.mem_univ k) hk_abs
    rw [hsum, mul_eq_zero] at hzero
    rcases hzero with h0 | h0
    · exact hck h0
    · have hne : (A k ∩ B k).Nonempty := (hφ_zero k k).mp h0
      exact (Finset.not_disjoint_iff_nonempty_inter.mpr hne) (hdisj k)
  have hle_rank : m ≤ Module.finrank ℚ (↥(triSet r) → ℚ) := by
    calc m = Fintype.card (Fin m) := (Fintype.card_fin m).symm
      _ ≤ Module.finrank ℚ (↥(triSet r) → ℚ) := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, card_triSet] at hle_rank
  exact hle_rank

end SkewTwo

section PinFranklBound
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

/-- Single compression step: any subset `I` of size `≥ 2` can be strictly compressed
by a word of length at most `(r + 1) * (r + 2) / 2`, where `r = |Q| - |I|`. -/
theorem pin_frankl_step (hsync : A.IsSync) {I : Finset Q} (hI : 2 ≤ I.card) :
    let r := Fintype.card Q - I.card
    ∃ w : List α, (A.image I w).card < I.card ∧ w.length ≤ (r + 1) * (r + 2) / 2 := by
  classical
  intro r
  have hex : ∃ m : ℕ, ∃ w : List α, w.length = m ∧ (A.image I w).card < I.card := by
    obtain ⟨w₀, hw₀⟩ := hsync
    have hle : (A.image I w₀).card ≤ (A.image Finset.univ w₀).card :=
      Finset.card_le_card (A.image_mono (Finset.subset_univ I) w₀)
    have h1 : (A.image Finset.univ w₀).card = 1 := hw₀
    exact ⟨w₀.length, w₀, rfl, by omega⟩
  let m := Nat.find hex
  obtain ⟨w, hw_len, hw_card⟩ := Nat.find_spec hex
  change w.length = m at hw_len
  have hm_pos : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, List.length_eq_zero_iff] at hw_len
    subst hw_len
    simp at hw_card
  have hnotinj : ¬ Set.InjOn (fun q => A.eval q w) I := by
    intro hinj
    have := Finset.card_image_of_injOn hinj
    change (A.image I w).card = I.card at this
    omega
  simp only [Set.InjOn, Finset.mem_coe, not_forall] at hnotinj
  obtain ⟨p, hpI, q, hqI, heq_pq, hne_pq⟩ := hnotinj
  let P : Finset Q := {p, q}
  have hP_sub : P ⊆ I := by
    intro x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hP_card : P.card = 2 := Finset.card_pair hne_pq
  let Ai : Fin m → Finset Q := fun i => A.image P (w.take i.1)
  let Bi : Fin m → Finset Q := fun i => Finset.univ \ A.image I (w.take i.1)
  have himg_card : ∀ i : Fin m, (A.image I (w.take i.1)).card = I.card := by
    intro i
    have hlt : (w.take i.1).length < m := by
      rw [List.length_take, hw_len]
      omega
    have hnot : ¬ (A.image I (w.take i.1)).card < I.card := by
      intro hlt_card
      exact Nat.find_min hex hlt ⟨w.take i.1, rfl, hlt_card⟩
    have hle := A.card_image_le I (w.take i.1)
    omega
  have hinj_take : ∀ i : Fin m, Set.InjOn (fun x => A.eval x (w.take i.1)) I := by
    intro i
    apply Finset.injOn_of_card_image_eq
    change (A.image I (w.take i.1)).card = I.card
    exact himg_card i
  have hA_card : ∀ i : Fin m, (Ai i).card = 2 := by
    intro i
    dsimp only [Ai]
    rw [Aut.image, Finset.card_image_of_injOn ((hinj_take i).mono hP_sub)]
    exact hP_card
  have hB_card : ∀ i : Fin m, (Bi i).card ≤ r := by
    intro i
    dsimp only [Bi, r]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
      himg_card i]
  have hdisj : ∀ i : Fin m, Disjoint (Ai i) (Bi i) := by
    intro i
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Bi, Finset.mem_sdiff, Finset.mem_univ, true_and] at hxB
    exact hxB (A.image_mono hP_sub (w.take i.1) hxA)
  have hskew : ∀ i j : Fin m, j < i → (Ai i ∩ Bi j).Nonempty := by
    intro i j hij
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hemp
    have hsub : Ai i ⊆ A.image I (w.take j.1) := by
      intro x hx
      have hx_not_B : x ∉ Bi j := Finset.disjoint_left.mp hemp hx
      simp only [Bi, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hx_not_B
      exact hx_not_B
    have hp_mem : A.eval p (w.take i.1) ∈ A.image I (w.take j.1) :=
      hsub (Finset.mem_image_of_mem _ (by simp [P]))
    have hq_mem : A.eval q (w.take i.1) ∈ A.image I (w.take j.1) :=
      hsub (Finset.mem_image_of_mem _ (by simp [P]))
    rcases (Aut.mem_image A).mp hp_mem with ⟨p', hp'I, hp'_eq⟩
    rcases (Aut.mem_image A).mp hq_mem with ⟨q', hq'I, hq'_eq⟩
    have hpq'_ne : p' ≠ q' := by
      intro h_eq
      subst h_eq
      have heval_eq : A.eval p (w.take i.1) = A.eval q (w.take i.1) := by rw [← hp'_eq, hq'_eq]
      exact hne_pq (hinj_take i hpI hqI heval_eq)
    let w' := w.take j.1 ++ w.drop i.1
    have hw'_len : w'.length < m := by
      simp only [w', List.length_append, List.length_take, List.length_drop, hw_len]
      omega
    have hw'_merge : A.eval p' w' = A.eval q' w' := by
      simp only [w', Aut.eval_append, hp'_eq, hq'_eq]
      rw [← Aut.eval_append, ← Aut.eval_append, List.take_append_drop, heq_pq]
    have hw'_card : (A.image I w').card < I.card := by
      have himg_eq : A.image (I.erase q') w' = A.image I w' := by
        ext x
        simp only [Aut.mem_image]
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z, Finset.erase_subset _ _ hz, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          by_cases hzq : z = q'
          · subst hzq
            exact ⟨p', Finset.mem_erase.mpr ⟨hpq'_ne, hp'I⟩, hw'_merge⟩
          · exact ⟨z, Finset.mem_erase.mpr ⟨hzq, hz⟩, rfl⟩
      rw [← himg_eq]
      calc (A.image (I.erase q') w').card
          ≤ (I.erase q').card := A.card_image_le _ _
        _ = I.card - 1 := Finset.card_erase_of_mem hq'I
        _ < I.card := by omega
    exact Nat.find_min hex hw'_len ⟨w', rfl, hw'_card⟩
  refine ⟨w, hw_card, ?_⟩
  rw [hw_len]
  exact frankl_skew_two Ai Bi hA_card hB_card hdisj hskew

private lemma sum_tri_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Finset.range (n - 1), (t + 1) * (t + 2) / 2 = (n ^ 3 - n) / 6 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      have ih' := ih (by omega)
      have hsub : (m + 1 + 1) - 1 = (m + 1) := by omega
      have hsub2 : (m + 1) - 1 = m := by omega
      rw [hsub, Finset.sum_range_succ]
      rw [hsub2] at ih'
      rw [ih']
      have hdiv1 : 2 ∣ (m + 1) * (m + 2) := by
        rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp [Nat.dvd_iff_mod_eq_zero] <;> ring_nf <;> omega
      have hdiv2 : 6 ∣ (m + 1) ^ 3 - (m + 1) := by
        have hpow1 : (m + 1) ^ 3 = m * (m + 1) * (m + 2) + (m + 1) := by ring
        have hfac : (m + 1) ^ 3 - (m + 1) = m * (m + 1) * (m + 2) := by omega
        rw [hfac]
        have h2 : 2 ∣ m * (m + 1) := by
          rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · exact ⟨k * (2 * k + 1), by ring⟩
          · exact ⟨(2 * k + 1) * (k + 1), by ring⟩
        have h3 : 3 ∣ m * (m + 1) * (m + 2) := by
          rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h) _) _
          · have h2' : 3 ∣ m + 2 := Nat.dvd_of_mod_eq_zero (by omega)
            exact dvd_mul_of_dvd_right h2' _
          · have h1' : 3 ∣ m + 1 := Nat.dvd_of_mod_eq_zero (by omega)
            exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1' _) _
        have h6 : 6 = Nat.lcm 2 3 := by decide
        rw [h6]
        exact Nat.lcm_dvd (dvd_mul_of_dvd_left h2 _) h3
      have hdiv3 : 6 ∣ (m + 2) ^ 3 - (m + 2) := by
        have hpow2 : (m + 2) ^ 3 = (m + 1) * (m + 2) * (m + 3) + (m + 2) := by ring
        have hfac : (m + 2) ^ 3 - (m + 2) = (m + 1) * (m + 2) * (m + 3) := by omega
        rw [hfac]
        have h2 : 2 ∣ (m + 1) * (m + 2) := hdiv1
        have h3 : 3 ∣ (m + 1) * (m + 2) * (m + 3) := by
          rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
          · have : 3 ∣ m + 3 := Nat.dvd_of_mod_eq_zero (by omega)
            exact dvd_mul_of_dvd_right this _
          · have : 3 ∣ m + 2 := Nat.dvd_of_mod_eq_zero (by omega)
            exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _
          · have : 3 ∣ m + 1 := Nat.dvd_of_mod_eq_zero (by omega)
            exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left this _) _
        have h6 : 6 = Nat.lcm 2 3 := by decide
        rw [h6]
        exact Nat.lcm_dvd (dvd_mul_of_dvd_left h2 _) h3
      have h1 : (m + 1) * (m + 2) / 2 * 2 = (m + 1) * (m + 2) := Nat.div_mul_cancel hdiv1
      have h2 : ((m + 1) ^ 3 - (m + 1)) / 6 * 6 = (m + 1) ^ 3 - (m + 1) := Nat.div_mul_cancel hdiv2
      have h3 : ((m + 2) ^ 3 - (m + 2)) / 6 * 6 = (m + 2) ^ 3 - (m + 2) := Nat.div_mul_cancel hdiv3
      have hpow1 : (m + 1) ^ 3 = m * (m + 1) * (m + 2) + (m + 1) := by ring
      have hpow2 : (m + 2) ^ 3 = (m + 1) * (m + 2) * (m + 3) + (m + 2) := by ring
      have hdiff : m * (m + 1) * (m + 2) + 3 * ((m + 1) * (m + 2)) = (m + 1) * (m + 2) * (m + 3) := by ring
      have hmul_eq : ((m + 1) ^ 3 - (m + 1)) + 3 * ((m + 1) * (m + 2)) = (m + 2) ^ 3 - (m + 2) := by omega
      have hgoal_eq : (m + 1 + 1) ^ 3 - (m + 1 + 1) = (m + 2) ^ 3 - (m + 2) := rfl
      rw [hgoal_eq]
      omega

/-- Pin–Frankl cubic upper bound: every synchronizing automaton on `n ≥ 1` states
has a synchronizing word of length at most `(n^3 - n) / 6`. -/
theorem pin_frankl_bound [Nonempty Q] (hsync : A.IsSync) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q ^ 3 - Fintype.card Q) / 6 := by
  let n := Fintype.card Q
  have hn_pos : 1 ≤ n := Fintype.card_pos
  have hmain : ∀ s : ℕ, ∀ I : Finset Q, I.card = s → 1 ≤ s → s ≤ n →
      ∃ w : List α, (A.image I w).card = 1 ∧
        w.length ≤ ∑ t ∈ Finset.Ico (n - s) (n - 1), (t + 1) * (t + 2) / 2 := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro I hIs hs1 hsn
      by_cases hs_eq : s = 1
      · subst hs_eq
        exact ⟨[], by simpa [Aut.image_nil] using hIs, by simp⟩
      · have hs2 : 2 ≤ I.card := by omega
        obtain ⟨u, hu_card, hu_len⟩ := pin_frankl_step A hsync hs2
        have hI'_pos : 1 ≤ (A.image I u).card := by
          have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
          exact (A.image_nonempty hIne u).card_pos
        have hI'_lt : (A.image I u).card < s := by omega
        have hI'_le : (A.image I u).card ≤ n :=
          (Finset.card_le_univ _).trans_eq rfl
        obtain ⟨v, hv_card, hv_len⟩ := ih (A.image I u).card hI'_lt (A.image I u) rfl hI'_pos hI'_le
        refine ⟨u ++ v, by rw [Aut.image_append]; exact hv_card, ?_⟩
        have hle_sum : ∑ t ∈ Finset.Ico (n - (A.image I u).card) (n - 1), (t + 1) * (t + 2) / 2 ≤
            ∑ t ∈ Finset.Ico (n - s + 1) (n - 1), (t + 1) * (t + 2) / 2 := by
          apply Finset.sum_le_sum_of_subset
          exact Finset.Ico_subset_Ico_left (by omega)
        have hsplit : ∑ t ∈ Finset.Ico (n - s) (n - 1), (t + 1) * (t + 2) / 2 =
            ((n - s) + 1) * ((n - s) + 2) / 2 +
            ∑ t ∈ Finset.Ico (n - s + 1) (n - 1), (t + 1) * (t + 2) / 2 := by
          rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : n - s < n - 1)]
        rw [List.length_append, hsplit]
        have hu_len' : u.length ≤ (n - s + 1) * (n - s + 2) / 2 := by
          simpa [hIs, n] using hu_len
        omega
  obtain ⟨w, hw_card, hw_len⟩ := hmain n Finset.univ (Finset.card_univ) hn_pos le_rfl
  refine ⟨w, hw_card, ?_⟩
  rw [Nat.sub_self] at hw_len
  change w.length ≤ ∑ t ∈ Finset.Ico 0 (n - 1), (t + 1) * (t + 2) / 2 at hw_len
  rw [Nat.Ico_zero_eq_range, sum_tri_eq n hn_pos] at hw_len
  exact hw_len

end PinFranklBound

end PinFrankl
