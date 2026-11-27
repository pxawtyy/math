import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Cerny.Defs
import Cerny.BalancedPermutations
import Cerny.OneClusterAnnular

namespace Cerny.AmortizedBalanced

section ThreePairLemma

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Indicator vector of a `Finset Q` in `Q → ℚ`. -/
def indQ (S : Finset Q) : Q → ℚ := fun q => if q ∈ S then 1 else 0

lemma indQ_compl (S : Finset Q) :
    indQ (Finset.univ \ S) = (fun _ => (1 : ℚ)) - indQ S := by
  ext q
  by_cases h : q ∈ S <;> simp [indQ, h]

private lemma compl_compl (S : Finset Q) : Finset.univ \ (Finset.univ \ S) = S := by
  ext q; simp

private lemma compl_nonempty_of_ne_univ {S : Finset Q} (h : S ≠ Finset.univ) :
    (Finset.univ \ S).Nonempty := by
  by_contra hemp
  apply h
  ext q
  simp only [Finset.mem_univ, iff_true]
  by_contra hq
  exact hemp ⟨q, Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hq⟩⟩


private lemma lin_dep_two_01 {S₁ S₂ : Finset Q}
    (hneq : S₁ ≠ S₂) (hncomp : S₁ ≠ Finset.univ \ S₂)
    {c₀ c₁ c₂ : ℚ} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hrel : ∀ q : Q, c₀ + c₁ * indQ S₁ q + c₂ * indQ S₂ q = 0) : False := by
  have hex_diff : ∃ q : Q, (q ∈ S₁ ∧ q ∉ S₂) ∨ (q ∉ S₁ ∧ q ∈ S₂) := by
    by_contra hall
    push_neg at hall
    apply hneq
    ext q
    exact ⟨fun h1 => (hall q).1 h1, fun h2 => by by_contra h1; exact (hall q).2 h1 h2⟩
  have hex_same : ∃ q : Q, (q ∈ S₁ ∧ q ∈ S₂) ∨ (q ∉ S₁ ∧ q ∉ S₂) := by
    by_contra hall
    push_neg at hall
    apply hncomp
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨fun h1 => (hall q).1 h1, fun h2 => by by_contra h1; exact h2 ((hall q).2 h1)⟩
  rcases hex_diff with ⟨q₁, ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩⟩ <;>
    rcases hex_same with ⟨q₂, ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩⟩
  · have e1 := hrel q₁; have e2 := hrel q₂
    simp only [indQ, h1a, h1b, h2a, h2b, ↓reduceIte, mul_one, mul_zero] at e1 e2
    exact hc₂ (by linarith)
  · have e1 := hrel q₁; have e2 := hrel q₂
    simp only [indQ, h1a, h1b, h2a, h2b, ↓reduceIte, mul_one, mul_zero] at e1 e2
    exact hc₁ (by linarith)
  · have e1 := hrel q₁; have e2 := hrel q₂
    simp only [indQ, h1a, h1b, h2a, h2b, ↓reduceIte, mul_one, mul_zero] at e1 e2
    exact hc₁ (by linarith)
  · have e1 := hrel q₁; have e2 := hrel q₂
    simp only [indQ, h1a, h1b, h2a, h2b, ↓reduceIte, mul_one, mul_zero] at e1 e2
    exact hc₂ (by linarith)

private lemma no_mix_aux {T₁ T₂ T₃ : Finset Q} {a₁ a₂ a₃ K : ℚ}
    (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (hT₂₃ : T₂ ≠ T₃)
    (hrel : ∀ x : Q, a₁ * indQ T₁ x + a₂ * indQ T₂ x + a₃ * indQ T₃ x = K)
    (hq : K = a₁)
    {p : Q} (hp_wt2 : (p ∈ T₁ ∧ p ∈ T₂ ∧ p ∉ T₃) ∨ (p ∈ T₁ ∧ p ∉ T₂ ∧ p ∈ T₃) ∨
      (p ∉ T₁ ∧ p ∈ T₂ ∧ p ∈ T₃)) : False := by
  have hp := hrel p
  rcases hp_wt2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · simp only [indQ, h1, h2, h3, ↓reduceIte, mul_one, mul_zero, add_zero] at hp; linarith
  · simp only [indQ, h1, h2, h3, ↓reduceIte, mul_one, mul_zero, add_zero] at hp; linarith
  · simp only [indQ, h1, h2, h3, ↓reduceIte, mul_one, mul_zero, zero_add] at hp
    apply hT₂₃
    ext x
    have hx := hrel x
    by_cases x1 : x ∈ T₁ <;> by_cases x2 : x ∈ T₂ <;> by_cases x3 : x ∈ T₃ <;>
      simp only [indQ, x1, x2, x3, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add] at hx
    · exact ⟨fun _ => x3, fun _ => x2⟩
    · exfalso; linarith
    · exfalso; linarith
    · exact ⟨fun h => absurd h x2, fun h => absurd h x3⟩
    · exact ⟨fun _ => x3, fun _ => x2⟩
    · exfalso; linarith
    · exfalso; linarith
    · exact ⟨fun h => absurd h x2, fun h => absurd h x3⟩

/-- **3-Pair Subspace Lemma:**
A subspace `W ≤ (Q → ℚ)` with `finrank ℚ W ≤ 3` containing the all-ones vector `1`
contains at most `3` proper nonempty subsets from distinct complementary pairs. -/
theorem card_noncomp_01_le_three
    (W : Submodule ℚ (Q → ℚ)) (hdim : Module.finrank ℚ W ≤ 3)
    (h1 : (fun _ : Q => (1 : ℚ)) ∈ W)
    (F : Finset (Finset Q))
    (hproper : ∀ S ∈ F, 1 ≤ S.card ∧ S.card < Fintype.card Q)
    (hmem : ∀ S ∈ F, indQ S ∈ W)
    (hncomp : ∀ S ∈ F, Finset.univ \ S ∉ F) :
    F.card ≤ 3 := by
  classical
  by_contra hgt
  -- Extract 4 pairwise distinct elements `S0, S1, S2, S3 ∈ F`
  obtain ⟨S0, hS0⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
  have hc1 : 3 ≤ (F.erase S0).card := by rw [Finset.card_erase_of_mem hS0]; omega
  obtain ⟨S1, hS1e⟩ := Finset.card_pos.mp (by omega : 0 < (F.erase S0).card)
  obtain ⟨h10, hS1⟩ := Finset.mem_erase.mp hS1e
  have hc2 : 2 ≤ ((F.erase S0).erase S1).card := by rw [Finset.card_erase_of_mem hS1e]; omega
  obtain ⟨S2, hS2e⟩ := Finset.card_pos.mp (by omega : 0 < ((F.erase S0).erase S1).card)
  obtain ⟨h21, hS2e'⟩ := Finset.mem_erase.mp hS2e
  obtain ⟨h20, hS2⟩ := Finset.mem_erase.mp hS2e'
  have hc3 : 1 ≤ (((F.erase S0).erase S1).erase S2).card := by
    rw [Finset.card_erase_of_mem hS2e]; omega
  obtain ⟨S3, hS3e⟩ := Finset.card_pos.mp (by omega : 0 < (((F.erase S0).erase S1).erase S2).card)
  obtain ⟨h32, hS3e1⟩ := Finset.mem_erase.mp hS3e
  obtain ⟨h31, hS3e2⟩ := Finset.mem_erase.mp hS3e1
  obtain ⟨h30, hS3⟩ := Finset.mem_erase.mp hS3e2
  have hne_univ : ∀ S ∈ F, S ≠ Finset.univ := fun S hS hEq => by
    have := (hproper S hS).2; rw [hEq, Finset.card_univ] at this; omega
  have hnonempty : ∀ S ∈ F, S.Nonempty := fun S hS => Finset.card_pos.mp (hproper S hS).1
  have hnc : ∀ X ∈ F, ∀ Y ∈ F, X ≠ Finset.univ \ Y := fun X hX Y hY h => hncomp Y hY (h ▸ hX)
  -- Linear dependence among `1, indQ S0, indQ S1, indQ S2` in `W`
  let v : Fin 4 → (Q → ℚ) := fun i =>
    if i.1 = 0 then (fun _ => 1)
    else if i.1 = 1 then indQ S0
    else if i.1 = 2 then indQ S1
    else indQ S2
  have hv_mem : ∀ i : Fin 4, v i ∈ W := by
    intro i
    rcases (by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 ∨ i.1 = 3) with h | h | h | h
    · simp only [v, h, ↓reduceIte]; exact h1
    · simp only [v, h, ↓reduceIte]; exact hmem S0 hS0
    · simp only [v, h, ↓reduceIte]; exact hmem S1 hS1
    · simp only [v, h, ↓reduceIte]; exact hmem S2 hS2
  have hnotli : ¬ LinearIndependent ℚ v := by
    intro hli
    have hsub : Submodule.span ℚ (Set.range v) ≤ W := by
      rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hv_mem i
    have hle := Submodule.finrank_mono hsub
    rw [finrank_span_eq_card hli, Fintype.card_fin] at hle
    omega
  rw [Fintype.linearIndependent_iff] at hnotli
  push_neg at hnotli
  obtain ⟨c, hc_sum, i₀, hi₀⟩ := hnotli
  have hrel_pt : ∀ q : Q,
      c 0 + c 1 * indQ S0 q + c 2 * indQ S1 q + c 3 * indQ S2 q = 0 := by
    intro q
    have h0 := congrFun hc_sum q
    rw [Finset.sum_apply, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_two] at h0
    change c 0 * 1 + c 1 * indQ S0 q + c 2 * indQ S1 q + c 3 * indQ S2 q = 0 at h0
    linarith
  have hno_single : ∀ {S : Finset Q} {c₀ r : ℚ}, S ∈ F → r ≠ 0 →
      (∀ q, c₀ + r * indQ S q = 0) → False := by
    intro S c₀ r hS hr hrel
    obtain ⟨q₁, hq₁⟩ := hnonempty S hS
    obtain ⟨q₂, hq₂⟩ := compl_nonempty_of_ne_univ (hne_univ S hS)
    have hq₂' : q₂ ∉ S := (Finset.mem_sdiff.mp hq₂).2
    have e1 := hrel q₁; have e2 := hrel q₂
    simp only [indQ, hq₁, hq₂', ↓reduceIte, mul_one, mul_zero] at e1 e2
    exact hr (by linarith)
  have hc1_ne : c 1 ≠ 0 := by
    intro h0
    by_cases h2 : c 2 = 0
    · by_cases h3 : c 3 = 0
      · have hc0 : c 0 = 0 := by
          obtain ⟨q, _⟩ := hnonempty S0 hS0
          have := hrel_pt q
          simp only [h0, h2, h3, zero_mul, add_zero] at this
          exact this
        rcases (by omega : i₀.1 = 0 ∨ i₀.1 = 1 ∨ i₀.1 = 2 ∨ i₀.1 = 3) with h | h | h | h
        · exact hi₀ (by rw [show i₀ = 0 from Fin.ext h]; exact hc0)
        · exact hi₀ (by rw [show i₀ = 1 from Fin.ext h]; exact h0)
        · exact hi₀ (by rw [show i₀ = 2 from Fin.ext h]; exact h2)
        · exact hi₀ (by rw [show i₀ = 3 from Fin.ext h]; exact h3)
      · exact hno_single hS2 h3 (fun q => by
          have := hrel_pt q; simp only [h0, h2, zero_mul, add_zero] at this; exact this)
    · by_cases h3 : c 3 = 0
      · exact hno_single hS1 h2 (fun q => by
          have := hrel_pt q; simp only [h0, h3, zero_mul, add_zero] at this; exact this)
      · exact lin_dep_two_01 h21.symm (hnc S1 hS1 S2 hS2) h2 h3 (fun q => by
          have := hrel_pt q; simp only [h0, zero_mul, add_zero] at this; exact this)
  have hc2_ne : c 2 ≠ 0 := by
    intro h0
    by_cases h3 : c 3 = 0
    · exact hno_single hS0 hc1_ne (fun q => by
        have := hrel_pt q; simp only [h0, h3, zero_mul, add_zero] at this; exact this)
    · exact lin_dep_two_01 h20.symm (hnc S0 hS0 S2 hS2) hc1_ne h3 (fun q => by
        have := hrel_pt q; simp only [h0, zero_mul, add_zero] at this; exact this)
  have hc3_ne : c 3 ≠ 0 := by
    intro h0
    exact lin_dep_two_01 h10.symm (hnc S0 hS0 S1 hS1) hc1_ne hc2_ne (fun q => by
      have := hrel_pt q; simp only [h0, zero_mul, add_zero] at this; exact this)
  -- Flip signs to get `a₁ * indQ T₁ + a₂ * indQ T₂ + a₃ * indQ T₃ = K` with `a₁, a₂, a₃ > 0`
  let absQ : ℚ → ℚ := fun r => if 0 < r then r else -r
  let flip : ℚ → Finset Q → Finset Q := fun r X => if 0 < r then X else Finset.univ \ X
  have habs_pos : ∀ {r : ℚ}, r ≠ 0 → 0 < absQ r := fun {r} hr => by
    dsimp only [absQ]
    by_cases h : 0 < r
    · rw [if_pos h]; exact h
    · rw [if_neg h]
      rcases lt_or_gt_of_ne hr with hlt | hgt
      · linarith
      · exact absurd hgt h
  have hflip_eq : ∀ (r : ℚ) (X : Finset Q) (q : Q),
      r * indQ X q = absQ r * indQ (flip r X) q - (if 0 < r then 0 else absQ r) := by
    intro r X q
    by_cases hr : 0 < r
    · simp only [absQ, flip, hr, ↓reduceIte, sub_zero]
    · simp only [absQ, flip, hr, ↓reduceIte, indQ_compl, Pi.sub_apply]; ring
  let T₁ := flip (c 1) S0
  let T₂ := flip (c 2) S1
  let T₃ := flip (c 3) S2
  let a₁ := absQ (c 1)
  let a₂ := absQ (c 2)
  let a₃ := absQ (c 3)
  have ha₁ : 0 < a₁ := habs_pos hc1_ne
  have ha₂ : 0 < a₂ := habs_pos hc2_ne
  have ha₃ : 0 < a₃ := habs_pos hc3_ne
  let K : ℚ := -c 0 + (if 0 < c 1 then 0 else a₁) + (if 0 < c 2 then 0 else a₂) +
    (if 0 < c 3 then 0 else a₃)
  have hpos_rel : ∀ q : Q, a₁ * indQ T₁ q + a₂ * indQ T₂ q + a₃ * indQ T₃ q = K := by
    intro q
    have h0 := hrel_pt q
    rw [hflip_eq (c 1) S0 q, hflip_eq (c 2) S1 q, hflip_eq (c 3) S2 q] at h0
    dsimp only [K, a₁, a₂, a₃, T₁, T₂, T₃] at h0 ⊢
    linarith
  have hT_props : ∀ (r : ℚ) {X : Finset Q}, X ∈ F →
      (flip r X).Nonempty ∧ flip r X ≠ Finset.univ ∧ indQ (flip r X) ∈ W := by
    intro r X hX
    by_cases hr : 0 < r
    · simp only [flip, hr, ↓reduceIte]; exact ⟨hnonempty X hX, hne_univ X hX, hmem X hX⟩
    · simp only [flip, hr, ↓reduceIte]
      refine ⟨compl_nonempty_of_ne_univ (hne_univ X hX), fun hEq => ?_, ?_⟩
      · obtain ⟨q, hq⟩ := hnonempty X hX
        have : q ∈ Finset.univ \ X := by rw [hEq]; exact Finset.mem_univ q
        exact (Finset.mem_sdiff.mp this).2 hq
      · rw [indQ_compl]; exact W.sub_mem h1 (hmem X hX)
  have hT_ne : ∀ (r₁ r₂ : ℚ) {X Y : Finset Q}, X ∈ F → Y ∈ F → X ≠ Y →
      flip r₁ X ≠ flip r₂ Y := by
    intro r₁ r₂ X Y hX hY hXY
    by_cases h1r : 0 < r₁ <;> by_cases h2r : 0 < r₂ <;> simp only [flip, h1r, h2r, ↓reduceIte]
    · exact hXY
    · exact hnc X hX Y hY
    · exact fun h => hnc Y hY X hX h.symm
    · intro h; apply hXY
      have := congrArg (fun Z => Finset.univ \ Z) h
      simpa only [compl_compl] using this
  have hT12 : T₁ ≠ T₂ := hT_ne (c 1) (c 2) hS0 hS1 h10.symm
  have hT13 : T₁ ≠ T₃ := hT_ne (c 1) (c 3) hS0 hS2 h20.symm
  have hT23 : T₂ ≠ T₃ := hT_ne (c 2) (c 3) hS1 hS2 h21.symm
  -- No state has `(0, 0, 0)` or `(1, 1, 1)` in `(T₁, T₂, T₃)`
  have hno000 : ∀ q : Q, q ∈ T₁ ∨ q ∈ T₂ ∨ q ∈ T₃ := by
    intro q; by_contra hnone; push_neg at hnone
    have hK0 : K = 0 := by
      have := hpos_rel q
      simp only [indQ, hnone.1, hnone.2.1, hnone.2.2, ↓reduceIte, mul_zero, add_zero] at this
      exact this.symm
    obtain ⟨p, hp⟩ := (hT_props (c 1) hS0).1
    have hp_rel := hpos_rel p
    have hp1_val : indQ T₁ p = 1 := if_pos hp
    have hge2 : 0 ≤ a₂ * indQ T₂ p := by by_cases h : p ∈ T₂ <;> simp [indQ, h, le_of_lt ha₂]
    have hge3 : 0 ≤ a₃ * indQ T₃ p := by by_cases h : p ∈ T₃ <;> simp [indQ, h, le_of_lt ha₃]
    rw [hp1_val, mul_one] at hp_rel
    linarith
  have hno111 : ∀ q : Q, ¬ (q ∈ T₁ ∧ q ∈ T₂ ∧ q ∈ T₃) := by
    intro q h111
    have hKsum : K = a₁ + a₂ + a₃ := by
      have := hpos_rel q
      simp only [indQ, h111.1, h111.2.1, h111.2.2, ↓reduceIte, mul_one] at this
      exact this.symm
    obtain ⟨p, hp⟩ := compl_nonempty_of_ne_univ (hT_props (c 1) hS0).2.1
    have hp1 : p ∉ T₁ := (Finset.mem_sdiff.mp hp).2
    have hp_rel := hpos_rel p
    have hp1_val : indQ T₁ p = 0 := if_neg hp1
    have hle2 : a₂ * indQ T₂ p ≤ a₂ := by by_cases h : p ∈ T₂ <;> simp [indQ, h, le_of_lt ha₂]
    have hle3 : a₃ * indQ T₃ p ≤ a₃ := by by_cases h : p ∈ T₃ <;> simp [indQ, h, le_of_lt ha₃]
    rw [hp1_val, mul_zero, zero_add] at hp_rel
    linarith
  let wt : Q → ℕ := fun q =>
    (if q ∈ T₁ then 1 else 0) + (if q ∈ T₂ then 1 else 0) + (if q ∈ T₃ then 1 else 0)
  have hwt_12 : ∀ q : Q, wt q = 1 ∨ wt q = 2 := by
    intro q
    have h0 := hno000 q; have h1' := hno111 q
    dsimp only [wt]
    by_cases b1 : q ∈ T₁ <;> by_cases b2 : q ∈ T₂ <;> by_cases b3 : q ∈ T₃
    · exact absurd ⟨b1, b2, b3⟩ h1'
    · right; simp [b1, b2, b3]
    · right; simp [b1, b2, b3]
    · left; simp [b1, b2, b3]
    · right; simp [b1, b2, b3]
    · left; simp [b1, b2, b3]
    · left; simp [b1, b2, b3]
    · rcases h0 with h | h | h
      · exact absurd h b1
      · exact absurd h b2
      · exact absurd h b3
  have hwt1_cases : ∀ q : Q, wt q = 1 →
      (q ∈ T₁ ∧ q ∉ T₂ ∧ q ∉ T₃) ∨ (q ∉ T₁ ∧ q ∈ T₂ ∧ q ∉ T₃) ∨ (q ∉ T₁ ∧ q ∉ T₂ ∧ q ∈ T₃) := by
    intro q hq; dsimp only [wt] at hq
    by_cases b1 : q ∈ T₁ <;> by_cases b2 : q ∈ T₂ <;> by_cases b3 : q ∈ T₃ <;>
      simp only [b1, b2, b3, ↓reduceIte] at hq
    · omega
    · omega
    · omega
    · exact Or.inl ⟨b1, b2, b3⟩
    · omega
    · exact Or.inr (Or.inl ⟨b1, b2, b3⟩)
    · exact Or.inr (Or.inr ⟨b1, b2, b3⟩)
    · omega
  have hwt2_cases : ∀ p : Q, wt p = 2 →
      (p ∈ T₁ ∧ p ∈ T₂ ∧ p ∉ T₃) ∨ (p ∈ T₁ ∧ p ∉ T₂ ∧ p ∈ T₃) ∨ (p ∉ T₁ ∧ p ∈ T₂ ∧ p ∈ T₃) := by
    intro p hp; dsimp only [wt] at hp
    by_cases b1 : p ∈ T₁ <;> by_cases b2 : p ∈ T₂ <;> by_cases b3 : p ∈ T₃ <;>
      simp only [b1, b2, b3, ↓reduceIte] at hp
    · omega
    · exact Or.inl ⟨b1, b2, b3⟩
    · exact Or.inr (Or.inl ⟨b1, b2, b3⟩)
    · omega
    · exact Or.inr (Or.inr ⟨b1, b2, b3⟩)
    · omega
    · omega
    · omega
  have hno_mix : ¬ ((∃ q, wt q = 1) ∧ (∃ p, wt p = 2)) := by
    rintro ⟨⟨q, hq⟩, ⟨p, hp⟩⟩
    have hp2 := hwt2_cases p hp
    rcases hwt1_cases q hq with ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩
    · have hK : K = a₁ := by
        have := hpos_rel q
        simp only [indQ, q1, q2, q3, ↓reduceIte, mul_one, mul_zero, add_zero] at this
        exact this.symm
      exact no_mix_aux ha₂ ha₃ hT23 hpos_rel hK hp2
    · have hK : K = a₂ := by
        have := hpos_rel q
        simp only [indQ, q1, q2, q3, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add] at this
        exact this.symm
      have hp2' : (p ∈ T₂ ∧ p ∈ T₁ ∧ p ∉ T₃) ∨ (p ∈ T₂ ∧ p ∉ T₁ ∧ p ∈ T₃) ∨
          (p ∉ T₂ ∧ p ∈ T₁ ∧ p ∈ T₃) := by
        rcases hp2 with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
        · exact Or.inl ⟨h2', h1', h3'⟩
        · exact Or.inr (Or.inr ⟨h2', h1', h3'⟩)
        · exact Or.inr (Or.inl ⟨h2', h1', h3'⟩)
      exact no_mix_aux ha₁ ha₃ hT13 (fun x => by have := hpos_rel x; linarith) hK hp2'
    · have hK : K = a₃ := by
        have := hpos_rel q
        simp only [indQ, q1, q2, q3, ↓reduceIte, mul_one, mul_zero, zero_add] at this
        exact this.symm
      have hp2' : (p ∈ T₃ ∧ p ∈ T₁ ∧ p ∉ T₂) ∨ (p ∈ T₃ ∧ p ∉ T₁ ∧ p ∈ T₂) ∨
          (p ∉ T₃ ∧ p ∈ T₁ ∧ p ∈ T₂) := by
        rcases hp2 with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
        · exact Or.inr (Or.inr ⟨h3', h1', h2'⟩)
        · exact Or.inl ⟨h3', h1', h2'⟩
        · exact Or.inr (Or.inl ⟨h3', h1', h2'⟩)
      exact no_mix_aux ha₁ ha₂ hT12 (fun x => by have := hpos_rel x; linarith) hK hp2'
  -- Obtain the 3 nonempty pairwise disjoint atoms `A, B, C` partitioning `Q`
  have hatoms : ∃ A B C : Finset Q,
      A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      (∀ q : Q, q ∈ A ∨ q ∈ B ∨ q ∈ C) ∧
      indQ A ∈ W ∧ indQ B ∈ W ∧ indQ C ∈ W ∧
      (A = S0 ∨ A = Finset.univ \ S0) ∧
      (B = S1 ∨ B = Finset.univ \ S1) ∧
      (C = S2 ∨ C = Finset.univ \ S2) := by
    have hflip_or : ∀ (r : ℚ) (X : Finset Q), flip r X = X ∨ flip r X = Finset.univ \ X := by
      intro r X; by_cases hr : 0 < r <;> simp [flip, hr]
    have hcompl_or : ∀ (r : ℚ) (X : Finset Q),
        Finset.univ \ flip r X = X ∨ Finset.univ \ flip r X = Finset.univ \ X := by
      intro r X; by_cases hr : 0 < r
      · right; simp [flip, hr]
      · left; simp [flip, hr, compl_compl]
    by_cases h1_ex : ∃ q, wt q = 1
    · have hall1 : ∀ q, wt q = 1 := fun q =>
        (hwt_12 q).resolve_right (fun h2 => hno_mix ⟨h1_ex, ⟨q, h2⟩⟩)
      refine ⟨T₁, T₂, T₃, (hT_props (c 1) hS0).1, (hT_props (c 2) hS1).1, (hT_props (c 3) hS2).1,
        ?_, ?_, ?_, hno000, (hT_props (c 1) hS0).2.2, (hT_props (c 2) hS1).2.2,
        (hT_props (c 3) hS2).2.2, hflip_or (c 1) S0, hflip_or (c 2) S1, hflip_or (c 3) S2⟩
      · rw [Finset.disjoint_left]; intro q h1q h2q
        have := hall1 q; dsimp only [wt] at this
        by_cases h3q : q ∈ T₃ <;> simp only [h1q, h2q, h3q, ↓reduceIte] at this <;> omega
      · rw [Finset.disjoint_left]; intro q h1q h3q
        have := hall1 q; dsimp only [wt] at this
        by_cases h2q : q ∈ T₂ <;> simp only [h1q, h2q, h3q, ↓reduceIte] at this <;> omega
      · rw [Finset.disjoint_left]; intro q h2q h3q
        have := hall1 q; dsimp only [wt] at this
        by_cases h1q : q ∈ T₁ <;> simp only [h1q, h2q, h3q, ↓reduceIte] at this <;> omega
    · push_neg at h1_ex
      have hall2 : ∀ q, wt q = 2 := fun q => (hwt_12 q).resolve_left (h1_ex q)
      refine ⟨Finset.univ \ T₁, Finset.univ \ T₂, Finset.univ \ T₃,
        compl_nonempty_of_ne_univ (hT_props (c 1) hS0).2.1,
        compl_nonempty_of_ne_univ (hT_props (c 2) hS1).2.1,
        compl_nonempty_of_ne_univ (hT_props (c 3) hS2).2.1,
        ?_, ?_, ?_, ?_,
        by rw [indQ_compl]; exact W.sub_mem h1 (hT_props (c 1) hS0).2.2,
        by rw [indQ_compl]; exact W.sub_mem h1 (hT_props (c 2) hS1).2.2,
        by rw [indQ_compl]; exact W.sub_mem h1 (hT_props (c 3) hS2).2.2,
        hcompl_or (c 1) S0, hcompl_or (c 2) S1, hcompl_or (c 3) S2⟩
      · rw [Finset.disjoint_left]; intro q h1q h2q
        have h1' := (Finset.mem_sdiff.mp h1q).2; have h2' := (Finset.mem_sdiff.mp h2q).2
        have := hall2 q; dsimp only [wt] at this
        by_cases h3q : q ∈ T₃ <;> simp only [h1', h2', h3q, ↓reduceIte] at this <;> omega
      · rw [Finset.disjoint_left]; intro q h1q h3q
        have h1' := (Finset.mem_sdiff.mp h1q).2; have h3' := (Finset.mem_sdiff.mp h3q).2
        have := hall2 q; dsimp only [wt] at this
        by_cases h2q : q ∈ T₂ <;> simp only [h1', h2q, h3', ↓reduceIte] at this <;> omega
      · rw [Finset.disjoint_left]; intro q h2q h3q
        have h2' := (Finset.mem_sdiff.mp h2q).2; have h3' := (Finset.mem_sdiff.mp h3q).2
        have := hall2 q; dsimp only [wt] at this
        by_cases h1q : q ∈ T₁ <;> simp only [h1q, h2', h3', ↓reduceIte] at this <;> omega
      · intro q; by_cases b1 : q ∈ T₁
        · by_cases b2 : q ∈ T₂
          · right; right; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, fun b3 => hno111 q ⟨b1, b2, b3⟩⟩
          · right; left; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, b2⟩
        · left; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, b1⟩
  obtain ⟨A, B, C, hAne, hBne, hCne, hAB, hAC, hBC, hcov, hAW, hBW, hCW, hA0, hB1, hC2⟩ := hatoms
  obtain ⟨qA, hqA⟩ := hAne; obtain ⟨qB, hqB⟩ := hBne; obtain ⟨qC, hqC⟩ := hCne
  have hBA : Disjoint B A := hAB.symm
  have hCA : Disjoint C A := hAC.symm
  have hCB : Disjoint C B := hBC.symm
  have hqA_nB : qA ∉ B := Finset.disjoint_left.mp hAB hqA
  have hqA_nC : qA ∉ C := Finset.disjoint_left.mp hAC hqA
  have hqB_nA : qB ∉ A := Finset.disjoint_left.mp hBA hqB
  have hqB_nC : qB ∉ C := Finset.disjoint_left.mp hBC hqB
  have hqC_nA : qC ∉ A := Finset.disjoint_left.mp hCA hqC
  have hqC_nB : qC ∉ B := Finset.disjoint_left.mp hCB hqC
  let basis : Fin 3 → (Q → ℚ) := fun i =>
    if i.1 = 0 then indQ A else if i.1 = 1 then indQ B else indQ C
  have hli_b : LinearIndependent ℚ basis := by
    rw [Fintype.linearIndependent_iff]
    intro α hα i
    rcases (by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2) with h | h | h
    · have hev := congrFun hα qA
      rw [Finset.sum_apply, Fin.sum_univ_castSucc, Fin.sum_univ_two] at hev
      change α 0 * indQ A qA + α 1 * indQ B qA + α 2 * indQ C qA = 0 at hev
      simp only [indQ, hqA, hqA_nB, hqA_nC, ↓reduceIte, mul_one, mul_zero, add_zero] at hev
      rw [show i = 0 from Fin.ext h]; exact hev
    · have hev := congrFun hα qB
      rw [Finset.sum_apply, Fin.sum_univ_castSucc, Fin.sum_univ_two] at hev
      change α 0 * indQ A qB + α 1 * indQ B qB + α 2 * indQ C qB = 0 at hev
      simp only [indQ, hqB, hqB_nA, hqB_nC, ↓reduceIte, mul_one, mul_zero, zero_add, add_zero] at hev
      rw [show i = 1 from Fin.ext h]; exact hev
    · have hev := congrFun hα qC
      rw [Finset.sum_apply, Fin.sum_univ_castSucc, Fin.sum_univ_two] at hev
      change α 0 * indQ A qC + α 1 * indQ B qC + α 2 * indQ C qC = 0 at hev
      simp only [indQ, hqC, hqC_nA, hqC_nB, ↓reduceIte, mul_one, mul_zero, zero_add] at hev
      rw [show i = 2 from Fin.ext h]; exact hev
  have hspan_le : Submodule.span ℚ (Set.range basis) ≤ W := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩
    rcases (by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2) with h | h | h
    · dsimp only [basis]; rw [if_pos h]; exact hAW
    · dsimp only [basis]; rw [if_neg (by omega), if_pos h]; exact hBW
    · dsimp only [basis]; rw [if_neg (by omega), if_neg (by omega)]; exact hCW
  have hspan_eq : Submodule.span ℚ (Set.range basis) = W := by
    apply Submodule.eq_of_le_of_finrank_eq hspan_le
    have hfr := finrank_span_eq_card hli_b
    rw [Fintype.card_fin] at hfr
    have hle := Submodule.finrank_mono hspan_le
    omega
  -- Every function in `W = span {indQ A, indQ B, indQ C}` is constant on `A`, on `B`, and on `C`
  have hconst_span : ∀ f ∈ Submodule.span ℚ (Set.range basis),
      (∀ q ∈ A, f q = f qA) ∧ (∀ q ∈ B, f q = f qB) ∧ (∀ q ∈ C, f q = f qC) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      rcases (by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2) with h | h | h
      · have hbi : basis i = indQ A := by dsimp only [basis]; rw [if_pos h]
        rw [hbi]
        refine ⟨fun q hq => by simp [indQ, hq, hqA],
                fun q hq => by simp [indQ, Finset.disjoint_left.mp hBA hq, hqB_nA],
                fun q hq => by simp [indQ, Finset.disjoint_left.mp hCA hq, hqC_nA]⟩
      · have hbi : basis i = indQ B := by dsimp only [basis]; rw [if_neg (by omega), if_pos h]
        rw [hbi]
        refine ⟨fun q hq => by simp [indQ, Finset.disjoint_left.mp hAB hq, hqA_nB],
                fun q hq => by simp [indQ, hq, hqB],
                fun q hq => by simp [indQ, Finset.disjoint_left.mp hCB hq, hqC_nB]⟩
      · have hbi : basis i = indQ C := by
          dsimp only [basis]; rw [if_neg (by omega), if_neg (by omega)]
        rw [hbi]
        refine ⟨fun q hq => by simp [indQ, Finset.disjoint_left.mp hAC hq, hqA_nC],
                fun q hq => by simp [indQ, Finset.disjoint_left.mp hBC hq, hqB_nC],
                fun q hq => by simp [indQ, hq, hqC]⟩
    | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    | add x y _ _ ihx ihy =>
      exact ⟨fun q hq => by simp [ihx.1 q hq, ihy.1 q hq],
             fun q hq => by simp [ihx.2.1 q hq, ihy.2.1 q hq],
             fun q hq => by simp [ihx.2.2 q hq, ihy.2.2 q hq]⟩
    | smul r x _ ihx =>
      exact ⟨fun q hq => by simp [ihx.1 q hq],
             fun q hq => by simp [ihx.2.1 q hq],
             fun q hq => by simp [ihx.2.2 q hq]⟩
  have hS3_const := hconst_span (indQ S3) (hspan_eq ▸ hmem S3 hS3)
  have hiffA : ∀ q ∈ A, (q ∈ S3 ↔ qA ∈ S3) := fun q hq => by
    have h := hS3_const.1 q hq
    by_cases h1' : q ∈ S3 <;> by_cases h2' : qA ∈ S3 <;> simp [indQ, h1', h2'] at h ⊢
  have hiffB : ∀ q ∈ B, (q ∈ S3 ↔ qB ∈ S3) := fun q hq => by
    have h := hS3_const.2.1 q hq
    by_cases h1' : q ∈ S3 <;> by_cases h2' : qB ∈ S3 <;> simp [indQ, h1', h2'] at h ⊢
  have hiffC : ∀ q ∈ C, (q ∈ S3 ↔ qC ∈ S3) := fun q hq => by
    have h := hS3_const.2.2 q hq
    by_cases h1' : q ∈ S3 <;> by_cases h2' : qC ∈ S3 <;> simp [indQ, h1', h2'] at h ⊢
  have hcontra_atom : ∀ {X Y : Finset Q}, Y ∈ F → S3 ≠ Y →
      (X = Y ∨ X = Finset.univ \ Y) → (S3 = X ∨ S3 = Finset.univ \ X) → False := by
    intro X Y hY hne hXY h3X
    rcases hXY with hXY | hXY
    · subst X
      rcases h3X with h | h
      · exact hne h
      · exact hnc S3 hS3 Y hY h
    · subst X
      rcases h3X with h | h
      · exact hnc S3 hS3 Y hY h
      · rw [compl_compl] at h; exact hne h
  by_cases bA : qA ∈ S3 <;> by_cases bB : qB ∈ S3 <;> by_cases bC : qC ∈ S3
  · apply hne_univ S3 hS3; ext q; simp only [Finset.mem_univ, iff_true]
    rcases hcov q with hq | hq | hq
    · exact (hiffA q hq).mpr bA
    · exact (hiffB q hq).mpr bB
    · exact (hiffC q hq).mpr bC
  · refine hcontra_atom hS2 h32 hC2 (Or.inr ?_)
    ext q; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hq3 hqC; exact bC ((hiffC q hqC).mp hq3)
    · intro hq_nC; rcases hcov q with hq | hq | hq
      · exact (hiffA q hq).mpr bA
      · exact (hiffB q hq).mpr bB
      · exact absurd hq hq_nC
  · refine hcontra_atom hS1 h31 hB1 (Or.inr ?_)
    ext q; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hq3 hqB; exact bB ((hiffB q hqB).mp hq3)
    · intro hq_nB; rcases hcov q with hq | hq | hq
      · exact (hiffA q hq).mpr bA
      · exact absurd hq hq_nB
      · exact (hiffC q hq).mpr bC
  · refine hcontra_atom hS0 h30 hA0 (Or.inl ?_)
    ext q; constructor
    · intro hq3; rcases hcov q with hq | hq | hq
      · exact hq
      · exact absurd ((hiffB q hq).mp hq3) bB
      · exact absurd ((hiffC q hq).mp hq3) bC
    · intro hqA'; exact (hiffA q hqA').mpr bA
  · refine hcontra_atom hS0 h30 hA0 (Or.inr ?_)
    ext q; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hq3 hqA'; exact bA ((hiffA q hqA').mp hq3)
    · intro hq_nA; rcases hcov q with hq | hq | hq
      · exact absurd hq hq_nA
      · exact (hiffB q hq).mpr bB
      · exact (hiffC q hq).mpr bC
  · refine hcontra_atom hS1 h31 hB1 (Or.inl ?_)
    ext q; constructor
    · intro hq3; rcases hcov q with hq | hq | hq
      · exact absurd ((hiffA q hq).mp hq3) bA
      · exact hq
      · exact absurd ((hiffC q hq).mp hq3) bC
    · intro hqB'; exact (hiffB q hqB').mpr bB
  · refine hcontra_atom hS2 h32 hC2 (Or.inl ?_)
    ext q; constructor
    · intro hq3; rcases hcov q with hq | hq | hq
      · exact absurd ((hiffA q hq).mp hq3) bA
      · exact absurd ((hiffB q hq).mp hq3) bB
      · exact hq
    · intro hqC'; exact (hiffC q hqC').mpr bC
  · obtain ⟨q, hq3⟩ := hnonempty S3 hS3
    rcases hcov q with hq | hq | hq
    · exact bA ((hiffA q hq).mp hq3)
    · exact bB ((hiffB q hq).mp hq3)
    · exact bC ((hiffC q hq).mp hq3)

end ThreePairLemma

section AmortizedChain

variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- **Amortized Černý Assembly Lemma:**
If at most `1` proper nonempty subset (`BadPlus`) needs length `n + 1`, at most `n - 3`
proper nonempty subsets in total (`BadGe`) need length `≥ n`, and every other subset
needs length `≤ n - 1`, then `A` admits a synchronizing word of length `≤ (n - 1)^2`! -/
theorem cerny_of_almost_n_extensible [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync)
    (BadPlus BadGe : Finset (Finset Q))
    (hsub : BadPlus ⊆ BadGe)
    (hplus_card : BadPlus.card ≤ 1)
    (hge_card : BadGe.card + 2 < Fintype.card Q)
    (hext_fast : ∀ S : Finset Q, 1 ≤ S.card → S.card < Fintype.card Q → S ∉ BadGe →
      ∃ w : List α, w.length ≤ Fintype.card Q - 1 ∧ S.card < (A.preimage S w).card)
    (hext_mid : ∀ S : Finset Q, 1 ≤ S.card → S.card < Fintype.card Q → S ∈ BadGe → S ∉ BadPlus →
      ∃ w : List α, w.length ≤ Fintype.card Q ∧ S.card < (A.preimage S w).card)
    (hext_slow : ∀ S : Finset Q, 1 ≤ S.card → S.card < Fintype.card Q → S ∈ BadPlus →
      ∃ w : List α, w.length ≤ Fintype.card Q + 1 ∧ S.card < (A.preimage S w).card) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  let n := Fintype.card Q
  have hn3 : 3 ≤ n := by omega
  obtain ⟨c₀, b₀, hc₀_card⟩ := A.exists_collision_letter_of_isSync hsync (by omega)
  let S₁ := A.preimage {c₀} [b₀]
  have hchain : ∀ d : ℕ, ∀ S : Finset Q, S.card + d = n → 2 ≤ S.card →
      ∃ (s : ℕ) (T : Fin (s + 1) → Finset Q) (ws : Fin s → List α),
        T 0 = S ∧ T (Fin.last s) = Finset.univ ∧
        (∀ i : Fin s, T i.succ = A.preimage (T i.castSucc) (ws i)) ∧
        (∀ i : Fin s, (T i.castSucc).card < (T i.succ).card) ∧
        (∀ i : Fin s, (ws i).length ≤
          if T i.castSucc ∈ BadPlus then n + 1
          else if T i.castSucc ∈ BadGe then n
          else n - 1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro S hd hS2
      by_cases hd0 : d = 0
      · subst hd0
        refine ⟨0, fun _ => Finset.univ, Fin.elim0,
          (Finset.eq_univ_of_card S (by omega)).symm, rfl,
          fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
      · have hS_lt : S.card < n := by omega
        have hstep_ex : ∃ u : List α, S.card < (A.preimage S u).card ∧
            u.length ≤ if S ∈ BadPlus then n + 1 else if S ∈ BadGe then n else n - 1 := by
          by_cases hp : S ∈ BadPlus
          · obtain ⟨u, hl, hg⟩ := hext_slow S (by omega) hS_lt hp
            exact ⟨u, hg, by simpa [hp, n] using hl⟩
          · by_cases hg' : S ∈ BadGe
            · obtain ⟨u, hl, hg⟩ := hext_mid S (by omega) hS_lt hg' hp
              exact ⟨u, hg, by simpa [hp, hg', n] using hl⟩
            · obtain ⟨u, hl, hg⟩ := hext_fast S (by omega) hS_lt hg'
              exact ⟨u, hg, by simpa [hp, hg', n] using hl⟩
        obtain ⟨u, hu_gt, hu_len⟩ := hstep_ex
        let S' := A.preimage S u
        have hd' : S'.card + (n - S'.card) = n := by
          have := Finset.card_le_univ S'; dsimp only [S', n] at *; omega
        obtain ⟨s, T, ws, hT0, hTlast, hTstep, hTinc, hTlen⟩ :=
          ih (n - S'.card) (by dsimp only [S', n] at *; omega) S' hd' (by dsimp only [S'] at *; omega)
        let T' : Fin (s + 2) → Finset Q := fun i =>
          if h : i.1 = 0 then S else T ⟨i.1 - 1, by omega⟩
        let ws' : Fin (s + 1) → List α := fun i =>
          if h : i.1 = 0 then u else ws ⟨i.1 - 1, by omega⟩
        refine ⟨s + 1, T', ws', by simp [T'], ?_, ?_, ?_, ?_⟩
        · dsimp only [T']
          rw [dif_neg (by simp)]
          have hlast : (⟨(Fin.last (s + 1)).1 - 1, by simp⟩ : Fin (s + 1)) = Fin.last s :=
            Fin.ext (by simp)
          rw [hlast]; exact hTlast
        · intro i
          by_cases hi : i.1 = 0
          · dsimp only [T', ws']
            rw [dif_neg (by simp), dif_pos (show i.castSucc.1 = 0 from hi), dif_pos hi]
            have h0 : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = 0 := Fin.ext (by simp [hi])
            rw [h0, hT0]
          · dsimp only [T', ws']
            rw [dif_neg (by simp), dif_neg (show i.castSucc.1 ≠ 0 from hi), dif_neg hi]
            have h1 : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = (⟨i.1 - 1, by omega⟩ : Fin s).succ :=
              Fin.ext (by simp; omega)
            have h2 : (⟨i.castSucc.1 - 1, by omega⟩ : Fin (s + 1)) =
                (⟨i.1 - 1, by omega⟩ : Fin s).castSucc := Fin.ext (by simp)
            rw [h1, h2]
            exact hTstep ⟨i.1 - 1, by omega⟩
        · intro i
          by_cases hi : i.1 = 0
          · dsimp only [T']
            rw [dif_pos (show i.castSucc.1 = 0 from hi), dif_neg (by simp)]
            have h0 : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = 0 := Fin.ext (by simp [hi])
            rw [h0, hT0]
            exact hu_gt
          · dsimp only [T']
            rw [dif_neg (show i.castSucc.1 ≠ 0 from hi), dif_neg (by simp)]
            have h1 : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = (⟨i.1 - 1, by omega⟩ : Fin s).succ :=
              Fin.ext (by simp; omega)
            have h2 : (⟨i.castSucc.1 - 1, by omega⟩ : Fin (s + 1)) =
                (⟨i.1 - 1, by omega⟩ : Fin s).castSucc := Fin.ext (by simp)
            rw [h1, h2]
            exact hTinc ⟨i.1 - 1, by omega⟩
        · intro i
          by_cases hi : i.1 = 0
          · have hi' : i = 0 := Fin.ext hi
            simpa [T', ws', hi'] using hu_len
          · have hi' : i ≠ 0 := fun h => hi (by simpa using congrArg Fin.val h)
            have hcast : (⟨i.castSucc.1 - 1, by omega⟩ : Fin (s + 1)) =
                (⟨i.1 - 1, by omega⟩ : Fin s).castSucc := Fin.ext (by simp)
            simp only [T', ws', hi', ↓reduceIte, hcast]
            have hif : (if h : (i : ℕ) = 0 then u else ws ⟨i.1 - 1, by omega⟩) =
                ws ⟨i.1 - 1, by omega⟩ := dif_neg hi
            rw [hif]
            have hcast' : (if h : (i.castSucc : ℕ) = 0 then S
                else T (⟨i.1 - 1, by omega⟩ : Fin s).castSucc) =
                T (⟨i.1 - 1, by omega⟩ : Fin s).castSucc := by
              rw [dif_neg]
              simpa using hi
            rw [hcast']
            exact hTlen ⟨i.1 - 1, by omega⟩
  obtain ⟨s, T, ws, hT0, hTlast, hTstep, hTinc, hTlen⟩ :=
    hchain (n - S₁.card) S₁ (by have := Finset.card_le_univ S₁; omega) hc₀_card
  have hT_mono : ∀ a b : ℕ, (hb : b ≤ s) → (hab : a < b) →
      (T ⟨a, Nat.lt_trans (Nat.lt_of_lt_of_le hab hb) (Nat.lt_succ_self s)⟩).card <
        (T ⟨b, Nat.lt_succ_of_le hb⟩).card := by
    intro a b hb hab
    induction b generalizing a with
    | zero => exact (Nat.not_lt_zero a hab).elim
    | succ b ihb =>
      have hb_lt : b < s := Nat.lt_of_succ_le hb
      have hstep_b : (T ⟨b, Nat.lt_trans hb_lt (Nat.lt_succ_self s)⟩).card <
          (T ⟨b + 1, Nat.lt_succ_of_le hb⟩).card := by
        simpa using (hTinc ⟨b, hb_lt⟩)
      by_cases heq : a = b
      · subst a
        simpa using hstep_b
      · have hle : a ≤ b := Nat.lt_succ_iff.mp hab
        have hab' : a < b := lt_of_le_of_ne hle heq
        exact lt_trans (ihb a (Nat.le_trans (Nat.le_succ b) hb) hab') hstep_b
  have hT_inj : Function.Injective (fun i : Fin s => T i.castSucc) := by
    intro i j hEq
    rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
    · exact absurd (congrArg Finset.card hEq) (ne_of_lt (hT_mono i.1 j.1 (by omega) hlt))
    · exact Fin.ext heq
    · exact absurd (congrArg Finset.card hEq) (ne_of_gt (hT_mono j.1 i.1 (by omega) hgt))
  have hs_le : s ≤ n - 2 := by
    have hgrow : ∀ k (hk : k ≤ s), 2 + k ≤ (T ⟨k, by omega⟩).card := by
      intro k
      induction k with
      | zero => intro _; rw [show (⟨0, by omega⟩ : Fin (s + 1)) = 0 from rfl, hT0]; exact hc₀_card
      | succ k ihk =>
        intro hk
        have h1 := ihk (by omega)
        have h2 : (T ⟨k, by omega⟩).card < (T ⟨k + 1, by omega⟩).card := hTinc ⟨k, by omega⟩
        omega
    have hlast := hgrow s le_rfl
    rw [show (⟨s, by omega⟩ : Fin (s + 1)) = Fin.last s from rfl, hTlast, Finset.card_univ] at hlast
    change 2 + s ≤ n at hlast
    omega
  let T_full : Fin (s + 2) → Finset Q := fun i =>
    if h : i.1 = 0 then {c₀} else T ⟨i.1 - 1, by omega⟩
  let ws_full : Fin (s + 1) → List α := fun i =>
    if h : i.1 = 0 then [b₀] else ws ⟨i.1 - 1, by omega⟩
  obtain ⟨u, hu_sync, hu_len⟩ := Aut.isSyncWord_of_chain A (s + 1) T_full ws_full c₀
    (by simp [T_full])
    (by
      dsimp only [T_full]
      rw [dif_neg (by simp)]
      have hlast : (⟨(Fin.last (s + 1)).1 - 1, by simp⟩ : Fin (s + 1)) = Fin.last s :=
        Fin.ext (by simp)
      rw [hlast]; exact hTlast)
    (fun i => by
      by_cases hi : i.1 = 0
      · have hi' : i = 0 := Fin.ext hi
        simp [T_full, ws_full, hi', hT0, S₁]
      · let j : Fin s := ⟨i.1 - 1, by omega⟩
        have hi' : i ≠ 0 := fun h => hi (by simpa using congrArg Fin.val h)
        have hsucc : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = j.succ := by
          dsimp only [j]; exact Fin.ext (by simp; omega)
        have hcast : (⟨i.castSucc.1 - 1, by omega⟩ : Fin (s + 1)) = j.castSucc := by
          dsimp only [j]; exact Fin.ext (by simp)
        simp [T_full, ws_full, hi', hsucc, hcast]
        have hi_succ : i = j.succ := by dsimp only [j]; exact Fin.ext (by simp; omega)
        have hj_eq : (⟨i.1 - 1, by omega⟩ : Fin s) = j := rfl
        have hsub : T j.succ ⊆ A.preimage (T j.castSucc) (ws j) := by rw [hTstep j]
        have hj_cast : (⟨j.1, by omega⟩ : Fin (s + 1)) = j.castSucc := rfl
        simpa [hi_succ, hj_eq, hj_cast] using hsub)
  refine ⟨u, hu_sync, ?_⟩
  rw [hu_len, Fin.sum_univ_succ]
  have hw0 : ws_full 0 = [b₀] := by simp [ws_full]
  have hws : ∀ i : Fin s, ws_full i.succ = ws i := fun i => by
    simp [ws_full]
  rw [hw0, List.length_singleton]
  simp_rw [hws]
  change 1 + ∑ i : Fin s, (ws i).length ≤ (n - 1) ^ 2
  set L := ∑ i : Fin s, (ws i).length
  let I_plus := Finset.univ.filter (fun i : Fin s => T i.castSucc ∈ BadPlus)
  let I_ge := Finset.univ.filter (fun i : Fin s => T i.castSucc ∈ BadGe)
  have hIplus_le : I_plus.card ≤ 1 := by
    calc I_plus.card = (I_plus.image (fun i : Fin s => T i.castSucc)).card :=
          (Finset.card_image_of_injective _ hT_inj).symm
      _ ≤ BadPlus.card := Finset.card_le_card (fun X hX => by
          rcases Finset.mem_image.mp hX with ⟨i, hi, rfl⟩
          exact (Finset.mem_filter.mp hi).2)
      _ ≤ 1 := hplus_card
  have hIge_le : I_ge.card ≤ BadGe.card := by
    calc I_ge.card = (I_ge.image (fun i : Fin s => T i.castSucc)).card :=
          (Finset.card_image_of_injective _ hT_inj).symm
      _ ≤ BadGe.card := Finset.card_le_card (fun X hX => by
          rcases Finset.mem_image.mp hX with ⟨i, hi, rfl⟩
          exact (Finset.mem_filter.mp hi).2)
  have hsum_le : L + (s - I_ge.card) ≤ s * n + I_plus.card := by
    have hpt : ∀ i : Fin s,
        (ws i).length + (if T i.castSucc ∈ BadGe then 0 else 1) ≤
          n + (if T i.castSucc ∈ BadPlus then 1 else 0) := by
      intro i
      have hi := hTlen i
      by_cases hp : T i.castSucc ∈ BadPlus
      · have hg : T i.castSucc ∈ BadGe := hsub hp
        simp only [hp, hg, ↓reduceIte] at hi ⊢; omega
      · by_cases hg : T i.castSucc ∈ BadGe
        · simp only [hp, hg, ↓reduceIte] at hi ⊢; omega
        · simp only [hp, hg, ↓reduceIte] at hi ⊢; omega
    have hsum :
        (∑ i : Fin s, ((ws i).length + (if T i.castSucc ∈ BadGe then 0 else 1))) ≤
          ∑ i : Fin s, (n + (if T i.castSucc ∈ BadPlus then 1 else 0)) :=
      Finset.sum_le_sum (fun i _ => hpt i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hsum
    have hnotge : ∑ i : Fin s, (if T i.castSucc ∈ BadGe then 0 else 1) = s - I_ge.card := by
      have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin s)))
        (p := fun i : Fin s => T i.castSucc ∈ BadGe)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      have h2 : ∑ i : Fin s, (if T i.castSucc ∈ BadGe then 0 else 1) =
          (Finset.univ.filter (fun i : Fin s => T i.castSucc ∉ BadGe)).card := by
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun i _ => by by_cases h : T i.castSucc ∈ BadGe <;> simp [h]
      dsimp only [I_ge] at h1 ⊢; omega
    have hplus_eq : ∑ i : Fin s, (if T i.castSucc ∈ BadPlus then 1 else 0) = I_plus.card := by
      rw [Finset.card_filter]
    rw [hnotge, hplus_eq] at hsum
    exact hsum
  have hIge_le_s : I_ge.card ≤ s := by
    calc I_ge.card ≤ (Finset.univ : Finset (Fin s)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = s := Finset.card_fin s
  have harith : 1 + (n - 2) * n = (n - 1) ^ 2 := by
    zify [show 2 ≤ n by omega, show 1 ≤ n by omega]; ring
  by_cases hs_top : s = n - 2
  · have hge_lt : BadGe.card + 2 < n := hge_card
    have hsn : s * n = (n - 2) * n := by rw [hs_top]
    have hsave : 1 ≤ s - I_ge.card := by omega
    omega
  · have hs_small : s ≤ n - 3 := by omega
    have hmul : s * n + n ≤ (n - 2) * n := by
      have : s + 1 ≤ n - 2 := by omega
      calc s * n + n = (s + 1) * n := by ring
        _ ≤ (n - 2) * n := Nat.mul_le_mul_right n this
    omega

end AmortizedChain

section LinearAndCombinatorialHelpers

open BalancedPermutations KrylovEulerian

variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

private lemma card_sdiff_univ_add (S : Finset Q) :
    (Finset.univ \ S).card + S.card = Fintype.card Q := by
  have hdisj : Disjoint (Finset.univ \ S) S := Finset.sdiff_disjoint
  have hunion : (Finset.univ \ S) ∪ S = Finset.univ := by
    ext q
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    by_cases hq : q ∈ S
    · exact Or.inr hq
    · exact Or.inl hq
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]

private lemma finrank_fun_rat (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.finrank ℚ (ι → ℚ) = Fintype.card ι := by
  let e : ι → (ι → ℚ) := fun i j => if j = i then 1 else 0
  have hli : LinearIndependent ℚ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrFun hc i
    rw [Finset.sum_apply] at h
    simp [e] at h
    exact h
  have hsp : Submodule.span ℚ (Set.range e) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    have hf : f = ∑ i : ι, f i • e i := by
      ext j; rw [Finset.sum_apply]; simp [e]
    rw [hf]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := finrank_span_eq_card hli
  rw [hsp, finrank_top] at h1
  exact h1

/-- **1-Pair Subspace Lemma (dimension ≤ 2):**
A subspace `W ≤ (Q → ℚ)` with `finrank ℚ W ≤ 2` containing `1` contains at most one
proper nonempty subset from distinct complementary pairs. -/
theorem card_noncomp_01_le_one
    (W : Submodule ℚ (Q → ℚ)) (hdim : Module.finrank ℚ W ≤ 2)
    (h1 : (fun _ : Q => (1 : ℚ)) ∈ W)
    (F : Finset (Finset Q))
    (hproper : ∀ S ∈ F, 1 ≤ S.card ∧ S.card < Fintype.card Q)
    (hmem : ∀ S ∈ F, indQ S ∈ W)
    (hncomp : ∀ S ∈ F, Finset.univ \ S ∉ F) :
    F.card ≤ 1 := by
  classical
  by_contra hgt
  obtain ⟨S0, hS0⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
  have hc1 : 1 ≤ (F.erase S0).card := by rw [Finset.card_erase_of_mem hS0]; omega
  obtain ⟨S1, hS1e⟩ := Finset.card_pos.mp (by omega : 0 < (F.erase S0).card)
  obtain ⟨h10, hS1⟩ := Finset.mem_erase.mp hS1e
  let v : Fin 3 → (Q → ℚ) := fun i =>
    if i.1 = 0 then (fun _ => 1) else if i.1 = 1 then indQ S0 else indQ S1
  have hv_mem : ∀ i : Fin 3, v i ∈ W := by
    intro i
    rcases (by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2) with h | h | h
    · simp only [v, h, ↓reduceIte]; exact h1
    · simp only [v, h, ↓reduceIte]; exact hmem S0 hS0
    · simp only [v, h, ↓reduceIte]; exact hmem S1 hS1
  have hnotli : ¬ LinearIndependent ℚ v := by
    intro hli
    have hsub : Submodule.span ℚ (Set.range v) ≤ W := by
      rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hv_mem i
    have hle := Submodule.finrank_mono hsub
    rw [finrank_span_eq_card hli, Fintype.card_fin] at hle
    omega
  rw [Fintype.linearIndependent_iff] at hnotli
  push_neg at hnotli
  obtain ⟨c, hc_sum, i₀, hi₀⟩ := hnotli
  have hrel : ∀ q : Q, c 0 + c 1 * indQ S0 q + c 2 * indQ S1 q = 0 := by
    intro q
    have h0 := congrFun hc_sum q
    rw [Finset.sum_apply, Fin.sum_univ_castSucc, Fin.sum_univ_two] at h0
    change c 0 * 1 + c 1 * indQ S0 q + c 2 * indQ S1 q = 0 at h0
    linarith
  have hno_single : ∀ {S : Finset Q} {c₀ r : ℚ}, S ∈ F → r ≠ 0 →
      (∀ q, c₀ + r * indQ S q = 0) → False := by
    intro S c₀ r hS hr hrelS
    obtain ⟨q₁, hq₁⟩ := Finset.card_pos.mp (hproper S hS).1
    have hne : S ≠ Finset.univ := fun hEq => by
      have := (hproper S hS).2; rw [hEq, Finset.card_univ] at this; omega
    obtain ⟨q₂, hq₂⟩ := compl_nonempty_of_ne_univ hne
    have hq₂' : q₂ ∉ S := (Finset.mem_sdiff.mp hq₂).2
    have e1 := hrelS q₁; have e2 := hrelS q₂
    simp only [indQ, hq₁, hq₂', ↓reduceIte, mul_one, mul_zero] at e1 e2
    exact hr (by linarith)
  by_cases hc1 : c 1 = 0
  · by_cases hc2 : c 2 = 0
    · obtain ⟨q, _⟩ := Finset.card_pos.mp (hproper S0 hS0).1
      have hc0 : c 0 = 0 := by
        have := hrel q; simp only [hc1, hc2, zero_mul, add_zero] at this; exact this
      rcases (by omega : i₀.1 = 0 ∨ i₀.1 = 1 ∨ i₀.1 = 2) with h | h | h
      · exact hi₀ (by rw [show i₀ = 0 from Fin.ext h]; exact hc0)
      · exact hi₀ (by rw [show i₀ = 1 from Fin.ext h]; exact hc1)
      · exact hi₀ (by rw [show i₀ = 2 from Fin.ext h]; exact hc2)
    · exact hno_single hS1 hc2 (fun q => by
        have := hrel q; simp only [hc1, zero_mul, add_zero] at this; exact this)
  · by_cases hc2 : c 2 = 0
    · exact hno_single hS0 hc1 (fun q => by
        have := hrel q; simp only [hc2, zero_mul, add_zero] at this; exact this)
    · exact lin_dep_two_01 h10.symm (fun h => hncomp S1 hS1 (h ▸ hS0)) hc1 hc2 hrel

private lemma eq_or_compl_of_finrank_le_two
    (W : Submodule ℚ (Q → ℚ)) (hdim : Module.finrank ℚ W ≤ 2)
    (h1 : (fun _ : Q => (1 : ℚ)) ∈ W)
    {T₀ S : Finset Q}
    (hT0 : 1 ≤ T₀.card ∧ T₀.card < Fintype.card Q)
    (hS : 1 ≤ S.card ∧ S.card < Fintype.card Q)
    (hT0W : indQ T₀ ∈ W) (hSW : indQ S ∈ W) :
    S = T₀ ∨ S = Finset.univ \ T₀ := by
  classical
  by_contra hneither
  push_neg at hneither
  have hle := card_noncomp_01_le_one W hdim h1 {T₀, S}
    (fun X hX => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with hX | hX <;> rw [hX]
      · exact hT0
      · exact hS)
    (fun X hX => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with hX | hX <;> rw [hX]
      · exact hT0W
      · exact hSW)
    (fun X hX hcompl => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX hcompl
      rcases hX with hX | hX
      · rw [hX] at hcompl
        rcases hcompl with h | h
        · obtain ⟨q, hq⟩ := Finset.card_pos.mp hT0.1
          have : q ∈ Finset.univ \ T₀ := by rw [h]; exact hq
          exact (Finset.mem_sdiff.mp this).2 hq
        · exact hneither.2 h.symm
      · rw [hX] at hcompl
        rcases hcompl with h | h
        · apply hneither.2
          have := congrArg (fun Z => Finset.univ \ Z) h
          simpa only [compl_compl] using this
        · obtain ⟨q, hq⟩ := Finset.card_pos.mp hS.1
          have : q ∈ Finset.univ \ S := by rw [h]; exact hq
          exact (Finset.mem_sdiff.mp this).2 hq)
  rw [Finset.card_pair hneither.1.symm] at hle
  omega

/-- Standard Černý assembly from `n`-extensibility (works for all `n ≥ 1`). -/
theorem cerny_of_n_extensible [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync)
    (hext : ∀ S : Finset Q, 1 ≤ S.card → S.card < Fintype.card Q →
      ∃ w : List α, w.length ≤ Fintype.card Q ∧ S.card < (A.preimage S w).card) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  let n := Fintype.card Q
  by_cases hn1 : n = 1
  · obtain ⟨c₀⟩ := ‹Nonempty Q›
    obtain ⟨u, hu_sync, hu_len⟩ := Aut.isSyncWord_of_chain A 0 (fun _ => {c₀}) Fin.elim0 c₀
      rfl (Finset.eq_univ_of_card {c₀} (by simp [n, hn1])) (fun i => Fin.elim0 i)
    refine ⟨u, hu_sync, ?_⟩
    rw [hu_len]; simp
  · have hn2 : 2 ≤ n := by have := Fintype.card_pos (α := Q); omega
    obtain ⟨c₀, b₀, hc₀_card⟩ := A.exists_collision_letter_of_isSync hsync hn2
    let S₁ := A.preimage {c₀} [b₀]
    have hchain : ∀ d : ℕ, ∀ S : Finset Q, S.card + d = n → 2 ≤ S.card →
        ∃ (s : ℕ) (T : Fin (s + 1) → Finset Q) (ws : Fin s → List α),
          T 0 = S ∧ T (Fin.last s) = Finset.univ ∧
          (∀ i : Fin s, T i.succ = A.preimage (T i.castSucc) (ws i)) ∧
          (∀ i : Fin s, (T i.castSucc).card < (T i.succ).card) ∧
          (∀ i : Fin s, (ws i).length ≤ n) := by
      intro d
      induction d using Nat.strong_induction_on with
      | ind d ih =>
        intro S hd hS2
        by_cases hd0 : d = 0
        · subst hd0
          refine ⟨0, fun _ => Finset.univ, Fin.elim0,
            (Finset.eq_univ_of_card S (by omega)).symm, rfl,
            fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
        · obtain ⟨u, hu_len, hu_gt⟩ := hext S (by omega) (by omega)
          let S' := A.preimage S u
          have hd' : S'.card + (n - S'.card) = n := by
            have := Finset.card_le_univ S'; dsimp only [S', n] at *; omega
          obtain ⟨s, T, ws, hT0, hTlast, hTstep, hTinc, hTlen⟩ :=
            ih (n - S'.card) (by dsimp only [S', n] at *; omega) S' hd' (by dsimp only [S'] at *; omega)
          let T' : Fin (s + 2) → Finset Q := fun i =>
            if h : i.1 = 0 then S else T ⟨i.1 - 1, by omega⟩
          let ws' : Fin (s + 1) → List α := fun i =>
            if h : i.1 = 0 then u else ws ⟨i.1 - 1, by omega⟩
          refine ⟨s + 1, T', ws', by simp [T'], ?_, ?_, ?_, ?_⟩
          · dsimp only [T']; rw [dif_neg (by simp)]
            have hlast : (⟨(Fin.last (s + 1)).1 - 1, by simp⟩ : Fin (s + 1)) = Fin.last s :=
              Fin.ext (by simp)
            rw [hlast]; exact hTlast
          · intro i
            by_cases hi : i.1 = 0
            · dsimp only [T', ws']
              rw [dif_neg (by simp), dif_pos (show i.castSucc.1 = 0 from hi), dif_pos hi]
              have h0 : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = 0 := Fin.ext (by simp [hi])
              rw [h0, hT0]
            · dsimp only [T', ws']
              rw [dif_neg (by simp), dif_neg (show i.castSucc.1 ≠ 0 from hi), dif_neg hi]
              have h1 : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = (⟨i.1 - 1, by omega⟩ : Fin s).succ :=
                Fin.ext (by simp; omega)
              have h2 : (⟨i.castSucc.1 - 1, by omega⟩ : Fin (s + 1)) =
                  (⟨i.1 - 1, by omega⟩ : Fin s).castSucc := Fin.ext (by simp)
              rw [h1, h2]; exact hTstep ⟨i.1 - 1, by omega⟩
          · intro i
            by_cases hi : i.1 = 0
            · dsimp only [T']
              rw [dif_pos (show i.castSucc.1 = 0 from hi), dif_neg (by simp)]
              have h0 : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = 0 := Fin.ext (by simp [hi])
              rw [h0, hT0]; exact hu_gt
            · dsimp only [T']
              rw [dif_neg (show i.castSucc.1 ≠ 0 from hi), dif_neg (by simp)]
              have h1 : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = (⟨i.1 - 1, by omega⟩ : Fin s).succ :=
                Fin.ext (by simp; omega)
              have h2 : (⟨i.castSucc.1 - 1, by omega⟩ : Fin (s + 1)) =
                  (⟨i.1 - 1, by omega⟩ : Fin s).castSucc := Fin.ext (by simp)
              rw [h1, h2]; exact hTinc ⟨i.1 - 1, by omega⟩
          · intro i
            by_cases hi : i.1 = 0
            · dsimp only [ws']; rw [dif_pos hi]; exact hu_len
            · dsimp only [ws']; rw [dif_neg hi]; exact hTlen ⟨i.1 - 1, by omega⟩
    obtain ⟨s, T, ws, hT0, hTlast, hTstep, hTinc, hTlen⟩ :=
      hchain (n - S₁.card) S₁ (by have := Finset.card_le_univ S₁; omega) hc₀_card
    have hs_le : s ≤ n - 2 := by
      have hgrow : ∀ k (hk : k ≤ s), 2 + k ≤ (T ⟨k, by omega⟩).card := by
        intro k
        induction k with
        | zero => intro _; rw [show (⟨0, by omega⟩ : Fin (s + 1)) = 0 from rfl, hT0]; exact hc₀_card
        | succ k ihk =>
          intro hk
          have h1 := ihk (by omega)
          have h2 : (T ⟨k, by omega⟩).card < (T ⟨k + 1, by omega⟩).card := hTinc ⟨k, by omega⟩
          omega
      have hlast := hgrow s le_rfl
      rw [show (⟨s, by omega⟩ : Fin (s + 1)) = Fin.last s from rfl, hTlast, Finset.card_univ] at hlast
      change 2 + s ≤ n at hlast; omega
    let T_full : Fin (s + 2) → Finset Q := fun i =>
      if h : i.1 = 0 then {c₀} else T ⟨i.1 - 1, by omega⟩
    let ws_full : Fin (s + 1) → List α := fun i =>
      if h : i.1 = 0 then [b₀] else ws ⟨i.1 - 1, by omega⟩
    obtain ⟨u, hu_sync, hu_len⟩ := Aut.isSyncWord_of_chain A (s + 1) T_full ws_full c₀
      (by simp [T_full])
      (by
        dsimp only [T_full]; rw [dif_neg (by simp)]
        have hlast : (⟨(Fin.last (s + 1)).1 - 1, by simp⟩ : Fin (s + 1)) = Fin.last s :=
          Fin.ext (by simp)
        rw [hlast]; exact hTlast)
      (fun i => by
        by_cases hi : i.1 = 0
        · have hi' : i = 0 := Fin.ext hi
          simp [T_full, ws_full, hi', hT0, S₁]
        · let j : Fin s := ⟨i.1 - 1, by omega⟩
          have hi' : i ≠ 0 := fun h => hi (by simpa using congrArg Fin.val h)
          have hsucc : (⟨i.succ.1 - 1, by omega⟩ : Fin (s + 1)) = j.succ := by
            dsimp only [j]; exact Fin.ext (by simp; omega)
          have hcast : (⟨i.castSucc.1 - 1, by omega⟩ : Fin (s + 1)) = j.castSucc := by
            dsimp only [j]; exact Fin.ext (by simp)
          simp [T_full, ws_full, hi', hsucc, hcast]
          have hi_succ : i = j.succ := by dsimp only [j]; exact Fin.ext (by simp; omega)
          have hj_eq : (⟨i.1 - 1, by omega⟩ : Fin s) = j := rfl
          have hsub : T j.succ ⊆ A.preimage (T j.castSucc) (ws j) := by rw [hTstep j]
          have hj_cast : (⟨j.1, by omega⟩ : Fin (s + 1)) = j.castSucc := rfl
          simpa [hi_succ, hj_eq, hj_cast] using hsub)
    refine ⟨u, hu_sync, ?_⟩
    rw [hu_len, Fin.sum_univ_succ]
    have hw0 : ws_full 0 = [b₀] := by simp [ws_full]
    have hws : ∀ i : Fin s, ws_full i.succ = ws i := fun i => by simp [ws_full]
    rw [hw0, List.length_singleton]; simp_rw [hws]
    have hsum : ∑ i : Fin s, (ws i).length ≤ s * n := by
      calc ∑ i : Fin s, (ws i).length ≤ ∑ _i : Fin s, n := Finset.sum_le_sum fun i _ => hTlen i
        _ = s * n := by simp
    have harith : 1 + (n - 2) * n = (n - 1) ^ 2 := by
      zify [show 2 ≤ n by omega, show 1 ≤ n by omega]; ring
    have hsn : s * n ≤ (n - 2) * n := Nat.mul_le_mul_right n hs_le
    change 1 + ∑ i : Fin s, (ws i).length ≤ (n - 1) ^ 2
    omega

private lemma eval_nil_aux (A : Aut Q α) (q : Q) : A.eval q [] = q := rfl
private lemma eval_cons_aux (A : Aut Q α) (q : Q) (σ : α) (w : List α) :
    A.eval q (σ :: w) = A.eval (A.step q σ) w := rfl

private lemma eval_append_aux (A : Aut Q α) (q : Q) (u v : List α) :
    A.eval q (u ++ v) = A.eval (A.eval q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons σ u ih => exact ih (A.step q σ)

private lemma eval_rep1 (A : Aut Q α) (a : α) (q : Q) :
    A.eval q (List.replicate 1 a) = A.step q a := by
  simp [List.replicate_succ, eval_cons_aux, eval_nil_aux]

private lemma eval_rep2 (A : Aut Q α) (a : α) (q : Q) :
    A.eval q (List.replicate 2 a) = A.step (A.step q a) a := by
  simp [List.replicate_succ, eval_cons_aux, eval_nil_aux]

private lemma eval_rep3 (A : Aut Q α) (a : α) (q : Q) :
    A.eval q (List.replicate 3 a) = A.step (A.step (A.step q a) a) a := by
  simp [List.replicate_succ, eval_cons_aux, eval_nil_aux]

private lemma eval_rep4 (A : Aut Q α) (a : α) (q : Q) :
    A.eval q (List.replicate 4 a) = A.step (A.step (A.step (A.step q a) a) a) a := by
  simp [List.replicate_succ, eval_cons_aux, eval_nil_aux]

private lemma preimage_nil_aux (A : Aut Q α) (S : Finset Q) : A.preimage S [] = S := by
  simpa using (A.preimage_nil S)

private lemma ρ_nil_aux (A : Aut Q α) : ρ A ([] : List α) = 0 := by
  ext q; simp [ρ, preimage_nil_aux]

private lemma replicate_add_append (a : α) (j k : ℕ) :
    List.replicate (j + k) a = List.replicate j a ++ List.replicate k a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih, List.cons_append]

private lemma replicate_succ_append (a : α) (k : ℕ) :
    List.replicate (k + 1) a = List.replicate k a ++ [a] := by
  simpa using (replicate_add_append a k 1)

private lemma eval_replicate_bijective (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (k : ℕ) :
    Function.Bijective (fun q => A.eval q (List.replicate k a)) := by
  induction k with
  | zero => exact Function.bijective_id
  | succ k ih =>
    have hcomp : (fun q => A.eval q (List.replicate (k + 1) a)) =
        (fun q => A.eval q (List.replicate k a)) ∘ (fun q => A.step q a) := by
      ext q; rw [List.replicate_succ]; rfl
    rw [hcomp]
    exact ih.comp hbij

private lemma R_apply_ite (A : Aut Q α) (w : List α) (x : Q → ℚ) (q : Q) :
    R A w x q = ∑ p : Q, if A.eval p w = q then x p else 0 := by
  simp [R, Aut.preimage, Finset.sum_filter]

private lemma R_nil (A : Aut Q α) (x : Q → ℚ) : R A [] x = x := by
  ext q
  rw [R_apply_ite]
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; simp at h

private lemma R_append (A : Aut Q α) (u v : List α) (x : Q → ℚ) :
    R A (u ++ v) x = R A v (R A u x) := by
  ext q
  rw [R_apply_ite, R_apply_ite]
  calc ∑ p : Q, (if A.eval p (u ++ v) = q then x p else 0)
      = ∑ p : Q, ∑ r : Q, (if r = A.eval p u ∧ A.eval r v = q then x p else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [eval_append_aux]
        by_cases hq : A.eval (A.eval p u) v = q
        · rw [if_pos hq, Finset.sum_eq_single (A.eval p u)]
          · simp [hq]
          · intro r _ hr; simp [hr]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [if_neg hq]
          exact (Finset.sum_eq_zero fun r _ => by
            by_cases hr : r = A.eval p u
            · subst hr; simp [hq]
            · simp [hr]).symm
    _ = ∑ r : Q, ∑ p : Q, (if r = A.eval p u ∧ A.eval r v = q then x p else 0) := Finset.sum_comm
    _ = ∑ r : Q, (if A.eval r v = q then R A u x r else 0) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases hr : A.eval r v = q
        · rw [if_pos hr, R_apply_ite]
          refine Finset.sum_congr rfl fun p _ => by
            by_cases hp : A.eval p u = r
            · rw [if_pos ⟨hp.symm, hr⟩, if_pos hp]
            · rw [if_neg (fun h => hp h.1.symm), if_neg hp]
        · rw [if_neg hr]
          exact Finset.sum_eq_zero fun p _ => by simp [hr]

private lemma R_a_a (A : Aut Q α) (a : α) (x : Q → ℚ) :
    R A [a] (R A [a] x) = R A (List.replicate 2 a) x := by
  rw [← R_append]; rfl

private lemma R_a_rep (A : Aut Q α) (a : α) (k : ℕ) (x : Q → ℚ) :
    R A [a] (R A (List.replicate k a) x) = R A (List.replicate (k + 1) a) x := by
  rw [← R_append, ← replicate_succ_append]

private lemma R_rep_rep (A : Aut Q α) (a : α) (j k : ℕ) (x : Q → ℚ) :
    R A (List.replicate k a) (R A (List.replicate j a) x) = R A (List.replicate (j + k) a) x := by
  rw [← R_append, ← replicate_add_append]

private lemma R_rep_a (A : Aut Q α) (a : α) (k : ℕ) (x : Q → ℚ) :
    R A (List.replicate k a) (R A [a] x) = R A (List.replicate (k + 1) a) x := by
  rw [← R_append, show [a] ++ List.replicate k a = List.replicate (k + 1) a from by
    rw [List.replicate_succ]; rfl]

private lemma R_bij_eval (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (k : ℕ) (x : Q → ℚ) (p : Q) :
    R A (List.replicate k a) x (A.eval p (List.replicate k a)) = x p := by
  rw [R_apply_ite]
  have hinj := (eval_replicate_bijective A hbij k).1
  rw [Finset.sum_eq_single p]
  · simp
  · intro r _ hr; rw [if_neg (fun h => hr (hinj h))]
  · intro h; exact absurd (Finset.mem_univ p) h

private lemma R_append_ρ (A : Aut Q α) (w u : List α) :
    R A u (ρ A w) = ρ A (w ++ u) - ρ A u := by
  rw [ρ_eq_R_ones_sub A w, map_sub, ← R_append, ρ_eq_R_ones_sub A (w ++ u), ρ_eq_R_ones_sub A u]
  abel

private lemma dotInd_ρ (A : Aut Q α) (w : List α) (S : Finset Q) :
    ∑ q ∈ S, ρ A w q = ((A.preimage S w).card : ℚ) - (S.card : ℚ) := by
  have h1 : ∑ q ∈ S, ρ A w q =
      (∑ q ∈ S, ((A.preimage {q} w).card : ℚ)) - (S.card : ℚ) := by
    simp only [ρ, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h1]
  congr 1
  have hcard : (A.preimage S w).card = ∑ q ∈ S, (A.preimage {q} w).card := by
    simp only [Finset.card_eq_sum_ones, Aut.preimage, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : A.eval p w ∈ S
    · rw [if_pos hp, Finset.sum_eq_single (A.eval p w)]
      · simp
      · intro q _ hq; simp [Ne.symm hq]
      · intro h; exact absurd hp h
    · rw [if_neg hp]
      exact (Finset.sum_eq_zero fun q hq => by
        have hne : A.eval p w ≠ q := fun hEq => hp (hEq ▸ hq)
        simp [hne]).symm
  rw [hcard, Nat.cast_sum]

private lemma sum_ρ_eq_zero (A : Aut Q α) (w : List α) :
    ∑ q : Q, ρ A w q = 0 := by
  have h := dotInd_ρ A w Finset.univ
  have hpre : A.preimage Finset.univ w = Finset.univ := by ext p; simp [Aut.preimage]
  rw [hpre] at h
  simpa using h

private lemma preimage_compl_card_add (A : Aut Q α) (S : Finset Q) (w : List α) :
    (A.preimage (Finset.univ \ S) w).card + (A.preimage S w).card = Fintype.card Q := by
  have hEq : A.preimage (Finset.univ \ S) w = Finset.univ \ A.preimage S w := by
    ext p; simp [Aut.preimage]
  rw [hEq]
  exact card_sdiff_univ_add (A.preimage S w)

private lemma sum_fin3_rat (f : Fin 3 → Q → ℚ) (q : Q) :
    (∑ j : Fin 3, f j) q = f 0 q + f 1 q + f 2 q := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_two]
  simp only [Pi.add_apply]; rfl

private lemma sum_fin4_rat (f : Fin 4 → Q → ℚ) (q : Q) :
    (∑ j : Fin 4, f j) q = f 0 q + f 1 q + f 2 q + f 3 q := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_two]
  simp only [Pi.add_apply]; rfl

private lemma sum_fin6_rat (f : Fin 6 → Q → ℚ) (q : Q) :
    (∑ j : Fin 6, f j) q = f 0 q + f 1 q + f 2 q + f 3 q + f 4 q + f 5 q := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
    Fin.sum_univ_castSucc, Fin.sum_univ_two]
  simp only [Pi.add_apply]; rfl

/-- Orthogonal complement of a subspace `U ≤ (Q → ℚ)` under the standard dot product. -/
def perpSubspace (U : Submodule ℚ (Q → ℚ)) : Submodule ℚ (Q → ℚ) where
  carrier := {f : Q → ℚ | ∀ x ∈ U, ∑ q : Q, x q * f q = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hf hg x hx => by
    have h1 := hf x hx; have h2 := hg x hx
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
  smul_mem' := fun r f hf x hx => by
    have h1 := hf x hx
    calc ∑ q : Q, x q * (r • f) q = r * ∑ q : Q, x q * f q := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => by simp [Pi.smul_apply]; ring
      _ = 0 := by rw [h1, mul_zero]

private lemma indQ_mem_perpSubspace_iff (U : Submodule ℚ (Q → ℚ)) (S : Finset Q) :
    indQ S ∈ perpSubspace U ↔ ∀ x ∈ U, ∑ q ∈ S, x q = 0 := by
  have hdot : ∀ x : Q → ℚ, ∑ q : Q, x q * indQ S q = ∑ q ∈ S, x q := by
    intro x
    have hf : Finset.univ.filter (fun q => q ∈ S) = S := by ext q; simp
    calc ∑ q : Q, x q * indQ S q
        = ∑ q : Q, if q ∈ S then x q else 0 :=
          Finset.sum_congr rfl fun q _ => by by_cases hq : q ∈ S <;> simp [indQ, hq]
      _ = ∑ q ∈ Finset.univ.filter (fun q => q ∈ S), x q := (Finset.sum_filter _ _).symm
      _ = ∑ q ∈ S, x q := by rw [hf]
  constructor
  · intro h x hx; rw [← hdot x]; exact h x hx
  · intro h x hx; rw [hdot x]; exact h x hx

private lemma finrank_perpSubspace_le (U : Submodule ℚ (Q → ℚ)) :
    Module.finrank ℚ (perpSubspace U) + Module.finrank ℚ U ≤ Fintype.card Q := by
  let d := Module.finrank ℚ U
  let b := Module.finBasis ℚ U
  let Φ : (Q → ℚ) →ₗ[ℚ] (Fin d → ℚ) :=
    { toFun := fun f i => ∑ q : Q, (b i : Q → ℚ) q * f q
      map_add' := fun f g => by
        ext i; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r f => by
        ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring }
  have hker : LinearMap.ker Φ = perpSubspace U := by
    ext f
    simp only [LinearMap.mem_ker, perpSubspace, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    constructor
    · intro hf x hx
      have hrepr := b.sum_repr ⟨x, hx⟩
      have hx_eq : x = ∑ i : Fin d, (b.repr ⟨x, hx⟩ i) • (b i : Q → ℚ) := by
        have hval := congrArg (fun u : U => (u : Q → ℚ)) hrepr
        simp only [Submodule.coe_sum, SetLike.val_smul] at hval
        exact hval.symm
      rw [hx_eq]
      calc ∑ q : Q, (∑ i : Fin d, (b.repr ⟨x, hx⟩ i) • (b i : Q → ℚ)) q * f q
          = ∑ q : Q, ∑ i : Fin d, b.repr ⟨x, hx⟩ i * ((b i : Q → ℚ) q * f q) := by
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.sum_apply, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply]; ring
        _ = ∑ i : Fin d, b.repr ⟨x, hx⟩ i * ∑ q : Q, (b i : Q → ℚ) q * f q := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun i _ => by
            have hi := congrFun hf i
            change ∑ q : Q, (b i : Q → ℚ) q * f q = 0 at hi
            rw [hi, mul_zero]
    · intro hf
      ext i
      exact hf (b i : Q → ℚ) (b i).2
  let Ψ : (Fin d → ℚ) →ₗ[ℚ] (Q → ℚ) :=
    { toFun := fun c q => ∑ i : Fin d, c i * (b i : Q → ℚ) q
      map_add' := fun c₁ c₂ => by
        ext q; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        ext q; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have hcomp_inj : Function.Injective (Φ.comp Ψ) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have hsq : ∑ q : Q, (Ψ c q) ^ 2 = 0 := by
      have h0 : ∑ i : Fin d, c i * (Φ (Ψ c) i) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have hi := congrFun hc i
        change Φ (Ψ c) i = 0 at hi
        rw [hi, mul_zero]
      have heq : ∑ i : Fin d, c i * (Φ (Ψ c) i) = ∑ q : Q, (Ψ c q) ^ 2 := by
        calc ∑ i : Fin d, c i * ∑ q : Q, (b i : Q → ℚ) q * Ψ c q
            = ∑ i : Fin d, ∑ q : Q, (c i * (b i : Q → ℚ) q) * Ψ c q := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun q _ => by ring
          _ = ∑ q : Q, ∑ i : Fin d, (c i * (b i : Q → ℚ) q) * Ψ c q := Finset.sum_comm
          _ = ∑ q : Q, (Ψ c q) ^ 2 := by
              refine Finset.sum_congr rfl fun q _ => ?_
              rw [← Finset.sum_mul]; change Ψ c q * Ψ c q = (Ψ c q) ^ 2; ring
      rw [← heq]; exact h0
    have hΨ0 : Ψ c = 0 := by
      ext q
      have hq_le : (Ψ c q) ^ 2 ≤ 0 := by
        have hsum_ge : (Ψ c q) ^ 2 ≤ ∑ p : Q, (Ψ c p) ^ 2 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)]
          have hnn : 0 ≤ ∑ p ∈ Finset.univ.erase q, (Ψ c p) ^ 2 :=
            Finset.sum_nonneg fun p _ => sq_nonneg _
          linarith
        linarith
      exact sq_eq_zero_iff.mp (le_antisymm hq_le (sq_nonneg _))
    have hsum_b : ∑ i : Fin d, c i • b i = 0 := by
      apply Subtype.ext
      ext q
      have hq := congrFun hΨ0 q
      simpa [Ψ, Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply] using hq
    have hli := Fintype.linearIndependent_iff.mp b.linearIndependent c hsum_b
    rw [Submodule.mem_bot]
    exact funext hli
  have hrange_ge : d ≤ Module.finrank ℚ (LinearMap.range Φ) := by
    have hle : LinearMap.range (Φ.comp Ψ) ≤ LinearMap.range Φ := by
      rintro y ⟨c, rfl⟩; exact ⟨Ψ c, rfl⟩
    have h1 := LinearMap.finrank_range_of_inj hcomp_inj
    rw [finrank_fun_rat, Fintype.card_fin] at h1
    have h2 := Submodule.finrank_mono hle
    omega
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hker, finrank_fun_rat] at hrk
  omega

private lemma exists_pos_of_weighted_sum_zero {m : ℕ}
    (c f : Fin m → ℚ) (hc : ∀ j, 0 ≤ c j)
    (hsum : ∑ j : Fin m, c j * f j = 0)
    (j₀ : Fin m) (hneg : c j₀ * f j₀ < 0) :
    ∃ j : Fin m, 0 < f j := by
  by_contra hall
  push_neg at hall
  have hle : ∑ j ∈ Finset.univ.erase j₀, c j * f j ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hc j) (hall j)
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => c j * f j) (Finset.mem_univ j₀)
  linarith

private lemma dubuc_of_distinct_orbit [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (m : ℕ) (hcard : Fintype.card Q = m) (hord : ∀ q : Q, A.eval q (List.replicate m a) = q)
    (q₀ : Q) (hinj : Function.Injective (fun i : Fin m => A.eval q₀ (List.replicate i.1 a))) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  let orb : Finset Q := Finset.univ.image (fun i : Fin m => A.eval q₀ (List.replicate i.1 a))
  have horb_card : orb.card = Fintype.card Q := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hcard]
  have horb_univ : orb = Finset.univ := Finset.eq_univ_of_card orb horb_card
  apply Cerny.OneClusterAnnular.dubuc_circular_bound A hsync a hbij
  intro p r
  have hp : p ∈ orb := horb_univ ▸ Finset.mem_univ p
  have hr : r ∈ orb := horb_univ ▸ Finset.mem_univ r
  rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hr with ⟨j, _, rfl⟩
  refine ⟨m - i.1 + j.1, ?_⟩
  rw [← eval_append_aux, ← replicate_add_append]
  have hadd : i.1 + (m - i.1 + j.1) = m + j.1 := by omega
  rw [hadd, replicate_add_append, eval_append_aux, hord q₀]

private lemma exists_nonzero_of_ne_bot {V : Submodule ℚ (Q → ℚ)} (hV : V ≠ ⊥) :
    ∃ v ∈ V, v ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hV
  ext x
  rw [Submodule.mem_bot]
  exact ⟨fun hx => hall x hx, fun hx => hx ▸ V.zero_mem⟩

private lemma ne_bot_implies_one_le_finrank {V : Submodule ℚ (Q → ℚ)} (hV : V ≠ ⊥) :
    1 ≤ Module.finrank ℚ V := by
  obtain ⟨v, hv, hv0⟩ := exists_nonzero_of_ne_bot hV
  let f : Fin 1 → (Q → ℚ) := fun _ => v
  have hli : LinearIndependent ℚ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [Fin.sum_univ_one] at hc
    have hc0 : c 0 = 0 := (smul_eq_zero.mp hc).resolve_right hv0
    rw [Fin.eq_zero i]; exact hc0
  have hle : Submodule.span ℚ (Set.range f) ≤ V := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hv
  have hfr := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_fin] at hfr
  exact hfr

private lemma const_on_pair_of_perp {U : Submodule ℚ (Q → ℚ)} {S : Finset Q}
    (hSW : indQ S ∈ perpSubspace U) {q r : Q}
    (hmem : (fun p : Q => if p = q then (1 : ℚ) else if p = r then -1 else 0) ∈ U) :
    q ∈ S ↔ r ∈ S := by
  by_cases hqr : q = r
  · subst hqr; rfl
  · let x : Q → ℚ := fun p => if p = q then 1 else if p = r then -1 else 0
    have h0 : ∑ p ∈ S, x p = 0 := (indQ_mem_perpSubspace_iff U S).mp hSW x hmem
    have hsum : ∑ p ∈ S, x p =
        (if q ∈ S then (1 : ℚ) else 0) + (if r ∈ S then (-1 : ℚ) else 0) := by
      have h1 : ∑ p ∈ S, (if p = q then (1 : ℚ) else 0) = if q ∈ S then 1 else 0 := by
        by_cases h : q ∈ S <;> simp [h]
      have h2 : ∑ p ∈ S, (if p = r then (-1 : ℚ) else 0) = if r ∈ S then -1 else 0 := by
        by_cases h : r ∈ S <;> simp [h]
      rw [← h1, ← h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by
        by_cases hpq : p = q
        · subst hpq; simp [x, hqr]
        · by_cases hpr : p = r <;> simp [x, hpq, hpr, hqr, Ne.symm hqr]
    rw [hsum] at h0
    by_cases hqS : q ∈ S <;> by_cases hrS : r ∈ S
    · simp [hqS, hrS]
    · simp only [hqS, hrS, ↓reduceIte] at h0; exfalso; linarith
    · simp only [hqS, hrS, ↓reduceIte] at h0; exfalso; linarith
    · simp [hqS, hrS]

end LinearAndCombinatorialHelpers


section KrylovChainAndExcessOne

open BalancedPermutations KrylovEulerian

variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- Fixed right-Krylov subspace chain `K(t) = span { ρ(b · a^j · u) | b ≠ a, j ≤ J, |u| ≤ t }`,
independent of the target subset `S`. -/
def krylovChain (A : Aut Q α) (a : α) (J t : ℕ) : Submodule ℚ (Q → ℚ) :=
  Submodule.span ℚ
    {x | ∃ (b : α) (j : ℕ) (u : List α),
      b ≠ a ∧ j ≤ J ∧ u.length ≤ t ∧ x = ρ A (b :: List.replicate j a ++ u)}

lemma krylovChain_mono (A : Aut Q α) (a : α) (J : ℕ) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    krylovChain A a J t₁ ≤ krylovChain A a J t₂ := by
  apply Submodule.span_mono
  rintro x ⟨b, j, u, hb, hj, hu, rfl⟩
  exact ⟨b, j, u, hb, hj, le_trans hu h, rfl⟩

lemma krylovChain_le_K0 (A : Aut Q α) (a : α) (J t : ℕ) :
    krylovChain A a J t ≤ K₀ Q := by
  rw [krylovChain, Submodule.span_le]
  rintro x ⟨b, j, u, _, _, _, rfl⟩
  exact ρ_mem_K0 A _

lemma krylovChain_zero_eq (A : Aut Q α) (a : α) (J : ℕ)
    (hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)}) :
    krylovChain A a J 0 = K₀' A a := by
  apply le_antisymm
  · rw [krylovChain, Submodule.span_le]
    rintro x ⟨b, j, u, hb, _, hu, rfl⟩
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hu)
    subst hu0
    rw [List.append_nil]
    exact Submodule.subset_span ⟨b, j, hb, rfl⟩
  · refine le_trans hspan (Submodule.span_mono ?_)
    rintro x ⟨b, j, hb, hj, rfl⟩
    exact ⟨b, j, [], hb, hj, le_rfl, by simp⟩

lemma sum_eq_zero_of_mem_krylovChain (A : Aut Q α) (a : α) (J t : ℕ)
    {x : Q → ℚ} (hx : x ∈ krylovChain A a J t) : ∑ q : Q, x q = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨b, j, u, _, _, _, rfl⟩
    exact sum_ρ_eq_zero A _
  | zero => simp
  | add y z _ _ ihy ihz => simp [Finset.sum_add_distrib, ihy, ihz]
  | smul r y _ ihy =>
    calc ∑ q : Q, (r • y) q = r * ∑ q : Q, y q := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => rfl
      _ = 0 := by rw [ihy, mul_zero]

lemma ones_mem_perpSubspace_krylovChain (A : Aut Q α) (a : α) (J t : ℕ) :
    (fun _ : Q => (1 : ℚ)) ∈ perpSubspace (krylovChain A a J t) := by
  intro x hx
  simpa using sum_eq_zero_of_mem_krylovChain A a J t hx

lemma R_single_mem_krylovChain_succ (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (J : ℕ)
    (hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)})
    (t : ℕ) (σ : α) {x : Q → ℚ} (hx : x ∈ krylovChain A a J t) :
    R A [σ] x ∈ krylovChain A a J (t + 1) := by
  have hρσ : ρ A [σ] ∈ krylovChain A a J (t + 1) := by
    have h0 : ρ A [σ] ∈ krylovChain A a J 0 := by
      rw [krylovChain_zero_eq A a J hspan]
      exact ρ_single_mem_K₀' A hbij σ
    exact krylovChain_mono A a J (Nat.zero_le _) h0
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨b, j, u, hb, hj, hu, rfl⟩
    rw [R_append_ρ]
    apply Submodule.sub_mem _ _ hρσ
    apply Submodule.subset_span
    refine ⟨b, j, u ++ [σ], hb, hj, by simp; omega, ?_⟩
    rw [List.append_assoc]
  | zero => simp
  | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
  | smul r y _ ihy => rw [map_smul]; exact Submodule.smul_mem _ r ihy

private lemma ρ_mem_krylovChain_length_sub_one (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (J : ℕ)
    (hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)})
    (u : List α) :
    ρ A u ∈ krylovChain A a J (u.length - 1) := by
  induction u using List.reverseRecOn with
  | nil => rw [ρ_nil_aux]; exact Submodule.zero_mem _
  | append_singleton v σ ih =>
    have hρσ : ρ A [σ] ∈ krylovChain A a J ((v ++ [σ]).length - 1) := by
      have h0 : ρ A [σ] ∈ krylovChain A a J 0 := by
        rw [krylovChain_zero_eq A a J hspan]
        exact ρ_single_mem_K₀' A hbij σ
      exact krylovChain_mono A a J (Nat.zero_le _) h0
    by_cases hv : v = []
    · subst hv; simpa using hρσ
    · have hv_pos : 1 ≤ v.length := by
        cases v with
        | nil => exact absurd rfl hv
        | cons _ _ => simp
      have hlen : (v ++ [σ]).length - 1 = (v.length - 1) + 1 := by simp; omega
      rw [hlen]
      have hstep : R A [σ] (ρ A v) ∈ krylovChain A a J ((v.length - 1) + 1) :=
        R_single_mem_krylovChain_succ A hbij J hspan (v.length - 1) σ ih
      have hEq : ρ A (v ++ [σ]) = R A [σ] (ρ A v) + ρ A [σ] := by
        rw [R_append_ρ]; abel
      rw [hEq]
      exact Submodule.add_mem _ hstep (by rwa [← hlen])

lemma ρ_mem_krylovChain_of_stable (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (J : ℕ)
    (hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)})
    {r : ℕ} (hstab : krylovChain A a J r = krylovChain A a J (r + 1)) (w : List α) :
    ρ A w ∈ krylovChain A a J r := by
  induction w using List.reverseRecOn with
  | nil => rw [ρ_nil_aux]; exact Submodule.zero_mem _
  | append_singleton v σ ih =>
    have hstep : R A [σ] (ρ A v) ∈ krylovChain A a J r := by
      rw [hstab]
      exact R_single_mem_krylovChain_succ A hbij J hspan r σ ih
    have hρσ : ρ A [σ] ∈ krylovChain A a J r := by
      have h0 : ρ A [σ] ∈ krylovChain A a J 0 := by
        rw [krylovChain_zero_eq A a J hspan]
        exact ρ_single_mem_K₀' A hbij σ
      exact krylovChain_mono A a J (Nat.zero_le _) h0
    have hEq : ρ A (v ++ [σ]) = R A [σ] (ρ A v) + ρ A [σ] := by
      rw [R_append_ρ]; abel
    rw [hEq]
    exact Submodule.add_mem _ hstep hρσ

/-- **Public Fixed-Chain Right-Krylov Detector:** -/
theorem right_krylov_chain_detect (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (J : ℕ)
    (hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)})
    {S : Finset Q} {t : ℕ}
    (hnot : indQ S ∉ perpSubspace (krylovChain A a J t)) :
    ∃ (t' : ℕ) (b : α) (j_star : ℕ) (u : List α),
      t' ≤ t ∧
      (1 ≤ t' → indQ S ∈ perpSubspace (krylovChain A a J (t' - 1))) ∧
      b ≠ a ∧ j_star ≤ J ∧ u.length ≤ t' ∧
      (A.preimage S u).card = S.card ∧
      (A.preimage S (b :: List.replicate j_star a ++ u)).card ≠ S.card := by
  classical
  let P : ℕ → Prop := fun k => indQ S ∉ perpSubspace (krylovChain A a J k)
  let t' := Nat.find (⟨t, hnot⟩ : ∃ k, P k)
  have ht'_spec : P t' := Nat.find_spec (⟨t, hnot⟩ : ∃ k, P k)
  have ht'_le : t' ≤ t := Nat.find_min' (⟨t, hnot⟩ : ∃ k, P k) hnot
  have ht'_prev : 1 ≤ t' → indQ S ∈ perpSubspace (krylovChain A a J (t' - 1)) := by
    intro h1
    by_contra hmem
    exact Nat.find_min (⟨t, hnot⟩ : ∃ k, P k) (by omega : t' - 1 < t') hmem
  have hex_gen : ∃ (b : α) (j_star : ℕ) (u : List α),
      b ≠ a ∧ j_star ≤ J ∧ u.length ≤ t' ∧
      ∑ q ∈ S, ρ A (b :: List.replicate j_star a ++ u) q ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply ht'_spec
    rw [indQ_mem_perpSubspace_iff]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨b, j, u, hb, hj, hu, rfl⟩
      exact hall b j u hb hj hu
    | zero => simp
    | add y z _ _ ihy ihz => simp [Finset.sum_add_distrib, ihy, ihz]
    | smul r y _ ihy =>
      calc ∑ q ∈ S, (r • y) q = r * ∑ q ∈ S, y q := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => rfl
        _ = 0 := by rw [ihy, mul_zero]
  obtain ⟨b, j_star, u, hb, hj, hu, hne0⟩ := hex_gen
  have hu_card : (A.preimage S u).card = S.card := by
    by_cases hu0 : u = []
    · subst hu0; rw [preimage_nil_aux]
    · have hu_pos : 1 ≤ u.length := by
        cases u with
        | nil => exact absurd rfl hu0
        | cons _ _ => simp
      have ht'_pos : 1 ≤ t' := by omega
      have hρu : ρ A u ∈ krylovChain A a J (t' - 1) :=
        krylovChain_mono A a J (by omega) (ρ_mem_krylovChain_length_sub_one A hbij J hspan u)
      have h0 : ∑ q ∈ S, ρ A u q = 0 :=
        (indQ_mem_perpSubspace_iff _ _).mp (ht'_prev ht'_pos) (ρ A u) hρu
      rw [dotInd_ρ] at h0
      exact Nat.cast_injective (sub_eq_zero.mp h0)
  have hne_card : (A.preimage S (b :: List.replicate j_star a ++ u)).card ≠ S.card := by
    intro hEq
    apply hne0
    rw [dotInd_ρ, hEq, sub_self]
  exact ⟨t', b, j_star, u, ht'_le, ht'_prev, hb, hj, hu, hu_card, hne_card⟩

private lemma krylovChain_dichotomy [Nonempty Q] (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (J : ℕ)
    (hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)})
    (hext_any : ∀ S : Finset Q, 1 ≤ S.card → S.card < Fintype.card Q →
      ∃ w : List α, S.card < (A.preimage S w).card)
    (hd0_le : Module.finrank ℚ (K₀' A a) + 3 ≤ Fintype.card Q) :
    (∀ S : Finset Q, 1 ≤ S.card → S.card < Fintype.card Q →
      indQ S ∉ perpSubspace (krylovChain A a J (Fintype.card Q - 2 - Module.finrank ℚ (K₀' A a)))) ∨
    ((∀ t ≤ Fintype.card Q - 2 - Module.finrank ℚ (K₀' A a),
        Module.finrank ℚ (krylovChain A a J t) = Module.finrank ℚ (K₀' A a) + t) ∧
     (∀ S : Finset Q, 1 ≤ S.card → S.card < Fintype.card Q →
        indQ S ∉ perpSubspace (krylovChain A a J (Fintype.card Q - 1 - Module.finrank ℚ (K₀' A a))))) := by
  let n := Fintype.card Q
  let d₀ := Module.finrank ℚ (K₀' A a)
  let m := n - 2 - d₀
  have hK0_fr : Module.finrank ℚ (K₀ Q) = n - 1 := finrank_ker_sumLin
  have hK0_not_perp : ∀ S : Finset Q, 1 ≤ S.card → S.card < n →
      indQ S ∉ perpSubspace (K₀ Q) := by
    intro S hS1 hSlt hmem
    obtain ⟨w, hw⟩ := hext_any S hS1 hSlt
    have h0 := (indQ_mem_perpSubspace_iff _ _).mp hmem (ρ A w) (ρ_mem_K0 A w)
    rw [dotInd_ρ] at h0
    have hEq : (A.preimage S w).card = S.card := Nat.cast_injective (sub_eq_zero.mp h0)
    omega
  have hstab_not_perp : ∀ {r : ℕ}, krylovChain A a J r = krylovChain A a J (r + 1) →
      ∀ S : Finset Q, 1 ≤ S.card → S.card < n → indQ S ∉ perpSubspace (krylovChain A a J r) := by
    intro r hstab S hS1 hSlt hmem
    obtain ⟨w, hw⟩ := hext_any S hS1 hSlt
    have h0 := (indQ_mem_perpSubspace_iff _ _).mp hmem (ρ A w)
      (ρ_mem_krylovChain_of_stable A hbij J hspan hstab w)
    rw [dotInd_ρ] at h0
    have hEq : (A.preimage S w).card = S.card := Nat.cast_injective (sub_eq_zero.mp h0)
    omega
  by_cases hex_stab : ∃ r < m, krylovChain A a J r = krylovChain A a J (r + 1)
  · left
    obtain ⟨r, hrm, hstab⟩ := hex_stab
    intro S hS1 hSlt hmem
    apply hstab_not_perp hstab S hS1 hSlt
    intro x hx
    exact hmem x (krylovChain_mono A a J (le_of_lt hrm) hx)
  · push_neg at hex_stab
    have hstrict : ∀ r < m,
        Module.finrank ℚ (krylovChain A a J r) < Module.finrank ℚ (krylovChain A a J (r + 1)) := by
      intro r hrm
      have hle := Submodule.finrank_mono (krylovChain_mono A a J (Nat.le_succ r))
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exact absurd (Submodule.eq_of_le_of_finrank_eq
          (krylovChain_mono A a J (Nat.le_succ r)) heq) (hex_stab r hrm)
    have hgrow : ∀ t ≤ m, d₀ + t ≤ Module.finrank ℚ (krylovChain A a J t) := by
      intro t
      induction t with
      | zero => intro _; rw [add_zero, krylovChain_zero_eq A a J hspan]
      | succ t iht =>
        intro ht
        have h1 := iht (by omega)
        have h2 := hstrict t (by omega)
        omega
    have hm_le : Module.finrank ℚ (krylovChain A a J m) ≤ n - 1 := by
      have := Submodule.finrank_mono (krylovChain_le_K0 A a J m)
      omega
    have hm_ge : n - 2 ≤ Module.finrank ℚ (krylovChain A a J m) := by
      have := hgrow m le_rfl
      dsimp only [m, d₀, n] at this hd0_le ⊢; omega
    by_cases htop : Module.finrank ℚ (krylovChain A a J m) = n - 1
    · left
      have hEq : krylovChain A a J m = K₀ Q :=
        Submodule.eq_of_le_of_finrank_eq (krylovChain_le_K0 A a J m) (by omega)
      intro S hS1 hSlt
      change indQ S ∉ perpSubspace (krylovChain A a J m)
      rw [hEq]
      exact hK0_not_perp S hS1 hSlt
    · right
      have hm_eq : Module.finrank ℚ (krylovChain A a J m) = n - 2 := by omega
      have hstep_eq : ∀ t ≤ m, Module.finrank ℚ (krylovChain A a J t) = d₀ + t := by
        intro t ht
        have hge := hgrow t ht
        have hgap : ∀ k, t + k ≤ m →
            Module.finrank ℚ (krylovChain A a J t) + k ≤
              Module.finrank ℚ (krylovChain A a J (t + k)) := by
          intro k
          induction k with
          | zero => intro _; simp
          | succ k ihk =>
            intro hk
            have h1 := ihk (by omega)
            have h2 := hstrict (t + k) (by omega)
            have hidx : t + (k + 1) = t + k + 1 := by omega
            rw [hidx]
            omega
        have htop_le := hgap (m - t) (by omega)
        rw [Nat.add_sub_cancel' ht, hm_eq] at htop_le
        dsimp only [m, d₀, n] at htop_le hd0_le ⊢
        omega
      refine ⟨hstep_eq, ?_⟩
      have hm1 : Fintype.card Q - 1 - Module.finrank ℚ (K₀' A a) = m + 1 := by
        dsimp only [m, d₀, n]; omega
      rw [hm1]
      by_cases hstab_m : krylovChain A a J m = krylovChain A a J (m + 1)
      · intro S hS1 hSlt hmem
        apply hstab_not_perp hstab_m S hS1 hSlt
        rwa [hstab_m]
      · have hgt_m : Module.finrank ℚ (krylovChain A a J m) <
            Module.finrank ℚ (krylovChain A a J (m + 1)) := by
          have hle := Submodule.finrank_mono (krylovChain_mono A a J (Nat.le_succ m))
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact hlt
          · exact absurd (Submodule.eq_of_le_of_finrank_eq
              (krylovChain_mono A a J (Nat.le_succ m)) heq) hstab_m
        have hle_m1 : Module.finrank ℚ (krylovChain A a J (m + 1)) ≤ n - 1 := by
          have := Submodule.finrank_mono (krylovChain_le_K0 A a J (m + 1))
          omega
        have hEq_m1 : krylovChain A a J (m + 1) = K₀ Q :=
          Submodule.eq_of_le_of_finrank_eq (krylovChain_le_K0 A a J (m + 1)) (by omega)
        intro S hS1 hSlt
        rw [hEq_m1]
        exact hK0_not_perp S hS1 hSlt

/-- **Master Theorem B with Excess `+1` (Amortized):** -/
theorem master_balanced_version_B_excess_one [Nonempty Q]
    (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (J D : ℕ)
    (hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)})
    (c : Fin (D + 1) → ℚ)
    (hc_nonneg : ∀ j, 0 ≤ c j) (hc0_pos : 0 < c 0) (hc_sum : ∑ j : Fin (D + 1), c j = 1)
    (hann : ∀ x ∈ K₀' A a, ∑ j : Fin (D + 1), c j • R A (List.replicate j.1 a) x = 0)
    (hn6 : 6 ≤ Fintype.card Q)
    (hd0_le : Module.finrank ℚ (K₀' A a) + 3 ≤ Fintype.card Q)
    (hD2 : 2 ≤ D)
    (hexcess : D + J ≤ Module.finrank ℚ (K₀' A a) + 1) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  let n := Fintype.card Q
  let d₀ := Module.finrank ℚ (K₀' A a)
  have hext_any : ∀ S : Finset Q, 1 ≤ S.card → S.card < n →
      ∃ w : List α, S.card < (A.preimage S w).card := by
    intro S hS1 hSlt
    obtain ⟨w, _, hw⟩ := master_balanced_version_B_span A hsync a hbij J D hspan c
      hc_nonneg hc0_pos hc_sum hann hS1 hSlt
    exact ⟨w, hw⟩
  have hext_from_det : ∀ (S : Finset Q) (b : α) (j_star : ℕ) (u : List α),
      b ≠ a → j_star ≤ J →
      (A.preimage S u).card = S.card →
      (A.preimage S (b :: List.replicate j_star a ++ u)).card ≠ S.card →
      (S.card < (A.preimage S (b :: List.replicate j_star a ++ u)).card) ∨
      ((Finset.univ \ S).card < (A.preimage (Finset.univ \ S) (b :: List.replicate j_star a ++ u)).card ∧
       ∃ j : Fin (D + 1),
         S.card < (A.preimage S (b :: List.replicate (j_star + j.1) a ++ u)).card) := by
    intro S b j_star u hb hj hu_eq hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      refine ⟨?_, ?_⟩
      · have h1 := preimage_compl_card_add A S (b :: List.replicate j_star a ++ u)
        have h2 := card_sdiff_univ_add S
        omega
      · have hmem : ρ A (b :: List.replicate j_star a) ∈ K₀' A a :=
          Submodule.subset_span ⟨b, j_star, hb, rfl⟩
        have hann_u : ∑ j : Fin (D + 1),
            c j • R A u (R A (List.replicate j.1 a) (ρ A (b :: List.replicate j_star a))) = 0 := by
          have h0 := congrArg (R A u) (hann _ hmem)
          rw [map_sum, map_zero] at h0
          simpa [map_smul] using h0
        have hsum_zero : ∑ j : Fin (D + 1),
            c j * (((A.preimage S (b :: List.replicate (j_star + j.1) a ++ u)).card : ℚ) -
              (S.card : ℚ)) = 0 := by
          have hS0 : ∑ q ∈ S, (∑ j : Fin (D + 1),
              c j • R A u (R A (List.replicate j.1 a) (ρ A (b :: List.replicate j_star a)))) q = 0 := by
            rw [hann_u]; simp
          rw [← hS0]
          calc ∑ j : Fin (D + 1),
                c j * (((A.preimage S (b :: List.replicate (j_star + j.1) a ++ u)).card : ℚ) -
                  (S.card : ℚ))
              = ∑ j : Fin (D + 1), c j * ∑ q ∈ S,
                  R A u (R A (List.replicate j.1 a) (ρ A (b :: List.replicate j_star a))) q := by
                refine Finset.sum_congr rfl fun j _ => ?_
                congr 1
                rw [ρ_append_replicate_a A hbij, R_append_ρ]
                have hrep : (b :: List.replicate j_star a) ++ List.replicate j.1 a =
                    b :: List.replicate (j_star + j.1) a := by
                  rw [List.cons_append, replicate_add_append]
                rw [hrep]
                have hsub : ∑ q ∈ S, (ρ A (b :: List.replicate (j_star + j.1) a ++ u) - ρ A u) q =
                    (∑ q ∈ S, ρ A (b :: List.replicate (j_star + j.1) a ++ u) q) -
                    (∑ q ∈ S, ρ A u q) := by
                  simp [Finset.sum_sub_distrib]
                rw [hsub, dotInd_ρ, dotInd_ρ, hu_eq, sub_self, sub_zero]
            _ = ∑ j : Fin (D + 1), ∑ q ∈ S,
                  (c j • R A u (R A (List.replicate j.1 a) (ρ A (b :: List.replicate j_star a)))) q := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => rfl
            _ = ∑ q ∈ S, ∑ j : Fin (D + 1),
                  (c j • R A u (R A (List.replicate j.1 a) (ρ A (b :: List.replicate j_star a)))) q :=
                Finset.sum_comm
            _ = ∑ q ∈ S, (∑ j : Fin (D + 1),
                  c j • R A u (R A (List.replicate j.1 a) (ρ A (b :: List.replicate j_star a)))) q := by
                refine Finset.sum_congr rfl fun q _ => by rw [Finset.sum_apply]
        have hneg0 : c 0 * (((A.preimage S (b :: List.replicate (j_star + (0 : Fin (D + 1)).1) a ++ u)).card : ℚ) -
            (S.card : ℚ)) < 0 := by
          have hltq : ((A.preimage S (b :: List.replicate j_star a ++ u)).card : ℚ) < (S.card : ℚ) :=
            Nat.cast_lt.mpr hlt
          simpa using mul_neg_of_pos_of_neg hc0_pos (sub_neg.mpr hltq)
        obtain ⟨j, hjpos⟩ := exists_pos_of_weighted_sum_zero c
          (fun j => ((A.preimage S (b :: List.replicate (j_star + j.1) a ++ u)).card : ℚ) - (S.card : ℚ))
          hc_nonneg hsum_zero 0 hneg0
        exact ⟨j, Nat.cast_lt.mp (sub_pos.mp hjpos)⟩
    · left; exact hgt
  rcases krylovChain_dichotomy A hbij J hspan hext_any hd0_le with hall_fast | ⟨hdims, hall_m1⟩
  · apply cerny_of_n_extensible A hsync
    intro S hS1 hSlt
    obtain ⟨t', b, j_star, u, ht'_le, _, hb, hj, hu_len, hu_eq, hne⟩ :=
      right_krylov_chain_detect A hbij J hspan (hall_fast S hS1 hSlt)
    rcases hext_from_det S b j_star u hb hj hu_eq hne with hgt | ⟨_, j, hjgt⟩
    · exact ⟨b :: List.replicate j_star a ++ u, by dsimp only [n, d₀] at *; simp; omega, hgt⟩
    · have hjD : j.1 ≤ D := Nat.le_of_lt_succ j.2
      exact ⟨b :: List.replicate (j_star + j.1) a ++ u, by dsimp only [n, d₀] at *; simp; omega, hjgt⟩
  · let m := n - 2 - d₀
    let W₂ := perpSubspace (krylovChain A a J m)
    let W₃ := perpSubspace (krylovChain A a J (n - 3 - d₀))
    have hW₂_dim : Module.finrank ℚ W₂ ≤ 2 := by
      have h1 := finrank_perpSubspace_le (krylovChain A a J m)
      have h2 := hdims m le_rfl
      have hfm : Module.finrank ℚ (krylovChain A a J m) = n - 2 := by
        rw [h2]
        dsimp only [m, d₀, n]; omega
      have hle : Module.finrank ℚ W₂ + (n - 2) ≤ n := by
        simpa [W₂, hfm] using h1
      dsimp only [n] at hle hd0_le ⊢
      omega
    have hW₃_dim : Module.finrank ℚ W₃ ≤ 3 := by
      have h1 := finrank_perpSubspace_le (krylovChain A a J (n - 3 - d₀))
      have h2 := hdims (n - 3 - d₀) (by dsimp only [m, d₀, n]; omega)
      have hfm : Module.finrank ℚ (krylovChain A a J (n - 3 - d₀)) = n - 3 := by
        rw [h2]
        dsimp only [m, d₀, n]; omega
      have hle : Module.finrank ℚ W₃ + (n - 3) ≤ n := by
        simpa [W₃, hfm] using h1
      dsimp only [n] at hle hd0_le ⊢
      omega
    let BadPlus : Finset (Finset Q) := Finset.univ.filter (fun S =>
      1 ≤ S.card ∧ S.card < n ∧
      ¬ ∃ w : List α, w.length ≤ n ∧ S.card < (A.preimage S w).card)
    let BadGe : Finset (Finset Q) := Finset.univ.filter (fun S =>
      1 ≤ S.card ∧ S.card < n ∧
      ¬ ∃ w : List α, w.length ≤ n - 1 ∧ S.card < (A.preimage S w).card)
    have hsub : BadPlus ⊆ BadGe := by
      intro S hS
      simp only [BadPlus, BadGe, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact ⟨hS.1, hS.2.1, fun ⟨w, hl, hg⟩ => hS.2.2 ⟨w, by omega, hg⟩⟩
    have hS_info : ∀ S : Finset Q, 1 ≤ S.card → S.card < n →
        (S ∈ BadGe → indQ S ∈ W₃ ∧ Finset.univ \ S ∉ BadGe) ∧
        (S ∈ BadPlus → indQ S ∈ W₂ ∧ Finset.univ \ S ∉ BadPlus) ∧
        (S ∈ BadGe → S ∉ BadPlus → ∃ w : List α, w.length ≤ n ∧ S.card < (A.preimage S w).card) ∧
        (∃ w : List α, w.length ≤ n + 1 ∧ S.card < (A.preimage S w).card) := by
      intro S hS1 hSlt
      obtain ⟨t', b, j_star, u, ht'_le, ht'_prev, hb, hj, hu_len, hu_eq, hne⟩ :=
        right_krylov_chain_detect A hbij J hspan (hall_m1 S hS1 hSlt)
      have hw0_len : (b :: List.replicate j_star a ++ u).length ≤ n - 1 := by
        dsimp only [n, d₀] at *; simp; omega
      rcases hext_from_det S b j_star u hb hj hu_eq hne with hgt | ⟨hcompl_gt, j, hjgt⟩
      · have hnotGe : S ∉ BadGe := by
          simp only [BadGe, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
          intro _ _; exact ⟨b :: List.replicate j_star a ++ u, hw0_len, hgt⟩
        have hnotPlus : S ∉ BadPlus := fun hp => hnotGe (hsub hp)
        refine ⟨fun h => absurd h hnotGe, fun h => absurd h hnotPlus,
          fun h _ => absurd h hnotGe,
          ⟨b :: List.replicate j_star a ++ u, by omega, hgt⟩⟩
      · have hcompl_notGe : Finset.univ \ S ∉ BadGe := by
          simp only [BadGe, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
          intro _ _; exact ⟨b :: List.replicate j_star a ++ u, hw0_len, hcompl_gt⟩
        have hcompl_notPlus : Finset.univ \ S ∉ BadPlus := fun hp => hcompl_notGe (hsub hp)
        have hwj_len : (b :: List.replicate (j_star + j.1) a ++ u).length ≤ d₀ + 2 + t' := by
          have hjD : j.1 ≤ D := Nat.le_of_lt_succ j.2
          dsimp only [d₀]; simp; omega
        refine ⟨?_, ?_, ?_, ⟨b :: List.replicate (j_star + j.1) a ++ u,
          by dsimp only [n, d₀] at *; omega, hjgt⟩⟩
        · intro hGe
          have hno : ¬ ∃ w : List α, w.length ≤ n - 1 ∧ S.card < (A.preimage S w).card :=
            (Finset.mem_filter.mp hGe).2.2.2
          have ht'_ge : n - 2 - d₀ ≤ t' := by
            by_contra hlt
            exact hno ⟨b :: List.replicate (j_star + j.1) a ++ u, by dsimp only [n, d₀] at *; omega, hjgt⟩
          have hmem : indQ S ∈ perpSubspace (krylovChain A a J (t' - 1)) :=
            ht'_prev (by dsimp only [n, d₀] at *; omega)
          refine ⟨?_, hcompl_notGe⟩
          intro x hx
          exact hmem x (krylovChain_mono A a J (by dsimp only [n, d₀] at *; omega) hx)
        · intro hPlus
          have hno : ¬ ∃ w : List α, w.length ≤ n ∧ S.card < (A.preimage S w).card :=
            (Finset.mem_filter.mp hPlus).2.2.2
          have ht'_ge : n - 1 - d₀ ≤ t' := by
            by_contra hlt
            exact hno ⟨b :: List.replicate (j_star + j.1) a ++ u, by dsimp only [n, d₀] at *; omega, hjgt⟩
          have hmem : indQ S ∈ perpSubspace (krylovChain A a J (t' - 1)) :=
            ht'_prev (by dsimp only [n, d₀] at *; omega)
          refine ⟨?_, hcompl_notPlus⟩
          intro x hx
          exact hmem x (krylovChain_mono A a J (by dsimp only [m, d₀, n] at *; omega) hx)
        · intro _ hnotPlus
          simp only [BadPlus, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hnotPlus
          exact hnotPlus hS1 hSlt
    have hplus_card : BadPlus.card ≤ 1 := by
      refine card_noncomp_01_le_one W₂ hW₂_dim (ones_mem_perpSubspace_krylovChain A a J m)
        BadPlus ?_ ?_ ?_
      · intro S hS; have h := (Finset.mem_filter.mp hS).2; exact ⟨h.1, h.2.1⟩
      · intro S hS; have h := (Finset.mem_filter.mp hS).2
        exact ((hS_info S h.1 h.2.1).2.1 hS).1
      · intro S hS; have h := (Finset.mem_filter.mp hS).2
        exact ((hS_info S h.1 h.2.1).2.1 hS).2
    have hge_card_le : BadGe.card ≤ 3 := by
      refine card_noncomp_01_le_three W₃ hW₃_dim
        (ones_mem_perpSubspace_krylovChain A a J (n - 3 - d₀)) BadGe ?_ ?_ ?_
      · intro S hS; have h := (Finset.mem_filter.mp hS).2; exact ⟨h.1, h.2.1⟩
      · intro S hS; have h := (Finset.mem_filter.mp hS).2
        exact ((hS_info S h.1 h.2.1).1 hS).1
      · intro S hS; have h := (Finset.mem_filter.mp hS).2
        exact ((hS_info S h.1 h.2.1).1 hS).2
    refine cerny_of_almost_n_extensible A hsync BadPlus BadGe hsub hplus_card (by omega) ?_ ?_ ?_
    · intro S hS1 hSlt hnotGe
      simp only [BadGe, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hnotGe
      exact hnotGe hS1 hSlt
    · intro S hS1 hSlt hGe hnotPlus
      exact (hS_info S hS1 hSlt).2.2.1 hGe hnotPlus
    · intro S hS1 hSlt _
      exact (hS_info S hS1 hSlt).2.2.2

/-- **Master Theorem A with Excess `+1` (Amortized):** -/
theorem master_balanced_version_A_excess_one [Nonempty Q]
    (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (D : ℕ) (hD : 1 ≤ D) (c : Fin (D + 1) → ℚ)
    (hc_pos : ∀ j, 0 < c j) (hc_sum : ∑ j : Fin (D + 1), c j = 1)
    (hann : ∀ x ∈ K₀' A a, ∑ j : Fin (D + 1), c j • R A (List.replicate j.1 a) x = 0)
    (hn7 : 7 ≤ Fintype.card Q)
    (hd0_le : Module.finrank ℚ (K₀' A a) + 3 ≤ Fintype.card Q)
    (hexcess : D ≤ Module.finrank ℚ (K₀' A a) + 1) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  let n := Fintype.card Q
  let d₀ := Module.finrank ℚ (K₀' A a)
  let J := D - 1
  have hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)} :=
    K₀'_span_of_annihilator A a hbij D hD c (ne_of_gt (hc_pos (Fin.last D))) hann
  have hext_any : ∀ S : Finset Q, 1 ≤ S.card → S.card < n →
      ∃ w : List α, S.card < (A.preimage S w).card := by
    intro S hS1 hSlt
    obtain ⟨w, _, hw⟩ := master_balanced_version_A A hsync a hbij D hD c hc_pos hc_sum hann hS1 hSlt
    exact ⟨w, hw⟩
  have hext_from_det : ∀ (S : Finset Q) (b : α) (j_star : ℕ) (u : List α),
      b ≠ a → j_star ≤ J →
      (A.preimage S u).card = S.card →
      (A.preimage S (b :: List.replicate j_star a ++ u)).card ≠ S.card →
      (S.card < (A.preimage S (b :: List.replicate j_star a ++ u)).card) ∨
      ((Finset.univ \ S).card < (A.preimage (Finset.univ \ S) (b :: List.replicate j_star a ++ u)).card ∧
       ∃ j : Fin (D + 1),
         S.card < (A.preimage S (b :: List.replicate j.1 a ++ u)).card) := by
    intro S b j_star u hb hj hu_eq hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      refine ⟨?_, ?_⟩
      · have h1 := preimage_compl_card_add A S (b :: List.replicate j_star a ++ u)
        have h2 := card_sdiff_univ_add S
        omega
      · have hmem : ρ A [b] ∈ K₀' A a := Submodule.subset_span ⟨b, 0, hb, rfl⟩
        have hann_u : ∑ j : Fin (D + 1),
            c j • R A u (R A (List.replicate j.1 a) (ρ A [b])) = 0 := by
          have h0 := congrArg (R A u) (hann _ hmem)
          rw [map_sum, map_zero] at h0
          simpa [map_smul] using h0
        have hsum_zero : ∑ j : Fin (D + 1),
            c j * (((A.preimage S (b :: List.replicate j.1 a ++ u)).card : ℚ) - (S.card : ℚ)) = 0 := by
          have hS0 : ∑ q ∈ S, (∑ j : Fin (D + 1),
              c j • R A u (R A (List.replicate j.1 a) (ρ A [b]))) q = 0 := by
            rw [hann_u]; simp
          rw [← hS0]
          calc ∑ j : Fin (D + 1),
                c j * (((A.preimage S (b :: List.replicate j.1 a ++ u)).card : ℚ) - (S.card : ℚ))
              = ∑ j : Fin (D + 1), c j * ∑ q ∈ S,
                  R A u (R A (List.replicate j.1 a) (ρ A [b])) q := by
                refine Finset.sum_congr rfl fun j _ => ?_
                congr 1
                rw [ρ_append_replicate_a A hbij, R_append_ρ]
                have hrep : [b] ++ List.replicate j.1 a = b :: List.replicate j.1 a := rfl
                rw [hrep]
                have hsub : ∑ q ∈ S, (ρ A (b :: List.replicate j.1 a ++ u) - ρ A u) q =
                    (∑ q ∈ S, ρ A (b :: List.replicate j.1 a ++ u) q) -
                    (∑ q ∈ S, ρ A u q) := by
                  simp [Finset.sum_sub_distrib]
                rw [hsub, dotInd_ρ, dotInd_ρ, hu_eq, sub_self, sub_zero]
            _ = ∑ j : Fin (D + 1), ∑ q ∈ S,
                  (c j • R A u (R A (List.replicate j.1 a) (ρ A [b]))) q := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => rfl
            _ = ∑ q ∈ S, ∑ j : Fin (D + 1),
                  (c j • R A u (R A (List.replicate j.1 a) (ρ A [b]))) q := Finset.sum_comm
            _ = ∑ q ∈ S, (∑ j : Fin (D + 1),
                  c j • R A u (R A (List.replicate j.1 a) (ρ A [b]))) q := by
                refine Finset.sum_congr rfl fun q _ => by rw [Finset.sum_apply]
        let j0 : Fin (D + 1) := ⟨j_star, by dsimp only [J] at hj; omega⟩
        have hneg0 : c j0 * (((A.preimage S (b :: List.replicate j0.1 a ++ u)).card : ℚ) -
            (S.card : ℚ)) < 0 := by
          have hltq : ((A.preimage S (b :: List.replicate j_star a ++ u)).card : ℚ) < (S.card : ℚ) :=
            Nat.cast_lt.mpr hlt
          exact mul_neg_of_pos_of_neg (hc_pos j0) (sub_neg.mpr hltq)
        obtain ⟨j, hjpos⟩ := exists_pos_of_weighted_sum_zero c
          (fun j => ((A.preimage S (b :: List.replicate j.1 a ++ u)).card : ℚ) - (S.card : ℚ))
          (fun j => le_of_lt (hc_pos j)) hsum_zero j0 hneg0
        exact ⟨j, Nat.cast_lt.mp (sub_pos.mp hjpos)⟩
    · left; exact hgt
  rcases krylovChain_dichotomy A hbij J hspan hext_any hd0_le with hall_fast | ⟨hdims, hall_m1⟩
  · apply cerny_of_n_extensible A hsync
    intro S hS1 hSlt
    obtain ⟨t', b, j_star, u, ht'_le, _, hb, hj, hu_len, hu_eq, hne⟩ :=
      right_krylov_chain_detect A hbij J hspan (hall_fast S hS1 hSlt)
    rcases hext_from_det S b j_star u hb hj hu_eq hne with hgt | ⟨_, j, hjgt⟩
    · exact ⟨b :: List.replicate j_star a ++ u, by dsimp only [J, n, d₀] at *; simp; omega, hgt⟩
    · have hjD : j.1 ≤ D := Nat.le_of_lt_succ j.2
      exact ⟨b :: List.replicate j.1 a ++ u, by dsimp only [n, d₀] at *; simp; omega, hjgt⟩
  · let m := n - 2 - d₀
    let W₂ := perpSubspace (krylovChain A a J m)
    let W₃ := perpSubspace (krylovChain A a J (n - 3 - d₀))
    have hW₂_dim : Module.finrank ℚ W₂ ≤ 2 := by
      have h1 := finrank_perpSubspace_le (krylovChain A a J m)
      have h2 := hdims m le_rfl
      have hfm : Module.finrank ℚ (krylovChain A a J m) = n - 2 := by
        rw [h2]
        dsimp only [m, d₀, n]; omega
      have hle : Module.finrank ℚ W₂ + (n - 2) ≤ n := by
        simpa [W₂, hfm] using h1
      dsimp only [n] at hle hd0_le ⊢
      omega
    have hW₃_dim : Module.finrank ℚ W₃ ≤ 3 := by
      have h1 := finrank_perpSubspace_le (krylovChain A a J (n - 3 - d₀))
      have h2 := hdims (n - 3 - d₀) (by dsimp only [m, d₀, n]; omega)
      have hfm : Module.finrank ℚ (krylovChain A a J (n - 3 - d₀)) = n - 3 := by
        rw [h2]
        dsimp only [m, d₀, n]; omega
      have hle : Module.finrank ℚ W₃ + (n - 3) ≤ n := by
        simpa [W₃, hfm] using h1
      dsimp only [n] at hle hd0_le ⊢
      omega
    let BadPlus : Finset (Finset Q) := Finset.univ.filter (fun S =>
      1 ≤ S.card ∧ S.card < n ∧
      ¬ ∃ w : List α, w.length ≤ n ∧ S.card < (A.preimage S w).card)
    let BadGe : Finset (Finset Q) := Finset.univ.filter (fun S =>
      1 ≤ S.card ∧ S.card < n ∧
      ¬ ∃ w : List α, w.length ≤ n - 1 ∧ S.card < (A.preimage S w).card)
    have hsub : BadPlus ⊆ BadGe := by
      intro S hS
      simp only [BadPlus, BadGe, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact ⟨hS.1, hS.2.1, fun ⟨w, hl, hg⟩ => hS.2.2 ⟨w, by omega, hg⟩⟩
    have hS_info : ∀ S : Finset Q, 1 ≤ S.card → S.card < n →
        (S ∈ BadGe → indQ S ∈ W₃) ∧
        (S ∈ BadGe → Finset.univ \ S ∈ BadGe → indQ S ∈ W₂) ∧
        (S ∈ BadPlus → indQ S ∈ W₂ ∧ Finset.univ \ S ∉ BadPlus) ∧
        (S ∈ BadGe → S ∉ BadPlus → ∃ w : List α, w.length ≤ n ∧ S.card < (A.preimage S w).card) ∧
        (∃ w : List α, w.length ≤ n + 1 ∧ S.card < (A.preimage S w).card) := by
      intro S hS1 hSlt
      obtain ⟨t', b, j_star, u, ht'_le, ht'_prev, hb, hj, hu_len, hu_eq, hne⟩ :=
        right_krylov_chain_detect A hbij J hspan (hall_m1 S hS1 hSlt)
      have hw0_len : (b :: List.replicate j_star a ++ u).length ≤ D + t' := by
        dsimp only [J] at hj; simp; omega
      rcases hext_from_det S b j_star u hb hj hu_eq hne with hgt | ⟨hcompl_gt, j, hjgt⟩
      · have hnotPlus : S ∉ BadPlus := by
          simp only [BadPlus, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
          intro _ _
          exact ⟨b :: List.replicate j_star a ++ u, by dsimp only [n, d₀] at *; omega, hgt⟩
        refine ⟨?_, ?_, fun h => absurd h hnotPlus, ?_,
          ⟨b :: List.replicate j_star a ++ u, by dsimp only [n, d₀] at *; omega, hgt⟩⟩
        · intro hGe
          have hno : ¬ ∃ w : List α, w.length ≤ n - 1 ∧ S.card < (A.preimage S w).card :=
            (Finset.mem_filter.mp hGe).2.2.2
          have ht'_ge : n - 1 - d₀ ≤ t' := by
            by_contra hlt
            exact hno ⟨b :: List.replicate j_star a ++ u, by dsimp only [n, d₀] at *; omega, hgt⟩
          have hmem := ht'_prev (by dsimp only [n, d₀] at *; omega)
          intro x hx
          exact hmem x (krylovChain_mono A a J (by dsimp only [n, d₀] at *; omega) hx)
        · intro hGe _
          have hno : ¬ ∃ w : List α, w.length ≤ n - 1 ∧ S.card < (A.preimage S w).card :=
            (Finset.mem_filter.mp hGe).2.2.2
          have ht'_ge : n - 1 - d₀ ≤ t' := by
            by_contra hlt
            exact hno ⟨b :: List.replicate j_star a ++ u, by dsimp only [n, d₀] at *; omega, hgt⟩
          have hmem := ht'_prev (by dsimp only [n, d₀] at *; omega)
          intro x hx
          exact hmem x (krylovChain_mono A a J (by dsimp only [m, d₀, n] at *; omega) hx)
        · intro _ _
          exact ⟨b :: List.replicate j_star a ++ u, by dsimp only [n, d₀] at *; omega, hgt⟩
      · have hcompl_notPlus : Finset.univ \ S ∉ BadPlus := by
          simp only [BadPlus, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
          intro _ _
          exact ⟨b :: List.replicate j_star a ++ u, by dsimp only [n, d₀] at *; omega, hcompl_gt⟩
        have hwj_len : (b :: List.replicate j.1 a ++ u).length ≤ 1 + D + t' := by
          have hjD : j.1 ≤ D := Nat.le_of_lt_succ j.2
          simp; omega
        refine ⟨?_, ?_, ?_, ?_, ⟨b :: List.replicate j.1 a ++ u,
          by dsimp only [n, d₀] at *; omega, hjgt⟩⟩
        · intro hGe
          have hno : ¬ ∃ w : List α, w.length ≤ n - 1 ∧ S.card < (A.preimage S w).card :=
            (Finset.mem_filter.mp hGe).2.2.2
          have ht'_ge : n - 2 - d₀ ≤ t' := by
            by_contra hlt
            exact hno ⟨b :: List.replicate j.1 a ++ u, by dsimp only [n, d₀] at *; omega, hjgt⟩
          have hmem := ht'_prev (by dsimp only [n, d₀] at *; omega)
          intro x hx
          exact hmem x (krylovChain_mono A a J (by dsimp only [n, d₀] at *; omega) hx)
        · intro _ hcomplGe
          have hno : ¬ ∃ w : List α, w.length ≤ n - 1 ∧
              (Finset.univ \ S).card < (A.preimage (Finset.univ \ S) w).card :=
            (Finset.mem_filter.mp hcomplGe).2.2.2
          have ht'_ge : n - 1 - d₀ ≤ t' := by
            by_contra hlt
            exact hno ⟨b :: List.replicate j_star a ++ u, by dsimp only [n, d₀] at *; omega, hcompl_gt⟩
          have hmem := ht'_prev (by dsimp only [n, d₀] at *; omega)
          intro x hx
          exact hmem x (krylovChain_mono A a J (by dsimp only [m, d₀, n] at *; omega) hx)
        · intro hPlus
          have hno : ¬ ∃ w : List α, w.length ≤ n ∧ S.card < (A.preimage S w).card :=
            (Finset.mem_filter.mp hPlus).2.2.2
          have ht'_ge : n - 1 - d₀ ≤ t' := by
            by_contra hlt
            exact hno ⟨b :: List.replicate j.1 a ++ u, by dsimp only [n, d₀] at *; omega, hjgt⟩
          have hmem := ht'_prev (by dsimp only [n, d₀] at *; omega)
          refine ⟨?_, hcompl_notPlus⟩
          intro x hx
          exact hmem x (krylovChain_mono A a J (by dsimp only [m, d₀, n] at *; omega) hx)
        · intro _ hnotPlus
          simp only [BadPlus, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hnotPlus
          exact hnotPlus hS1 hSlt
    have hplus_card : BadPlus.card ≤ 1 := by
      refine card_noncomp_01_le_one W₂ hW₂_dim (ones_mem_perpSubspace_krylovChain A a J m)
        BadPlus ?_ ?_ ?_
      · intro S hS; have h := (Finset.mem_filter.mp hS).2; exact ⟨h.1, h.2.1⟩
      · intro S hS; have h := (Finset.mem_filter.mp hS).2
        exact ((hS_info S h.1 h.2.1).2.2.1 hS).1
      · intro S hS; have h := (Finset.mem_filter.mp hS).2
        exact ((hS_info S h.1 h.2.1).2.2.1 hS).2
    have hge_card_le : BadGe.card ≤ 4 := by
      by_cases hex_pair : ∃ T₀ ∈ BadGe, Finset.univ \ T₀ ∈ BadGe
      · obtain ⟨T₀, hT0, hT0c⟩ := hex_pair
        have hT0_p : 1 ≤ T₀.card ∧ T₀.card < n := by
          have h := (Finset.mem_filter.mp hT0).2; exact ⟨h.1, h.2.1⟩
        have hT0_W2 : indQ T₀ ∈ W₂ := (hS_info T₀ hT0_p.1 hT0_p.2).2.1 hT0 hT0c
        let BadGe' := BadGe.erase (Finset.univ \ T₀)
        have hcard3 : BadGe'.card ≤ 3 := by
          refine card_noncomp_01_le_three W₃ hW₃_dim
            (ones_mem_perpSubspace_krylovChain A a J (n - 3 - d₀)) BadGe' ?_ ?_ ?_
          · intro S hS
            have hS' := (Finset.mem_erase.mp hS).2
            have h := (Finset.mem_filter.mp hS').2; exact ⟨h.1, h.2.1⟩
          · intro S hS
            have hS' := (Finset.mem_erase.mp hS).2
            have h := (Finset.mem_filter.mp hS').2
            exact (hS_info S h.1 h.2.1).1 hS'
          · intro S hS hSc
            obtain ⟨hSne, hS'⟩ := Finset.mem_erase.mp hS
            obtain ⟨hScne, hSc'⟩ := Finset.mem_erase.mp hSc
            have h := (Finset.mem_filter.mp hS').2
            have hSW2 : indQ S ∈ W₂ := (hS_info S h.1 h.2.1).2.1 hS' hSc'
            rcases eq_or_compl_of_finrank_le_two W₂ hW₂_dim
              (ones_mem_perpSubspace_krylovChain A a J m) hT0_p ⟨h.1, h.2.1⟩ hT0_W2 hSW2 with
              hEq | hEq
            · apply hScne; rw [hEq]
            · exact hSne hEq
        have herase : BadGe'.card + 1 = BadGe.card := by
          rw [Finset.card_erase_of_mem hT0c]
          have hpos : 1 ≤ BadGe.card := Finset.card_pos.mpr ⟨T₀, hT0⟩
          omega
        omega
      · push_neg at hex_pair
        have hcard3 : BadGe.card ≤ 3 := by
          refine card_noncomp_01_le_three W₃ hW₃_dim
            (ones_mem_perpSubspace_krylovChain A a J (n - 3 - d₀)) BadGe ?_ ?_ hex_pair
          · intro S hS; have h := (Finset.mem_filter.mp hS).2; exact ⟨h.1, h.2.1⟩
          · intro S hS; have h := (Finset.mem_filter.mp hS).2
            exact (hS_info S h.1 h.2.1).1 hS
        omega
    refine cerny_of_almost_n_extensible A hsync BadPlus BadGe hsub hplus_card (by omega) ?_ ?_ ?_
    · intro S hS1 hSlt hnotGe
      simp only [BadGe, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hnotGe
      exact hnotGe hS1 hSlt
    · intro S hS1 hSlt hGe hnotPlus
      exact (hS_info S hS1 hSlt).2.2.2.1 hGe hnotPlus
    · intro S hS1 hSlt _
      exact (hS_info S hS1 hSlt).2.2.2.2

end KrylovChainAndExcessOne


section OrderFourBalanced

open BalancedPermutations KrylovEulerian

variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- Cyclotomic component `V₂ = K₀' ∩ ker (R[a] + I)`. -/
def V₂ (A : Aut Q α) (a : α) : Submodule ℚ (Q → ℚ) :=
  K₀' A a ⊓ LinearMap.ker (R A [a] + LinearMap.id)

/-- Cyclotomic component `V₄ = K₀' ∩ ker (R[a²] + I)`. -/
def V₄ (A : Aut Q α) (a : α) : Submodule ℚ (Q → ℚ) :=
  K₀' A a ⊓ LinearMap.ker (R A (List.replicate 2 a) + LinearMap.id)

private lemma mem_V₂_iff (A : Aut Q α) (a : α) (x : Q → ℚ) :
    x ∈ V₂ A a ↔ x ∈ K₀' A a ∧ R A [a] x + x = 0 := by
  simp [V₂, LinearMap.mem_ker]

private lemma mem_V₄_iff (A : Aut Q α) (a : α) (x : Q → ℚ) :
    x ∈ V₄ A a ↔ x ∈ K₀' A a ∧ R A (List.replicate 2 a) x + x = 0 := by
  simp [V₄, LinearMap.mem_ker]

private lemma c4_annihilates (A : Aut Q α) (a : α)
    (hphi4 : ∀ x ∈ K₀' A a, R A (List.replicate 2 a) x + x = 0) :
    ∀ x ∈ K₀' A a,
      ∑ j : Fin 3, (if j.1 = 0 then (1 / 2 : ℚ) else if j.1 = 1 then 0 else 1 / 2) •
        R A (List.replicate j.1 a) x = 0 := by
  intro x hx
  ext q
  rw [sum_fin3_rat]
  have hq := congrFun (hphi4 x hx) q
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hq ⊢
  norm_num [Fin.val_zero, Fin.val_one, Fin.val_two] at hq ⊢
  linarith

private lemma order4_decomp (A : Aut Q α) (a : α)
    (hord : ∀ q : Q, A.eval q (List.replicate 4 a) = q)
    (hbal : IsCycleBalanced A a) :
    V₂ A a ⊔ V₄ A a = K₀' A a ∧ V₂ A a ⊓ V₄ A a = ⊥ := by
  have hbij := hbal.1
  have hT4 : ∀ x : Q → ℚ, R A (List.replicate 4 a) x = x := by
    intro x; ext q
    rw [R_apply_ite]
    simp only [hord]
    rw [Finset.sum_eq_single q]
    · simp
    · intro p _ hp; rw [if_neg hp]
    · intro h; exact absurd (Finset.mem_univ q) h
  have hann4 : ∀ x ∈ K₀' A a,
      x + R A [a] x + R A (List.replicate 2 a) x + R A (List.replicate 3 a) x = 0 := by
    intro x hx
    have h := sum_orbit_annihilates_K₀' A a 4 (by omega) hord hbal x hx
    ext q
    have hq := congrFun h q
    rw [sum_fin4_rat] at hq
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hq ⊢
    change (1 / ((4 : ℕ) : ℚ)) * R A [] x q + (1 / ((4 : ℕ) : ℚ)) * R A [a] x q +
      (1 / ((4 : ℕ) : ℚ)) * R A (List.replicate 2 a) x q +
      (1 / ((4 : ℕ) : ℚ)) * R A (List.replicate 3 a) x q = 0 at hq
    rw [R_nil] at hq
    norm_num at hq
    rw [R_apply_ite A [a] x q, R_apply_ite A (List.replicate 2 a) x q,
      R_apply_ite A (List.replicate 3 a) x q]
    simp only [List.replicate_succ, List.replicate, eval_cons_aux, eval_nil_aux]
    linarith
  constructor
  · apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · intro x hx
      let x₂ : Q → ℚ := (1 / 2 : ℚ) • (x + R A (List.replicate 2 a) x)
      let x₄ : Q → ℚ := (1 / 2 : ℚ) • (x - R A (List.replicate 2 a) x)
      have hx2_K : R A (List.replicate 2 a) x ∈ K₀' A a := by
        rw [← R_a_a]; exact K₀'_R_a_inv A hbij (K₀'_R_a_inv A hbij hx)
      have hx₂_mem : x₂ ∈ V₂ A a := by
        rw [mem_V₂_iff]
        refine ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hx hx2_K), ?_⟩
        dsimp only [x₂]
        rw [map_smul, map_add, R_a_rep, ← smul_add]
        have hsum := hann4 x hx
        have hEq : R A [a] x + R A (List.replicate 3 a) x + (x + R A (List.replicate 2 a) x) =
            x + R A [a] x + R A (List.replicate 2 a) x + R A (List.replicate 3 a) x := by abel
        rw [hEq, hsum, smul_zero]
      have hx₄_mem : x₄ ∈ V₄ A a := by
        rw [mem_V₄_iff]
        refine ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ hx hx2_K), ?_⟩
        dsimp only [x₄]
        rw [map_smul, map_sub, R_rep_rep, show 2 + 2 = 4 from rfl, hT4, ← smul_add]
        have hzero : R A (List.replicate 2 a) x - x + (x - R A (List.replicate 2 a) x) = 0 := by abel
        rw [hzero, smul_zero]
      have hdecomp : x = x₂ + x₄ := by
        ext q; simp only [x₂, x₄, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hdecomp]
      exact Submodule.add_mem_sup hx₂_mem hx₄_mem
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, mem_V₂_iff, mem_V₄_iff] at hx
    have h1 : R A [a] x = -x := eq_neg_of_add_eq_zero_left hx.1.2
    have h2 : R A (List.replicate 2 a) x = x := by
      rw [← R_a_a, h1, map_neg, h1, neg_neg]
    have h3 := hx.2.2
    rw [h2] at h3
    rw [Submodule.mem_bot]
    ext q
    have hq := congrFun h3 q
    simp only [Pi.add_apply, Pi.zero_apply] at hq
    change x q = 0
    linarith

private lemma two_le_finrank_V₄_of_bij (A : Aut Q α) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a)) (hV4 : V₄ A a ≠ ⊥) :
    2 ≤ Module.finrank ℚ (V₄ A a) := by
  obtain ⟨v, hv, hv0⟩ := exists_nonzero_of_ne_bot hV4
  have hv_mem := (mem_V₄_iff A a v).mp hv
  have hT2v : R A (List.replicate 2 a) v = -v := eq_neg_of_add_eq_zero_left hv_mem.2
  have hRv_mem : R A [a] v ∈ V₄ A a := by
    rw [mem_V₄_iff]
    refine ⟨K₀'_R_a_inv A hbij hv_mem.1, ?_⟩
    rw [R_rep_a, ← R_a_rep, hT2v, map_neg]
    abel
  let f : Fin 2 → (Q → ℚ) := fun i => if i.1 = 0 then v else R A [a] v
  have hli : LinearIndependent ℚ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_two] at hc
    change c 0 • v + c 1 • R A [a] v = 0 at hc
    have hT := congrArg (R A [a]) hc
    rw [map_add, map_smul, map_smul, map_zero, R_a_a, hT2v] at hT
    have hcomb : (c 0 ^ 2 + c 1 ^ 2) • v = 0 := by
      ext q
      have h1 := congrFun hc q
      have h2 := congrFun hT q
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h1 h2 ⊢
      have hid : (c 0 ^ 2 + c 1 ^ 2) * v q =
          c 0 * (c 0 * v q + c 1 * R A [a] v q) - c 1 * (c 0 * R A [a] v q + c 1 * (-v q)) := by ring
      rw [hid, h1, h2]; ring
    have hsq : c 0 ^ 2 + c 1 ^ 2 = 0 := (smul_eq_zero.mp hcomb).resolve_right hv0
    have hc0 : c 0 = 0 := by
      have : c 0 ^ 2 ≤ 0 := by linarith [sq_nonneg (c 1)]
      exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _))
    have hc1 : c 1 = 0 := by
      have : c 1 ^ 2 ≤ 0 := by linarith [sq_nonneg (c 0)]
      exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _))
    intro i
    rcases (by omega : i.1 = 0 ∨ i.1 = 1) with h | h
    · rw [show i = 0 from Fin.ext h]; exact hc0
    · rw [show i = 1 from Fin.ext h]; exact hc1
  have hle : Submodule.span ℚ (Set.range f) ≤ V₄ A a := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩
    rcases (by omega : i.1 = 0 ∨ i.1 = 1) with hi | hi
    · rw [show i = 0 from Fin.ext hi]; simpa [f] using hv
    · rw [show i = 1 from Fin.ext hi]; simpa [f] using hRv_mem
  have hfr := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_fin] at hfr
  exact hfr

private lemma cerny_five_of_size_bound [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync)
    (hn5 : Fintype.card Q = 5)
    (hext6 : ∀ S : Finset Q, 1 ≤ S.card → S.card < 5 →
      ∃ w : List α, w.length ≤ 6 ∧ S.card < (A.preimage S w).card)
    (hext4_5 : ∀ S : Finset Q, S.card = 4 →
      ∃ w : List α, w.length ≤ 5 ∧ 4 < (A.preimage S w).card)
    (hext_fast : (∀ S : Finset Q, S.card = 2 →
        ∃ w : List α, w.length ≤ 4 ∧ 2 < (A.preimage S w).card) ∨
      (∀ S : Finset Q, S.card = 3 →
        ∃ w : List α, w.length ≤ 4 ∧ 3 < (A.preimage S w).card)) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  have hpre_app : ∀ (S : Finset Q) (u v : List α),
      A.preimage S (v ++ u) = A.preimage (A.preimage S u) v := by
    intro S u v; ext q; simp [Aut.preimage, eval_append_aux]
  have hfrom4 : ∀ (S : Finset Q), 4 ≤ S.card →
      ∃ w : List α, A.preimage S w = Finset.univ ∧ w.length ≤ 5 := by
    intro S hS4
    have hSle5 : S.card ≤ 5 := by rw [← hn5]; exact Finset.card_le_univ S
    by_cases h5 : S.card = 5
    · refine ⟨[], ?_, by simp⟩
      rw [preimage_nil_aux]; exact Finset.eq_univ_of_card S (by omega)
    · obtain ⟨u, hul, hug⟩ := hext4_5 S (by omega)
      refine ⟨u, Finset.eq_univ_of_card _ (by have := Finset.card_le_univ (A.preimage S u); omega), hul⟩
  have hfrom3_gen : ∀ (k : ℕ) (S : Finset Q), 3 ≤ S.card →
      (∀ T : Finset Q, T.card = 3 → ∃ u : List α, u.length ≤ k ∧ 3 < (A.preimage T u).card) →
      ∃ w : List α, A.preimage S w = Finset.univ ∧ w.length ≤ k + 5 := by
    intro k S hS3 hstep
    by_cases h4 : 4 ≤ S.card
    · obtain ⟨w, hw, hwl⟩ := hfrom4 S h4
      exact ⟨w, hw, by omega⟩
    · obtain ⟨u, hul, hug⟩ := hstep S (by omega)
      obtain ⟨v, hv, hvl⟩ := hfrom4 (A.preimage S u) (by omega)
      exact ⟨v ++ u, by rw [hpre_app, hv], by simp; omega⟩
  obtain ⟨c₀, b₀, hc₀⟩ := A.exists_collision_letter_of_isSync hsync (by omega)
  let S₁ := A.preimage {c₀} [b₀]
  have hfinish : ∀ (w : List α), A.preimage S₁ w = Finset.univ → w.length ≤ 15 →
      ∃ u : List α, A.IsSyncWord u ∧ u.length ≤ (Fintype.card Q - 1) ^ 2 := by
    intro w hw hwl
    have hpre : A.preimage {c₀} (w ++ [b₀]) = Finset.univ := by rw [hpre_app]; exact hw
    obtain ⟨u, hu_sync, hu_len⟩ := Aut.isSyncWord_of_chain A 1
      (fun i => if i.1 = 0 then {c₀} else Finset.univ) (fun _ => w ++ [b₀]) c₀
      (by simp) (by simp) (fun i => by rw [Fin.eq_zero i]; simp [hpre])
    refine ⟨u, hu_sync, ?_⟩
    rw [hu_len, Fin.sum_univ_one, hn5]; simp; omega
  by_cases hS₁3 : 3 ≤ S₁.card
  · obtain ⟨w, hw, hwl⟩ := hfrom3_gen 6 S₁ hS₁3 (fun T hT => by
      obtain ⟨u, hul, hug⟩ := hext6 T (by omega) (by omega); exact ⟨u, hul, by omega⟩)
    exact hfinish w hw (by omega)
  · have hS₁2 : S₁.card = 2 := by
      have hge : 2 ≤ S₁.card := by simpa [S₁] using hc₀
      omega
    rcases hext_fast with hf2 | hf3
    · obtain ⟨u, hul, hug⟩ := hf2 S₁ hS₁2
      obtain ⟨v, hv, hvl⟩ := hfrom3_gen 6 (A.preimage S₁ u) (by omega) (fun T hT => by
        obtain ⟨w', hl, hg⟩ := hext6 T (by omega) (by omega); exact ⟨w', hl, by omega⟩)
      exact hfinish (v ++ u) (by rw [hpre_app, hv]) (by simp; omega)
    · obtain ⟨u, hul, hug⟩ := hext6 S₁ (by omega) (by omega)
      obtain ⟨v, hv, hvl⟩ := hfrom3_gen 4 (A.preimage S₁ u) (by omega) hf3
      exact hfinish (v ++ u) (by rw [hpre_app, hv]) (by simp; omega)

/-- Symmetric helper for the `n = 5, d₀ = 2, K₀' = V₄` case once `indQ B ∈ perpSubspace (K(1))`. -/
private lemma order_four_n5_atom_step [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (hn5 : Fintype.card Q = 5)
    (q₀ : Q) (B C : Finset Q)
    (hstep_q0 : A.step q₀ a = q₀)
    (hB_card : B.card = 2) (hC_card : C.card = 2)
    (hAB : q₀ ∉ B) (hAC : q₀ ∉ C) (hBC : Disjoint B C)
    (hcov : ∀ q : Q, q = q₀ ∨ q ∈ B ∨ q ∈ C)
    (ha_B : ∀ q : Q, A.step q a ∈ B ↔ q ∈ C)
    (ha_C : ∀ q : Q, A.step q a ∈ C ↔ q ∈ B)
    (hK0_atoms : ∀ x : Q → ℚ, x ∈ K₀' A a ↔
      x q₀ = 0 ∧ (∑ q ∈ B, x q = 0) ∧ (∑ q ∈ C, x q = 0))
    (hdimK1 : Module.finrank ℚ (krylovChain A a 1 1) = 3)
    (hd0 : Module.finrank ℚ (K₀' A a) = 2)
    (hB_K1 : indQ B ∈ perpSubspace (krylovChain A a 1 1))
    (hnot_K0_fast : ∀ S : Finset Q, 1 ≤ S.card → S.card < 5 →
      indQ S ∉ perpSubspace (K₀' A a) →
      ∃ w : List α, w.length ≤ 4 ∧ S.card < (A.preimage S w).card)
    (hext6 : ∀ S : Finset Q, 1 ≤ S.card → S.card < 5 →
      ∃ w : List α, w.length ≤ 6 ∧ S.card < (A.preimage S w).card)
    (hext4_5 : ∀ S : Finset Q, S.card = 4 →
      ∃ w : List α, w.length ≤ 5 ∧ 4 < (A.preimage S w).card) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  have hex_gen : ∃ (b : α) (j : ℕ) (u : List α),
      b ≠ a ∧ j ≤ 1 ∧ u.length ≤ 1 ∧ ρ A (b :: List.replicate j a ++ u) ∉ K₀' A a := by
    by_contra hall; push_neg at hall
    have hle : krylovChain A a 1 1 ≤ K₀' A a := by
      rw [krylovChain, Submodule.span_le]
      rintro x ⟨b, j, u, hb, hj, hu, rfl⟩
      exact hall b j u hb hj hu
    have hfr := Submodule.finrank_mono hle
    omega
  obtain ⟨b, j, u, hb, hj, hu, hy_notK0⟩ := hex_gen
  let w := b :: List.replicate j a ++ u
  let y := ρ A w
  have hw_len : w.length ≤ 3 := by simp [w]; omega
  have hy_K1 : y ∈ krylovChain A a 1 1 :=
    Submodule.subset_span ⟨b, j, u, hb, hj, hu, rfl⟩
  have hyB : ∑ q ∈ B, y q = 0 := (indQ_mem_perpSubspace_iff _ _).mp hB_K1 y hy_K1
  have hdisj_q0B : Disjoint ({q₀} : Finset Q) B := Finset.disjoint_singleton_left.mpr hAB
  have hdisj_q0C : Disjoint ({q₀} : Finset Q) C := Finset.disjoint_singleton_left.mpr hAC
  have hsum_part : ∀ f : Q → ℚ, ∑ q : Q, f q = f q₀ + (∑ q ∈ B, f q) + (∑ q ∈ C, f q) := by
    intro f
    have hdisj2 : Disjoint ({q₀} ∪ B) C := Finset.disjoint_union_left.mpr ⟨hdisj_q0C, hBC⟩
    have hunion : ({q₀} ∪ B) ∪ C = Finset.univ := by
      ext q; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_univ, iff_true]
      rcases hcov q with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    rw [← hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj_q0B, Finset.sum_singleton]
  have hy_tot : y q₀ + (∑ q ∈ B, y q) + (∑ q ∈ C, y q) = 0 := by
    rw [← hsum_part y]; exact sum_ρ_eq_zero A w
  have hyC : ∑ q ∈ C, y q = - y q₀ := by linarith
  have hy0_ne : y q₀ ≠ 0 := by
    intro h0
    apply hy_notK0
    rw [hK0_atoms]
    exact ⟨h0, hyB, by linarith⟩
  have hRy_eq : R A [a] y = ρ A (w ++ [a]) := by
    simpa [y] using (ρ_append_replicate_a A hbij w 1)
  have hRy_q0 : R A [a] y q₀ = y q₀ := by
    have := R_bij_eval A hbij 1 y q₀
    rw [eval_rep1, hstep_q0] at this
    exact this
  have hRy_sum : ∀ S T : Finset Q, (∀ q : Q, A.step q a ∈ S ↔ q ∈ T) →
      ∑ q ∈ S, R A [a] y q = ∑ p ∈ T, y p := by
    intro S T hST
    calc ∑ q ∈ S, R A [a] y q
        = ∑ q ∈ S, ∑ p : Q, (if A.step p a = q then y p else 0) := by
          simp [R_apply_ite, eval_cons_aux, eval_nil_aux]
          rfl
      _ = ∑ p : Q, ∑ q ∈ S, (if A.step p a = q then y p else 0) := Finset.sum_comm
      _ = ∑ p : Q, (if A.step p a ∈ S then y p else 0) := by
          refine Finset.sum_congr rfl fun p _ => by
            by_cases hp : A.step p a ∈ S
            · rw [if_pos hp, Finset.sum_eq_single (A.step p a)]
              · simp
              · intro q _ hq; rw [if_neg (Ne.symm hq)]
              · intro h; exact absurd hp h
            · rw [if_neg hp]
              exact Finset.sum_eq_zero fun q hq => by
                have hne : A.step p a ≠ q := fun heq => hp (heq.symm ▸ hq)
                simp [hne]
      _ = ∑ p : Q, (if p ∈ T then y p else 0) := by
          refine Finset.sum_congr rfl fun p _ => by
            by_cases hp : p ∈ T
            · have hs : A.step p a ∈ S := (hST p).2 hp
              simp [hp, hs]
            · have hs : A.step p a ∉ S := fun h => hp ((hST p).1 h)
              simp [hp, hs]
      _ = ∑ p ∈ T, y p := by
          rw [← Finset.sum_filter]
          have hf : Finset.univ.filter (fun p => p ∈ T) = T := by ext p; simp
          rw [hf]
  have hRyB : ∑ q ∈ B, R A [a] y q = - y q₀ := by rw [hRy_sum B C ha_B, hyC]
  have hRyC : ∑ q ∈ C, R A [a] y q = 0 := by rw [hRy_sum C B ha_C, hyB]
  have hS_atoms : ∀ S : Finset Q, indQ S ∈ perpSubspace (K₀' A a) →
      (∀ q ∈ B, ∀ r ∈ B, (q ∈ S ↔ r ∈ S)) ∧ (∀ q ∈ C, ∀ r ∈ C, (q ∈ S ↔ r ∈ S)) := by
    intro S hSW
    have hK0_swap : ∀ x : Q → ℚ, x ∈ K₀' A a ↔
        x q₀ = 0 ∧ (∑ p ∈ C, x p = 0) ∧ (∑ p ∈ B, x p = 0) := fun x => by
      rw [hK0_atoms]; exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩⟩
    constructor
    · intro q hq r hr
      by_cases hqr : q = r
      · subst hqr; rfl
      · exact const_on_pair_of_perp hSW (by
          rw [hK0_atoms]
          have hq0 : q₀ ≠ q := fun h => hAB (by rwa [← h] at hq)
          have hr0 : q₀ ≠ r := fun h => hAB (by rwa [← h] at hr)
          refine ⟨by simp [hq0, hr0], ?_, ?_⟩
          · have h1 : ∑ p ∈ B, (if p = q then (1 : ℚ) else 0) = 1 := by simp [hq]
            have h2 : ∑ p ∈ B, (if p = r then (-1 : ℚ) else 0) = -1 := by simp [hr]
            have hsum : ∑ p ∈ B, (if p = q then (1 : ℚ) else if p = r then -1 else 0) =
                (∑ p ∈ B, if p = q then (1 : ℚ) else 0) +
                (∑ p ∈ B, if p = r then (-1 : ℚ) else 0) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun p _ => by
                by_cases hpq : p = q
                · subst hpq; simp [hqr]
                · by_cases hpr : p = r <;> simp [hpq, hpr, hqr, Ne.symm hqr]
            rw [hsum, h1, h2]; ring
          · refine Finset.sum_eq_zero fun p hp => ?_
            have hpq : p ≠ q := fun h => Finset.disjoint_left.mp hBC (by rwa [← h] at hq) hp
            have hpr : p ≠ r := fun h => Finset.disjoint_left.mp hBC (by rwa [← h] at hr) hp
            simp [hpq, hpr])
    · intro q hq r hr
      by_cases hqr : q = r
      · subst hqr; rfl
      · exact const_on_pair_of_perp hSW (by
          rw [hK0_swap]
          have hq0 : q₀ ≠ q := fun h => hAC (by rwa [← h] at hq)
          have hr0 : q₀ ≠ r := fun h => hAC (by rwa [← h] at hr)
          refine ⟨by simp [hq0, hr0], ?_, ?_⟩
          · have h1 : ∑ p ∈ C, (if p = q then (1 : ℚ) else 0) = 1 := by simp [hq]
            have h2 : ∑ p ∈ C, (if p = r then (-1 : ℚ) else 0) = -1 := by simp [hr]
            have hsum : ∑ p ∈ C, (if p = q then (1 : ℚ) else if p = r then -1 else 0) =
                (∑ p ∈ C, if p = q then (1 : ℚ) else 0) +
                (∑ p ∈ C, if p = r then (-1 : ℚ) else 0) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun p _ => by
                by_cases hpq : p = q
                · subst hpq; simp [hqr]
                · by_cases hpr : p = r <;> simp [hpq, hpr, hqr, Ne.symm hqr]
            rw [hsum, h1, h2]; ring
          · refine Finset.sum_eq_zero fun p hp => ?_
            have hpq : p ≠ q := fun h => Finset.disjoint_left.mp hBC.symm (by rwa [← h] at hq) hp
            have hpr : p ≠ r := fun h => Finset.disjoint_left.mp hBC.symm (by rwa [← h] at hr) hp
            simp [hpq, hpr])
  apply cerny_five_of_size_bound A hsync hn5 hext6 hext4_5
  rcases lt_or_gt_of_ne hy0_ne with hneg | hpos
  · left
    intro S hS2
    by_cases hSW : indQ S ∈ perpSubspace (K₀' A a)
    · have hat := hS_atoms S hSW
      obtain ⟨qB, hqB⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
      obtain ⟨qC, hqC⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
      by_cases hB_in : qB ∈ S
      · have hBsub : B ⊆ S := fun r hr => (hat.1 qB hqB r hr).mp hB_in
        have hSB : S = B := (Finset.eq_of_subset_of_card_le hBsub (by omega)).symm
        rw [hSB]
        refine ⟨w ++ [a], by simp [w]; omega, ?_⟩
        have hgt : 0 < ((A.preimage B (w ++ [a])).card : ℚ) - (B.card : ℚ) := by
          rw [← dotInd_ρ, ← hRy_eq, hRyB]; linarith
        have hgt' : (B.card : ℚ) < (A.preimage B (w ++ [a])).card := sub_pos.mp hgt
        have hgtNat : B.card < (A.preimage B (w ++ [a])).card := Nat.cast_lt.mp hgt'
        simpa [hB_card] using hgtNat
      · by_cases hC_in : qC ∈ S
        · have hCsub : C ⊆ S := fun r hr => (hat.2 qC hqC r hr).mp hC_in
          have hSC : S = C := (Finset.eq_of_subset_of_card_le hCsub (by omega)).symm
          rw [hSC]
          refine ⟨w, by omega, ?_⟩
          have hgt : 0 < ((A.preimage C w).card : ℚ) - (C.card : ℚ) := by
            rw [← dotInd_ρ]; change 0 < ∑ q ∈ C, y q; rw [hyC]; linarith
          have hgt' : (C.card : ℚ) < (A.preimage C w).card := sub_pos.mp hgt
          have hgtNat : C.card < (A.preimage C w).card := Nat.cast_lt.mp hgt'
          simpa [hC_card] using hgtNat
        · exfalso
          have hsub : S ⊆ {q₀} := by
            intro q hqS; rw [Finset.mem_singleton]
            rcases hcov q with h | h | h
            · exact h
            · exact absurd ((hat.1 q h qB hqB).mp hqS) hB_in
            · exact absurd ((hat.2 q h qC hqC).mp hqS) hC_in
          have := Finset.card_le_card hsub; simp at this; omega
    · simpa [hS2] using hnot_K0_fast S (by omega) (by omega) hSW
  · right
    intro S hS3
    by_cases hSW : indQ S ∈ perpSubspace (K₀' A a)
    · have hat := hS_atoms S hSW
      obtain ⟨qB, hqB⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
      obtain ⟨qC, hqC⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
      by_cases hq0S : q₀ ∈ S
      · by_cases hB_in : qB ∈ S
        · have hsub : ({q₀} ∪ B) ⊆ S := by
            intro r hr
            rcases Finset.mem_union.mp hr with h | h
            · rw [Finset.mem_singleton.mp h]; exact hq0S
            · exact (hat.1 qB hqB r h).mp hB_in
          have hcardAB : ({q₀} ∪ B).card = 3 := by
            rw [Finset.card_union_of_disjoint hdisj_q0B, Finset.card_singleton, hB_card]
          have hEq : S = {q₀} ∪ B := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
          rw [hEq]
          refine ⟨w, by omega, ?_⟩
          have hgt : 0 < ((A.preimage ({q₀} ∪ B) w).card : ℚ) - (({q₀} ∪ B).card : ℚ) := by
            rw [← dotInd_ρ]
            change 0 < ∑ q ∈ {q₀} ∪ B, y q
            rw [Finset.sum_union hdisj_q0B, Finset.sum_singleton, hyB, add_zero]
            exact hpos
          have hgt' : (({q₀} ∪ B).card : ℚ) < (A.preimage ({q₀} ∪ B) w).card := sub_pos.mp hgt
          have hgtNat : ({q₀} ∪ B).card < (A.preimage ({q₀} ∪ B) w).card := Nat.cast_lt.mp hgt'
          rw [hcardAB] at hgtNat
          exact hgtNat
        · by_cases hC_in : qC ∈ S
          · have hsub : ({q₀} ∪ C) ⊆ S := by
              intro r hr
              rcases Finset.mem_union.mp hr with h | h
              · rw [Finset.mem_singleton.mp h]; exact hq0S
              · exact (hat.2 qC hqC r h).mp hC_in
            have hcardAC : ({q₀} ∪ C).card = 3 := by
              rw [Finset.card_union_of_disjoint hdisj_q0C, Finset.card_singleton, hC_card]
            have hEq : S = {q₀} ∪ C := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
            rw [hEq]
            refine ⟨w ++ [a], by simp [w]; omega, ?_⟩
            have hgt : 0 < ((A.preimage ({q₀} ∪ C) (w ++ [a])).card : ℚ) - (({q₀} ∪ C).card : ℚ) := by
              rw [← dotInd_ρ, ← hRy_eq, Finset.sum_union hdisj_q0C, Finset.sum_singleton,
                hRy_q0, hRyC, add_zero]
              exact hpos
            have hgt' : (({q₀} ∪ C).card : ℚ) < (A.preimage ({q₀} ∪ C) (w ++ [a])).card := sub_pos.mp hgt
            have hgtNat : ({q₀} ∪ C).card < (A.preimage ({q₀} ∪ C) (w ++ [a])).card := Nat.cast_lt.mp hgt'
            rw [hcardAC] at hgtNat
            exact hgtNat
          · exfalso
            have hsub : S ⊆ {q₀} := by
              intro q hqS; rw [Finset.mem_singleton]
              rcases hcov q with h | h | h
              · exact h
              · exact absurd ((hat.1 q h qB hqB).mp hqS) hB_in
              · exact absurd ((hat.2 q h qC hqC).mp hqS) hC_in
            have := Finset.card_le_card hsub; simp at this; omega
      · exfalso
        have hsub : S ⊆ B ∪ C := by
          intro q hqS
          rcases hcov q with h | h | h
          · exact absurd (h ▸ hqS) hq0S
          · exact Finset.mem_union_left C h
          · exact Finset.mem_union_right B h
        by_cases hB_in : qB ∈ S
        · by_cases hC_in : qC ∈ S
          · have hBCsub : B ∪ C ⊆ S := by
              intro r hr
              rcases Finset.mem_union.mp hr with h | h
              · exact (hat.1 qB hqB r h).mp hB_in
              · exact (hat.2 qC hqC r h).mp hC_in
            have hcardBC : (B ∪ C).card = 4 := by
              rw [Finset.card_union_of_disjoint hBC, hB_card, hC_card]
            have := Finset.card_le_card hBCsub; omega
          · have hsubB : S ⊆ B := by
              intro q hqS
              rcases Finset.mem_union.mp (hsub hqS) with h | h
              · exact h
              · exact absurd ((hat.2 q h qC hqC).mp hqS) hC_in
            have := Finset.card_le_card hsubB; omega
        · by_cases hC_in : qC ∈ S
          · have hsubC : S ⊆ C := by
              intro q hqS
              rcases Finset.mem_union.mp (hsub hqS) with h | h
              · exact absurd ((hat.1 q h qB hqB).mp hqS) hB_in
              · exact h
            have := Finset.card_le_card hsubC; omega
          · have hsub0 : S = ∅ := by
              ext q; simp only [Finset.notMem_empty, iff_false]
              intro hqS
              rcases Finset.mem_union.mp (hsub hqS) with h | h
              · exact hB_in ((hat.1 q h qB hqB).mp hqS)
              · exact hC_in ((hat.2 q h qC hqC).mp hqS)
            rw [hsub0] at hS3; simp at hS3
    · simpa [hS3] using hnot_K0_fast S (by omega) (by omega) hSW

/-- Complete handling of the `n = 5, d₀ = 2, K₀' = V₄` boundary case of Order 4. -/
private lemma order_four_n5_phi4_dim2 [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hord : ∀ q : Q, A.eval q (List.replicate 4 a) = q)
    (hbal : IsCycleBalanced A a)
    (hn5 : Fintype.card Q = 5)
    (hphi4 : ∀ x ∈ K₀' A a, R A (List.replicate 2 a) x + x = 0)
    (hd0 : Module.finrank ℚ (K₀' A a) = 2) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  have hbij := hbal.1
  let c4 : Fin 3 → ℚ := fun j => if j.1 = 0 then 1 / 2 else if j.1 = 1 then 0 else 1 / 2
  have hc4_nonneg : ∀ j : Fin 3, 0 ≤ c4 j := by
    intro j
    rcases (by omega : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2) with h | h | h
    · rw [show j = 0 from Fin.ext h]; norm_num [c4]
    · rw [show j = 1 from Fin.ext h]; norm_num [c4]
    · rw [show j = 2 from Fin.ext h]; norm_num [c4]
  have hc4_0 : 0 < c4 0 := by simp [c4]
  have hc4_sum : ∑ j : Fin 3, c4 j = 1 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_two]; simp [c4]; norm_num
  have hc4_top : c4 (Fin.last 2) ≠ 0 := by simp [c4]
  have hann_c4 : ∀ x ∈ K₀' A a, ∑ j : Fin 3, c4 j • R A (List.replicate j.1 a) x = 0 :=
    c4_annihilates A a hphi4
  have hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ 1 ∧ x = ρ A (b :: List.replicate j a)} := by
    simpa using K₀'_span_of_annihilator A a hbij 2 (by omega) c4 hc4_top hann_c4
  have hext6 : ∀ S : Finset Q, 1 ≤ S.card → S.card < 5 →
      ∃ w : List α, w.length ≤ 6 ∧ S.card < (A.preimage S w).card := by
    intro S hS1 hSlt
    obtain ⟨w, hl, hg⟩ := master_balanced_version_B_span A hsync a hbij 1 2 hspan c4
      hc4_nonneg hc4_0 hc4_sum hann_c4 hS1 (by omega)
    exact ⟨w, by omega, hg⟩
  have hphi4_ext_of_not_perp : ∀ (t : ℕ) (S : Finset Q),
      indQ S ∉ perpSubspace (krylovChain A a 1 t) →
      ∃ w : List α, w.length ≤ 4 + t ∧ S.card < (A.preimage S w).card := by
    intro t S hnot
    obtain ⟨t', b, j_star, u, ht'_le, _, hb, hj, hu_len, hu_eq, hne⟩ :=
      right_krylov_chain_detect A hbij 1 hspan hnot
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : ρ A (b :: List.replicate j_star a) ∈ K₀' A a :=
        Submodule.subset_span ⟨b, j_star, hb, rfl⟩
      have h0 := congrArg (R A u) (hphi4 _ hmem)
      rw [map_add, map_zero, ρ_append_replicate_a A hbij, R_append_ρ, R_append_ρ] at h0
      have hrep : (b :: List.replicate j_star a) ++ List.replicate 2 a =
          b :: List.replicate (j_star + 2) a := by
        rw [List.cons_append, replicate_add_append]
      rw [hrep] at h0
      have hS0 : ∑ q ∈ S, ((ρ A (b :: List.replicate (j_star + 2) a ++ u) - ρ A u) +
          (ρ A (b :: List.replicate j_star a ++ u) - ρ A u)) q = 0 := by
        rw [h0]; simp
      have hS_calc :
          (((A.preimage S (b :: List.replicate (j_star + 2) a ++ u)).card : ℚ) - (S.card : ℚ)) +
          (((A.preimage S (b :: List.replicate j_star a ++ u)).card : ℚ) - (S.card : ℚ)) = 0 := by
        rw [← hS0]
        simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          dotInd_ρ, hu_eq, sub_self, sub_zero]
      have hltq : ((A.preimage S (b :: List.replicate j_star a ++ u)).card : ℚ) < (S.card : ℚ) :=
        Nat.cast_lt.mpr hlt
      have hgtq : (S.card : ℚ) < ((A.preimage S (b :: List.replicate (j_star + 2) a ++ u)).card : ℚ) := by
        linarith
      exact ⟨b :: List.replicate (j_star + 2) a ++ u, by simp; omega, Nat.cast_lt.mp hgtq⟩
    · exact ⟨b :: List.replicate j_star a ++ u, by simp; omega, hgt⟩
  have hK0_ne : K₀' A a ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hd0; omega
  obtain ⟨v, hvK, hv0⟩ := exists_nonzero_of_ne_bot hK0_ne
  have hex_q1 : ∃ q₁ : Q, v q₁ ≠ 0 := by
    by_contra hall; push_neg at hall; exact hv0 (funext hall)
  obtain ⟨q₁, hq1_ne⟩ := hex_q1
  let f : Q → Q := fun q => A.step q a
  let q₂ := f q₁
  let q₃ := f q₂
  let q₄ := f q₃
  have hf_q4 : f q₄ = q₁ := by
    have h4 := hord q₁; rw [eval_rep4] at h4; exact h4
  have h13 : q₁ ≠ q₃ := by
    intro hEq
    have hev2 : A.eval q₁ (List.replicate 2 a) = q₁ := by rw [eval_rep2]; exact hEq.symm
    have hR := R_bij_eval A hbij 2 v q₁
    rw [hev2] at hR
    have h0 := congrFun (hphi4 v hvK) q₁
    simp only [Pi.add_apply, Pi.zero_apply, hR] at h0
    exact hq1_ne (by linarith)
  have h24 : q₂ ≠ q₄ := fun h => h13 (hbij.1 h)
  have h12 : q₁ ≠ q₂ := by
    intro h
    apply h13
    have hfix : q₁ = f q₁ := by simpa [q₂] using h
    change q₁ = f (f q₁)
    exact hfix.trans (congrArg f hfix)
  have h23 : q₂ ≠ q₃ := fun h => h12 (hbij.1 h)
  have h34 : q₃ ≠ q₄ := fun h => h23 (hbij.1 h)
  have h41 : q₄ ≠ q₁ := by
    intro h
    apply h12
    have hfix : f q₄ = f q₁ := congrArg f h
    rw [hf_q4] at hfix
    exact hfix
  let C4 : Finset Q := {q₁, q₂, q₃, q₄}
  have hC4_card : C4.card = 4 := by
    dsimp only [C4]
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h41.symm]),
        Finset.card_insert_of_notMem (by simp [h23, h24]),
        Finset.card_insert_of_notMem (by simp [h34]),
        Finset.card_singleton]
  have hex_q0 : ∃ q₀ : Q, q₀ ∉ C4 := by
    by_contra hall; push_neg at hall
    have huniv : C4 = Finset.univ := by ext q; simp [hall q]
    rw [huniv, Finset.card_univ, hn5] at hC4_card; omega
  obtain ⟨q₀, hq0_notC4⟩ := hex_q0
  have h01 : q₀ ≠ q₁ := fun h => hq0_notC4 (by simp [C4, h])
  have h02 : q₀ ≠ q₂ := fun h => hq0_notC4 (by simp [C4, h])
  have h03 : q₀ ≠ q₃ := fun h => hq0_notC4 (by simp [C4, h])
  have h04 : q₀ ≠ q₄ := fun h => hq0_notC4 (by simp [C4, h])
  have hcov_all : ∀ q : Q, q = q₀ ∨ q = q₁ ∨ q = q₂ ∨ q = q₃ ∨ q = q₄ := by
    have huniv : insert q₀ C4 = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Finset.card_insert_of_notMem hq0_notC4, hC4_card, hn5])
    intro q
    have hq : q ∈ insert q₀ C4 := huniv ▸ Finset.mem_univ q
    simpa [C4] using hq
  have hstep_q0 : A.step q₀ a = q₀ := by
    rcases hcov_all (f q₀) with h | h | h | h | h
    · exact h
    · exact absurd (hbij.1 (h.trans hf_q4.symm)) h04
    · exact absurd (hbij.1 h) h01
    · exact absurd (hbij.1 h) h02
    · exact absurd (hbij.1 h) h03
  let B : Finset Q := {q₁, q₃}
  let C : Finset Q := {q₂, q₄}
  have hB_card : B.card = 2 := Finset.card_pair h13
  have hC_card : C.card = 2 := Finset.card_pair h24
  have hAB : q₀ ∉ B := by simp [B, h01, h03]
  have hAC : q₀ ∉ C := by simp [C, h02, h04]
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]; intro q hqB hqC
    simp only [B, C, Finset.mem_insert, Finset.mem_singleton] at hqB hqC
    rcases hqB with hqB | hqB <;> rcases hqC with hqC | hqC
    · exact h12 (hqB.symm.trans hqC)
    · exact h41 (hqC.symm.trans hqB)
    · exact h23 (hqC.symm.trans hqB)
    · exact h34 (hqB.symm.trans hqC)
  have hcov : ∀ q : Q, q = q₀ ∨ q ∈ B ∨ q ∈ C := fun q => by
    rcases hcov_all q with h | h | h | h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by simp [B]))
    · exact Or.inr (Or.inr (by simp [C]))
    · exact Or.inr (Or.inl (by simp [B]))
    · exact Or.inr (Or.inr (by simp [C]))
  have ha_B : ∀ q : Q, A.step q a ∈ B ↔ q ∈ C := fun q => by
    rcases hcov_all q with h | h | h | h | h <;> rw [h]
    · simp [B, C, hstep_q0, h01, h02, h03, h04]
    · change q₂ ∈ B ↔ q₁ ∈ C; simp [B, C, h12.symm, h23, h12, h41.symm]
    · change q₃ ∈ B ↔ q₂ ∈ C; simp [B, C]
    · change q₄ ∈ B ↔ q₃ ∈ C; simp [B, C, h41, h34.symm, h23.symm, h34]
    · change f q₄ ∈ B ↔ q₄ ∈ C; rw [hf_q4]; simp [B, C]
  have ha_C : ∀ q : Q, A.step q a ∈ C ↔ q ∈ B := fun q => by
    rcases hcov_all q with h | h | h | h | h <;> rw [h]
    · simp [B, C, hstep_q0, h01, h02, h03, h04]
    · change q₂ ∈ C ↔ q₁ ∈ B; simp [B, C]
    · change q₃ ∈ C ↔ q₂ ∈ B; simp [B, C, h23.symm, h34, h12.symm, h23]
    · change q₄ ∈ C ↔ q₃ ∈ B; simp [B, C]
    · change f q₄ ∈ C ↔ q₄ ∈ B; rw [hf_q4]; simp [B, C, h12, h41.symm, h41, h34.symm]
  let atomsSpan : Submodule ℚ (Q → ℚ) :=
    Submodule.span ℚ (Set.range (fun i : Fin 3 =>
      if i.1 = 0 then indQ {q₀} else if i.1 = 1 then indQ B else indQ C))
  have hatoms_fr : Module.finrank ℚ atomsSpan = 3 := by
    let g : Fin 3 → (Q → ℚ) := fun i =>
      if i.1 = 0 then indQ {q₀} else if i.1 = 1 then indQ B else indQ C
    have hli : LinearIndependent ℚ g := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      rcases (by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2) with h | h | h
      · have h0 := congrFun hc q₀
        rw [Finset.sum_apply, Fin.sum_univ_castSucc, Fin.sum_univ_two] at h0
        change c 0 * indQ {q₀} q₀ + c 1 * indQ B q₀ + c 2 * indQ C q₀ = 0 at h0
        simp only [indQ, Finset.mem_singleton_self, hAB, hAC, ↓reduceIte, mul_one, mul_zero,
          add_zero] at h0
        rw [show i = 0 from Fin.ext h]; exact h0
      · have h0 := congrFun hc q₁
        rw [Finset.sum_apply, Fin.sum_univ_castSucc, Fin.sum_univ_two] at h0
        change c 0 * indQ {q₀} q₁ + c 1 * indQ B q₁ + c 2 * indQ C q₁ = 0 at h0
        have h1nC : q₁ ∉ C := Finset.disjoint_left.mp hBC (by simp [B])
        simp only [indQ, Finset.mem_singleton, h01.symm, B, Finset.mem_insert_self, h1nC,
          ↓reduceIte, mul_one, mul_zero, zero_add, add_zero] at h0
        rw [show i = 1 from Fin.ext h]; exact h0
      · have h0 := congrFun hc q₂
        rw [Finset.sum_apply, Fin.sum_univ_castSucc, Fin.sum_univ_two] at h0
        change c 0 * indQ {q₀} q₂ + c 1 * indQ B q₂ + c 2 * indQ C q₂ = 0 at h0
        have h2nB : q₂ ∉ B := Finset.disjoint_left.mp hBC.symm (by simp [C])
        simp only [indQ, Finset.mem_singleton, h02.symm, h2nB, C, Finset.mem_insert_self,
          ↓reduceIte, mul_one, mul_zero, zero_add] at h0
        rw [show i = 2 from Fin.ext h]; exact h0
    have hfr := finrank_span_eq_card hli
    rw [Fintype.card_fin] at hfr
    exact hfr
  have hK0_le_perp : K₀' A a ≤ perpSubspace atomsSpan := by
    intro x hx
    have hx_q0 : x q₀ = 0 := by
      have hev2 : A.eval q₀ (List.replicate 2 a) = q₀ := by
        rw [eval_rep2, hstep_q0, hstep_q0]
      have hR := R_bij_eval A hbij 2 x q₀
      rw [hev2] at hR
      have h0 := congrFun (hphi4 x hx) q₀
      simp only [Pi.add_apply, Pi.zero_apply, hR] at h0
      linarith
    have hx_B : ∑ q ∈ B, x q = 0 := by
      have hev2 : A.eval q₁ (List.replicate 2 a) = q₃ := by rw [eval_rep2]
      have hR := R_bij_eval A hbij 2 x q₁
      rw [hev2] at hR
      have h0 := congrFun (hphi4 x hx) q₃
      simp only [Pi.add_apply, Pi.zero_apply, hR] at h0
      rw [show B = {q₁, q₃} from rfl, Finset.sum_pair h13]
      exact h0
    have hx_C : ∑ q ∈ C, x q = 0 := by
      have hev2 : A.eval q₂ (List.replicate 2 a) = q₄ := by rw [eval_rep2]
      have hR := R_bij_eval A hbij 2 x q₂
      rw [hev2] at hR
      have h0 := congrFun (hphi4 x hx) q₄
      simp only [Pi.add_apply, Pi.zero_apply, hR] at h0
      rw [show C = {q₂, q₄} from rfl, Finset.sum_pair h24]
      exact h0
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨i, rfl⟩
      have hcomm : ∀ S : Finset Q, (∑ q ∈ S, x q = 0) → ∑ q : Q, indQ S q * x q = 0 := by
        intro S hS
        calc ∑ q : Q, indQ S q * x q
            = ∑ q : Q, if q ∈ S then x q else 0 :=
              Finset.sum_congr rfl fun q _ => by by_cases hq : q ∈ S <;> simp [indQ, hq]
          _ = ∑ q ∈ Finset.univ.filter (fun q => q ∈ S), x q := (Finset.sum_filter _ _).symm
          _ = ∑ q ∈ S, x q := by
              have : Finset.univ.filter (fun q => q ∈ S) = S := by ext q; simp
              rw [this]
          _ = 0 := hS
      rcases (by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2) with h | h | h
      · simp only [h, ↓reduceIte]; exact hcomm {q₀} (by simp [hx_q0])
      · simp only [h, ↓reduceIte]; exact hcomm B hx_B
      · simp only [h, ↓reduceIte]; exact hcomm C hx_C
    | zero => simp
    | add y₁ y₂ _ _ ih1 ih2 =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ih1, ih2, add_zero]
    | smul r y₁ _ ih1 =>
      calc ∑ q : Q, (r • y₁) q * x q = r * ∑ q : Q, y₁ q * x q := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => by simp [Pi.smul_apply]; ring
        _ = 0 := by rw [ih1, mul_zero]
  have hK0_eq_perp : K₀' A a = perpSubspace atomsSpan := by
    apply Submodule.eq_of_le_of_finrank_eq hK0_le_perp
    have hle := finrank_perpSubspace_le atomsSpan
    have hge := Submodule.finrank_mono hK0_le_perp
    omega
  have hK0_atoms : ∀ x : Q → ℚ, x ∈ K₀' A a ↔
      x q₀ = 0 ∧ (∑ q ∈ B, x q = 0) ∧ (∑ q ∈ C, x q = 0) := by
    intro x
    rw [hK0_eq_perp]
    constructor
    · intro hx
      have hdot : ∀ S : Finset Q, indQ S ∈ atomsSpan → ∑ q ∈ S, x q = 0 := by
        intro S hS
        have h0 := hx (indQ S) hS
        calc ∑ q ∈ S, x q
            = ∑ q ∈ Finset.univ.filter (fun q => q ∈ S), x q := by
              have : Finset.univ.filter (fun q => q ∈ S) = S := by ext q; simp
              rw [this]
          _ = ∑ q : Q, if q ∈ S then x q else 0 := Finset.sum_filter _ _
          _ = ∑ q : Q, indQ S q * x q :=
              Finset.sum_congr rfl fun q _ => by by_cases hq : q ∈ S <;> simp [indQ, hq]
          _ = 0 := h0
      refine ⟨?_, hdot B (Submodule.subset_span ⟨1, by simp⟩),
        hdot C (Submodule.subset_span ⟨2, by simp⟩)⟩
      simpa using hdot {q₀} (Submodule.subset_span ⟨0, by simp⟩)
    · rintro ⟨hx0, hxB, hxC⟩ y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        rcases hz with ⟨i, rfl⟩
        have hcomm : ∀ S : Finset Q, (∑ q ∈ S, x q = 0) → ∑ q : Q, indQ S q * x q = 0 := by
          intro S hS
          calc ∑ q : Q, indQ S q * x q
              = ∑ q : Q, if q ∈ S then x q else 0 :=
                Finset.sum_congr rfl fun q _ => by by_cases hq : q ∈ S <;> simp [indQ, hq]
            _ = ∑ q ∈ Finset.univ.filter (fun q => q ∈ S), x q := (Finset.sum_filter _ _).symm
            _ = ∑ q ∈ S, x q := by
                have : Finset.univ.filter (fun q => q ∈ S) = S := by ext q; simp
                rw [this]
            _ = 0 := hS
        rcases (by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2) with h | h | h
        · simp only [h, ↓reduceIte]; exact hcomm {q₀} (by simp [hx0])
        · simp only [h, ↓reduceIte]; exact hcomm B hxB
        · simp only [h, ↓reduceIte]; exact hcomm C hxC
      | zero => simp
      | add y₁ y₂ _ _ ih1 ih2 =>
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ih1, ih2, add_zero]
      | smul r y₁ _ ih1 =>
        calc ∑ q : Q, (r • y₁) q * x q = r * ∑ q : Q, y₁ q * x q := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => by simp [Pi.smul_apply]; ring
          _ = 0 := by rw [ih1, mul_zero]
  have hK0_nonzero_on_C4 : ∀ q : Q, q ≠ q₀ → ∃ x ∈ K₀' A a, x q ≠ 0 := by
    intro q hq0
    rcases hcov_all q with h | h | h | h | h
    · exact absurd h hq0
    · exact ⟨v, hvK, h ▸ hq1_ne⟩
    · refine ⟨R A [a] v, K₀'_R_a_inv A hbij hvK, ?_⟩
      have hval := R_bij_eval A hbij 1 v q₁
      rw [eval_rep1] at hval; rw [h]; exact hval.symm ▸ hq1_ne
    · refine ⟨R A (List.replicate 2 a) v, by rw [← R_a_a]; exact K₀'_R_a_inv A hbij (K₀'_R_a_inv A hbij hvK), ?_⟩
      have hval := R_bij_eval A hbij 2 v q₁
      rw [eval_rep2] at hval; rw [h]; exact hval.symm ▸ hq1_ne
    · refine ⟨R A (List.replicate 3 a) v, by
        rw [← R_a_rep, ← R_a_a]
        exact K₀'_R_a_inv A hbij (K₀'_R_a_inv A hbij (K₀'_R_a_inv A hbij hvK)), ?_⟩
      have hval := R_bij_eval A hbij 3 v q₁
      rw [eval_rep3] at hval; rw [h]; exact hval.symm ▸ hq1_ne
  have hnot_q0_K1 : indQ {q₀} ∉ perpSubspace (krylovChain A a 1 1) := by
    intro hmem
    have hpre_single : ∀ σ : α, A.preimage {q₀} [σ] = {q₀} := by
      intro σ
      have hρσ : ρ A [σ] ∈ K₀' A a := ρ_single_mem_K₀' A hbij σ
      have hcard1 : (A.preimage {q₀} [σ]).card = 1 := by
        have h0 := ((hK0_atoms (ρ A [σ])).mp hρσ).1
        dsimp only [ρ] at h0
        exact Nat.cast_injective (sub_eq_zero.mp h0)
      obtain ⟨p_σ, hp_eq⟩ := Finset.card_eq_one.mp hcard1
      have hstep_p : ∀ x : Q → ℚ, R A [σ] x q₀ = x p_σ := by
        intro x
        rw [R_apply_ite]
        have hiff : ∀ p : Q, A.eval p [σ] = q₀ ↔ p = p_σ := by
          intro p
          have h1 : p ∈ A.preimage {q₀} [σ] ↔ A.eval p [σ] = q₀ := by simp [Aut.preimage]
          rw [hp_eq, Finset.mem_singleton] at h1
          exact h1.symm
        have hiff' : ∀ p : Q, A.step p σ = q₀ ↔ p = p_σ := fun p => by
          simpa [eval_cons_aux, eval_nil_aux] using hiff p
        calc ∑ p : Q, (if A.eval p [σ] = q₀ then x p else 0)
            = ∑ p : Q, (if p = p_σ then x p else 0) :=
              Finset.sum_congr rfl fun p _ => by simp [hiff' p]
          _ = x p_σ := by simp
      have hp_eq_q0 : p_σ = q₀ := by
        by_contra hne
        obtain ⟨x, hxK, hx_ne⟩ := hK0_nonzero_on_C4 p_σ hne
        have hxK0 : x ∈ krylovChain A a 1 0 := by rw [krylovChain_zero_eq A a 1 hspan]; exact hxK
        have hRx : R A [σ] x ∈ krylovChain A a 1 1 :=
          R_single_mem_krylovChain_succ A hbij 1 hspan 0 σ hxK0
        have h0 := (indQ_mem_perpSubspace_iff _ _).mp hmem (R A [σ] x) hRx
        simp only [Finset.sum_singleton, hstep_p] at h0
        exact hx_ne h0
      rw [hp_eq, hp_eq_q0]
    have hpre_all : ∀ w : List α, A.preimage {q₀} w = {q₀} := by
      intro w
      induction w with
      | nil => exact preimage_nil_aux A {q₀}
      | cons σ w ih =>
        ext q
        have h1 : A.eval (A.step q σ) w = q₀ ↔ A.step q σ = q₀ := by
          have := Finset.ext_iff.mp ih (A.step q σ)
          simpa [Aut.preimage] using this
        have h2 : A.step q σ = q₀ ↔ q = q₀ := by
          have := Finset.ext_iff.mp (hpre_single σ) q
          simpa [Aut.preimage, eval_cons_aux, eval_nil_aux] using this
        simp only [Aut.preimage, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, eval_cons_aux, h1, h2]
    obtain ⟨w, _, hgt⟩ := hext6 {q₀} (by simp) (by simp)
    rw [hpre_all w] at hgt
    simp at hgt
  have hK0_le_K1 : K₀' A a ≤ krylovChain A a 1 1 := by
    rw [← krylovChain_zero_eq A a 1 hspan]; exact krylovChain_mono A a 1 (Nat.zero_le 1)
  have hK1_ge : 2 ≤ Module.finrank ℚ (krylovChain A a 1 1) := by
    have := Submodule.finrank_mono hK0_le_K1; omega
  have hK1_le : Module.finrank ℚ (krylovChain A a 1 1) ≤ 4 := by
    have := Submodule.finrank_mono (krylovChain_le_K0 A a 1 1)
    have hK0fr : Module.finrank ℚ (K₀ Q) = 4 := by rw [finrank_ker_sumLin, hn5]
    omega
  by_cases hdim2 : Module.finrank ℚ (krylovChain A a 1 1) = 2
  · have hstab : krylovChain A a 1 0 = krylovChain A a 1 1 :=
      Submodule.eq_of_le_of_finrank_eq (krylovChain_mono A a 1 (Nat.zero_le 1))
        (by rw [krylovChain_zero_eq A a 1 hspan, hd0, hdim2])
    apply cerny_of_n_extensible A hsync
    intro S hS1 hSlt
    have hnot : indQ S ∉ perpSubspace (krylovChain A a 1 0) := by
      intro hmem
      obtain ⟨w, _, hgt⟩ := hext6 S hS1 (by omega)
      have h0 := (indQ_mem_perpSubspace_iff _ _).mp hmem (ρ A w)
        (ρ_mem_krylovChain_of_stable A hbij 1 hspan hstab w)
      rw [dotInd_ρ] at h0
      have hEq : (A.preimage S w).card = S.card := Nat.cast_injective (sub_eq_zero.mp h0)
      omega
    obtain ⟨w, hl, hg⟩ := hphi4_ext_of_not_perp 0 S hnot
    exact ⟨w, by omega, hg⟩
  · by_cases hdim4 : Module.finrank ℚ (krylovChain A a 1 1) = 4
    · have hEq : krylovChain A a 1 1 = K₀ Q :=
        Submodule.eq_of_le_of_finrank_eq (krylovChain_le_K0 A a 1 1)
          (by rw [finrank_ker_sumLin, hn5, hdim4])
      apply cerny_of_n_extensible A hsync
      intro S hS1 hSlt
      have hnot : indQ S ∉ perpSubspace (krylovChain A a 1 1) := by
        rw [hEq]; intro hmem
        obtain ⟨w, _, hgt⟩ := hext6 S hS1 (by omega)
        have h0 := (indQ_mem_perpSubspace_iff _ _).mp hmem (ρ A w) (ρ_mem_K0 A w)
        rw [dotInd_ρ] at h0
        have hEq' : (A.preimage S w).card = S.card := Nat.cast_injective (sub_eq_zero.mp h0)
        omega
      obtain ⟨w, hl, hg⟩ := hphi4_ext_of_not_perp 1 S hnot
      exact ⟨w, by omega, hg⟩
    · have hdim3 : Module.finrank ℚ (krylovChain A a 1 1) = 3 := by omega
      have hnot_K0_fast : ∀ S : Finset Q, 1 ≤ S.card → S.card < 5 →
          indQ S ∉ perpSubspace (K₀' A a) →
          ∃ w : List α, w.length ≤ 4 ∧ S.card < (A.preimage S w).card := by
        intro S _ _ hnot
        have hnot0 : indQ S ∉ perpSubspace (krylovChain A a 1 0) := by
          rwa [krylovChain_zero_eq A a 1 hspan]
        obtain ⟨w, hl, hg⟩ := hphi4_ext_of_not_perp 0 S hnot0
        exact ⟨w, by omega, hg⟩
      have hext4_5 : ∀ S : Finset Q, S.card = 4 →
          ∃ w : List α, w.length ≤ 5 ∧ 4 < (A.preimage S w).card := by
        intro S hS4
        by_cases hnot1 : indQ S ∉ perpSubspace (krylovChain A a 1 1)
        · obtain ⟨w, hl, hg⟩ := hphi4_ext_of_not_perp 1 S hnot1
          exact ⟨w, by omega, by omega⟩
        · push_neg at hnot1
          have hcomp1 : (Finset.univ \ S).card = 1 := by
            have := card_sdiff_univ_add S; omega
          obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hcomp1
          have hq_K1 : indQ {q} ∈ perpSubspace (krylovChain A a 1 1) := by
            rw [← hq_eq, indQ_compl]
            exact (perpSubspace _).sub_mem (ones_mem_perpSubspace_krylovChain A a 1 1) hnot1
          have hq_K0 : indQ {q} ∈ perpSubspace (K₀' A a) := fun x hx =>
            hq_K1 x (hK0_le_K1 hx)
          have hq_eq_q0 : q = q₀ := by
            by_contra hne
            obtain ⟨x, hxK, hx_ne⟩ := hK0_nonzero_on_C4 q hne
            have h0 := (indQ_mem_perpSubspace_iff _ _).mp hq_K0 x hxK
            simp only [Finset.sum_singleton] at h0
            exact hx_ne h0
          rw [hq_eq_q0] at hq_K1
          exact absurd hq_K1 hnot_q0_K1
      by_cases hB_K1 : indQ B ∈ perpSubspace (krylovChain A a 1 1)
      · exact order_four_n5_atom_step A hsync a hbij hn5 q₀ B C hstep_q0 hB_card hC_card
          hAB hAC hBC hcov ha_B ha_C hK0_atoms hdim3 hd0 hB_K1 hnot_K0_fast hext6 hext4_5
      · by_cases hC_K1 : indQ C ∈ perpSubspace (krylovChain A a 1 1)
        · exact order_four_n5_atom_step A hsync a hbij hn5 q₀ C B hstep_q0 hC_card hB_card
            hAC hAB hBC.symm
            (fun q => by
              rcases hcov q with h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr h)
              · exact Or.inr (Or.inl h))
            ha_C ha_B
            (fun x => by
              rw [hK0_atoms]
              exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩⟩)
            hdim3 hd0 hC_K1 hnot_K0_fast hext6 hext4_5
        · apply cerny_of_n_extensible A hsync
          intro S hS1 hSlt
          by_cases hnot1 : indQ S ∉ perpSubspace (krylovChain A a 1 1)
          · obtain ⟨w, hl, hg⟩ := hphi4_ext_of_not_perp 1 S hnot1
            exact ⟨w, by omega, hg⟩
          · push_neg at hnot1
            exfalso
            have hS_K0 : indQ S ∈ perpSubspace (K₀' A a) := fun x hx => hnot1 x (hK0_le_K1 hx)
            have hconstB : q₁ ∈ S ↔ q₃ ∈ S := by
              refine const_on_pair_of_perp hS_K0 ?_
              rw [hK0_atoms]
              refine ⟨by simp [h01, h03], ?_, ?_⟩
              · rw [show B = {q₁, q₃} from rfl, Finset.sum_pair h13]; simp [h13, h13.symm]
              · rw [show C = {q₂, q₄} from rfl, Finset.sum_pair h24]
                simp [h12.symm, h23, h41, h34.symm]
            have hconstC : q₂ ∈ S ↔ q₄ ∈ S := by
              refine const_on_pair_of_perp hS_K0 ?_
              rw [hK0_atoms]
              refine ⟨by simp [h02, h04], ?_, ?_⟩
              · rw [show B = {q₁, q₃} from rfl, Finset.sum_pair h13]
                simp [h12, h41.symm, h23.symm, h34]
              · rw [show C = {q₂, q₄} from rfl, Finset.sum_pair h24]; simp [h24, h24.symm]
            have h1W : (fun _ : Q => (1 : ℚ)) ∈ perpSubspace (krylovChain A a 1 1) :=
              ones_mem_perpSubspace_krylovChain A a 1 1
            by_cases b0 : q₀ ∈ S <;> by_cases b1 : q₁ ∈ S <;> by_cases b2 : q₂ ∈ S
            · have huniv : S = Finset.univ := by
                ext q; simp only [Finset.mem_univ, iff_true]
                rcases hcov_all q with h | h | h | h | h <;> rw [h]
                · exact b0
                · exact b1
                · exact b2
                · exact hconstB.mp b1
                · exact hconstC.mp b2
              rw [huniv, Finset.card_univ] at hSlt; omega
            · have hEq : Finset.univ \ S = C := by
                ext q; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, C,
                  Finset.mem_insert, Finset.mem_singleton]
                rcases hcov_all q with h | h | h | h | h <;> rw [h]
                · simp [b0, h02, h04]
                · simp [b1, h12, h41.symm]
                · simp [b2]
                · simp [hconstB.mp b1, h23.symm, h34]
                · simp [show q₄ ∉ S from fun h => b2 (hconstC.mpr h)]
              apply hC_K1; rw [← hEq, indQ_compl]; exact (perpSubspace _).sub_mem h1W hnot1
            · have hEq : Finset.univ \ S = B := by
                ext q; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, B,
                  Finset.mem_insert, Finset.mem_singleton]
                rcases hcov_all q with h | h | h | h | h <;> rw [h]
                · simp [b0, h01, h03]
                · simp [b1]
                · simp [b2, h12.symm, h23]
                · simp [show q₃ ∉ S from fun h => b1 (hconstB.mpr h)]
                · simp [hconstC.mp b2, h41, h34.symm]
              apply hB_K1; rw [← hEq, indQ_compl]; exact (perpSubspace _).sub_mem h1W hnot1
            · have hEq : S = {q₀} := by
                ext q; simp only [Finset.mem_singleton]
                rcases hcov_all q with h | h | h | h | h <;> rw [h]
                · simp [b0]
                · simp [b1, h01.symm]
                · simp [b2, h02.symm]
                · simp [show q₃ ∉ S from fun h => b1 (hconstB.mpr h), h03.symm]
                · simp [show q₄ ∉ S from fun h => b2 (hconstC.mpr h), h04.symm]
              exact hnot_q0_K1 (hEq ▸ hnot1)
            · have hEq : Finset.univ \ S = {q₀} := by
                ext q; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
                rcases hcov_all q with h | h | h | h | h <;> rw [h]
                · simp [b0]
                · simp [b1, h01.symm]
                · simp [b2, h02.symm]
                · simp [hconstB.mp b1, h03.symm]
                · simp [hconstC.mp b2, h04.symm]
              apply hnot_q0_K1; rw [← hEq, indQ_compl]; exact (perpSubspace _).sub_mem h1W hnot1
            · have hEq : S = B := by
                ext q; simp only [B, Finset.mem_insert, Finset.mem_singleton]
                rcases hcov_all q with h | h | h | h | h <;> rw [h]
                · simp [b0, h01, h03]
                · simp [b1]
                · simp [b2, h12.symm, h23]
                · simp [hconstB.mp b1]
                · simp [show q₄ ∉ S from fun h => b2 (hconstC.mpr h), h41, h34.symm]
              exact hB_K1 (hEq ▸ hnot1)
            · have hEq : S = C := by
                ext q; simp only [C, Finset.mem_insert, Finset.mem_singleton]
                rcases hcov_all q with h | h | h | h | h <;> rw [h]
                · simp [b0, h02, h04]
                · simp [b1, h12, h41.symm]
                · simp [b2]
                · simp [show q₃ ∉ S from fun h => b1 (hconstB.mpr h), h23.symm, h34]
                · simp [hconstC.mp b2]
              exact hC_K1 (hEq ▸ hnot1)
            · have hemp : S = ∅ := by
                ext q; simp only [Finset.notMem_empty, iff_false]
                rcases hcov_all q with h | h | h | h | h <;> rw [h]
                · exact b0
                · exact b1
                · exact b2
                · exact fun h => b1 (hconstB.mpr h)
                · exact fun h => b2 (hconstC.mpr h)
              rw [hemp] at hS1; simp at hS1

/-- **Complete Unconditional Order-4 Balanced Černý Theorem:** -/
theorem order_four_balanced_cerny [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hord : ∀ q : Q, A.eval q (List.replicate 4 a) = q)
    (hbal : IsCycleBalanced A a) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  have hbij := hbal.1
  let n := Fintype.card Q
  have hnot_inj_sq : ∀ q : Q,
      ¬ Function.Injective (fun i : Fin 4 => A.eval q (List.replicate i.1 a)) →
      A.eval q (List.replicate 2 a) = q := by
    intro q hninj
    unfold Function.Injective at hninj
    push_neg at hninj
    obtain ⟨i, j, hij_eq, hij_ne⟩ := hninj
    have hstep_cancel : ∀ k₁ k₂ : ℕ, k₁ < k₂ →
        A.eval q (List.replicate k₁ a) = A.eval q (List.replicate k₂ a) →
        A.eval q (List.replicate (k₂ - k₁) a) = q := by
      intro k₁ k₂ hlt heq
      have h1 : A.eval (A.eval q (List.replicate (k₂ - k₁) a)) (List.replicate k₁ a) =
          A.eval q (List.replicate k₁ a) := by
        rw [← eval_append_aux, ← replicate_add_append, Nat.sub_add_cancel (le_of_lt hlt)]
        exact heq.symm
      exact (eval_replicate_bijective A hbij k₁).1 h1
    have hex_d : ∃ d : ℕ, 1 ≤ d ∧ d ≤ 3 ∧ A.eval q (List.replicate d a) = q := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
      · exact ⟨j.1 - i.1, by omega, by omega, hstep_cancel i.1 j.1 hlt hij_eq⟩
      · exact ⟨i.1 - j.1, by omega, by omega, hstep_cancel j.1 i.1 hgt hij_eq.symm⟩
    obtain ⟨d, hd1, hd3, hd_eq⟩ := hex_d
    rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl
    · rw [show (2 : ℕ) = 1 + 1 from rfl, replicate_add_append, eval_append_aux, hd_eq, hd_eq]
    · exact hd_eq
    · have h1 : A.eval q (List.replicate 1 a) = q := by
        have := hord q
        rw [show (4 : ℕ) = 3 + 1 from rfl, replicate_add_append, eval_append_aux, hd_eq] at this
        exact this
      rw [show (2 : ℕ) = 1 + 1 from rfl, replicate_add_append, eval_append_aux, h1, h1]
  by_cases hn3 : n ≤ 3
  · have hord2 : ∀ q : Q, A.eval q (List.replicate 2 a) = q := by
      intro q
      apply hnot_inj_sq q
      intro hinj
      have hcard := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_fin] at hcard
      dsimp only [n] at hn3; omega
    exact prime_order_balanced_cerny A hsync a 2 Nat.prime_two hord2 hbal
  · by_cases hn4 : n = 4
    · by_cases hex4 : ∃ q : Q, Function.Injective (fun i : Fin 4 => A.eval q (List.replicate i.1 a))
      · obtain ⟨q₀, hinj⟩ := hex4
        exact dubuc_of_distinct_orbit A hsync a hbij 4 hn4 hord q₀ hinj
      · push_neg at hex4
        have hord2 : ∀ q : Q, A.eval q (List.replicate 2 a) = q := fun q => hnot_inj_sq q (hex4 q)
        exact prime_order_balanced_cerny A hsync a 2 Nat.prime_two hord2 hbal
    · have hn5 : 5 ≤ n := by omega
      obtain ⟨hsup, hinf⟩ := order4_decomp A a hord hbal
      have hdim_sum : Module.finrank ℚ (K₀' A a) =
          Module.finrank ℚ (V₂ A a) + Module.finrank ℚ (V₄ A a) := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq (V₂ A a) (V₄ A a)
        rw [hsup, hinf, finrank_bot, add_zero] at h
        exact h
      by_cases hV4_bot : V₄ A a = ⊥
      · have hKeq : K₀' A a = V₂ A a := by rw [← hsup, hV4_bot, sup_bot_eq]
        apply antisymmetric_balanced_cerny A hsync a hbij
        intro b hb
        have hmem : ρ A [b] ∈ V₂ A a := by
          rw [← hKeq]; exact Submodule.subset_span ⟨b, 0, hb, rfl⟩
        exact eq_neg_of_add_eq_zero_left ((mem_V₂_iff A a _).mp hmem).2
      · have hV4_ge2 : 2 ≤ Module.finrank ℚ (V₄ A a) := two_le_finrank_V₄_of_bij A a hbij hV4_bot
        by_cases hV2_bot : V₂ A a = ⊥
        · have hKeq : K₀' A a = V₄ A a := by rw [← hsup, hV2_bot, bot_sup_eq]
          have hphi4 : ∀ x ∈ K₀' A a, R A (List.replicate 2 a) x + x = 0 := fun x hx =>
            ((mem_V₄_iff A a x).mp (hKeq ▸ hx)).2
          by_cases hd3 : 3 ≤ Module.finrank ℚ (K₀' A a)
          · exact phi4_high_dim_balanced_cerny A hsync a hbij hphi4 hd3
          · have hd2 : Module.finrank ℚ (K₀' A a) = 2 := by
              rw [hdim_sum, hV2_bot, finrank_bot, zero_add] at hd3 ⊢; omega
            by_cases hn6 : 6 ≤ n
            · let c4 : Fin 3 → ℚ := fun j => if j.1 = 0 then 1 / 2 else if j.1 = 1 then 0 else 1 / 2
              have hc4_nonneg : ∀ j : Fin 3, 0 ≤ c4 j := by
                intro j
                rcases (by omega : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2) with h | h | h
                · rw [show j = 0 from Fin.ext h]; norm_num [c4]
                · rw [show j = 1 from Fin.ext h]; norm_num [c4]
                · rw [show j = 2 from Fin.ext h]; norm_num [c4]
              have hc4_0 : 0 < c4 0 := by simp [c4]
              have hc4_sum : ∑ j : Fin 3, c4 j = 1 := by
                rw [Fin.sum_univ_castSucc, Fin.sum_univ_two]; simp [c4]; norm_num
              have hc4_top : c4 (Fin.last 2) ≠ 0 := by simp [c4]
              have hann_c4 : ∀ x ∈ K₀' A a, ∑ j : Fin 3, c4 j • R A (List.replicate j.1 a) x = 0 :=
                c4_annihilates A a hphi4
              have hspan : K₀' A a ≤ Submodule.span ℚ
                  {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ 1 ∧ x = ρ A (b :: List.replicate j a)} := by
                simpa using K₀'_span_of_annihilator A a hbij 2 (by omega) c4 hc4_top hann_c4
              exact master_balanced_version_B_excess_one A hsync a hbij 1 2 hspan c4
                hc4_nonneg hc4_0 hc4_sum hann_c4 hn6 (by dsimp only [n] at *; omega)
                (by omega) (by omega)
            · exact order_four_n5_phi4_dim2 A hsync a hord hbal (by dsimp only [n] at *; omega)
                hphi4 hd2
        · have hV2_ge1 : 1 ≤ Module.finrank ℚ (V₂ A a) := ne_bot_implies_one_le_finrank hV2_bot
          have hd3 : 3 ≤ Module.finrank ℚ (K₀' A a) := by omega
          apply cerny_of_n_extensible A hsync
          intro S hS1 hSlt
          let c : Fin 4 → ℚ := fun _ => 1 / 4
          have hc_pos : ∀ j : Fin 4, 0 < c j := fun _ => by simp [c]
          have hc_sum : ∑ j : Fin 4, c j = 1 := by
            rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_two]; simp [c]; norm_num
          have hann : ∀ x ∈ K₀' A a, ∑ j : Fin 4, c j • R A (List.replicate j.1 a) x = 0 := by
            intro x hx
            simpa [c] using sum_orbit_annihilates_K₀' A a 4 (by omega) hord hbal x hx
          obtain ⟨w, hl, hg⟩ := master_balanced_version_A A hsync a hbij 3 (by omega) c hc_pos hc_sum
            hann hS1 hSlt
          exact ⟨w, by omega, hg⟩

end OrderFourBalanced


section OrderSixBalanced

open BalancedPermutations KrylovEulerian

variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- Cyclotomic component `V₃ = K₀' ∩ ker (R[a²] + R[a] + I)`. -/
def V₃ (A : Aut Q α) (a : α) : Submodule ℚ (Q → ℚ) :=
  K₀' A a ⊓ LinearMap.ker (R A (List.replicate 2 a) + R A [a] + LinearMap.id)

/-- Cyclotomic component `V₆ = K₀' ∩ ker (R[a²] - R[a] + I)`. -/
def V₆ (A : Aut Q α) (a : α) : Submodule ℚ (Q → ℚ) :=
  K₀' A a ⊓ LinearMap.ker (R A (List.replicate 2 a) - R A [a] + LinearMap.id)

private lemma mem_V₃_iff (A : Aut Q α) (a : α) (x : Q → ℚ) :
    x ∈ V₃ A a ↔ x ∈ K₀' A a ∧ R A (List.replicate 2 a) x + R A [a] x + x = 0 := by
  simp [V₃, LinearMap.mem_ker]

private lemma mem_V₆_iff (A : Aut Q α) (a : α) (x : Q → ℚ) :
    x ∈ V₆ A a ↔ x ∈ K₀' A a ∧ R A (List.replicate 2 a) x - R A [a] x + x = 0 := by
  simp [V₆, LinearMap.mem_ker]

private lemma order6_decomp (A : Aut Q α) (a : α)
    (hord : ∀ q : Q, A.eval q (List.replicate 6 a) = q)
    (hbal : IsCycleBalanced A a) :
    V₂ A a ⊔ (V₃ A a ⊔ V₆ A a) = K₀' A a ∧
    V₃ A a ⊓ V₆ A a = ⊥ ∧
    V₂ A a ⊓ (V₃ A a ⊔ V₆ A a) = ⊥ := by
  have hbij := hbal.1
  have hT6 : ∀ x : Q → ℚ, R A (List.replicate 6 a) x = x := by
    intro x; ext q
    rw [R_apply_ite]
    simp only [hord]
    rw [Finset.sum_eq_single q]
    · simp
    · intro p _ hp; rw [if_neg hp]
    · intro h; exact absurd (Finset.mem_univ q) h
  have hann6 : ∀ x ∈ K₀' A a,
      x + R A [a] x + R A (List.replicate 2 a) x + R A (List.replicate 3 a) x +
      R A (List.replicate 4 a) x + R A (List.replicate 5 a) x = 0 := by
    intro x hx
    have h := sum_orbit_annihilates_K₀' A a 6 (by omega) hord hbal x hx
    ext q
    have hq := congrFun h q
    rw [sum_fin6_rat] at hq
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hq ⊢
    change (1 / ((6 : ℕ) : ℚ)) * R A [] x q + (1 / ((6 : ℕ) : ℚ)) * R A [a] x q +
      (1 / ((6 : ℕ) : ℚ)) * R A (List.replicate 2 a) x q +
      (1 / ((6 : ℕ) : ℚ)) * R A (List.replicate 3 a) x q +
      (1 / ((6 : ℕ) : ℚ)) * R A (List.replicate 4 a) x q +
      (1 / ((6 : ℕ) : ℚ)) * R A (List.replicate 5 a) x q = 0 at hq
    rw [R_nil] at hq
    norm_num at hq
    rw [R_apply_ite A [a] x q, R_apply_ite A (List.replicate 2 a) x q,
      R_apply_ite A (List.replicate 3 a) x q, R_apply_ite A (List.replicate 4 a) x q,
      R_apply_ite A (List.replicate 5 a) x q]
    simp only [List.replicate_succ, List.replicate, eval_cons_aux, eval_nil_aux]
    linarith
  have hK_rep : ∀ {x : Q → ℚ}, x ∈ K₀' A a → ∀ k : ℕ, R A (List.replicate k a) x ∈ K₀' A a := by
    intro x hx k
    induction k with
    | zero => rw [show List.replicate 0 a = [] from rfl, R_nil]; exact hx
    | succ k ih => rw [← R_a_rep]; exact K₀'_R_a_inv A hbij ih
  have hV36_inf : V₃ A a ⊓ V₆ A a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, mem_V₃_iff, mem_V₆_iff] at hx
    have h2T : R A [a] x = 0 := by
      ext q
      have h1 := congrFun hx.1.2 q
      have h2 := congrFun hx.2.2 q
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at h1 h2 ⊢
      linarith
    have hx0 : x = 0 := by
      have h := congrArg (R A (List.replicate 5 a)) h2T
      rw [R_rep_a, show 5 + 1 = 6 from rfl, hT6, map_zero] at h
      exact h
    rw [Submodule.mem_bot]; exact hx0
  have hV3_inv : ∀ {v : Q → ℚ}, v ∈ V₃ A a → R A [a] v ∈ V₃ A a := by
    intro v hv
    rw [mem_V₃_iff] at hv ⊢
    refine ⟨K₀'_R_a_inv A hbij hv.1, ?_⟩
    have h0 := congrArg (R A [a]) hv.2
    rw [map_add, map_add, map_zero, R_a_rep, R_a_a] at h0
    rw [R_rep_a, R_a_a]
    exact h0
  have hV6_inv : ∀ {v : Q → ℚ}, v ∈ V₆ A a → R A [a] v ∈ V₆ A a := by
    intro v hv
    rw [mem_V₆_iff] at hv ⊢
    refine ⟨K₀'_R_a_inv A hbij hv.1, ?_⟩
    have h0 := congrArg (R A [a]) hv.2
    rw [map_add, map_sub, map_zero, R_a_rep, R_a_a] at h0
    rw [R_rep_a, R_a_a]
    exact h0
  refine ⟨?_, hV36_inf, ?_⟩
  · apply le_antisymm
    · exact sup_le inf_le_left (sup_le inf_le_left inf_le_left)
    · intro x hx
      let x₂ : Q → ℚ := (1 / 3 : ℚ) • (x + R A (List.replicate 2 a) x + R A (List.replicate 4 a) x)
      let x₃ : Q → ℚ := (1 / 2 : ℚ) • (x + R A (List.replicate 3 a) x)
      let x₆ : Q → ℚ := (1 / 6 : ℚ) • (x - (2 : ℚ) • R A (List.replicate 2 a) x -
        (3 : ℚ) • R A (List.replicate 3 a) x - (2 : ℚ) • R A (List.replicate 4 a) x)
      have hx₂ : x₂ ∈ V₂ A a := by
        rw [mem_V₂_iff]
        refine ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ hx (hK_rep hx 2))
          (hK_rep hx 4)), ?_⟩
        dsimp only [x₂]
        rw [map_smul, map_add, map_add, R_a_rep, R_a_rep]
        ext q
        have hq := congrFun (hann6 x hx) q
        simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hq ⊢
        linarith
      have hx₃ : x₃ ∈ V₃ A a := by
        rw [mem_V₃_iff]
        refine ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hx (hK_rep hx 3)), ?_⟩
        dsimp only [x₃]
        rw [map_smul, map_add, map_smul, map_add, R_rep_rep, R_a_rep]
        ext q
        have hq := congrFun (hann6 x hx) q
        simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hq ⊢
        linarith
      have hx₆ : x₆ ∈ V₆ A a := by
        rw [mem_V₆_iff]
        refine ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.sub_mem _
          (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (hK_rep hx 2)))
          (Submodule.smul_mem _ _ (hK_rep hx 3)))
          (Submodule.smul_mem _ _ (hK_rep hx 4))), ?_⟩
        dsimp only [x₆]
        rw [map_smul, map_sub, map_sub, map_sub, map_smul, map_smul, map_smul,
            map_smul, map_sub, map_sub, map_sub, map_smul, map_smul, map_smul,
            R_rep_rep, R_rep_rep, R_rep_rep,
            R_a_rep, R_a_rep, R_a_rep,
            show 4 + 2 = 6 from rfl, hT6]
        ext q
        have hq := congrFun (hann6 x hx) q
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hq ⊢
        linarith
      have hdecomp : x = x₂ + (x₃ + x₆) := by
        ext q
        simp only [x₂, x₃, x₆, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hdecomp]
      exact Submodule.add_mem_sup hx₂ (Submodule.add_mem_sup hx₃ hx₆)
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, mem_V₂_iff] at hx
    rcases Submodule.mem_sup.mp hx.2 with ⟨v₃, hv₃, v₆, hv₆, rfl⟩
    have hsum0 : (R A [a] v₃ + v₃) + (R A [a] v₆ + v₆) = 0 := by
      have h := hx.1.2; rw [map_add] at h
      calc (R A [a] v₃ + v₃) + (R A [a] v₆ + v₆) = R A [a] v₃ + R A [a] v₆ + (v₃ + v₆) := by abel
        _ = 0 := h
    have hv3_eq : R A [a] v₃ + v₃ = -(R A [a] v₆ + v₆) := eq_neg_of_add_eq_zero_left hsum0
    have hmem_inf : R A [a] v₃ + v₃ ∈ V₃ A a ⊓ V₆ A a := by
      refine ⟨Submodule.add_mem _ (hV3_inv hv₃) hv₃, ?_⟩
      rw [hv3_eq]
      exact Submodule.neg_mem _ (Submodule.add_mem _ (hV6_inv hv₆) hv₆)
    rw [hV36_inf, Submodule.mem_bot] at hmem_inf
    have h3_anti : R A [a] v₃ = -v₃ := eq_neg_of_add_eq_zero_left hmem_inf
    have h6_anti : R A [a] v₆ = -v₆ := by
      have h0 : R A [a] v₆ + v₆ = 0 := by rw [hmem_inf, zero_add] at hsum0; exact hsum0
      exact eq_neg_of_add_eq_zero_left h0
    have hv3_0 : v₃ = 0 := by
      have h2 : R A (List.replicate 2 a) v₃ = v₃ := by
        rw [← R_a_a, h3_anti, map_neg, h3_anti, neg_neg]
      have h3 := ((mem_V₃_iff A a v₃).mp hv₃).2
      rw [h2, h3_anti] at h3
      ext q; have hq := congrFun h3 q
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hq
      change v₃ q = 0
      linarith
    have hv6_0 : v₆ = 0 := by
      have h2 : R A (List.replicate 2 a) v₆ = v₆ := by
        rw [← R_a_a, h6_anti, map_neg, h6_anti, neg_neg]
      have h6 := ((mem_V₆_iff A a v₆).mp hv₆).2
      rw [h2, h6_anti] at h6
      ext q; have hq := congrFun h6 q
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at hq
      change v₆ q = 0
      linarith
    rw [hv3_0, hv6_0, add_zero]; exact Submodule.zero_mem _

private lemma two_le_finrank_V₃_of_bij (A : Aut Q α) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a)) (hV3 : V₃ A a ≠ ⊥) :
    2 ≤ Module.finrank ℚ (V₃ A a) := by
  obtain ⟨v, hv, hv0⟩ := exists_nonzero_of_ne_bot hV3
  have hv_mem := (mem_V₃_iff A a v).mp hv
  have hT2v : R A (List.replicate 2 a) v = -R A [a] v - v := by
    ext q; have hq := congrFun hv_mem.2 q
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at hq ⊢; linarith
  have hRv_mem : R A [a] v ∈ V₃ A a := by
    rw [mem_V₃_iff]
    refine ⟨K₀'_R_a_inv A hbij hv_mem.1, ?_⟩
    have h0 := congrArg (R A [a]) hv_mem.2
    rw [map_add, map_add, map_zero, R_a_rep, R_a_a] at h0
    rw [R_rep_a, R_a_a]; exact h0
  let f : Fin 2 → (Q → ℚ) := fun i => if i.1 = 0 then v else R A [a] v
  have hli : LinearIndependent ℚ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_two] at hc
    change c 0 • v + c 1 • R A [a] v = 0 at hc
    have hT := congrArg (R A [a]) hc
    rw [map_add, map_smul, map_smul, map_zero, R_a_a, hT2v] at hT
    have hcomb : (c 0 ^ 2 - c 0 * c 1 + c 1 ^ 2) • v = 0 := by
      ext q
      have h1 := congrFun hc q
      have h2 := congrFun hT q
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply,
        smul_eq_mul] at h1 h2 ⊢
      have hid : (c 0 ^ 2 - c 0 * c 1 + c 1 ^ 2) * v q =
          (c 0 - c 1) * (c 0 * v q + c 1 * R A [a] v q) -
          c 1 * (c 0 * R A [a] v q + c 1 * (-R A [a] v q - v q)) := by ring
      rw [hid, h1, h2]; ring
    have hq0 : c 0 ^ 2 - c 0 * c 1 + c 1 ^ 2 = 0 := (smul_eq_zero.mp hcomb).resolve_right hv0
    have hquad : (c 0 - c 1 / 2) ^ 2 + 3 / 4 * c 1 ^ 2 = 0 := by
      have hid : (c 0 - c 1 / 2) ^ 2 + 3 / 4 * c 1 ^ 2 = c 0 ^ 2 - c 0 * c 1 + c 1 ^ 2 := by ring
      rw [hid, hq0]
    have hc1 : c 1 = 0 := by
      have hnn : 0 ≤ (c 0 - c 1 / 2) ^ 2 := sq_nonneg _
      have : c 1 ^ 2 ≤ 0 := by linarith
      exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _))
    have hc0 : c 0 = 0 := by
      have : c 0 ^ 2 = 0 := by rw [hc1] at hq0; linarith
      exact sq_eq_zero_iff.mp this
    intro i
    rcases (by omega : i.1 = 0 ∨ i.1 = 1) with h | h
    · rw [show i = 0 from Fin.ext h]; exact hc0
    · rw [show i = 1 from Fin.ext h]; exact hc1
  have hle : Submodule.span ℚ (Set.range f) ≤ V₃ A a := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩
    rcases (by omega : i.1 = 0 ∨ i.1 = 1) with hi | hi
    · rw [show i = 0 from Fin.ext hi]; simpa [f] using hv
    · rw [show i = 1 from Fin.ext hi]; simpa [f] using hRv_mem
  have hfr := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_fin] at hfr
  exact hfr

private lemma two_le_finrank_V₆_of_bij (A : Aut Q α) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a)) (hV6 : V₆ A a ≠ ⊥) :
    2 ≤ Module.finrank ℚ (V₆ A a) := by
  obtain ⟨v, hv, hv0⟩ := exists_nonzero_of_ne_bot hV6
  have hv_mem := (mem_V₆_iff A a v).mp hv
  have hT2v : R A (List.replicate 2 a) v = R A [a] v - v := by
    ext q; have hq := congrFun hv_mem.2 q
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hq ⊢; linarith
  have hRv_mem : R A [a] v ∈ V₆ A a := by
    rw [mem_V₆_iff]
    refine ⟨K₀'_R_a_inv A hbij hv_mem.1, ?_⟩
    have h0 := congrArg (R A [a]) hv_mem.2
    rw [map_add, map_sub, map_zero, R_a_rep, R_a_a] at h0
    rw [R_rep_a, R_a_a]; exact h0
  let f : Fin 2 → (Q → ℚ) := fun i => if i.1 = 0 then v else R A [a] v
  have hli : LinearIndependent ℚ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_two] at hc
    change c 0 • v + c 1 • R A [a] v = 0 at hc
    have hT := congrArg (R A [a]) hc
    rw [map_add, map_smul, map_smul, map_zero, R_a_a, hT2v] at hT
    have hcomb : (c 0 ^ 2 + c 0 * c 1 + c 1 ^ 2) • v = 0 := by
      ext q
      have h1 := congrFun hc q
      have h2 := congrFun hT q
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul] at h1 h2 ⊢
      have hid : (c 0 ^ 2 + c 0 * c 1 + c 1 ^ 2) * v q =
          (c 0 + c 1) * (c 0 * v q + c 1 * R A [a] v q) -
          c 1 * (c 0 * R A [a] v q + c 1 * (R A [a] v q - v q)) := by ring
      rw [hid, h1, h2]; ring
    have hq0 : c 0 ^ 2 + c 0 * c 1 + c 1 ^ 2 = 0 := (smul_eq_zero.mp hcomb).resolve_right hv0
    have hquad : (c 0 + c 1 / 2) ^ 2 + 3 / 4 * c 1 ^ 2 = 0 := by
      have hid : (c 0 + c 1 / 2) ^ 2 + 3 / 4 * c 1 ^ 2 = c 0 ^ 2 + c 0 * c 1 + c 1 ^ 2 := by ring
      rw [hid, hq0]
    have hc1 : c 1 = 0 := by
      have hnn : 0 ≤ (c 0 + c 1 / 2) ^ 2 := sq_nonneg _
      have : c 1 ^ 2 ≤ 0 := by linarith
      exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _))
    have hc0 : c 0 = 0 := by
      have : c 0 ^ 2 = 0 := by rw [hc1] at hq0; linarith
      exact sq_eq_zero_iff.mp this
    intro i
    rcases (by omega : i.1 = 0 ∨ i.1 = 1) with h | h
    · rw [show i = 0 from Fin.ext h]; exact hc0
    · rw [show i = 1 from Fin.ext h]; exact hc1
  have hle : Submodule.span ℚ (Set.range f) ≤ V₆ A a := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩
    rcases (by omega : i.1 = 0 ∨ i.1 = 1) with hi | hi
    · rw [show i = 0 from Fin.ext hi]; simpa [f] using hv
    · rw [show i = 1 from Fin.ext hi]; simpa [f] using hRv_mem
  have hfr := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_fin] at hfr
  exact hfr

private lemma exists_six_cycle_of_V₆_ne_bot (A : Aut Q α) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (hord : ∀ q : Q, A.eval q (List.replicate 6 a) = q)
    (hV6 : V₆ A a ≠ ⊥) :
    ∃ q₀ : Q, Function.Injective (fun i : Fin 6 => A.eval q₀ (List.replicate i.1 a)) := by
  obtain ⟨v, hv, hv0⟩ := exists_nonzero_of_ne_bot hV6
  have hv_eq := ((mem_V₆_iff A a v).mp hv).2
  have hT3v : R A (List.replicate 3 a) v + v = 0 := by
    have h1 := congrArg (R A [a]) hv_eq
    rw [map_add, map_sub, map_zero, R_a_rep, R_a_a] at h1
    ext q
    have hq0 := congrFun hv_eq q
    have hq1 := congrFun h1 q
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hq0 hq1 ⊢
    linarith
  have hex_q0 : ∃ q₀ : Q, v q₀ ≠ 0 := by
    by_contra hall; push_neg at hall; exact hv0 (funext hall)
  obtain ⟨q₀, hq0_ne⟩ := hex_q0
  refine ⟨q₀, ?_⟩
  by_contra hninj
  unfold Function.Injective at hninj
  push_neg at hninj
  obtain ⟨i, j, hij_eq, hij_ne⟩ := hninj
  have hstep_cancel : ∀ k₁ k₂ : ℕ, k₁ < k₂ →
      A.eval q₀ (List.replicate k₁ a) = A.eval q₀ (List.replicate k₂ a) →
      A.eval q₀ (List.replicate (k₂ - k₁) a) = q₀ := by
    intro k₁ k₂ hlt heq
    have h1 : A.eval (A.eval q₀ (List.replicate (k₂ - k₁) a)) (List.replicate k₁ a) =
        A.eval q₀ (List.replicate k₁ a) := by
      rw [← eval_append_aux, ← replicate_add_append, Nat.sub_add_cancel (le_of_lt hlt)]
      exact heq.symm
    exact (eval_replicate_bijective A hbij k₁).1 h1
  have hex_d : ∃ d : ℕ, 1 ≤ d ∧ d ≤ 5 ∧ A.eval q₀ (List.replicate d a) = q₀ := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
    · exact ⟨j.1 - i.1, by omega, by omega, hstep_cancel i.1 j.1 hlt hij_eq⟩
    · exact ⟨i.1 - j.1, by omega, by omega, hstep_cancel j.1 i.1 hgt hij_eq.symm⟩
  obtain ⟨d, hd1, hd5, hd_eq⟩ := hex_d
  have hcontra3 : A.eval q₀ (List.replicate 3 a) = q₀ → False := by
    intro h3
    have hR := R_bij_eval A hbij 3 v q₀
    rw [h3] at hR
    have h0 := congrFun hT3v q₀
    simp only [Pi.add_apply, Pi.zero_apply, hR] at h0
    exact hq0_ne (by linarith)
  have hcontra2 : A.eval q₀ (List.replicate 2 a) = q₀ → False := by
    intro h2
    let q₁ := A.step q₀ a
    have hq1_step : A.step q₁ a = q₀ := by rw [eval_rep2] at h2; exact h2
    have hq1_2 : A.eval q₁ (List.replicate 2 a) = q₁ := by
      rw [eval_rep2, hq1_step]
    have hR2_0 : R A (List.replicate 2 a) v q₀ = v q₀ := by
      have := R_bij_eval A hbij 2 v q₀; rwa [h2] at this
    have hR1_0 : R A [a] v q₀ = v q₁ := by
      have := R_bij_eval A hbij 1 v q₁; rw [eval_rep1, hq1_step] at this; exact this
    have hR2_1 : R A (List.replicate 2 a) v q₁ = v q₁ := by
      have := R_bij_eval A hbij 2 v q₁; rwa [hq1_2] at this
    have hR1_1 : R A [a] v q₁ = v q₀ := by
      have := R_bij_eval A hbij 1 v q₀; rw [eval_rep1] at this; exact this
    have e0 := congrFun hv_eq q₀
    have e1 := congrFun hv_eq q₁
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, hR2_0, hR1_0, hR2_1, hR1_1] at e0 e1
    exact hq0_ne (by linarith)
  rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5) with rfl | rfl | rfl | rfl | rfl
  · apply hcontra3
    rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, replicate_add_append, eval_append_aux,
      replicate_add_append, eval_append_aux, hd_eq, hd_eq, hd_eq]
  · exact hcontra2 hd_eq
  · exact hcontra3 hd_eq
  · apply hcontra2
    have := hord q₀
    rw [show (6 : ℕ) = 4 + 2 from rfl, replicate_add_append, eval_append_aux, hd_eq] at this
    exact this
  · apply hcontra3
    have h1 : A.eval q₀ (List.replicate 1 a) = q₀ := by
      have := hord q₀
      rw [show (6 : ℕ) = 5 + 1 from rfl, replicate_add_append, eval_append_aux, hd_eq] at this
      exact this
    rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, replicate_add_append, eval_append_aux,
      replicate_add_append, eval_append_aux, h1, h1, h1]

/-- **Order-6 Balanced Černý Theorem (No `Φ₆` Component):** -/
theorem order_six_no_phi6_balanced_cerny [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hord : ∀ q : Q, A.eval q (List.replicate 6 a) = q)
    (hbal : IsCycleBalanced A a)
    (hV6 : V₆ A a = ⊥) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  have hbij := hbal.1
  by_cases hn1 : Fintype.card Q = 1
  · apply cerny_of_n_extensible A hsync
    intro S hS1 hSlt; omega
  · have hn2 : 2 ≤ Fintype.card Q := by have := Fintype.card_pos (α := Q); omega
    obtain ⟨hsup, _, hinf2⟩ := order6_decomp A a hord hbal
    rw [hV6, sup_bot_eq] at hsup hinf2
    have hdim_sum : Module.finrank ℚ (K₀' A a) =
        Module.finrank ℚ (V₂ A a) + Module.finrank ℚ (V₃ A a) := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (V₂ A a) (V₃ A a)
      rw [hsup, hinf2, finrank_bot, add_zero] at h
      exact h
    by_cases hV3_bot : V₃ A a = ⊥
    · have hKeq : K₀' A a = V₂ A a := by rw [← hsup, hV3_bot, sup_bot_eq]
      apply antisymmetric_balanced_cerny A hsync a hbij
      intro b hb
      have hmem : ρ A [b] ∈ V₂ A a := by
        rw [← hKeq]; exact Submodule.subset_span ⟨b, 0, hb, rfl⟩
      exact eq_neg_of_add_eq_zero_left ((mem_V₂_iff A a _).mp hmem).2
    · have hV3_ge2 : 2 ≤ Module.finrank ℚ (V₃ A a) := two_le_finrank_V₃_of_bij A a hbij hV3_bot
      by_cases hV2_bot : V₂ A a = ⊥
      · have hKeq : K₀' A a = V₃ A a := by rw [← hsup, hV2_bot, bot_sup_eq]
        have hd2 : 2 ≤ Module.finrank ℚ (K₀' A a) := by omega
        apply cerny_of_n_extensible A hsync
        intro S hS1 hSlt
        let c : Fin 3 → ℚ := fun _ => 1 / 3
        have hc_pos : ∀ j : Fin 3, 0 < c j := fun _ => by simp [c]
        have hc_sum : ∑ j : Fin 3, c j = 1 := by
          rw [Fin.sum_univ_castSucc, Fin.sum_univ_two]; simp [c]; norm_num
        have hann : ∀ x ∈ K₀' A a, ∑ j : Fin 3, c j • R A (List.replicate j.1 a) x = 0 := by
          intro x hx
          have h3 := ((mem_V₃_iff A a x).mp (hKeq ▸ hx)).2
          ext q
          rw [sum_fin3_rat]
          have hq := congrFun h3 q
          simp only [c, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hq ⊢
          change (1 / 3 : ℚ) * R A [] x q + (1 / 3 : ℚ) * R A [a] x q +
            (1 / 3 : ℚ) * R A (List.replicate 2 a) x q = 0
          rw [R_nil]; linarith
        obtain ⟨w, hl, hg⟩ := master_balanced_version_A A hsync a hbij 2 (by omega) c hc_pos hc_sum
          hann hS1 hSlt
        exact ⟨w, by omega, hg⟩
      · have hV2_ge1 : 1 ≤ Module.finrank ℚ (V₂ A a) := ne_bot_implies_one_le_finrank hV2_bot
        have hd3 : 3 ≤ Module.finrank ℚ (K₀' A a) := by omega
        apply cerny_of_n_extensible A hsync
        intro S hS1 hSlt
        let c : Fin 4 → ℚ := fun j =>
          if j.1 = 0 then 1 / 6 else if j.1 = 1 then 1 / 3 else if j.1 = 2 then 1 / 3 else 1 / 6
        have hc_pos : ∀ j : Fin 4, 0 < c j := by
          intro j
          rcases (by omega : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 ∨ j.1 = 3) with h | h | h | h
          · rw [show j = 0 from Fin.ext h]; norm_num [c]
          · rw [show j = 1 from Fin.ext h]; norm_num [c]
          · rw [show j = 2 from Fin.ext h]; norm_num [c]
          · rw [show j = 3 from Fin.ext h]; norm_num [c]
        have hc_sum : ∑ j : Fin 4, c j = 1 := by
          rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_two]
          simp [c]; norm_num
        have hann : ∀ x ∈ K₀' A a, ∑ j : Fin 4, c j • R A (List.replicate j.1 a) x = 0 := by
          intro x hx
          rcases Submodule.mem_sup.mp (hsup.symm ▸ hx) with ⟨v₂, hv₂, v₃, hv₃, rfl⟩
          have h2_0 := ((mem_V₂_iff A a v₂).mp hv₂).2
          have h3_0 := ((mem_V₃_iff A a v₃).mp hv₃).2
          have h2_1 : R A (List.replicate 2 a) v₂ + R A [a] v₂ = 0 := by
            have := congrArg (R A [a]) h2_0
            rwa [map_add, map_zero, R_a_a] at this
          have h2_2 : R A (List.replicate 3 a) v₂ + R A (List.replicate 2 a) v₂ = 0 := by
            have := congrArg (R A [a]) h2_1
            rwa [map_add, map_zero, R_a_rep, R_a_a] at this
          have h3_1 : R A (List.replicate 3 a) v₃ + R A (List.replicate 2 a) v₃ + R A [a] v₃ = 0 := by
            have := congrArg (R A [a]) h3_0
            rwa [map_add, map_add, map_zero, R_a_rep, R_a_a] at this
          ext q
          rw [sum_fin4_rat]
          have e20 := congrFun h2_0 q; have e21 := congrFun h2_1 q; have e22 := congrFun h2_2 q
          have e30 := congrFun h3_0 q; have e31 := congrFun h3_1 q
          have hc0 : c 0 = 1 / 6 := by simp [c]
          have hc1 : c 1 = 1 / 3 := by simp [c]
          have hc2 : c 2 = 1 / 3 := by simp [c]
          have hc3 : c 3 = 1 / 6 := by simp [c]
          simp only [map_add, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
            hc0, hc1, hc2, hc3] at e20 e21 e22 e30 e31 ⊢
          change (1 / 6 : ℚ) * (R A [] v₂ q + R A [] v₃ q) +
            (1 / 3 : ℚ) * (R A [a] v₂ q + R A [a] v₃ q) +
            (1 / 3 : ℚ) * (R A (List.replicate 2 a) v₂ q + R A (List.replicate 2 a) v₃ q) +
            (1 / 6 : ℚ) * (R A (List.replicate 3 a) v₂ q + R A (List.replicate 3 a) v₃ q) = 0
          rw [R_nil, R_nil]
          linarith
        obtain ⟨w, hl, hg⟩ := master_balanced_version_A A hsync a hbij 3 (by omega) c hc_pos hc_sum
          hann hS1 hSlt
        exact ⟨w, by omega, hg⟩

/-- **Order-6 Balanced Černý Theorem (`Φ₃ ⊕ Φ₆` and full-support cases — resolves `ex4`'s class):** -/
theorem order_six_phi3_phi6_balanced_cerny [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hord : ∀ q : Q, A.eval q (List.replicate 6 a) = q)
    (hbal : IsCycleBalanced A a)
    (hV3 : V₃ A a ≠ ⊥) (hV6 : V₆ A a ≠ ⊥) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  have hbij := hbal.1
  obtain ⟨hsup, hinf36, hinf2⟩ := order6_decomp A a hord hbal
  have hdim36 : Module.finrank ℚ ↥(V₃ A a ⊔ V₆ A a) =
      Module.finrank ℚ (V₃ A a) + Module.finrank ℚ (V₆ A a) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (V₃ A a) (V₆ A a)
    rw [hinf36, finrank_bot, add_zero] at h
    exact h
  have hdim_sum : Module.finrank ℚ (K₀' A a) =
      Module.finrank ℚ (V₂ A a) + Module.finrank ℚ (V₃ A a) + Module.finrank ℚ (V₆ A a) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (V₂ A a) (V₃ A a ⊔ V₆ A a)
    rw [hsup, hinf2, finrank_bot, add_zero, hdim36] at h
    omega
  have hV3_ge2 : 2 ≤ Module.finrank ℚ (V₃ A a) := two_le_finrank_V₃_of_bij A a hbij hV3
  have hV6_ge2 : 2 ≤ Module.finrank ℚ (V₆ A a) := two_le_finrank_V₆_of_bij A a hbij hV6
  have hd4 : 4 ≤ Module.finrank ℚ (K₀' A a) := by omega
  let c : Fin 6 → ℚ := fun _ => 1 / 6
  have hc_pos : ∀ j : Fin 6, 0 < c j := fun _ => by simp [c]
  have hc_sum : ∑ j : Fin 6, c j = 1 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
      Fin.sum_univ_castSucc, Fin.sum_univ_two]
    simp [c]; norm_num
  have hann : ∀ x ∈ K₀' A a, ∑ j : Fin 6, c j • R A (List.replicate j.1 a) x = 0 := by
    intro x hx
    simpa [c] using sum_orbit_annihilates_K₀' A a 6 (by omega) hord hbal x hx
  by_cases hd5 : 5 ≤ Module.finrank ℚ (K₀' A a)
  · apply cerny_of_n_extensible A hsync
    intro S hS1 hSlt
    obtain ⟨w, hl, hg⟩ := master_balanced_version_A A hsync a hbij 5 (by omega) c hc_pos hc_sum
      hann hS1 hSlt
    exact ⟨w, by omega, hg⟩
  · have hd_eq4 : Module.finrank ℚ (K₀' A a) = 4 := by omega
    obtain ⟨q₀, hinj⟩ := exists_six_cycle_of_V₆_ne_bot A a hbij hord hV6
    have hn6 : 6 ≤ Fintype.card Q := by
      have := Fintype.card_le_of_injective _ hinj
      rwa [Fintype.card_fin] at this
    by_cases hn_eq6 : Fintype.card Q = 6
    · exact dubuc_of_distinct_orbit A hsync a hbij 6 hn_eq6 hord q₀ hinj
    · have hn7 : 7 ≤ Fintype.card Q := by omega
      exact master_balanced_version_A_excess_one A hsync a hbij 5 (by omega) c hc_pos hc_sum
        hann hn7 (by omega) (by omega)

end OrderSixBalanced

end Cerny.AmortizedBalanced