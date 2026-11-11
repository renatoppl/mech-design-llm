import TokenAuctions.Defs
import TokenAuctions.VCG
import TokenAuctions.StableSampling

set_option maxHeartbeats 4000000

/-!
# Second-Price Token Auctions: Expected Payments, Closed Form & VCG Comparison

This module formalizes Section 5.2 (Proposition 5.6, Footnotes 7 & 8, Corollary 5.7, Remark 5.8)
and Appendix D.2 of *Mechanism Design for Large Language Models: Token Auctions with Proxy Bidders*.

## Main Results
- `prop_5_6_second_price_payment`: Expected payment under any stable sampling implementation `σ` of
  a robust-monotone curve `q : ℚ₊ → Δ(T)` equals the sampler-independent Myerson total-variation
  integral `(1/2) ∫_0^{b_i} [‖q(b') - p_i‖₁ - ‖q(b_i) - p_i‖₁] db'`, together with per-token
  charging identities on `T⁺`/`T⁻` and invariance across antitone real extensions (Proposition 5.6,
  Appendix D.2, and Footnote 8).
- `prop_5_6_token_pricing_decomp`: Connects Section 2.2's per-token conditional pricing function
  `PricingRule` (`myersonTokenPricing`) and `expectedPaymentOfPricing` directly to Proposition 5.6's
  per-token critical-price expectations and `myersonTVPayment`.
- `fn_7_second_price_payment_monotone`: Payment monotonicity of `myersonTVPayment` on positive
  bids `b_i > 0`, and on all of `ℚ₊` when `q` is right-continuous at `0` (Footnote 7).
- `cor_5_7_linear_closed_form_with_platform`: Closed-form expected second-price payment, payment
  admissibility, and payment monotonicity for the linear aggregation rule `q_KL` with platform
  bidder `(b_0, p_0)` (Corollary 5.7).
- `cor_5_7_linear_closed_form_general`: Robust monotonicity, payment admissibility, payment
  monotonicity (on positive bids and on all of `ℚ₊` when `B_{-i} > 0`), closed-form expected
  second-price payment, and `[0, 1]²` stable-sampler realization for the general linear aggregation
  rule without platform bidder (`b_0 = 0`), covering both `B_{-i} > 0` and `B_{-i} = 0`
  (Corollary 5.7).
- `cor_5_7_right_continuity_at_zero`: Appendix D.2 representation in terms of `D = ‖q^*_{-i} - p_i‖₁`
  and right-continuity limit `z_i(b_i, b_{-i}, p) → 0 = z_i(0, b_{-i}, p)` as `b_i → 0⁺` directly
  for `linearSecondPriceClosedFormWithPlatform` (Corollary 5.7 & Appendix D.2).
- `cor_5_7_linear_stable_sampler_payment`: End-to-end synthesis of Remark 5.2, Theorem 5.5,
  Proposition 5.6, and Corollary 5.7 — existence of a stable sampler on `[0, 1]²` for `q_KL` whose
  expected second-price payment equals `linearSecondPriceClosedFormWithPlatform`.
- `rem_5_8_zero_payment_iff` and `rem_5_8_vcg_ne_second_price`: Supplementary zero-payment
  equivalence (`z_i = 0 ↔ q_KL(b, p) = q^*_{-i}` for both forward-KL VCG and linear second-price
  payments) alongside an explicit full-support instance proving the two payment rules do not
  coincide in general (Remark 5.8).
-/

namespace TokenAuctions

open scoped BigOperators
open Classical MeasureTheory

noncomputable section

/-! ## Internal Riemann-Grid & Monotone-Extension Helpers -/

private lemma h_grid : ∀ (b_i : Bid) (f : ℝ → ℝ),
    0 < b_i →
    AntitoneOn f (Set.Icc 0 (b_i : ℝ)) →
    ∀ (N : ℕ), 1 ≤ N →
      let g : ℕ → Bid := fun k => b_i * (k : Bid) / (N : Bid)
      (∀ k ≤ N, g k ≤ b_i) ∧
      ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, f ((g (k + 1)) : ℝ)) ≤
        ∫ x in (0 : ℝ)..(b_i : ℝ), f x ∧
      ∫ x in (0 : ℝ)..(b_i : ℝ), f x ≤
        ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, f ((g k) : ℝ)) ∧
      ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, f ((g k) : ℝ)) -
        ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, f ((g (k + 1)) : ℝ)) =
        ((b_i : ℝ) / (N : ℝ)) * (f 0 - f (b_i : ℝ)) := by
  intro b_i f hbi hf N hN
  dsimp only
  set g : ℕ → Bid := fun k => b_i * (k : Bid) / (N : Bid)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hbi_pos : (0 : ℝ) < (b_i : ℝ) := by exact_mod_cast hbi
  have hg_real : ∀ k : ℕ, ((g k) : ℝ) = (b_i : ℝ) * (k : ℝ) / (N : ℝ) := by
    intro k
    simp [g, NNRat.cast_div, NNRat.cast_mul, NNRat.cast_natCast]
  have hg0 : ((g 0) : ℝ) = 0 := by simp [hg_real]
  have hgN : ((g N) : ℝ) = (b_i : ℝ) := by
    rw [hg_real, mul_div_assoc, div_self hN_ne, mul_one]
  have hg_le : ∀ k ≤ N, g k ≤ b_i := by
    intro k hk
    rw [← @NNRat.cast_le ℝ, hg_real]
    have hk_le : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    have hdiv : (k : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hN_pos).mpr hk_le
    calc (b_i : ℝ) * (k : ℝ) / (N : ℝ)
        = (b_i : ℝ) * ((k : ℝ) / (N : ℝ)) := by ring
      _ ≤ (b_i : ℝ) * 1 := mul_le_mul_of_nonneg_left hdiv (le_of_lt hbi_pos)
      _ = (b_i : ℝ) := mul_one _
  have hg_step : ∀ k : ℕ, ((g (k + 1)) : ℝ) - ((g k) : ℝ) = (b_i : ℝ) / (N : ℝ) := by
    intro k
    rw [hg_real, hg_real]
    push_cast
    ring
  have hg_mono : ∀ k : ℕ, ((g k) : ℝ) ≤ ((g (k + 1)) : ℝ) := by
    intro k
    have hdiff := hg_step k
    have hpos : 0 ≤ (b_i : ℝ) / (N : ℝ) := div_nonneg (le_of_lt hbi_pos) (le_of_lt hN_pos)
    linarith
  have hg_in_Icc : ∀ k ≤ N, ((g k) : ℝ) ∈ Set.Icc 0 (b_i : ℝ) := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    exact_mod_cast hg_le k hk
  have hf_int_sub : ∀ k < N, IntervalIntegrable f volume ((g k) : ℝ) ((g (k + 1)) : ℝ) := by
    intro k hk
    apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le (hg_mono k)]
    exact hf.mono (Set.Icc_subset_Icc (hg_in_Icc k (Nat.le_of_lt hk)).1 (hg_in_Icc (k + 1) hk).2)
  have hsum_adj : ∑ k ∈ Finset.range N, ∫ x in ((g k) : ℝ)..((g (k + 1)) : ℝ), f x =
      ∫ x in (0 : ℝ)..(b_i : ℝ), f x := by
    have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) hf_int_sub
    rwa [hg0, hgN] at hadj
  have h_sub_lo : ∀ k ∈ Finset.range N,
      ((b_i : ℝ) / (N : ℝ)) * f ((g (k + 1)) : ℝ) ≤ ∫ x in ((g k) : ℝ)..((g (k + 1)) : ℝ), f x := by
    intro k hk
    have hk_lt : k < N := Finset.mem_range.mp hk
    have hsub : Set.Icc ((g k) : ℝ) ((g (k + 1)) : ℝ) ⊆ Set.Icc 0 (b_i : ℝ) :=
      Set.Icc_subset_Icc (hg_in_Icc k (Nat.le_of_lt hk_lt)).1 (hg_in_Icc (k + 1) hk_lt).2
    have hmono := intervalIntegral.integral_mono_on (hg_mono k)
      (intervalIntegral.intervalIntegrable_const) (hf_int_sub k hk_lt)
      (fun x hx => hf (hsub hx) (hg_in_Icc (k + 1) hk_lt) hx.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, hg_step k] at hmono
    exact hmono
  have h_sub_hi : ∀ k ∈ Finset.range N,
      ∫ x in ((g k) : ℝ)..((g (k + 1)) : ℝ), f x ≤ ((b_i : ℝ) / (N : ℝ)) * f ((g k) : ℝ) := by
    intro k hk
    have hk_lt : k < N := Finset.mem_range.mp hk
    have hsub : Set.Icc ((g k) : ℝ) ((g (k + 1)) : ℝ) ⊆ Set.Icc 0 (b_i : ℝ) :=
      Set.Icc_subset_Icc (hg_in_Icc k (Nat.le_of_lt hk_lt)).1 (hg_in_Icc (k + 1) hk_lt).2
    have hmono := intervalIntegral.integral_mono_on (hg_mono k)
      (hf_int_sub k hk_lt) (intervalIntegral.intervalIntegrable_const)
      (fun x hx => hf (hg_in_Icc k (Nat.le_of_lt hk_lt)) (hsub hx) hx.1)
    rw [intervalIntegral.integral_const, smul_eq_mul, hg_step k] at hmono
    exact hmono
  refine ⟨hg_le, ?_, ?_, ?_⟩
  · calc ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, f ((g (k + 1)) : ℝ))
        = ∑ k ∈ Finset.range N, ((b_i : ℝ) / (N : ℝ)) * f ((g (k + 1)) : ℝ) := Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ Finset.range N, ∫ x in ((g k) : ℝ)..((g (k + 1)) : ℝ), f x := Finset.sum_le_sum h_sub_lo
      _ = ∫ x in (0 : ℝ)..(b_i : ℝ), f x := hsum_adj
  · calc ∫ x in (0 : ℝ)..(b_i : ℝ), f x
        = ∑ k ∈ Finset.range N, ∫ x in ((g k) : ℝ)..((g (k + 1)) : ℝ), f x := hsum_adj.symm
      _ ≤ ∑ k ∈ Finset.range N, ((b_i : ℝ) / (N : ℝ)) * f ((g k) : ℝ) := Finset.sum_le_sum h_sub_hi
      _ = ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, f ((g k) : ℝ)) := (Finset.mul_sum _ _ _).symm
  · have htel : (∑ k ∈ Finset.range N, f ((g k) : ℝ)) - (∑ k ∈ Finset.range N, f ((g (k + 1)) : ℝ)) =
        f 0 - f (b_i : ℝ) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_range_sub' (fun k => f ((g k) : ℝ)) N, hg0, hgN]
    calc ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, f ((g k) : ℝ)) -
          ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, f ((g (k + 1)) : ℝ))
        = ((b_i : ℝ) / (N : ℝ)) * ((∑ k ∈ Finset.range N, f ((g k) : ℝ)) -
            (∑ k ∈ Finset.range N, f ((g (k + 1)) : ℝ))) := by ring
      _ = ((b_i : ℝ) / (N : ℝ)) * (f 0 - f (b_i : ℝ)) := by rw [htel]

private lemma h_s1 : ∀ (T : Type) [Fintype T] [DecidableEq T] (q : Bid → TokenDist T) (target : TokenDist T),
    IsSingleAgentRobustMonotone q target →
    (∀ t ∈ undersampledTokens q target,
      MonotoneOn (tokenProbUnderExt q t) (Set.Ici 0) ∧
      (∀ b' : Bid, tokenProbUnderExt q t (b' : ℝ) = (q b').prob t)) ∧
    (AntitoneOn (l1DistRealExt q target) (Set.Ici 0) ∧
      (∀ b' : Bid, l1DistRealExt q target (b' : ℝ) = l1Dist (q b') target)) ∧
    (∀ b_i : Bid,
      0 ≤ myersonTVPayment q target b_i ∧
      (∀ G : ℝ → ℝ,
        AntitoneOn G (Set.Icc 0 (b_i : ℝ)) →
        (∀ b' : Bid, b' ≤ b_i → G (b' : ℝ) = l1Dist (q b') target) →
          IntervalIntegrable (fun x => G x - l1Dist (q b_i) target) volume 0 (b_i : ℝ) ∧
          (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..(b_i : ℝ), (G x - l1Dist (q b_i) target) =
            myersonTVPayment q target b_i) ∧
      myersonTVPayment q target b_i =
        ∑ t : T, (if t ∈ undersampledTokens q target then
          ∫ x in (0 : ℝ)..(b_i : ℝ), ((q b_i).prob t - tokenProbUnderExt q t x) else 0)) := by
  intro T _ _ q target hq
  have hCoord := (lem_5_3_monotone_coord_iff T q target).mp hq
  have h_under_le : ∀ t ∈ undersampledTokens q target, ∀ b : Bid, (q b).prob t ≤ target.prob t :=
    fun t ht => (hCoord.1 t ht).1
  have h_under_mono : ∀ t ∈ undersampledTokens q target, ∀ b₁ b₂ : Bid, b₁ ≤ b₂ →
      (q b₁).prob t ≤ (q b₂).prob t :=
    fun t ht _ _ hb => (hCoord.1 t ht).2 hb
  have h_over_ge : ∀ t : T, t ∉ undersampledTokens q target → ∀ b : Bid, target.prob t ≤ (q b).prob t :=
    fun t ht => (hCoord.2 t (not_le.mp (show ¬((q 0).prob t ≤ target.prob t) from ht))).1
  have h_l1_anti : ∀ b₁ b₂ : Bid, b₁ ≤ b₂ → l1Dist (q b₂) target ≤ l1Dist (q b₁) target := by
    intro b₁ b₂ hb
    exact Finset.sum_le_sum (fun t _ => (hq b₂ b₁ hb).1 t)
  have h_l1_decomp : ∀ b : Bid,
      l1Dist (q b) target =
        2 * ∑ t : T, (if t ∈ undersampledTokens q target then target.prob t - (q b).prob t else 0) := by
    intro b
    have hpt : ∀ t : T,
        |(q b).prob t - target.prob t| - ((q b).prob t - target.prob t) =
          if t ∈ undersampledTokens q target then 2 * (target.prob t - (q b).prob t) else 0 := by
      intro t
      by_cases ht : t ∈ undersampledTokens q target
      · simp only [ht, ↓reduceIte]
        rw [abs_of_nonpos (by linarith [h_under_le t ht b])]
        ring
      · simp only [ht, ↓reduceIte]
        rw [abs_of_nonneg (by linarith [h_over_ge t ht b])]
        ring
    have hsum_diff : ∑ t : T, ((q b).prob t - target.prob t) = 0 := by
      rw [Finset.sum_sub_distrib, (q b).sum_eq_one, target.sum_eq_one, sub_self]
    calc l1Dist (q b) target
        = (∑ t : T, |(q b).prob t - target.prob t|) - ∑ t : T, ((q b).prob t - target.prob t) := by
            rw [l1Dist, hsum_diff, sub_zero]
      _ = ∑ t : T, (|(q b).prob t - target.prob t| - ((q b).prob t - target.prob t)) :=
            (Finset.sum_sub_distrib _ _).symm
      _ = ∑ t : T, (if t ∈ undersampledTokens q target then 2 * (target.prob t - (q b).prob t) else 0) :=
            Finset.sum_congr rfl (fun t _ => hpt t)
      _ = 2 * ∑ t : T, (if t ∈ undersampledTokens q target then target.prob t - (q b).prob t else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            split_ifs <;> ring
  have h_tokenExt : ∀ t ∈ undersampledTokens q target,
      MonotoneOn (tokenProbUnderExt q t) (Set.Ici 0) ∧
      (∀ b' : Bid, tokenProbUnderExt q t (b' : ℝ) = (q b').prob t) := by
    intro t ht
    have hbdd : ∀ x : ℝ, BddAbove ((fun b : Bid => (q b).prob t) '' {b : Bid | (b : ℝ) ≤ x}) := by
      intro x
      refine ⟨target.prob t, ?_⟩
      rintro _ ⟨b, _, rfl⟩
      exact h_under_le t ht b
    have hne : ∀ x : ℝ, 0 ≤ x → ((fun b : Bid => (q b).prob t) '' {b : Bid | (b : ℝ) ≤ x}).Nonempty := by
      intro x hx
      exact ⟨(q 0).prob t, 0, by simpa using hx, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      have hx0 : ¬(x < 0) := not_lt.mpr hx
      have hy0 : ¬(y < 0) := not_lt.mpr hy
      simp only [tokenProbUnderExt, hx0, hy0, ↓reduceIte]
      exact csSup_le_csSup (hbdd y) (hne x hx)
        (Set.image_mono (fun b (hb : (b : ℝ) ≤ x) => le_trans hb hxy))
    · intro b'
      have hb0 : ¬((b' : ℝ) < 0) := not_lt.mpr (by positivity)
      simp only [tokenProbUnderExt, hb0, ↓reduceIte]
      apply le_antisymm
      · refine csSup_le (hne (b' : ℝ) (by positivity)) ?_
        rintro _ ⟨b, hb, rfl⟩
        exact h_under_mono t ht b b' (by exact_mod_cast hb)
      · exact le_csSup (hbdd (b' : ℝ)) ⟨b', le_refl (b' : ℝ), rfl⟩
  have h_l1Ext : AntitoneOn (l1DistRealExt q target) (Set.Ici 0) ∧
      (∀ b' : Bid, l1DistRealExt q target (b' : ℝ) = l1Dist (q b') target) := by
    have hbdd : ∀ x : ℝ, BddBelow ((fun b : Bid => l1Dist (q b) target) '' {b : Bid | (b : ℝ) ≤ x}) := by
      intro x
      refine ⟨0, ?_⟩
      rintro _ ⟨b, _, rfl⟩
      exact Finset.sum_nonneg (fun t _ => abs_nonneg _)
    have hne : ∀ x : ℝ, 0 ≤ x → ((fun b : Bid => l1Dist (q b) target) '' {b : Bid | (b : ℝ) ≤ x}).Nonempty := by
      intro x hx
      exact ⟨l1Dist (q 0) target, 0, by simpa using hx, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      have hx0 : ¬(x < 0) := not_lt.mpr hx
      have hy0 : ¬(y < 0) := not_lt.mpr hy
      simp only [l1DistRealExt, hx0, hy0, ↓reduceIte]
      exact csInf_le_csInf (hbdd y) (hne x hx)
        (Set.image_mono (fun b (hb : (b : ℝ) ≤ x) => le_trans hb hxy))
    · intro b'
      have hb0 : ¬((b' : ℝ) < 0) := not_lt.mpr (by positivity)
      simp only [l1DistRealExt, hb0, ↓reduceIte]
      apply le_antisymm
      · exact csInf_le (hbdd (b' : ℝ)) ⟨b', le_refl (b' : ℝ), rfl⟩
      · refine le_csInf (hne (b' : ℝ) (by positivity)) ?_
        rintro _ ⟨b, hb, rfl⟩
        exact h_l1_anti b b' (by exact_mod_cast hb)
  refine ⟨h_tokenExt, h_l1Ext, ?_⟩
  intro b_i
  have hbi_nonneg : (0 : ℝ) ≤ (b_i : ℝ) := by positivity
  have h_nonneg : 0 ≤ myersonTVPayment q target b_i := by
    unfold myersonTVPayment
    apply mul_nonneg (by norm_num)
    apply intervalIntegral.integral_nonneg hbi_nonneg
    intro x hx
    have hge : l1DistRealExt q target (b_i : ℝ) ≤ l1DistRealExt q target x :=
      h_l1Ext.1 hx.1 hbi_nonneg hx.2
    rw [h_l1Ext.2 b_i] at hge
    linarith
  have h_G_inv : ∀ G : ℝ → ℝ,
      AntitoneOn G (Set.Icc 0 (b_i : ℝ)) →
      (∀ b' : Bid, b' ≤ b_i → G (b' : ℝ) = l1Dist (q b') target) →
        IntervalIntegrable (fun x => G x - l1Dist (q b_i) target) volume 0 (b_i : ℝ) ∧
        (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..(b_i : ℝ), (G x - l1Dist (q b_i) target) =
          myersonTVPayment q target b_i := by
    intro G hG_anti hG_rat
    set c := l1Dist (q b_i) target
    have hf1_anti : AntitoneOn (fun x => G x - c) (Set.Icc 0 (b_i : ℝ)) :=
      fun x hx y hy hxy => sub_le_sub_right (hG_anti hx hy hxy) c
    have hf2_anti : AntitoneOn (fun x => l1DistRealExt q target x - c) (Set.Icc 0 (b_i : ℝ)) :=
      fun x hx y hy hxy => sub_le_sub_right (h_l1Ext.1 hx.1 hy.1 hxy) c
    have hf1_int : IntervalIntegrable (fun x => G x - c) volume 0 (b_i : ℝ) := by
      apply AntitoneOn.intervalIntegrable
      rwa [Set.uIcc_of_le hbi_nonneg]
    refine ⟨hf1_int, ?_⟩
    unfold myersonTVPayment
    congr 1
    rcases eq_or_lt_of_le (zero_le b_i) with rfl | hbi_pos
    · simp
    · by_contra hne_int
      set I1 := ∫ x in (0 : ℝ)..(b_i : ℝ), (G x - c)
      set I2 := ∫ x in (0 : ℝ)..(b_i : ℝ), (l1DistRealExt q target x - c)
      have hdiff_pos : 0 < |I1 - I2| := abs_pos.mpr (sub_ne_zero.mpr hne_int)
      set C := (b_i : ℝ) * (l1Dist (q 0) target - c)
      obtain ⟨N, hN_gt⟩ := exists_nat_gt (C / |I1 - I2| + 1)
      have hC_nonneg : 0 ≤ C :=
        mul_nonneg hbi_nonneg (sub_nonneg.mpr (h_l1_anti 0 b_i (zero_le b_i)))
      have hN_ge1 : 1 ≤ N := by
        have : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hN_gt
        have : 0 < N := by exact_mod_cast this
        omega
      obtain ⟨hg_le, hlo1, hhi1, hgap1⟩ := h_grid b_i (fun x => G x - c) hbi_pos hf1_anti N hN_ge1
      obtain ⟨_, hlo2, hhi2, _⟩ := h_grid b_i (fun x => l1DistRealExt q target x - c) hbi_pos hf2_anti N hN_ge1
      set g : ℕ → Bid := fun k => b_i * (k : Bid) / (N : Bid)
      have hsum_eq1 : ∑ k ∈ Finset.range N, (G ((g k) : ℝ) - c) =
          ∑ k ∈ Finset.range N, (l1DistRealExt q target ((g k) : ℝ) - c) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk_le : k ≤ N := Nat.le_of_lt (Finset.mem_range.mp hk)
        rw [hG_rat (g k) (hg_le k hk_le), h_l1Ext.2 (g k)]
      have hsum_eq2 : ∑ k ∈ Finset.range N, (G ((g (k + 1)) : ℝ) - c) =
          ∑ k ∈ Finset.range N, (l1DistRealExt q target ((g (k + 1)) : ℝ) - c) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk_le : k + 1 ≤ N := Finset.mem_range.mp hk
        rw [hG_rat (g (k + 1)) (hg_le (k + 1) hk_le), h_l1Ext.2 (g (k + 1))]
      rw [← hsum_eq2] at hlo2
      rw [← hsum_eq1] at hhi2
      have hG0 : G 0 - c - (G (b_i : ℝ) - c) = l1Dist (q 0) target - c := by
        have h0 : G ((0 : Bid) : ℝ) = l1Dist (q 0) target := hG_rat 0 (zero_le b_i)
        have hbi_eq : G (b_i : ℝ) = c := hG_rat b_i le_rfl
        simp only [NNRat.cast_zero] at h0
        linarith
      have habs_le : |I1 - I2| ≤ C / (N : ℝ) := by
        rw [abs_le]
        have hgap' : ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, (G ((g k) : ℝ) - c)) -
            ((b_i : ℝ) / (N : ℝ)) * (∑ k ∈ Finset.range N, (G ((g (k + 1)) : ℝ) - c)) = C / (N : ℝ) := by
          rw [hgap1, hG0]
          ring
        constructor <;> linarith
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN_ge1)
      have hlt_C : C / (N : ℝ) < |I1 - I2| := by
        rw [div_lt_iff₀ hN_pos]
        have h1 : C / |I1 - I2| < (N : ℝ) := by linarith
        have h2 := (div_lt_iff₀ hdiff_pos).mp h1
        linarith
      linarith
  have h_sum_T : myersonTVPayment q target b_i =
      ∑ t : T, (if t ∈ undersampledTokens q target then
        ∫ x in (0 : ℝ)..(b_i : ℝ), ((q b_i).prob t - tokenProbUnderExt q t x) else 0) := by
    set H : ℝ → ℝ := fun x =>
      2 * ∑ t : T, (if t ∈ undersampledTokens q target then target.prob t - tokenProbUnderExt q t x else 0)
    have hH_anti : AntitoneOn H (Set.Icc 0 (b_i : ℝ)) := by
      intro x hx y hy hxy
      dsimp only [H]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      refine Finset.sum_le_sum (fun t _ => ?_)
      split_ifs with ht
      · exact sub_le_sub_left ((h_tokenExt t ht).1 hx.1 hy.1 hxy) _
      · exact le_rfl
    have hH_rat : ∀ b' : Bid, b' ≤ b_i → H (b' : ℝ) = l1Dist (q b') target := by
      intro b' _
      dsimp only [H]
      rw [h_l1_decomp b']
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs with ht
      · rw [(h_tokenExt t ht).2 b']
      · rfl
    have hH_eq := (h_G_inv H hH_anti hH_rat).2.symm
    rw [hH_eq, ← hH_rat b_i le_rfl]
    have h_integrand : ∀ x : ℝ,
        (1 / 2 : ℝ) * (H x - H (b_i : ℝ)) =
          ∑ t : T, (if t ∈ undersampledTokens q target then (q b_i).prob t - tokenProbUnderExt q t x else 0) := by
      intro x
      dsimp only [H]
      have : (1 / 2 : ℝ) *
          (2 * ∑ t : T, (if t ∈ undersampledTokens q target then target.prob t - tokenProbUnderExt q t x else 0) -
           2 * ∑ t : T, (if t ∈ undersampledTokens q target then target.prob t - tokenProbUnderExt q t (b_i : ℝ) else 0)) =
          (∑ t : T, (if t ∈ undersampledTokens q target then target.prob t - tokenProbUnderExt q t x else 0)) -
          (∑ t : T, (if t ∈ undersampledTokens q target then target.prob t - tokenProbUnderExt q t (b_i : ℝ) else 0)) := by ring
      rw [this, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs with ht
      · rw [(h_tokenExt t ht).2 b_i]; ring
      · ring
    have h_term_int : ∀ t ∈ (Finset.univ : Finset T),
        IntervalIntegrable
          (fun x => if t ∈ undersampledTokens q target then (q b_i).prob t - tokenProbUnderExt q t x else 0)
          volume 0 (b_i : ℝ) := by
      intro t _
      by_cases ht : t ∈ undersampledTokens q target
      · simp only [ht, ↓reduceIte]
        apply AntitoneOn.intervalIntegrable
        rw [Set.uIcc_of_le hbi_nonneg]
        intro x hx y hy hxy
        exact sub_le_sub_left ((h_tokenExt t ht).1 hx.1 hy.1 hxy) _
      · simp only [ht, ↓reduceIte]
        exact intervalIntegral.intervalIntegrable_const
    calc (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..(b_i : ℝ), (H x - H (b_i : ℝ))
        = ∫ x in (0 : ℝ)..(b_i : ℝ), (1 / 2 : ℝ) * (H x - H (b_i : ℝ)) :=
            (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ x in (0 : ℝ)..(b_i : ℝ),
            ∑ t : T, (if t ∈ undersampledTokens q target then (q b_i).prob t - tokenProbUnderExt q t x else 0) := by
            congr 1; ext x; exact h_integrand x
      _ = ∑ t : T, ∫ x in (0 : ℝ)..(b_i : ℝ),
            (if t ∈ undersampledTokens q target then (q b_i).prob t - tokenProbUnderExt q t x else 0) :=
            intervalIntegral.integral_finset_sum h_term_int
      _ = ∑ t : T, (if t ∈ undersampledTokens q target then
            ∫ x in (0 : ℝ)..(b_i : ℝ), ((q b_i).prob t - tokenProbUnderExt q t x) else 0) := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            split_ifs <;> simp
  exact ⟨h_nonneg, h_G_inv, h_sum_T⟩

private lemma h_s2 : ∀ (T : Type) [Fintype T] [DecidableEq T] (q : Bid → TokenDist T) (target : TokenDist T),
    IsSingleAgentRobustMonotone q target →
    ∀ (R : Type) [MeasurableSpace R] (μ : Measure R) [IsProbabilityMeasure μ] (σ : Bid → R → T),
      IsStableSampler μ q target σ →
        secondPriceExpectedPayment μ σ 0 = 0 ∧
        (∀ b_i : Bid,
          Integrable (secondPriceCharge σ b_i) μ ∧
          0 ≤ secondPriceExpectedPayment μ σ b_i ∧
          (∀ t ∈ oversampledTokens q target,
            ∫ r, (if σ b_i r = t then secondPriceCharge σ b_i r else 0) ∂μ = 0) ∧
          (∀ t ∈ undersampledTokens q target,
            IntervalIntegrable (fun x => (q b_i).prob t - tokenProbUnderExt q t x) volume 0 (b_i : ℝ) ∧
            ∫ r, (if σ b_i r = t then secondPriceCharge σ b_i r else 0) ∂μ =
              ∫ x in (0 : ℝ)..(b_i : ℝ), ((q b_i).prob t - tokenProbUnderExt q t x)) ∧
          secondPriceExpectedPayment μ σ b_i =
            ∑ t : T, (if t ∈ undersampledTokens q target then
              ∫ x in (0 : ℝ)..(b_i : ℝ), ((q b_i).prob t - tokenProbUnderExt q t x) else 0)) := by
  intro T _ _ q target hq R _ μ _ σ hσ
  haveI : Countable Bid := Function.Injective.countable NNRat.coe_injective
  have h_sum_lt : ∀ (N M : ℕ), M ≤ N →
      ∑ k ∈ Finset.range N, (if k < M then (1 : ℝ) else 0) = (M : ℝ) := by
    intro N M hMN
    rw [← Finset.sum_filter]
    have hfilt : (Finset.range N).filter (· < M) = Finset.range M := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilt, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have h_zero : secondPriceExpectedPayment μ σ 0 = 0 := by
    have h0 : ∀ r : R, secondPriceCharge σ 0 r = 0 := by
      intro r
      simp [secondPriceCharge, samplerWinningSet]
    simp [secondPriceExpectedPayment, h0]
  refine ⟨h_zero, ?_⟩
  intro b_i
  set Win : Bid → Set R := fun b => {r : R | b ∈ samplerWinningSet σ r}
  have hWin_meas : ∀ b : Bid, MeasurableSet (Win b) := by
    intro b
    have hcompl : (Win b)ᶜ = ⋃ t : T, ({r : R | σ b r = t} ∩ {r : R | σ 0 r = t}) := by
      ext r
      simp only [Win, samplerWinningSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_not,
        Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨fun h => ⟨σ 0 r, h, rfl⟩, fun ⟨_, h1, h2⟩ => h1.trans h2.symm⟩
    rw [← compl_compl (Win b), hcompl]
    exact (MeasurableSet.iUnion (fun t => (hσ.1.1 b t).inter (hσ.1.1 0 t))).compl
  have hCharge_bounds : ∀ r : R, 0 ≤ secondPriceCharge σ b_i r ∧ secondPriceCharge σ b_i r ≤ (b_i : ℝ) := by
    intro r
    unfold secondPriceCharge criticalPrice
    by_cases hwin : b_i ∈ samplerWinningSet σ r
    · have hne : (samplerWinningSet σ r).Nonempty := ⟨b_i, hwin⟩
      simp only [hwin, hne, ↓reduceIte]
      have hA_bdd : BddBelow ((fun b : Bid => (b : ℝ)) '' samplerWinningSet σ r) :=
        ⟨0, fun _ ⟨b, _, hy⟩ => hy ▸ by positivity⟩
      have hA_ne : ((fun b : Bid => (b : ℝ)) '' samplerWinningSet σ r).Nonempty :=
        ⟨(b_i : ℝ), b_i, hwin, rfl⟩
      exact ⟨le_csInf hA_ne (fun _ ⟨b, _, hy⟩ => hy ▸ by positivity),
        csInf_le hA_bdd ⟨b_i, hwin, rfl⟩⟩
    · simp only [hwin, ↓reduceIte]
      exact ⟨le_rfl, by positivity⟩
  have hCharge_meas : Measurable (secondPriceCharge σ b_i) := by
    apply measurable_of_Iio
    intro c
    rcases le_or_gt c 0 with hc | hc
    · convert MeasurableSet.empty
      ext r
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans hc (hCharge_bounds r).1
    · have hset : (secondPriceCharge σ b_i) ⁻¹' Set.Iio c =
          (Win b_i)ᶜ ∪ ⋃ b : Bid, (if (b : ℝ) < c then Win b else ∅) := by
        ext r
        simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion]
        by_cases hwin : r ∈ Win b_i
        · have hwin' : b_i ∈ samplerWinningSet σ r := hwin
          have hne : (samplerWinningSet σ r).Nonempty := ⟨b_i, hwin'⟩
          simp only [hwin, not_true_eq_false, false_or, secondPriceCharge, criticalPrice, hwin', hne, ↓reduceIte]
          have hA_bdd : BddBelow ((fun b : Bid => (b : ℝ)) '' samplerWinningSet σ r) :=
            ⟨0, fun _ ⟨b, _, hy⟩ => hy ▸ by positivity⟩
          have hA_ne : ((fun b : Bid => (b : ℝ)) '' samplerWinningSet σ r).Nonempty :=
            ⟨(b_i : ℝ), b_i, hwin', rfl⟩
          rw [csInf_lt_iff hA_bdd hA_ne]
          constructor
          · rintro ⟨_, ⟨b, hb_mem, rfl⟩, hb_lt⟩
            exact ⟨b, by simp [hb_lt, Win, hb_mem]⟩
          · rintro ⟨b, hb⟩
            by_cases hbc : (b : ℝ) < c
            · simp only [hbc, ↓reduceIte] at hb
              exact ⟨(b : ℝ), ⟨b, hb, rfl⟩, hbc⟩
            · simp only [hbc, ↓reduceIte, Set.mem_empty_iff_false] at hb
        · simp only [hwin, not_false_eq_true, true_or, iff_true]
          have hnot : b_i ∉ samplerWinningSet σ r := hwin
          simp only [secondPriceCharge, hnot, ↓reduceIte]
          exact hc
      rw [hset]
      refine (hWin_meas b_i).compl.union (MeasurableSet.iUnion (fun b => ?_))
      split_ifs
      · exact hWin_meas b
      · exact MeasurableSet.empty
  have hCharge_int : Integrable (secondPriceCharge σ b_i) μ := by
    refine Integrable.of_bound hCharge_meas.aestronglyMeasurable (b_i : ℝ)
      (Filter.Eventually.of_forall (fun r => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hCharge_bounds r).1]
    exact (hCharge_bounds r).2
  have hPayment_nonneg : 0 ≤ secondPriceExpectedPayment μ σ b_i :=
    integral_nonneg (fun r => (hCharge_bounds r).1)
  have h_disj : ∀ u ∈ undersampledTokens q target, ∀ o ∈ oversampledTokens q target, u ≠ o := by
    intro u hu o ho heq
    subst heq
    have hu' : (q 0).prob u ≤ target.prob u := hu
    have ho' : target.prob u < (q 0).prob u := ho
    linarith
  have h_switch_props : ∀ (r : R) (u_r o_r : T) (W_r : Set Bid),
      u_r ∈ undersampledTokens q target →
      o_r ∈ oversampledTokens q target →
      IsUpperSet W_r → W_r.Nonempty → W_r ≠ Set.univ →
      (∀ b : Bid, σ b r = if b ∈ W_r then u_r else o_r) →
      (0 : Bid) ∉ W_r ∧
      samplerWinningSet σ r = W_r ∧
      (∀ b' ∈ W_r, criticalPrice σ r ≤ (b' : ℝ)) ∧
      (∀ b' : Bid, b' ∉ W_r → (b' : ℝ) ≤ criticalPrice σ r) := by
    intro r u_r o_r W_r hu ho hUpper hWne hWuniv hpath
    have h0_not_mem : (0 : Bid) ∉ W_r := by
      intro h0
      apply hWuniv
      exact Set.eq_univ_of_forall (fun b => hUpper (zero_le b) h0)
    have huo_ne : u_r ≠ o_r := h_disj u_r hu o_r ho
    have hWin_eq : samplerWinningSet σ r = W_r := by
      ext b
      simp only [samplerWinningSet, Set.mem_setOf_eq, hpath b, hpath 0, h0_not_mem, ↓reduceIte]
      split_ifs with hb
      · simp [hb, huo_ne]
      · simp [hb]
    have hA_bdd : BddBelow ((fun b : Bid => (b : ℝ)) '' W_r) :=
      ⟨0, fun _ ⟨b, _, hy⟩ => hy ▸ by positivity⟩
    have hA_ne : ((fun b : Bid => (b : ℝ)) '' W_r).Nonempty := hWne.image _
    have hcrit_eq : criticalPrice σ r = sInf ((fun b : Bid => (b : ℝ)) '' W_r) := by
      unfold criticalPrice
      rw [hWin_eq, if_pos hWne]
    refine ⟨h0_not_mem, hWin_eq, ?_, ?_⟩
    · intro b' hb'
      rw [hcrit_eq]
      exact csInf_le hA_bdd ⟨b', hb', rfl⟩
    · intro b' hb'
      rw [hcrit_eq]
      by_contra hlt
      push_neg at hlt
      obtain ⟨_, ⟨w, hw_mem, rfl⟩, hw_lt⟩ := (csInf_lt_iff hA_bdd hA_ne).mp hlt
      dsimp only at hw_lt
      have hw_le : w ≤ b' := le_of_lt (by exact_mod_cast hw_lt)
      exact hb' (hUpper hw_le hw_mem)
  have hCharge_t_int : ∀ t : T,
      Integrable (fun r => if σ b_i r = t then secondPriceCharge σ b_i r else 0) μ := by
    intro t
    have heq : (fun r => if σ b_i r = t then secondPriceCharge σ b_i r else 0) =
        ({r : R | σ b_i r = t}).indicator (secondPriceCharge σ b_i) := by
      ext r
      simp [Set.indicator]
    rw [heq]
    exact hCharge_int.indicator (hσ.1.1 b_i t)
  have h_over_zero : ∀ t ∈ oversampledTokens q target,
      ∫ r, (if σ b_i r = t then secondPriceCharge σ b_i r else 0) ∂μ = 0 := by
    intro t ht
    have hpt0 : ∀ r : R, (if σ b_i r = t then secondPriceCharge σ b_i r else 0) = 0 := by
      intro r
      rcases hσ.2 r with ⟨t₀, hconst⟩ | ⟨u_r, hu, o_r, ho, W_r, hUpper, hWne, hWuniv, hpath⟩
      · have hnot : b_i ∉ samplerWinningSet σ r := by
          simp [samplerWinningSet, hconst b_i, hconst 0]
        simp [secondPriceCharge, hnot]
      · obtain ⟨_, hWin_eq, _, _⟩ := h_switch_props r u_r o_r W_r hu ho hUpper hWne hWuniv hpath
        by_cases hb_mem : b_i ∈ W_r
        · have h_ut_ne : u_r ≠ t := h_disj u_r hu t ht
          simp [hpath b_i, hb_mem, h_ut_ne]
        · have hnot : b_i ∉ samplerWinningSet σ r := by rwa [hWin_eq]
          simp [secondPriceCharge, hnot]
    simp [hpt0]
  have h_under_eq : ∀ t ∈ undersampledTokens q target,
      IntervalIntegrable (fun x => (q b_i).prob t - tokenProbUnderExt q t x) volume 0 (b_i : ℝ) ∧
      ∫ r, (if σ b_i r = t then secondPriceCharge σ b_i r else 0) ∂μ =
        ∫ x in (0 : ℝ)..(b_i : ℝ), ((q b_i).prob t - tokenProbUnderExt q t x) := by
    intro t ht
    obtain ⟨ht_mono, ht_rat⟩ := (h_s1 T q target hq).1 t ht
    have hbi_nonneg : (0 : ℝ) ≤ (b_i : ℝ) := by positivity
    have hf_anti : AntitoneOn (fun x => (q b_i).prob t - tokenProbUnderExt q t x) (Set.Icc 0 (b_i : ℝ)) :=
      fun x hx y hy hxy => sub_le_sub_left (ht_mono hx.1 hy.1 hxy) _
    have hf_int : IntervalIntegrable (fun x => (q b_i).prob t - tokenProbUnderExt q t x) volume 0 (b_i : ℝ) := by
      apply AntitoneOn.intervalIntegrable
      rwa [Set.uIcc_of_le hbi_nonneg]
    refine ⟨hf_int, ?_⟩
    rcases eq_or_lt_of_le (zero_le b_i) with rfl | hbi_pos
    · have h0 : ∀ r : R, secondPriceCharge σ 0 r = 0 := fun r => by simp [secondPriceCharge, samplerWinningSet]
      simp [h0]
    · set charge_t : R → ℝ := fun r => if σ b_i r = t then secondPriceCharge σ b_i r else 0
      set I_lhs := ∫ r, charge_t r ∂μ
      set I_rhs := ∫ x in (0 : ℝ)..(b_i : ℝ), ((q b_i).prob t - tokenProbUnderExt q t x)
      by_contra hne_int
      have hdiff_pos : 0 < |I_lhs - I_rhs| := abs_pos.mpr (sub_ne_zero.mpr hne_int)
      have hprob_mono : (q 0).prob t ≤ (q b_i).prob t := by
        rw [← ht_rat 0, ← ht_rat b_i, NNRat.cast_zero]
        exact ht_mono (le_refl (0 : ℝ)) hbi_nonneg hbi_nonneg
      set C := (b_i : ℝ) * ((q b_i).prob t - (q 0).prob t)
      have hC_nonneg : 0 ≤ C := mul_nonneg hbi_nonneg (sub_nonneg.mpr hprob_mono)
      obtain ⟨N, hN_gt⟩ := exists_nat_gt (C / |I_lhs - I_rhs| + 1)
      have hN_ge1 : 1 ≤ N := by
        have : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hN_gt
        have : 0 < N := by exact_mod_cast this
        omega
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN_ge1)
      have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
      obtain ⟨hg_le, hlo_rhs, hhi_rhs, hgap_rhs⟩ :=
        h_grid b_i (fun x => (q b_i).prob t - tokenProbUnderExt q t x) hbi_pos hf_anti N hN_ge1
      set g : ℕ → Bid := fun k => b_i * (k : Bid) / (N : Bid)
      set h : ℝ := (b_i : ℝ) / (N : ℝ)
      have hh_pos : 0 < h := div_pos (by exact_mod_cast hbi_pos) hN_pos
      have hg_real : ∀ k : ℕ, ((g k) : ℝ) = (k : ℝ) * h := by
        intro k
        simp only [g, h, NNRat.cast_div, NNRat.cast_mul, NNRat.cast_natCast]
        ring
      have hg0 : g 0 = 0 := by simp [g]
      have hgN : g N = b_i := by
        rw [← @NNRat.cast_inj ℝ, hg_real N]
        dsimp only [h]
        rw [mul_div_cancel₀ _ hN_ne]
      have hg_mono_bid : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → g k₁ ≤ g k₂ := by
        intro k₁ k₂ hk
        rw [← @NNRat.cast_le ℝ, hg_real k₁, hg_real k₂]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (le_of_lt hh_pos)
      set ind : Bid → R → ℝ := fun b' r => if σ b' r = t then (1 : ℝ) else 0
      set indDiff : Bid → R → ℝ := fun b' r => ind b_i r - ind b' r
      have h_pt_sandwich : ∀ r : R,
          h * (∑ k ∈ Finset.range N, indDiff (g (k + 1)) r) ≤ charge_t r ∧
          charge_t r ≤ h * (∑ k ∈ Finset.range N, indDiff (g k) r) := by
        intro r
        rcases hσ.2 r with ⟨t₀, hconst⟩ | ⟨u_r, hu, o_r, ho, W_r, hUpper, hWne, hWuniv, hpath⟩
        · have hnot : b_i ∉ samplerWinningSet σ r := by simp [samplerWinningSet, hconst b_i, hconst 0]
          have hchg : charge_t r = 0 := by simp [charge_t, secondPriceCharge, hnot]
          have hind0 : ∀ b' : Bid, indDiff b' r = 0 := fun b' => by simp [indDiff, ind, hconst b_i, hconst b']
          simp [hchg, hind0]
        · obtain ⟨h0_not, hWin_eq, hcrit_le, hle_crit⟩ :=
            h_switch_props r u_r o_r W_r hu ho hUpper hWne hWuniv hpath
          have hot_ne : o_r ≠ t := (h_disj t ht o_r ho).symm
          have hσ_eq_t : ∀ b' : Bid, (σ b' r = t) ↔ (u_r = t ∧ b' ∈ W_r) := by
            intro b'
            rw [hpath b']
            split_ifs with hb'
            · simp [hb']
            · simp [hb', hot_ne]
          by_cases hcase : u_r = t ∧ b_i ∈ W_r
          · rcases hcase with ⟨rfl, hbi_W⟩
            have hbi_win : b_i ∈ samplerWinningSet σ r := by rwa [hWin_eq]
            have hchg : charge_t r = criticalPrice σ r := by
              have h1 : σ b_i r = u_r := by rw [hpath b_i, if_pos hbi_W]
              simp [charge_t, h1, secondPriceCharge, hbi_win]
            have hind_eq : ∀ b' : Bid, indDiff b' r = if b' ∈ W_r then 0 else 1 := by
              intro b'
              have h1 : σ b_i r = u_r := by rw [hpath b_i, if_pos hbi_W]
              by_cases hb' : b' ∈ W_r
              · have h2 : σ b' r = u_r := by rw [hpath b', if_pos hb']
                simp [indDiff, ind, h1, h2, hb']
              · have h2 : σ b' r ≠ u_r := fun h2 => hb' ((hσ_eq_t b').mp h2).2
                simp [indDiff, ind, h1, h2, hb']
            set S : Finset ℕ := (Finset.Icc 0 N).filter (fun k => g k ∈ W_r)
            have hN_mem_S : N ∈ S := by
              simp only [S, Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, le_rfl, true_and, hgN]
              exact hbi_W
            have hS_ne : S.Nonempty := ⟨N, hN_mem_S⟩
            set m : ℕ := S.min' hS_ne
            have hm_mem : m ∈ S := Finset.min'_mem S hS_ne
            have hm_le_N : m ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm_mem).1).2
            have hgm_W : g m ∈ W_r := (Finset.mem_filter.mp hm_mem).2
            have hm_ne0 : m ≠ 0 := by
              intro hm0
              rw [hm0] at hgm_W
              rw [hg0] at hgm_W
              exact h0_not hgm_W
            have hm_ge1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm_ne0
            have hgm1_not : g (m - 1) ∉ W_r := by
              intro hmem
              have hm1_S : m - 1 ∈ S := by
                simp only [S, Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and]
                exact ⟨by omega, hmem⟩
              have hle := Finset.min'_le S (m - 1) hm1_S
              omega
            have hgk_iff : ∀ k ≤ N, (g k ∈ W_r) ↔ m ≤ k := by
              intro k hk
              constructor
              · intro hgk
                have hk_S : k ∈ S := by
                  simp only [S, Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, hk, and_self, hgk]
                exact Finset.min'_le S k hk_S
              · intro hmk
                exact hUpper (hg_mono_bid m k hmk) hgm_W
            have hsum_hi : ∑ k ∈ Finset.range N, indDiff (g k) r = (m : ℝ) := by
              calc ∑ k ∈ Finset.range N, indDiff (g k) r
                  = ∑ k ∈ Finset.range N, (if k < m then (1 : ℝ) else 0) := by
                      refine Finset.sum_congr rfl (fun k hk => ?_)
                      have hk_le : k ≤ N := Nat.le_of_lt (Finset.mem_range.mp hk)
                      rw [hind_eq (g k)]
                      by_cases hkm : k < m
                      · have hnotW : g k ∉ W_r := by rw [hgk_iff k hk_le]; omega
                        simp [hkm, hnotW]
                      · have hW : g k ∈ W_r := by rw [hgk_iff k hk_le]; omega
                        simp [hkm, hW]
                _ = (m : ℝ) := h_sum_lt N m hm_le_N
            have hsum_lo : ∑ k ∈ Finset.range N, indDiff (g (k + 1)) r = ((m - 1 : ℕ) : ℝ) := by
              calc ∑ k ∈ Finset.range N, indDiff (g (k + 1)) r
                  = ∑ k ∈ Finset.range N, (if k < m - 1 then (1 : ℝ) else 0) := by
                      refine Finset.sum_congr rfl (fun k hk => ?_)
                      have hk1_le : k + 1 ≤ N := Finset.mem_range.mp hk
                      rw [hind_eq (g (k + 1))]
                      by_cases hkm : k < m - 1
                      · have hnotW : g (k + 1) ∉ W_r := by rw [hgk_iff (k + 1) hk1_le]; omega
                        simp [hkm, hnotW]
                      · have hW : g (k + 1) ∈ W_r := by rw [hgk_iff (k + 1) hk1_le]; omega
                        simp [hkm, hW]
                _ = ((m - 1 : ℕ) : ℝ) := h_sum_lt N (m - 1) (by omega)
            rw [hchg, hsum_lo, hsum_hi]
            have h1 := hle_crit (g (m - 1)) hgm1_not
            have h2 := hcrit_le (g m) hgm_W
            rw [hg_real (m - 1)] at h1
            rw [hg_real m] at h2
            exact ⟨by linarith, by linarith⟩
          · have hbi_not_t : σ b_i r ≠ t := fun h => hcase ((hσ_eq_t b_i).mp h)
            have hchg : charge_t r = 0 := by simp [charge_t, hbi_not_t]
            have hgk_not_t : ∀ k ≤ N, σ (g k) r ≠ t := by
              intro k hk h_eq
              rw [hσ_eq_t (g k)] at h_eq
              exact hcase ⟨h_eq.1, hUpper (hg_le k hk) h_eq.2⟩
            have hsum_hi : ∑ k ∈ Finset.range N, indDiff (g k) r = 0 := by
              refine Finset.sum_eq_zero (fun k hk => ?_)
              have hk_le : k ≤ N := Nat.le_of_lt (Finset.mem_range.mp hk)
              simp [indDiff, ind, hbi_not_t, hgk_not_t k hk_le]
            have hsum_lo : ∑ k ∈ Finset.range N, indDiff (g (k + 1)) r = 0 := by
              refine Finset.sum_eq_zero (fun k hk => ?_)
              have hk1_le : k + 1 ≤ N := Finset.mem_range.mp hk
              simp [indDiff, ind, hbi_not_t, hgk_not_t (k + 1) hk1_le]
            simp [hchg, hsum_lo, hsum_hi]
      have hind_int : ∀ b' : Bid, Integrable (ind b') μ ∧ ∫ r, ind b' r ∂μ = (q b').prob t := by
        intro b'
        have heq : ind b' = ({r : R | σ b' r = t}).indicator 1 := by
          ext r
          simp [ind, Set.indicator]
        rw [heq]
        refine ⟨(integrable_const (1 : ℝ)).indicator (hσ.1.1 b' t), ?_⟩
        rw [integral_indicator_one (hσ.1.1 b' t), hσ.1.2 b' t]
      have hindDiff_int : ∀ b' : Bid, Integrable (indDiff b') μ ∧
          ∫ r, indDiff b' r ∂μ = (q b_i).prob t - (q b').prob t := by
        intro b'
        refine ⟨(hind_int b_i).1.sub (hind_int b').1, ?_⟩
        dsimp only [indDiff]
        rw [integral_sub (hind_int b_i).1 (hind_int b').1, (hind_int b_i).2, (hind_int b').2]
      have h_int_sum : ∀ φ : ℕ → Bid,
          Integrable (fun r => h * ∑ k ∈ Finset.range N, indDiff (φ k) r) μ ∧
          ∫ r, (h * ∑ k ∈ Finset.range N, indDiff (φ k) r) ∂μ =
            h * ∑ k ∈ Finset.range N, ((q b_i).prob t - (q (φ k)).prob t) := by
        intro φ
        have hsum_int : Integrable (fun r => ∑ k ∈ Finset.range N, indDiff (φ k) r) μ :=
          integrable_finset_sum _ (fun k _ => (hindDiff_int (φ k)).1)
        refine ⟨hsum_int.const_mul h, ?_⟩
        rw [integral_const_mul, integral_finset_sum _ (fun k _ => (hindDiff_int (φ k)).1)]
        congr 1
        exact Finset.sum_congr rfl (fun k _ => (hindDiff_int (φ k)).2)
      have hlo_lhs : h * ∑ k ∈ Finset.range N, ((q b_i).prob t - (q (g (k + 1))).prob t) ≤ I_lhs := by
        rw [← (h_int_sum (fun k => g (k + 1))).2]
        exact integral_mono (h_int_sum (fun k => g (k + 1))).1 (hCharge_t_int t)
          (fun r => (h_pt_sandwich r).1)
      have hhi_lhs : I_lhs ≤ h * ∑ k ∈ Finset.range N, ((q b_i).prob t - (q (g k)).prob t) := by
        rw [← (h_int_sum g).2]
        exact integral_mono (hCharge_t_int t) (h_int_sum g).1
          (fun r => (h_pt_sandwich r).2)
      have hsum_eq1 : ∑ k ∈ Finset.range N, ((q b_i).prob t - tokenProbUnderExt q t ((g k) : ℝ)) =
          ∑ k ∈ Finset.range N, ((q b_i).prob t - (q (g k)).prob t) :=
        Finset.sum_congr rfl (fun k _ => by rw [ht_rat (g k)])
      have hsum_eq2 : ∑ k ∈ Finset.range N, ((q b_i).prob t - tokenProbUnderExt q t ((g (k + 1)) : ℝ)) =
          ∑ k ∈ Finset.range N, ((q b_i).prob t - (q (g (k + 1))).prob t) :=
        Finset.sum_congr rfl (fun k _ => by rw [ht_rat (g (k + 1))])
      rw [hsum_eq2] at hlo_rhs
      rw [hsum_eq1] at hhi_rhs
      rw [hsum_eq1, hsum_eq2] at hgap_rhs
      have hf0_diff : ((q b_i).prob t - tokenProbUnderExt q t 0) -
          ((q b_i).prob t - tokenProbUnderExt q t (b_i : ℝ)) =
          (q b_i).prob t - (q 0).prob t := by
        have h0' : tokenProbUnderExt q t ((0 : Bid) : ℝ) = (q 0).prob t := ht_rat 0
        simp only [NNRat.cast_zero] at h0'
        rw [h0', ht_rat b_i]
        ring
      have habs_le : |I_lhs - I_rhs| ≤ C / (N : ℝ) := by
        rw [abs_le]
        have hgap' : h * (∑ k ∈ Finset.range N, ((q b_i).prob t - (q (g k)).prob t)) -
            h * (∑ k ∈ Finset.range N, ((q b_i).prob t - (q (g (k + 1))).prob t)) = C / (N : ℝ) := by
          dsimp only [h, C]
          rw [hgap_rhs, hf0_diff]
          ring
        dsimp only [h] at hlo_lhs hhi_lhs hgap'
        constructor <;> linarith
      have hlt_C : C / (N : ℝ) < |I_lhs - I_rhs| := by
        rw [div_lt_iff₀ hN_pos]
        have h1 : C / |I_lhs - I_rhs| < (N : ℝ) := by linarith
        have h2 := (div_lt_iff₀ hdiff_pos).mp h1
        linarith
      linarith
  have h_sum_total : secondPriceExpectedPayment μ σ b_i =
      ∑ t : T, (if t ∈ undersampledTokens q target then
        ∫ x in (0 : ℝ)..(b_i : ℝ), ((q b_i).prob t - tokenProbUnderExt q t x) else 0) := by
    have hpt_sum : (fun r => secondPriceCharge σ b_i r) =
        (fun r => ∑ t : T, (if σ b_i r = t then secondPriceCharge σ b_i r else 0)) := by
      ext r
      simp [Finset.sum_ite_eq]
    unfold secondPriceExpectedPayment
    rw [hpt_sum, integral_finset_sum _ (fun t _ => hCharge_t_int t)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases ht : t ∈ undersampledTokens q target
    · simp only [ht, ↓reduceIte]
      exact (h_under_eq t ht).2
    · simp only [ht, ↓reduceIte]
      have ho : t ∈ oversampledTokens q target :=
        not_le.mp (show ¬((q 0).prob t ≤ target.prob t) from ht)
      exact h_over_zero t ho
  exact ⟨hCharge_int, hPayment_nonneg, h_over_zero, h_under_eq, h_sum_total⟩

/-! ## Section 5.2 & Appendix D.2: Proposition 5.6 & Footnote 7 -/

/-- Proposition 5.6 (`prop:second-price-payment`) & Footnote 8: Under any stable sampler `σ` of a
    robust-monotone curve `q`, oversampled tokens carry zero expected charge, undersampled tokens
    satisfy `E_r[θ_r 1{σ(b_i, r) = t}] = ∫_0^{b_i} [q_t(b_i) - q_t(b')] db'`, any antitone real
    extension `G` of `b' ↦ ‖q(b') - p_i‖₁` yields the same integral, and the expected second-price
    payment equals `myersonTVPayment q target b_i` independently of the choice of stable sampler. -/
theorem prop_5_6_second_price_payment (T : Type) [Fintype T] [DecidableEq T]
    (q : Bid → TokenDist T) (target : TokenDist T)
    (hq : IsSingleAgentRobustMonotone q target)
    (R : Type) [MeasurableSpace R] (μ : Measure R) [IsProbabilityMeasure μ]
    (σ : Bid → R → T) (hσ : IsStableSampler μ q target σ) :
    secondPriceExpectedPayment μ σ 0 = 0 ∧
    (∀ b_i : Bid,
      Integrable (secondPriceCharge σ b_i) μ ∧
      0 ≤ secondPriceExpectedPayment μ σ b_i ∧
      (∀ t ∈ oversampledTokens q target,
        ∫ r, (if σ b_i r = t then secondPriceCharge σ b_i r else 0) ∂μ = 0) ∧
      (∀ t ∈ undersampledTokens q target,
        IntervalIntegrable (fun x => (q b_i).prob t - tokenProbUnderExt q t x) volume 0 (b_i : ℝ) ∧
        ∫ r, (if σ b_i r = t then secondPriceCharge σ b_i r else 0) ∂μ =
          ∫ x in (0 : ℝ)..(b_i : ℝ), ((q b_i).prob t - tokenProbUnderExt q t x)) ∧
      (∀ G : ℝ → ℝ,
        AntitoneOn G (Set.Icc 0 (b_i : ℝ)) →
        (∀ b' : Bid, b' ≤ b_i → G (b' : ℝ) = l1Dist (q b') target) →
          IntervalIntegrable (fun x => G x - l1Dist (q b_i) target) volume 0 (b_i : ℝ) ∧
          secondPriceExpectedPayment μ σ b_i =
            (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..(b_i : ℝ), (G x - l1Dist (q b_i) target)) ∧
      secondPriceExpectedPayment μ σ b_i = myersonTVPayment q target b_i) := by
  obtain ⟨h_zero, h_s2_bi⟩ := h_s2 T q target hq R μ σ hσ
  obtain ⟨_, _, h_s1_bi⟩ := h_s1 T q target hq
  refine ⟨h_zero, fun b_i => ?_⟩
  obtain ⟨h_int, h_nonneg, h_over, h_under, h_sum_total⟩ := h_s2_bi b_i
  obtain ⟨_, h_G_inv, h_sum_T⟩ := h_s1_bi b_i
  have h_eq_myerson : secondPriceExpectedPayment μ σ b_i = myersonTVPayment q target b_i :=
    h_sum_total.trans h_sum_T.symm
  refine ⟨h_int, h_nonneg, h_over, h_under, ?_, h_eq_myerson⟩
  intro G hG_anti hG_rat
  obtain ⟨hG_int, hG_eq⟩ := h_G_inv G hG_anti hG_rat
  exact ⟨hG_int, h_eq_myerson.trans hG_eq.symm⟩

/-- Proposition 5.6 & Section 2.2 (`expectedPaymentOfPricing` decomposition): For any aggregation
    rule `q` whose slice `b' ↦ q(b', b_{-i}, p)` is robust-monotone toward `p_i`, the conditional
    per-token pricing rule `myersonTokenPricing q` is nonnegative, vanishes on oversampled tokens
    `T⁻`, matches the expected critical charge on every token `t ∈ T` under any stable sampler `σ`,
    and recovers `myersonTVPayment` (and `secondPriceExpectedPayment`) via
    `expectedPaymentOfPricing q (myersonTokenPricing q)`. -/
theorem prop_5_6_token_pricing_decomp (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (q : AggRule n T) (i : Fin n) (b : BidProfile n) (p : DistProfile n T)
    (hq : IsSingleAgentRobustMonotone
      (fun b' => q (joinBid i b' (restrictBids i b)) p) (p i)) :
    let qSlice : Bid → TokenDist T := fun b' => q (joinBid i b' (restrictBids i b)) p
    (∀ t : T, 0 ≤ myersonTokenPricing q i b p t) ∧
    (∀ t ∈ oversampledTokens qSlice (p i), myersonTokenPricing q i b p t = 0) ∧
    expectedPaymentOfPricing q (myersonTokenPricing q) i b p =
      myersonTVPayment qSlice (p i) (b i) ∧
    (∀ (R : Type) [MeasurableSpace R] (μ : Measure R) [IsProbabilityMeasure μ]
       (σ : Bid → R → T),
      IsStableSampler μ qSlice (p i) σ →
        (∀ t : T,
          (q b p).prob t * myersonTokenPricing q i b p t =
            ∫ r, (if σ (b i) r = t then secondPriceCharge σ (b i) r else 0) ∂μ) ∧
        expectedPaymentOfPricing q (myersonTokenPricing q) i b p =
          secondPriceExpectedPayment μ σ (b i)) := by
  intro qSlice
  have hq_self : qSlice (b i) = q b p := by
    dsimp only [qSlice]
    rw [joinBid_restrictBids]
  obtain ⟨h_tokenExt, _, h_s1_bi⟩ := h_s1 T qSlice (p i) hq
  have h_sum_T := (h_s1_bi (b i)).2.2
  have hbi_nonneg : (0 : ℝ) ≤ (b i : ℝ) := by positivity
  have h_int_nonneg : ∀ t ∈ undersampledTokens qSlice (p i),
      0 ≤ ∫ x in (0 : ℝ)..(b i : ℝ), ((q b p).prob t - tokenProbUnderExt qSlice t x) := by
    intro t ht
    obtain ⟨ht_mono, ht_rat⟩ := h_tokenExt t ht
    apply intervalIntegral.integral_nonneg hbi_nonneg
    intro x hx
    have hle : tokenProbUnderExt qSlice t x ≤ tokenProbUnderExt qSlice t (b i : ℝ) :=
      ht_mono hx.1 hbi_nonneg hx.2
    rw [ht_rat (b i), hq_self] at hle
    linarith
  have h_prod : ∀ t : T,
      (q b p).prob t * myersonTokenPricing q i b p t =
        if t ∈ undersampledTokens qSlice (p i) then
          ∫ x in (0 : ℝ)..(b i : ℝ), ((qSlice (b i)).prob t - tokenProbUnderExt qSlice t x)
        else 0 := by
    intro t
    by_cases ht : t ∈ undersampledTokens qSlice (p i)
    · by_cases hpos : 0 < (q b p).prob t
      · have hcond : t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t := ⟨ht, hpos⟩
        unfold myersonTokenPricing
        dsimp only
        change (q b p).prob t *
          (if t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t then
            (∫ x in (0 : ℝ)..(b i : ℝ), ((q b p).prob t - tokenProbUnderExt qSlice t x)) / (q b p).prob t
           else 0) = _
        rw [if_pos hcond, if_pos ht, mul_div_cancel₀ _ (ne_of_gt hpos), hq_self]
      · have hprob0 : (q b p).prob t = 0 := le_antisymm (not_lt.mp hpos) ((q b p).nonneg t)
        have hcond : ¬(t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t) :=
          fun hc => hpos hc.2
        unfold myersonTokenPricing
        dsimp only
        change (q b p).prob t *
          (if t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t then
            (∫ x in (0 : ℝ)..(b i : ℝ), ((q b p).prob t - tokenProbUnderExt qSlice t x)) / (q b p).prob t
           else 0) = _
        rw [if_neg hcond, mul_zero, if_pos ht]
        obtain ⟨ht_mono, ht_rat⟩ := h_tokenExt t ht
        have h_congr : ∫ x in (0 : ℝ)..(b i : ℝ),
            ((qSlice (b i)).prob t - tokenProbUnderExt qSlice t x) =
          ∫ x in (0 : ℝ)..(b i : ℝ), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le hbi_nonneg]
          intro x hx
          have hlo : (qSlice 0).prob t ≤ tokenProbUnderExt qSlice t x := by
            have h0 := ht_rat 0
            simp only [NNRat.cast_zero] at h0
            rw [← h0]
            exact ht_mono (le_refl (0 : ℝ)) hx.1 hx.1
          have hhi : tokenProbUnderExt qSlice t x ≤ (qSlice (b i)).prob t := by
            rw [← ht_rat (b i)]
            exact ht_mono hx.1 hbi_nonneg hx.2
          have h0_nn : 0 ≤ (qSlice 0).prob t := (qSlice 0).nonneg t
          have hbi_0 : (qSlice (b i)).prob t = 0 := by rwa [hq_self]
          linarith
        rw [h_congr]
        simp
    · have hcond : ¬(t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t) :=
        fun hc => ht hc.1
      unfold myersonTokenPricing
      dsimp only
      change (q b p).prob t *
        (if t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t then
          (∫ x in (0 : ℝ)..(b i : ℝ), ((q b p).prob t - tokenProbUnderExt qSlice t x)) / (q b p).prob t
         else 0) = _
      rw [if_neg hcond, mul_zero, if_neg ht]
  have h_nonneg_price : ∀ t : T, 0 ≤ myersonTokenPricing q i b p t := by
    intro t
    unfold myersonTokenPricing
    dsimp only
    change 0 ≤
      if t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t then
        (∫ x in (0 : ℝ)..(b i : ℝ), ((q b p).prob t - tokenProbUnderExt qSlice t x)) / (q b p).prob t
      else 0
    split_ifs with hc
    · exact div_nonneg (h_int_nonneg t hc.1) (le_of_lt hc.2)
    · exact le_rfl
  have h_over_price : ∀ t ∈ oversampledTokens qSlice (p i), myersonTokenPricing q i b p t = 0 := by
    intro t ht
    have hnot : t ∉ undersampledTokens qSlice (p i) := by
      intro hu
      have hu' : (qSlice 0).prob t ≤ (p i).prob t := hu
      have ht' : (p i).prob t < (qSlice 0).prob t := ht
      linarith
    have hcond : ¬(t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t) :=
      fun hc => hnot hc.1
    unfold myersonTokenPricing
    dsimp only
    change (if t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t then
        (∫ x in (0 : ℝ)..(b i : ℝ), ((q b p).prob t - tokenProbUnderExt qSlice t x)) / (q b p).prob t
      else 0) = 0
    exact if_neg hcond
  have h_exp_myerson : expectedPaymentOfPricing q (myersonTokenPricing q) i b p =
      myersonTVPayment qSlice (p i) (b i) := by
    unfold expectedPaymentOfPricing
    rw [h_sum_T]
    exact Finset.sum_congr rfl (fun t _ => h_prod t)
  refine ⟨h_nonneg_price, h_over_price, h_exp_myerson, ?_⟩
  intro R _ μ _ σ hσ
  obtain ⟨_, _, h_over, h_under, _, h_eq_myerson⟩ :=
    (prop_5_6_second_price_payment T qSlice (p i) hq R μ σ hσ).2 (b i)
  refine ⟨?_, h_exp_myerson.trans h_eq_myerson.symm⟩
  intro t
  rw [h_prod t]
  by_cases ht : t ∈ undersampledTokens qSlice (p i)
  · rw [if_pos ht, ((h_under t ht).2).symm]
  · rw [if_neg ht]
    have ho : t ∈ oversampledTokens qSlice (p i) :=
      not_le.mp (show ¬((qSlice 0).prob t ≤ (p i).prob t) from ht)
    exact (h_over t ho).symm

/-- Footnote 7 (Proposition 5.6): `myersonTVPayment` is payment-monotone on strictly positive bids
    `b_1, b_2 > 0`, and payment-monotone on all of `ℚ₊` whenever `q` is right-continuous at `0`. -/
theorem fn_7_second_price_payment_monotone (T : Type) [Fintype T] [DecidableEq T]
    (q : Bid → TokenDist T) (target : TokenDist T)
    (hq : IsSingleAgentRobustMonotone q target) :
    (∀ b₁ b₂ : Bid, 0 < b₁ → 0 < b₂ →
        (myersonTVPayment q target b₂ ≤ myersonTVPayment q target b₁ ↔
          RobustPref target (q b₁) (q b₂))) ∧
    ((∀ ε : ℝ, 0 < ε → ∃ δ : Bid, 0 < δ ∧ l1Dist (q 0) target - l1Dist (q δ) target < ε) →
      ∀ b₁ b₂ : Bid,
        (myersonTVPayment q target b₂ ≤ myersonTVPayment q target b₁ ↔
          RobustPref target (q b₁) (q b₂))) := by
  obtain ⟨_, ⟨hD_anti, hD_rat⟩, h_s1_bi⟩ := h_s1 T q target hq
  have h_d_anti : ∀ a b : Bid, a ≤ b → l1Dist (q b) target ≤ l1Dist (q a) target :=
    fun a b hab => Finset.sum_le_sum (fun t _ => (hq b a hab).1 t)
  have h_eq_of_l1 : ∀ q₁ q₂ : TokenDist T,
      RobustPref target q₁ q₂ → l1Dist q₁ target = l1Dist q₂ target → q₁ = q₂ := by
    intro q₁ q₂ hpref hl1
    have hdiff0 : ∑ t : T, (|q₂.prob t - target.prob t| - |q₁.prob t - target.prob t|) = 0 := by
      rw [Finset.sum_sub_distrib, ← l1Dist, ← l1Dist, hl1, sub_self]
    have h_abs_eq : ∀ t : T, |q₁.prob t - target.prob t| = |q₂.prob t - target.prob t| := by
      intro t
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => sub_nonneg.mpr (hpref.1 s))).mp hdiff0 t (Finset.mem_univ t)
      linarith
    ext t
    have habs := h_abs_eq t
    have hprod := hpref.2 t
    rcases abs_eq_abs.mp habs with heq | hneg
    · linarith
    · nlinarith
  have h_pref_refl : ∀ q₀ : TokenDist T, RobustPref target q₀ q₀ :=
    fun q₀ => ⟨fun _ => le_rfl, fun _ => mul_self_nonneg _⟩
  have h_pref_iff_l1 : ∀ a b : Bid, a ≤ b →
      (RobustPref target (q a) (q b) ↔ l1Dist (q a) target = l1Dist (q b) target) := by
    intro a b hab
    constructor
    · intro hpref
      exact le_antisymm (Finset.sum_le_sum (fun t _ => hpref.1 t)) (h_d_anti a b hab)
    · intro hl1
      have h_eq : q b = q a := h_eq_of_l1 (q b) (q a) (hq b a hab) hl1.symm
      rw [h_eq]
      exact h_pref_refl (q a)
  have h_z_diff : ∀ a b : Bid, a ≤ b →
      myersonTVPayment q target b - myersonTVPayment q target a =
        ((a : ℝ) / 2) * (l1Dist (q a) target - l1Dist (q b) target) +
        (1 / 2 : ℝ) * ∫ x in (a : ℝ)..(b : ℝ), (l1DistRealExt q target x - l1Dist (q b) target) := by
    intro a b hab
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := le_trans ha0 hab'
    have hint_0a : ∀ c : ℝ, IntervalIntegrable (fun x => l1DistRealExt q target x - c) volume 0 (a : ℝ) := by
      intro c
      apply AntitoneOn.intervalIntegrable
      rw [Set.uIcc_of_le ha0]
      exact fun x hx y hy hxy => sub_le_sub_right (hD_anti hx.1 hy.1 hxy) c
    have hint_ab : ∀ c : ℝ, IntervalIntegrable (fun x => l1DistRealExt q target x - c) volume (a : ℝ) (b : ℝ) := by
      intro c
      apply AntitoneOn.intervalIntegrable
      rw [Set.uIcc_of_le hab']
      exact fun x hx y hy hxy => sub_le_sub_right (hD_anti (le_trans ha0 hx.1) (le_trans ha0 hy.1) hxy) c
    have hsplit := (intervalIntegral.integral_add_adjacent_intervals (hint_0a (l1Dist (q b) target))
      (hint_ab (l1Dist (q b) target))).symm
    have hshift : ∫ x in (0 : ℝ)..(a : ℝ), (l1DistRealExt q target x - l1Dist (q b) target) =
        (∫ x in (0 : ℝ)..(a : ℝ), (l1DistRealExt q target x - l1Dist (q a) target)) +
        (a : ℝ) * (l1Dist (q a) target - l1Dist (q b) target) := by
      have heq : (fun x => l1DistRealExt q target x - l1Dist (q b) target) =
          (fun x => (l1DistRealExt q target x - l1Dist (q a) target) + (l1Dist (q a) target - l1Dist (q b) target)) := by
        ext x; ring
      rw [heq, intervalIntegral.integral_add (hint_0a (l1Dist (q a) target)) intervalIntegral.intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    unfold myersonTVPayment
    rw [hsplit, hshift]
    ring
  have h_rem_nonneg : ∀ a b : Bid, a ≤ b →
      0 ≤ ∫ x in (a : ℝ)..(b : ℝ), (l1DistRealExt q target x - l1Dist (q b) target) := by
    intro a b hab
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    apply intervalIntegral.integral_nonneg hab'
    intro x hx
    have hge : l1DistRealExt q target (b : ℝ) ≤ l1DistRealExt q target x :=
      hD_anti (le_trans ha0 hx.1) (le_trans ha0 hab') hx.2
    rw [hD_rat b] at hge
    linarith
  have h_z_mono : ∀ a b : Bid, a ≤ b → myersonTVPayment q target a ≤ myersonTVPayment q target b := by
    intro a b hab
    have hdiff := h_z_diff a b hab
    have h1 : 0 ≤ ((a : ℝ) / 2) * (l1Dist (q a) target - l1Dist (q b) target) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (h_d_anti a b hab))
    have h2 : 0 ≤ (1 / 2 : ℝ) * ∫ x in (a : ℝ)..(b : ℝ), (l1DistRealExt q target x - l1Dist (q b) target) :=
      mul_nonneg (by norm_num) (h_rem_nonneg a b hab)
    linarith
  have h_z_eq_of_d_eq : ∀ a b : Bid, a ≤ b → l1Dist (q a) target = l1Dist (q b) target →
      myersonTVPayment q target a = myersonTVPayment q target b := by
    intro a b hab hd
    have hdiff := h_z_diff a b hab
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hint0 : ∫ x in (a : ℝ)..(b : ℝ), (l1DistRealExt q target x - l1Dist (q b) target) = 0 := by
      have hcongr : ∫ x in (a : ℝ)..(b : ℝ), (l1DistRealExt q target x - l1Dist (q b) target) =
          ∫ x in (a : ℝ)..(b : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hab']
        intro x hx
        have hlo : l1DistRealExt q target (b : ℝ) ≤ l1DistRealExt q target x :=
          hD_anti (le_trans ha0 hx.1) (le_trans ha0 hab') hx.2
        have hhi : l1DistRealExt q target x ≤ l1DistRealExt q target (a : ℝ) :=
          hD_anti ha0 (le_trans ha0 hx.1) hx.1
        rw [hD_rat b] at hlo
        rw [hD_rat a, hd] at hhi
        linarith
      rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, mul_zero]
    rw [hd, sub_self, mul_zero, hint0, mul_zero, add_zero] at hdiff
    linarith
  have h_pos_case : ∀ b₁ b₂ : Bid, 0 < b₁ →
      (myersonTVPayment q target b₂ ≤ myersonTVPayment q target b₁ ↔ RobustPref target (q b₁) (q b₂)) := by
    intro b₁ b₂ hb₁
    rcases le_or_gt b₂ b₁ with hle | hlt
    · exact ⟨fun _ => hq b₁ b₂ hle, fun _ => h_z_mono b₂ b₁ hle⟩
    · have hle : b₁ ≤ b₂ := le_of_lt hlt
      rw [h_pref_iff_l1 b₁ b₂ hle]
      constructor
      · intro hz_le
        have hz_eq : myersonTVPayment q target b₂ = myersonTVPayment q target b₁ :=
          le_antisymm hz_le (h_z_mono b₁ b₂ hle)
        have hdiff := h_z_diff b₁ b₂ hle
        have hrem := h_rem_nonneg b₁ b₂ hle
        have hb1_pos : (0 : ℝ) < (b₁ : ℝ) := by exact_mod_cast hb₁
        have hd_ge : 0 ≤ l1Dist (q b₁) target - l1Dist (q b₂) target := sub_nonneg.mpr (h_d_anti b₁ b₂ hle)
        have hterm1 : ((b₁ : ℝ) / 2) * (l1Dist (q b₁) target - l1Dist (q b₂) target) ≤ 0 := by linarith
        have hd_le : l1Dist (q b₁) target - l1Dist (q b₂) target ≤ 0 := by
          by_contra hpos
          push_neg at hpos
          have : 0 < ((b₁ : ℝ) / 2) * (l1Dist (q b₁) target - l1Dist (q b₂) target) := by positivity
          linarith
        linarith
      · intro hd_eq
        exact le_of_eq (h_z_eq_of_d_eq b₁ b₂ hle hd_eq).symm
  refine ⟨fun b₁ b₂ hb₁ _ => h_pos_case b₁ b₂ hb₁, ?_⟩
  intro h_rc b₁ b₂
  rcases eq_or_lt_of_le (zero_le b₁) with rfl | hb₁_pos
  · rcases eq_or_lt_of_le (zero_le b₂) with rfl | hb₂_pos
    · exact ⟨fun _ => h_pref_refl (q 0), fun _ => le_rfl⟩
    · have hle : (0 : Bid) ≤ b₂ := zero_le b₂
      rw [h_pref_iff_l1 0 b₂ hle]
      have hz0 : myersonTVPayment q target 0 = 0 := by simp [myersonTVPayment]
      constructor
      · intro hz_le
        have hz_eq : myersonTVPayment q target b₂ = 0 :=
          le_antisymm (hz_le.trans (le_of_eq hz0)) (hz0 ▸ h_z_mono 0 b₂ hle)
        by_contra hd_ne
        have hd_gt : l1Dist (q b₂) target < l1Dist (q 0) target :=
          lt_of_le_of_ne (h_d_anti 0 b₂ hle) (Ne.symm hd_ne)
        set ε := (l1Dist (q 0) target - l1Dist (q b₂) target) / 2
        have hε : 0 < ε := by dsimp [ε]; linarith
        obtain ⟨δ, hδ_pos, hδ_lt⟩ := h_rc ε hε
        set δ' : Bid := min δ b₂
        have hδ'_pos : 0 < δ' := lt_min hδ_pos hb₂_pos
        have hδ'_le_δ : δ' ≤ δ := min_le_left δ b₂
        have hδ'_le_b2 : δ' ≤ b₂ := min_le_right δ b₂
        have hd_δ' : l1Dist (q δ) target ≤ l1Dist (q δ') target := h_d_anti δ' δ hδ'_le_δ
        have hgap_pos : 0 < l1Dist (q δ') target - l1Dist (q b₂) target := by
          dsimp [ε] at hδ_lt; linarith
        have hz_δ'_nonneg : 0 ≤ myersonTVPayment q target δ' := (h_s1_bi δ').1
        have hdiff := h_z_diff δ' b₂ hδ'_le_b2
        have hrem := h_rem_nonneg δ' b₂ hδ'_le_b2
        have hδ'_real_pos : (0 : ℝ) < (δ' : ℝ) := by exact_mod_cast hδ'_pos
        have hterm_pos : 0 < ((δ' : ℝ) / 2) * (l1Dist (q δ') target - l1Dist (q b₂) target) := by positivity
        linarith
      · intro hd_eq
        exact le_of_eq (h_z_eq_of_d_eq 0 b₂ hle hd_eq).symm
  · exact h_pos_case b₁ b₂ hb₁_pos

/-! ## Section 5.2 & Appendix D.2: Corollary 5.7 (Closed-Form Linear Second-Price Payments) -/

private lemma h_G_ext : ∀ (T : Type) [Fintype T] [DecidableEq T] (q : Bid → TokenDist T) (target : TokenDist T),
    IsSingleAgentRobustMonotone q target →
    ∀ (b_i : Bid),
      0 ≤ myersonTVPayment q target b_i ∧
      (∀ G : ℝ → ℝ,
        AntitoneOn G (Set.Icc 0 (b_i : ℝ)) →
        (∀ b' : Bid, b' ≤ b_i → G (b' : ℝ) = l1Dist (q b') target) →
          IntervalIntegrable (fun x => G x - l1Dist (q b_i) target) volume 0 (b_i : ℝ) ∧
          (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..(b_i : ℝ), (G x - l1Dist (q b_i) target) =
            myersonTVPayment q target b_i) :=
  fun T _ _ q target hq b_i => ⟨((h_s1 T q target hq).2.2 b_i).1, ((h_s1 T q target hq).2.2 b_i).2.1⟩
private lemma h_mono_rc : ∀ (T : Type) [Fintype T] [DecidableEq T] (q : Bid → TokenDist T) (target : TokenDist T),
    IsSingleAgentRobustMonotone q target →
    (∀ ε : ℝ, 0 < ε → ∃ δ : Bid, 0 < δ ∧ l1Dist (q 0) target - l1Dist (q δ) target < ε) →
    ∀ b₁ b₂ : Bid,
      (myersonTVPayment q target b₂ ≤ myersonTVPayment q target b₁ ↔
        RobustPref target (q b₁) (q b₂)) :=
  fun T _ _ q target hq => (fn_7_second_price_payment_monotone T q target hq).2

private lemma h_sum_joinBid : ∀ {n : ℕ} (i : Fin n) (b' : Bid) (b : BidProfile n) (w : Fin n → ℝ),
    ∑ j : Fin n, ((joinBid i b' (restrictBids i b) j) : ℝ) * w j =
      (b' : ℝ) * w i + ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * w j := by
  intro n i b' b w
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), joinBid_self]
  congr 1
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  simp [joinBid, restrictBids, hji]
private lemma h_strat_sum_join : ∀ {n : ℕ} (i : Fin n) (b' : Bid) (b : BidProfile n),
    strategicBidSum (joinBid i b' (restrictBids i b)) = (b' : ℝ) + opposingStrategicBidSum i b := by
  intro n i b' b
  simpa [strategicBidSum, opposingStrategicBidSum] using
    h_sum_joinBid i b' b (fun _ => (1 : ℝ))
private lemma h_total_split : ∀ {n : ℕ} (b₀ : Bid) (i : Fin n) (b : BidProfile n),
    totalBidWithPlatform b₀ b = (b i : ℝ) + opposingBidWithPlatform b₀ i b := by
  intro n b₀ i b
  have h1 := h_strat_sum_join i (b i) b
  rw [joinBid_restrictBids] at h1
  unfold totalBidWithPlatform opposingBidWithPlatform
  linarith

private lemma h_conv_slice : ∀ (T : Type) [Fintype T] [DecidableEq T]
    (qSlice : Bid → TokenDist T) (qWithout target : TokenDist T) (Bminus : ℝ),
    0 < Bminus →
    (∀ (b' : Bid) (t : T),
      (qSlice b').prob t = (Bminus * qWithout.prob t + (b' : ℝ) * target.prob t) / ((b' : ℝ) + Bminus)) →
    IsSingleAgentRobustMonotone qSlice target ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : Bid, 0 < δ ∧ l1Dist (qSlice 0) target - l1Dist (qSlice δ) target < ε) ∧
    (∀ b_i : Bid, 0 < (b_i : ℝ) →
      myersonTVPayment qSlice target b_i =
        Bminus * l1Dist qWithout (qSlice b_i) *
          ((((b_i : ℝ) + Bminus) / (2 * (b_i : ℝ))) * Real.log (((b_i : ℝ) + Bminus) / Bminus) - (1 / 2 : ℝ))) := by
  intro T _ _ qSlice qWithout target Bminus hBminus hprob
  have hden_pos : ∀ b' : Bid, 0 < (b' : ℝ) + Bminus :=
    fun b' => add_pos_of_nonneg_of_pos (by positivity) hBminus
  have hdiff_target : ∀ (b' : Bid) (t : T),
      (qSlice b').prob t - target.prob t =
        (Bminus / ((b' : ℝ) + Bminus)) * (qWithout.prob t - target.prob t) := by
    intro b' t
    have hden : (b' : ℝ) + Bminus ≠ 0 := ne_of_gt (hden_pos b')
    rw [hprob b' t]
    field_simp [hden]
    ring
  have hdiff_without : ∀ (b' : Bid) (t : T),
      qWithout.prob t - (qSlice b').prob t =
        ((b' : ℝ) / ((b' : ℝ) + Bminus)) * (qWithout.prob t - target.prob t) := by
    intro b' t
    have hden : (b' : ℝ) + Bminus ≠ 0 := ne_of_gt (hden_pos b')
    rw [hprob b' t]
    field_simp [hden]
    ring
  have hl1_target : ∀ b' : Bid,
      l1Dist (qSlice b') target = (Bminus / ((b' : ℝ) + Bminus)) * l1Dist qWithout target := by
    intro b'
    have hpos : 0 ≤ Bminus / ((b' : ℝ) + Bminus) := div_nonneg (le_of_lt hBminus) (le_of_lt (hden_pos b'))
    unfold l1Dist
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hdiff_target b' t, abs_mul, abs_of_nonneg hpos]
  have hl1_without : ∀ b' : Bid,
      l1Dist qWithout (qSlice b') = ((b' : ℝ) / ((b' : ℝ) + Bminus)) * l1Dist qWithout target := by
    intro b'
    have hpos : 0 ≤ (b' : ℝ) / ((b' : ℝ) + Bminus) := div_nonneg (by positivity) (le_of_lt (hden_pos b'))
    unfold l1Dist
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hdiff_without b' t, abs_mul, abs_of_nonneg hpos]
  have hq_mono : IsSingleAgentRobustMonotone qSlice target := by
    intro b₁ b₂ hb
    have hb_real : (b₂ : ℝ) ≤ (b₁ : ℝ) := by exact_mod_cast hb
    have hα1_pos : 0 < Bminus / ((b₁ : ℝ) + Bminus) := div_pos hBminus (hden_pos b₁)
    have hα2_pos : 0 < Bminus / ((b₂ : ℝ) + Bminus) := div_pos hBminus (hden_pos b₂)
    have hα_le : Bminus / ((b₁ : ℝ) + Bminus) ≤ Bminus / ((b₂ : ℝ) + Bminus) :=
      div_le_div_of_nonneg_left (le_of_lt hBminus) (hden_pos b₂) (by linarith)
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [hdiff_target b₁ t, hdiff_target b₂ t, abs_mul, abs_mul,
        abs_of_pos hα1_pos, abs_of_pos hα2_pos]
      exact mul_le_mul_of_nonneg_right hα_le (abs_nonneg _)
    · rw [hdiff_target b₁ t, hdiff_target b₂ t]
      have : (Bminus / ((b₁ : ℝ) + Bminus) * (qWithout.prob t - target.prob t)) *
          (Bminus / ((b₂ : ℝ) + Bminus) * (qWithout.prob t - target.prob t)) =
          (Bminus / ((b₁ : ℝ) + Bminus)) * (Bminus / ((b₂ : ℝ) + Bminus)) *
            ((qWithout.prob t - target.prob t) * (qWithout.prob t - target.prob t)) := by ring
      rw [this]
      exact mul_nonneg (mul_nonneg (le_of_lt hα1_pos) (le_of_lt hα2_pos)) (mul_self_nonneg _)
  have h_rc : ∀ ε : ℝ, 0 < ε → ∃ δ : Bid, 0 < δ ∧ l1Dist (qSlice 0) target - l1Dist (qSlice δ) target < ε := by
    intro ε hε
    set D := l1Dist qWithout target
    have hD_nonneg : 0 ≤ D := Finset.sum_nonneg (fun t _ => abs_nonneg _)
    have hl1_0 : l1Dist (qSlice 0) target = D := by
      rw [hl1_target 0]
      simp [ne_of_gt hBminus]
    rcases eq_or_lt_of_le hD_nonneg with hD0 | hD_pos
    · refine ⟨1, by norm_num, ?_⟩
      rw [hl1_0, hl1_target 1, ← hD0]
      simpa using hε
    · obtain ⟨N, hN_gt⟩ := exists_nat_gt (D / (ε * Bminus) + 1)
      have hN_pos_real : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hN_gt
      have hN_pos_nat : 0 < N := by exact_mod_cast hN_pos_real
      set δ : Bid := 1 / (N : Bid)
      have hδ_pos : 0 < δ := div_pos zero_lt_one (by exact_mod_cast hN_pos_nat)
      have hδ_real : (δ : ℝ) = 1 / (N : ℝ) := by simp [δ]
      have hδ_real_pos : 0 < (δ : ℝ) := by exact_mod_cast hδ_pos
      refine ⟨δ, hδ_pos, ?_⟩
      rw [hl1_0, hl1_target δ]
      have h_eq : D - Bminus / ((δ : ℝ) + Bminus) * D = ((δ : ℝ) / ((δ : ℝ) + Bminus)) * D := by
        have hden : (δ : ℝ) + Bminus ≠ 0 := ne_of_gt (hden_pos δ)
        field_simp [hden]
        ring
      rw [h_eq]
      have h_le : ((δ : ℝ) / ((δ : ℝ) + Bminus)) * D ≤ ((δ : ℝ) / Bminus) * D := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hD_pos)
        exact div_le_div_of_nonneg_left (le_of_lt hδ_real_pos) hBminus (by linarith)
      have h_lt : ((δ : ℝ) / Bminus) * D < ε := by
        rw [hδ_real]
        have h1 : D / (ε * Bminus) < (N : ℝ) := by linarith
        have h2 : D < (N : ℝ) * (ε * Bminus) := (div_lt_iff₀ (mul_pos hε hBminus)).mp h1
        have h3 : (1 / (N : ℝ) / Bminus) * D = D / ((N : ℝ) * Bminus) := by field_simp
        rw [h3, div_lt_iff₀ (mul_pos hN_pos_real hBminus)]
        linarith
      exact lt_of_le_of_lt h_le h_lt
  refine ⟨hq_mono, h_rc, ?_⟩
  intro b_i hbi_pos
  set bi := (b_i : ℝ)
  set B := bi + Bminus
  have hB_pos : 0 < B := add_pos hbi_pos hBminus
  set D := l1Dist qWithout target
  have hD_nonneg : 0 ≤ D := Finset.sum_nonneg (fun t _ => abs_nonneg _)
  set G : ℝ → ℝ := fun x => (Bminus / (x + Bminus)) * D
  have hG_anti : AntitoneOn G (Set.Icc 0 bi) := by
    intro x hx y hy hxy
    dsimp only [G]
    apply mul_le_mul_of_nonneg_right _ hD_nonneg
    exact div_le_div_of_nonneg_left (le_of_lt hBminus) (by linarith [hx.1]) (by linarith)
  have hG_rat : ∀ b' : Bid, b' ≤ b_i → G (b' : ℝ) = l1Dist (qSlice b') target :=
    fun b' _ => (hl1_target b').symm
  obtain ⟨hG_int, hG_myerson⟩ := (h_G_ext T qSlice target hq_mono b_i).2 G hG_anti hG_rat
  rw [← hG_myerson]
  set F : ℝ → ℝ := fun x => (Bminus * D / 2) * (Real.log (x + Bminus) - x / B)
  have hF_deriv : ∀ x ∈ Set.uIcc 0 bi,
      HasDerivAt F ((1 / 2 : ℝ) * (G x - l1Dist (qSlice b_i) target)) x := by
    intro x hx
    rw [Set.uIcc_of_le (le_of_lt hbi_pos)] at hx
    have hxB_pos : 0 < x + Bminus := by linarith [hx.1]
    have hd1 : HasDerivAt (fun y => y + Bminus) 1 x := (hasDerivAt_id x).add_const Bminus
    have hd2 : HasDerivAt (fun y => Real.log (y + Bminus)) (1 / (x + Bminus)) x :=
      hd1.log (ne_of_gt hxB_pos)
    have hd3 : HasDerivAt (fun y => y / B) (1 / B) x := by
      simpa using (hasDerivAt_id x).div_const B
    have hdF := (hd2.sub hd3).const_mul (Bminus * D / 2)
    convert hdF using 1
    rw [hl1_target b_i]
    dsimp only [G, B, bi]
    have hB_ne : bi + Bminus ≠ 0 := ne_of_gt hB_pos
    have hxB_ne : x + Bminus ≠ 0 := ne_of_gt hxB_pos
    field_simp [hB_ne, hxB_ne]
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv (hG_int.const_mul (1 / 2 : ℝ))
  have h_int_eq : (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..bi, (G x - l1Dist (qSlice b_i) target) = F bi - F 0 := by
    rw [← intervalIntegral.integral_const_mul, h_ftc]
  rw [h_int_eq, hl1_without b_i]
  dsimp only [F, B, bi]
  have hlog_sub : Real.log ((b_i : ℝ) + Bminus) - Real.log (0 + Bminus) =
      Real.log (((b_i : ℝ) + Bminus) / Bminus) := by
    rw [zero_add, ← Real.log_div (ne_of_gt hB_pos) (ne_of_gt hBminus)]
  have hbi_ne : (b_i : ℝ) ≠ 0 := ne_of_gt hbi_pos
  have hB_ne : (b_i : ℝ) + Bminus ≠ 0 := ne_of_gt hB_pos
  calc (Bminus * D / 2) * (Real.log ((b_i : ℝ) + Bminus) - (b_i : ℝ) / ((b_i : ℝ) + Bminus)) -
        (Bminus * D / 2) * (Real.log (0 + Bminus) - 0 / ((b_i : ℝ) + Bminus))
      = (Bminus * D / 2) *
          ((Real.log ((b_i : ℝ) + Bminus) - Real.log (0 + Bminus)) - (b_i : ℝ) / ((b_i : ℝ) + Bminus)) := by ring
    _ = (Bminus * D / 2) *
          (Real.log (((b_i : ℝ) + Bminus) / Bminus) - (b_i : ℝ) / ((b_i : ℝ) + Bminus)) := by rw [hlog_sub]
    _ = Bminus * ((b_i : ℝ) / ((b_i : ℝ) + Bminus) * D) *
          ((((b_i : ℝ) + Bminus) / (2 * (b_i : ℝ))) * Real.log (((b_i : ℝ) + Bminus) / Bminus) - (1 / 2 : ℝ)) := by
        field_simp [hbi_ne, hB_ne]

private lemma h_platform_bridge : ∀ {n : ℕ} {T : Type} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
    (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
    0 < opposingBidWithPlatform b₀ i b ∧
    (∀ (b' : Bid) (t : T),
      (linearAggRule b₀ hb₀ p₀ (joinBid i b' (restrictBids i b)) p).prob t =
        (opposingBidWithPlatform b₀ i b * (linearAggWithout b₀ hb₀ p₀ i b p).prob t +
          (b' : ℝ) * (p i).prob t) /
        ((b' : ℝ) + opposingBidWithPlatform b₀ i b)) := by
  intro n T _ b₀ hb₀ p₀ i b p
  have hb₀_pos : (0 : ℝ) < (b₀ : ℝ) := by exact_mod_cast hb₀
  have hopp_nonneg : 0 ≤ opposingStrategicBidSum i b :=
    Finset.sum_nonneg (fun j _ => by positivity)
  have hBminus_pos : 0 < opposingBidWithPlatform b₀ i b := by
    unfold opposingBidWithPlatform; linarith
  refine ⟨hBminus_pos, ?_⟩
  intro b' t
  have htot_b' : totalBidWithPlatform b₀ (joinBid i b' (restrictBids i b)) =
      (b' : ℝ) + opposingBidWithPlatform b₀ i b := by
    unfold totalBidWithPlatform opposingBidWithPlatform
    rw [h_strat_sum_join i b' b]
    ring
  have htot_0 : totalBidWithPlatform b₀ (joinBid i 0 (restrictBids i b)) =
      opposingBidWithPlatform b₀ i b := by
    have h0 := h_strat_sum_join i 0 b
    simp only [NNRat.cast_zero, zero_add] at h0
    unfold totalBidWithPlatform opposingBidWithPlatform
    rw [h0]
  have hnum_0 : opposingBidWithPlatform b₀ i b * (linearAggWithout b₀ hb₀ p₀ i b p).prob t =
      (b₀ : ℝ) * p₀.prob t + ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * (p j).prob t := by
    unfold linearAggWithout linearAggRule
    dsimp only
    rw [htot_0, mul_div_cancel₀ _ (ne_of_gt hBminus_pos), h_sum_joinBid i 0 b (fun j => (p j).prob t)]
    simp
  unfold linearAggRule
  dsimp only
  rw [htot_b', h_sum_joinBid i b' b (fun j => (p j).prob t), hnum_0]
  ring_nf

/-- Corollary 5.7 (`cor:second-price-closed-form`, platform-bidder setting `b_0 > 0`):
    `linearSecondPriceClosedFormWithPlatform` is admissible, satisfies payment monotonicity on all
    of `ℚ₊`, and equals `myersonTVPayment` for every strategic bidder `i`. -/
theorem cor_5_7_linear_closed_form_with_platform (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) :
    IsAdmissiblePayment (linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ : PaymentRule n T) ∧
    IsPaymentMonotone (robustAgentPrefs n T)
      ⟨linearAggRule b₀ hb₀ p₀, linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀⟩ ∧
    (∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      myersonTVPayment
        (fun b_i => linearAggRule b₀ hb₀ p₀ (joinBid i b_i (restrictBids i b)) p)
        (p i) (b i) =
      linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i b p) := by
  have hCF : ∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      myersonTVPayment
        (fun b_i => linearAggRule b₀ hb₀ p₀ (joinBid i b_i (restrictBids i b)) p)
        (p i) (b i) =
      linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i b p := by
    intro i b p
    obtain ⟨hBminus_pos, hprob⟩ := h_platform_bridge b₀ hb₀ p₀ i b p
    obtain ⟨_, _, h_val⟩ := h_conv_slice T
      (fun b_i => linearAggRule b₀ hb₀ p₀ (joinBid i b_i (restrictBids i b)) p)
      (linearAggWithout b₀ hb₀ p₀ i b p) (p i) (opposingBidWithPlatform b₀ i b) hBminus_pos hprob
    unfold linearSecondPriceClosedFormWithPlatform
    by_cases hbi : (b i : ℝ) > 0
    · rw [if_pos hbi, h_val (b i) hbi, joinBid_restrictBids, h_total_split b₀ i b]
    · rw [if_neg hbi]
      have hbi0 : b i = 0 := by
        have hle : (b i : ℝ) ≤ 0 := not_lt.mp hbi
        have heq : (b i : ℝ) = ((0 : Bid) : ℝ) := by simp [le_antisymm hle (by positivity)]
        exact_mod_cast heq
      rw [hbi0]
      simp [myersonTVPayment]
  have hAdm : IsAdmissiblePayment (linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ : PaymentRule n T) := by
    refine ⟨fun i b p => ?_, fun i bOthers p => ?_⟩
    · rw [← hCF i b p]
      obtain ⟨hBminus_pos, hprob⟩ := h_platform_bridge b₀ hb₀ p₀ i b p
      obtain ⟨hq_mono, _, _⟩ := h_conv_slice T
        (fun b_i => linearAggRule b₀ hb₀ p₀ (joinBid i b_i (restrictBids i b)) p)
        (linearAggWithout b₀ hb₀ p₀ i b p) (p i) (opposingBidWithPlatform b₀ i b) hBminus_pos hprob
      exact (h_G_ext T _ (p i) hq_mono (b i)).1
    · unfold linearSecondPriceClosedFormWithPlatform
      simp [joinBid_self]
  have hPayMono : IsPaymentMonotone (robustAgentPrefs n T)
      ⟨linearAggRule b₀ hb₀ p₀, linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀⟩ := by
    intro i p bOthers b_i b'_i
    dsimp only [robustAgentPrefs]
    set bBase := joinBid i 0 bOthers
    set qSlice : Bid → TokenDist T := fun y => linearAggRule b₀ hb₀ p₀ (joinBid i y bOthers) p
    have h_z_eq : ∀ y : Bid,
        linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i (joinBid i y bOthers) p =
          myersonTVPayment qSlice (p i) y := by
      intro y
      rw [← hCF i (joinBid i y bOthers) p, restrictBids_joinBid, joinBid_self]
    rw [h_z_eq b'_i, h_z_eq b_i]
    obtain ⟨hBminus_pos, hprob⟩ := h_platform_bridge b₀ hb₀ p₀ i bBase p
    rw [restrictBids_joinBid] at hprob
    obtain ⟨hq_mono, h_rc, _⟩ := h_conv_slice T qSlice
      (linearAggWithout b₀ hb₀ p₀ i bBase p) (p i) (opposingBidWithPlatform b₀ i bBase) hBminus_pos hprob
    exact h_mono_rc T qSlice (p i) hq_mono h_rc b_i b'_i
  exact ⟨hAdm, hPayMono, hCF⟩

/-- Corollary 5.7 (`cor:second-price-closed-form`, general `b_0 = 0` setting):
    Without a platform bidder, `linearAggNoPlatform pDefault` is robust-monotone, and
    `linearSecondPriceClosedFormGeneral pDefault` is admissible, satisfies payment monotonicity on
    all positive bids (and on all of `ℚ₊` whenever `B_{-i} > 0`), equals `myersonTVPayment` across
    both `B_{-i} > 0` and `B_{-i} = 0`, and is realized by an explicit `[0, 1]²` stable sampler. -/
theorem cor_5_7_linear_closed_form_general (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (pDefault : TokenDist T) :
    IsMonotoneAgg (robustAgentPrefs n T) (linearAggNoPlatform pDefault) ∧
    IsAdmissiblePayment (linearSecondPriceClosedFormGeneral pDefault : PaymentRule n T) ∧
    (∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i) (b_i b'_i : Bid),
      0 < b_i → 0 < b'_i →
        (linearSecondPriceClosedFormGeneral pDefault i (joinBid i b'_i bOthers) p ≤
          linearSecondPriceClosedFormGeneral pDefault i (joinBid i b_i bOthers) p ↔
          RobustPref (p i)
            (linearAggNoPlatform pDefault (joinBid i b_i bOthers) p)
            (linearAggNoPlatform pDefault (joinBid i b'_i bOthers) p))) ∧
    (∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i),
      0 < opposingStrategicBidSum i (joinBid i 0 bOthers) →
      ∀ b_i b'_i : Bid,
        (linearSecondPriceClosedFormGeneral pDefault i (joinBid i b'_i bOthers) p ≤
          linearSecondPriceClosedFormGeneral pDefault i (joinBid i b_i bOthers) p ↔
          RobustPref (p i)
            (linearAggNoPlatform pDefault (joinBid i b_i bOthers) p)
            (linearAggNoPlatform pDefault (joinBid i b'_i bOthers) p))) ∧
    (∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      let qSlice : Bid → TokenDist T :=
        fun b_i => linearAggNoPlatform pDefault (joinBid i b_i (restrictBids i b)) p
      myersonTVPayment qSlice (p i) (b i) =
        linearSecondPriceClosedFormGeneral pDefault i b p ∧
      ∃ (μ₂ : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure μ₂) (σ : Bid → (ℝ × ℝ) → T),
        μ₂ = (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
        IsStableSampler μ₂ qSlice (p i) σ ∧
        secondPriceExpectedPayment μ₂ σ (b i) =
          linearSecondPriceClosedFormGeneral pDefault i b p) := by
  have h_noplat_prob : ∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      0 < opposingStrategicBidSum i b →
      ∀ (b' : Bid) (t : T),
        (linearAggNoPlatform pDefault (joinBid i b' (restrictBids i b)) p).prob t =
          (opposingStrategicBidSum i b *
              (linearAggNoPlatform pDefault (joinBid i 0 (restrictBids i b)) p).prob t +
            (b' : ℝ) * (p i).prob t) /
          ((b' : ℝ) + opposingStrategicBidSum i b) := by
    intro i b p hBminus_pos b' t
    set Bminus := opposingStrategicBidSum i b
    have hB_b' : strategicBidSum (joinBid i b' (restrictBids i b)) = (b' : ℝ) + Bminus :=
      h_strat_sum_join i b' b
    have hB_b'_pos : 0 < strategicBidSum (joinBid i b' (restrictBids i b)) := by
      rw [hB_b']; linarith [show (0 : ℝ) ≤ (b' : ℝ) by positivity]
    have hB_0 : strategicBidSum (joinBid i 0 (restrictBids i b)) = Bminus := by
      have h0 := h_strat_sum_join i 0 b
      simpa using h0
    have hB_0_pos : 0 < strategicBidSum (joinBid i 0 (restrictBids i b)) := by rwa [hB_0]
    have hq0 : Bminus * (linearAggNoPlatform pDefault (joinBid i 0 (restrictBids i b)) p).prob t =
        ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * (p j).prob t := by
      unfold linearAggNoPlatform
      rw [dif_pos hB_0_pos]
      dsimp only
      rw [hB_0, mul_div_cancel₀ _ (ne_of_gt hBminus_pos), h_sum_joinBid i 0 b (fun j => (p j).prob t)]
      simp
    have hqb' : (linearAggNoPlatform pDefault (joinBid i b' (restrictBids i b)) p).prob t =
        ((b' : ℝ) * (p i).prob t + ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * (p j).prob t) /
          ((b' : ℝ) + Bminus) := by
      unfold linearAggNoPlatform
      rw [dif_pos hB_b'_pos]
      dsimp only
      rw [hB_b', h_sum_joinBid i b' b (fun j => (p j).prob t)]
    rw [hqb', hq0]
    ring
  have h_noplat_zero_opp : ∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      opposingStrategicBidSum i b = 0 →
      ∀ b' : Bid, 0 < b' →
        linearAggNoPlatform pDefault (joinBid i b' (restrictBids i b)) p = p i := by
    intro i b p hBminus_eq0 b' hb'
    have hb'_real : 0 < (b' : ℝ) := by exact_mod_cast hb'
    have hbj_zero : ∀ j ∈ Finset.univ.erase i, (b j : ℝ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp hBminus_eq0
    have hB_b' : strategicBidSum (joinBid i b' (restrictBids i b)) = (b' : ℝ) := by
      rw [h_strat_sum_join i b' b, hBminus_eq0, add_zero]
    have hB_b'_pos : 0 < strategicBidSum (joinBid i b' (restrictBids i b)) := by rwa [hB_b']
    ext t
    unfold linearAggNoPlatform
    rw [dif_pos hB_b'_pos]
    dsimp only
    have hrest0 : ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * (p j).prob t = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [hbj_zero j hj, zero_mul])
    rw [hB_b', h_sum_joinBid i b' b (fun j => (p j).prob t), hrest0, add_zero,
      mul_div_cancel_left₀ _ (ne_of_gt hb'_real)]
  have hMonoAgg : IsMonotoneAgg (robustAgentPrefs n T) (linearAggNoPlatform pDefault) := by
    intro i p bOthers b_i b'_i hle
    dsimp only [robustAgentPrefs]
    set bBase := joinBid i 0 bOthers
    have hbBase_rest : restrictBids i bBase = bOthers := restrictBids_joinBid i 0 bOthers
    set Bminus := opposingStrategicBidSum i bBase
    have hBminus_nn : 0 ≤ Bminus := Finset.sum_nonneg (fun _ _ => by positivity)
    rcases eq_or_lt_of_le hBminus_nn with hB0 | hB_pos
    · rcases eq_or_lt_of_le (zero_le b_i) with rfl | hbi_pos
      · have hb'_0 : b'_i = 0 := le_antisymm hle (zero_le b'_i)
        subst hb'_0
        exact ⟨fun _ => le_rfl, fun _ => mul_self_nonneg _⟩
      · have hq_bi : linearAggNoPlatform pDefault (joinBid i b_i bOthers) p = p i := by
          rw [← hbBase_rest]
          exact h_noplat_zero_opp i bBase p hB0.symm b_i hbi_pos
        rw [hq_bi]
        exact ⟨fun t => by simp [abs_nonneg], fun t => by simp⟩
    · have hprob := h_noplat_prob i bBase p hB_pos
      rw [hbBase_rest] at hprob
      exact (h_conv_slice T (fun y => linearAggNoPlatform pDefault (joinBid i y bOthers) p)
        (linearAggNoPlatform pDefault (joinBid i 0 bOthers) p) (p i) Bminus hB_pos hprob).1
        b_i b'_i hle
  have hCF : ∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      myersonTVPayment
        (fun b_i => linearAggNoPlatform pDefault (joinBid i b_i (restrictBids i b)) p)
        (p i) (b i) =
      linearSecondPriceClosedFormGeneral pDefault i b p := by
    intro i b p
    set qSlice : Bid → TokenDist T := fun b_i => linearAggNoPlatform pDefault (joinBid i b_i (restrictBids i b)) p
    set Bminus := opposingStrategicBidSum i b
    have hBminus_nonneg : 0 ≤ Bminus := Finset.sum_nonneg (fun j _ => by positivity)
    unfold linearSecondPriceClosedFormGeneral
    by_cases hcond : (b i : ℝ) > 0 ∧ Bminus > 0
    · rw [if_pos hcond]
      rcases hcond with ⟨hbi_pos, hBminus_pos⟩
      have hprob := h_noplat_prob i b p hBminus_pos
      obtain ⟨_, _, h_val⟩ := h_conv_slice T qSlice (qSlice 0) (p i) Bminus hBminus_pos hprob
      rw [h_val (b i) hbi_pos]
      have hq_self : qSlice (b i) = linearAggNoPlatform pDefault b p := by
        dsimp only [qSlice]
        rw [joinBid_restrictBids]
      rw [hq_self]
    · rw [if_neg hcond]
      rcases eq_or_lt_of_le (zero_le (b i)) with hbi0 | hbi_pos
      · rw [← hbi0]
        simp [myersonTVPayment]
      · have hbi_real_pos : (b i : ℝ) > 0 := by exact_mod_cast hbi_pos
        have hBminus_le0 : Bminus ≤ 0 := by
          by_contra hpos
          push_neg at hpos
          exact hcond ⟨hbi_real_pos, hpos⟩
        have hBminus_eq0 : Bminus = 0 := le_antisymm hBminus_le0 hBminus_nonneg
        have hq_pos_eq : ∀ b' : Bid, 0 < b' → qSlice b' = p i :=
          h_noplat_zero_opp i b p hBminus_eq0
        have hl1_pos_zero : ∀ b' : Bid, 0 < b' → l1Dist (qSlice b') (p i) = 0 := by
          intro b' hb'
          rw [hq_pos_eq b' hb']
          simp [l1Dist]
        have hExt_zero_Ioc : ∀ x ∈ Set.Ioc 0 (b i : ℝ), l1DistRealExt qSlice (p i) x = 0 := by
          intro x hx
          have hx_pos : 0 < x := hx.1
          have hx_not_lt : ¬(x < 0) := not_lt.mpr (le_of_lt hx_pos)
          simp only [l1DistRealExt, hx_not_lt, ↓reduceIte]
          have hbdd : BddBelow ((fun b' : Bid => l1Dist (qSlice b') (p i)) '' {b' : Bid | (b' : ℝ) ≤ x}) :=
            ⟨0, fun _ ⟨_, _, hy⟩ => hy ▸ Finset.sum_nonneg (fun _ _ => abs_nonneg _)⟩
          have hne : ((fun b' : Bid => l1Dist (qSlice b') (p i)) '' {b' : Bid | (b' : ℝ) ≤ x}).Nonempty :=
            ⟨l1Dist (qSlice 0) (p i), 0, by simpa using le_of_lt hx_pos, rfl⟩
          apply le_antisymm
          · obtain ⟨N, hN_gt⟩ := exists_nat_gt (1 / x + 1)
            have hN_pos_real : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hN_gt
            have hN_pos_nat : 0 < N := by exact_mod_cast hN_pos_real
            set b' : Bid := 1 / (N : Bid)
            have hb'_pos : 0 < b' := div_pos zero_lt_one (by exact_mod_cast hN_pos_nat)
            have hb'_le_x : (b' : ℝ) ≤ x := by
              have hb'_real : (b' : ℝ) = 1 / (N : ℝ) := by simp [b']
              rw [hb'_real, div_le_iff₀ hN_pos_real]
              have h1 : 1 / x < (N : ℝ) := by linarith
              have h2 : 1 < (N : ℝ) * x := (div_lt_iff₀ hx.1).mp h1
              linarith
            calc sInf ((fun b'' : Bid => l1Dist (qSlice b'') (p i)) '' {b'' : Bid | (b'' : ℝ) ≤ x})
                ≤ l1Dist (qSlice b') (p i) := csInf_le hbdd ⟨b', hb'_le_x, rfl⟩
              _ = 0 := hl1_pos_zero b' hb'_pos
          · exact le_csInf hne (fun _ ⟨_, _, hy⟩ => hy ▸ Finset.sum_nonneg (fun _ _ => abs_nonneg _))
        unfold myersonTVPayment
        rw [hl1_pos_zero (b i) hbi_pos, intervalIntegral.integral_of_le (le_of_lt hbi_real_pos)]
        have hcongr : ∫ x in Set.Ioc 0 (b i : ℝ), (l1DistRealExt qSlice (p i) x - 0) =
            ∫ x in Set.Ioc 0 (b i : ℝ), (0 : ℝ) := by
          refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
          simp [hExt_zero_Ioc x hx]
        rw [hcongr]
        simp
  have hAdm : IsAdmissiblePayment (linearSecondPriceClosedFormGeneral pDefault : PaymentRule n T) := by
    refine ⟨fun i b p => ?_, fun i bOthers p => ?_⟩
    · rw [← hCF i b p]
      have hq_mono : IsSingleAgentRobustMonotone
          (fun b_i => linearAggNoPlatform pDefault (joinBid i b_i (restrictBids i b)) p) (p i) :=
        fun b₁ b₂ hle => hMonoAgg i p (restrictBids i b) b₁ b₂ hle
      exact (h_G_ext T _ (p i) hq_mono (b i)).1
    · unfold linearSecondPriceClosedFormGeneral
      simp [joinBid_self]
  have hPayMonoPos : ∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i) (b_i b'_i : Bid),
      0 < b_i → 0 < b'_i →
        (linearSecondPriceClosedFormGeneral pDefault i (joinBid i b'_i bOthers) p ≤
          linearSecondPriceClosedFormGeneral pDefault i (joinBid i b_i bOthers) p ↔
          RobustPref (p i)
            (linearAggNoPlatform pDefault (joinBid i b_i bOthers) p)
            (linearAggNoPlatform pDefault (joinBid i b'_i bOthers) p)) := by
    intro i p bOthers b_i b'_i hb_i hb'_i
    set qSlice : Bid → TokenDist T := fun y => linearAggNoPlatform pDefault (joinBid i y bOthers) p
    have h_z_eq : ∀ y : Bid,
        linearSecondPriceClosedFormGeneral pDefault i (joinBid i y bOthers) p =
          myersonTVPayment qSlice (p i) y := by
      intro y
      rw [← hCF i (joinBid i y bOthers) p, restrictBids_joinBid, joinBid_self]
    rw [h_z_eq b'_i, h_z_eq b_i]
    have hq_mono : IsSingleAgentRobustMonotone qSlice (p i) :=
      fun b₁ b₂ hle => hMonoAgg i p bOthers b₁ b₂ hle
    exact (fn_7_second_price_payment_monotone T qSlice (p i) hq_mono).1 b_i b'_i hb_i hb'_i
  have hPayMonoOppPos : ∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i),
      0 < opposingStrategicBidSum i (joinBid i 0 bOthers) →
      ∀ b_i b'_i : Bid,
        (linearSecondPriceClosedFormGeneral pDefault i (joinBid i b'_i bOthers) p ≤
          linearSecondPriceClosedFormGeneral pDefault i (joinBid i b_i bOthers) p ↔
          RobustPref (p i)
            (linearAggNoPlatform pDefault (joinBid i b_i bOthers) p)
            (linearAggNoPlatform pDefault (joinBid i b'_i bOthers) p)) := by
    intro i p bOthers hB_pos b_i b'_i
    set bBase := joinBid i 0 bOthers
    set qSlice : Bid → TokenDist T := fun y => linearAggNoPlatform pDefault (joinBid i y bOthers) p
    have h_z_eq : ∀ y : Bid,
        linearSecondPriceClosedFormGeneral pDefault i (joinBid i y bOthers) p =
          myersonTVPayment qSlice (p i) y := by
      intro y
      rw [← hCF i (joinBid i y bOthers) p, restrictBids_joinBid, joinBid_self]
    rw [h_z_eq b'_i, h_z_eq b_i]
    have hprob := h_noplat_prob i bBase p hB_pos
    rw [restrictBids_joinBid] at hprob
    obtain ⟨hq_mono, h_rc, _⟩ := h_conv_slice T qSlice
      (linearAggNoPlatform pDefault bBase p) (p i) (opposingStrategicBidSum i bBase) hB_pos hprob
    exact h_mono_rc T qSlice (p i) hq_mono h_rc b_i b'_i
  refine ⟨hMonoAgg, hAdm, hPayMonoPos, hPayMonoOppPos, ?_⟩
  intro i b p
  dsimp only
  set qSlice : Bid → TokenDist T :=
    fun b_i => linearAggNoPlatform pDefault (joinBid i b_i (restrictBids i b)) p
  have hq_mono : IsSingleAgentRobustMonotone qSlice (p i) :=
    fun b₁ b₂ hle => hMonoAgg i p (restrictBids i b) b₁ b₂ hle
  obtain ⟨μ₂, hProb, σ, hμ₂, hStab⟩ := thm_5_5_stable_sampling_exists T qSlice (p i) hq_mono
  have hPay := ((prop_5_6_second_price_payment T qSlice (p i) hq_mono (ℝ × ℝ) μ₂ σ hStab).2 (b i)).2.2.2.2.2
  exact ⟨hCF i b p, μ₂, hProb, σ, hμ₂, hStab, hPay.trans (hCF i b p)⟩

/-- Corollary 5.7 & Appendix D.2 right-continuity at `b_i = 0`:
    Expresses `linearSecondPriceClosedFormWithPlatform` directly in terms of the bid-independent
    distance `D = ‖q^*_{-i} - p_i‖₁` across all `b_i ∈ ℚ₊`, proves `ε–δ` right-continuity of
    `linearSecondPriceClosedFormWithPlatform` at `b_i = 0` on `ℚ₊`, and establishes the right-hand
    real limit `(B_{-i} D / 2) (ln((x + B_{-i}) / B_{-i}) - x / (x + B_{-i})) → 0` as `x → 0⁺`. -/
theorem cor_5_7_right_continuity_at_zero :
    (∀ (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
       (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
       (i : Fin n) (bOthers : OpposingBids n i) (p : DistProfile n T),
      let bZero := joinBid i 0 bOthers
      let Bminus := opposingBidWithPlatform b₀ i bZero
      let D := l1Dist (linearAggWithout b₀ hb₀ p₀ i bZero p) (p i)
      (∀ b_i : Bid,
        linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i (joinBid i b_i bOthers) p =
          (Bminus * D / 2) *
            (Real.log (((b_i : ℝ) + Bminus) / Bminus) - (b_i : ℝ) / ((b_i : ℝ) + Bminus))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : Bid, 0 < δ ∧ ∀ b_i : Bid, b_i < δ →
        linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i (joinBid i b_i bOthers) p < ε) ∧
      Filter.Tendsto
        (fun x : ℝ => (Bminus * D / 2) * (Real.log ((x + Bminus) / Bminus) - x / (x + Bminus)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i bZero p))) ∧
    (∀ (Bminus D : ℝ), 0 < Bminus →
      Filter.Tendsto
        (fun x : ℝ => (Bminus * D / 2) * (Real.log ((x + Bminus) / Bminus) - x / (x + Bminus)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)) := by
  have h_cont0 : ∀ (Bminus D : ℝ), 0 < Bminus →
      ContinuousAt
        (fun x : ℝ => (Bminus * D / 2) * (Real.log ((x + Bminus) / Bminus) - x / (x + Bminus))) 0 ∧
      (Bminus * D / 2) * (Real.log (((0 : ℝ) + Bminus) / Bminus) - (0 : ℝ) / ((0 : ℝ) + Bminus)) = 0 := by
    intro Bminus D hBminus
    have hB_ne : Bminus ≠ 0 := ne_of_gt hBminus
    have h0B_ne : (0 : ℝ) + Bminus ≠ 0 := by simpa using hB_ne
    have hdiv_ne : ((0 : ℝ) + Bminus) / Bminus ≠ 0 := by rw [zero_add, div_self hB_ne]; norm_num
    have hcont : ContinuousAt
        (fun x : ℝ => (Bminus * D / 2) * (Real.log ((x + Bminus) / Bminus) - x / (x + Bminus))) 0 := by
      have hc1 : ContinuousAt (fun x : ℝ => (x + Bminus) / Bminus) 0 :=
        (continuousAt_id.add continuousAt_const).div continuousAt_const hB_ne
      have hc2 : ContinuousAt (fun x : ℝ => Real.log ((x + Bminus) / Bminus)) 0 :=
        ContinuousAt.comp (g := Real.log) (f := fun x : ℝ => (x + Bminus) / Bminus)
          (Real.continuousAt_log hdiv_ne) hc1
      have hc3 : ContinuousAt (fun x : ℝ => x / (x + Bminus)) 0 :=
        continuousAt_id.div (continuousAt_id.add continuousAt_const) h0B_ne
      exact continuousAt_const.mul (hc2.sub hc3)
    have hval0 : (Bminus * D / 2) *
        (Real.log (((0 : ℝ) + Bminus) / Bminus) - (0 : ℝ) / ((0 : ℝ) + Bminus)) = 0 := by
      rw [zero_add, div_self hB_ne, Real.log_one, zero_div, sub_self, mul_zero]
    exact ⟨hcont, hval0⟩
  have h_lim : ∀ (Bminus D : ℝ), 0 < Bminus →
      Filter.Tendsto
        (fun x : ℝ => (Bminus * D / 2) * (Real.log ((x + Bminus) / Bminus) - x / (x + Bminus)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    intro Bminus D hBminus
    obtain ⟨hcont, hval0⟩ := h_cont0 Bminus D hBminus
    have htend := hcont.tendsto
    rw [hval0] at htend
    exact tendsto_nhdsWithin_of_tendsto_nhds htend
  refine ⟨?_, h_lim⟩
  intro n T _ _ b₀ hb₀ p₀ i bOthers p
  dsimp only
  set bZero := joinBid i 0 bOthers
  set Bminus := opposingBidWithPlatform b₀ i bZero
  set qWithout := linearAggWithout b₀ hb₀ p₀ i bZero p
  set D := l1Dist qWithout (p i)
  obtain ⟨hBminus_pos, hprob⟩ := h_platform_bridge b₀ hb₀ p₀ i bZero p
  have h_opp_inv : ∀ b_i : Bid, opposingBidWithPlatform b₀ i (joinBid i b_i bOthers) = Bminus := by
    intro b_i
    unfold opposingBidWithPlatform opposingStrategicBidSum
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [bZero, joinBid, hji]
  have h_without_inv : ∀ b_i : Bid, linearAggWithout b₀ hb₀ p₀ i (joinBid i b_i bOthers) p = qWithout := by
    intro b_i
    dsimp only [qWithout, bZero]
    unfold linearAggWithout
    rw [restrictBids_joinBid, restrictBids_joinBid]
  have h_formula : ∀ b_i : Bid,
      linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i (joinBid i b_i bOthers) p =
        (Bminus * D / 2) *
          (Real.log (((b_i : ℝ) + Bminus) / Bminus) - (b_i : ℝ) / ((b_i : ℝ) + Bminus)) := by
    intro b_i
    unfold linearSecondPriceClosedFormWithPlatform
    rw [joinBid_self]
    by_cases hbi : (b_i : ℝ) > 0
    · rw [if_pos hbi]
      dsimp only
      rw [h_opp_inv b_i, h_without_inv b_i]
      have hB_eq : totalBidWithPlatform b₀ (joinBid i b_i bOthers) = (b_i : ℝ) + Bminus := by
        rw [h_total_split b₀ i (joinBid i b_i bOthers), joinBid_self, h_opp_inv b_i]
      rw [hB_eq]
      have hden_pos : 0 < (b_i : ℝ) + Bminus := add_pos hbi hBminus_pos
      have hden_ne : (b_i : ℝ) + Bminus ≠ 0 := ne_of_gt hden_pos
      have hbi_ne : (b_i : ℝ) ≠ 0 := ne_of_gt hbi
      have hdiff_t : ∀ t : T,
          qWithout.prob t - (linearAggRule b₀ hb₀ p₀ (joinBid i b_i bOthers) p).prob t =
            ((b_i : ℝ) / ((b_i : ℝ) + Bminus)) * (qWithout.prob t - (p i).prob t) := by
        intro t
        have hp_t := hprob b_i t
        rw [restrictBids_joinBid] at hp_t
        rw [hp_t]
        field_simp [hden_ne]
        ring
      have hl1_eq : l1Dist qWithout (linearAggRule b₀ hb₀ p₀ (joinBid i b_i bOthers) p) =
          ((b_i : ℝ) / ((b_i : ℝ) + Bminus)) * D := by
        have hfac_nn : 0 ≤ (b_i : ℝ) / ((b_i : ℝ) + Bminus) :=
          div_nonneg (le_of_lt hbi) (le_of_lt hden_pos)
        unfold l1Dist
        dsimp only [D]
        unfold l1Dist
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [hdiff_t t, abs_mul, abs_of_nonneg hfac_nn]
      rw [hl1_eq]
      field_simp [hbi_ne, hden_ne]
    · rw [if_neg hbi]
      have hbi0 : (b_i : ℝ) = 0 := le_antisymm (not_lt.mp hbi) (by positivity)
      rw [hbi0, zero_add, div_self (ne_of_gt hBminus_pos), Real.log_one, zero_div, sub_self, mul_zero]
  have hz0 : linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i bZero p = 0 := by
    dsimp only [bZero]
    unfold linearSecondPriceClosedFormWithPlatform
    simp [joinBid_self]
  refine ⟨h_formula, ?_, ?_⟩
  · intro ε hε
    obtain ⟨hcont, hval0⟩ := h_cont0 Bminus D hBminus_pos
    obtain ⟨δ_r, hδ_r_pos, hδ_r_spec⟩ := Metric.continuousAt_iff.mp hcont ε hε
    obtain ⟨N, hN_gt⟩ := exists_nat_gt (1 / δ_r + 1)
    have hN_pos_r : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hN_gt
    have hN_pos : 0 < N := by exact_mod_cast hN_pos_r
    set δ : Bid := 1 / (N : Bid)
    have hδ_pos : 0 < δ := div_pos zero_lt_one (by exact_mod_cast hN_pos)
    have hδ_lt_r : (δ : ℝ) < δ_r := by
      have hδ_eq : (δ : ℝ) = 1 / (N : ℝ) := by simp [δ]
      rw [hδ_eq, div_lt_iff₀ hN_pos_r]
      have h1 : 1 / δ_r < (N : ℝ) := by linarith
      have h2 : 1 < (N : ℝ) * δ_r := (div_lt_iff₀ hδ_r_pos).mp h1
      linarith
    refine ⟨δ, hδ_pos, ?_⟩
    intro b_i hb_i
    have hbi_lt : (b_i : ℝ) < δ_r := lt_trans (by exact_mod_cast hb_i) hδ_lt_r
    have hdist : dist (b_i : ℝ) 0 < δ_r := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      exact hbi_lt
    have h_near := hδ_r_spec hdist
    rw [Real.dist_eq, hval0, sub_zero] at h_near
    rw [h_formula b_i]
    exact lt_of_le_of_lt (le_abs_self _) h_near
  · rw [hz0]
    exact h_lim Bminus D hBminus_pos

/-- End-to-end synthesis of Remark 5.2, Theorem 5.5, Proposition 5.6, and Corollary 5.7:
    for every strategic bidder `i` and opposing profile, the linear aggregation rule `q_KL` admits
    a stable sampling implementation on `[0, 1]²` whose expected second-price payment equals
    `linearSecondPriceClosedFormWithPlatform`. -/
theorem cor_5_7_linear_stable_sampler_payment (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
    (i : Fin n) (b : BidProfile n) (p : DistProfile n T) :
    let qSlice : Bid → TokenDist T :=
      fun b_i => linearAggRule b₀ hb₀ p₀ (joinBid i b_i (restrictBids i b)) p
    ∃ (μ₂ : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure μ₂) (σ : Bid → (ℝ × ℝ) → T),
      μ₂ = (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      IsStableSampler μ₂ qSlice (p i) σ ∧
      secondPriceExpectedPayment μ₂ σ (b i) =
        linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i b p := by
  intro qSlice
  have hMonoAgg := (rem_5_2_linear_monotone_consistent n T b₀ hb₀ p₀).1
  have hMonoSlice : IsSingleAgentRobustMonotone qSlice (p i) :=
    fun b₁ b₂ hle => hMonoAgg i p (restrictBids i b) b₁ b₂ hle
  obtain ⟨μ₂, hProb, σ, hμ₂, hStab⟩ := thm_5_5_stable_sampling_exists T qSlice (p i) hMonoSlice
  have hPay := ((prop_5_6_second_price_payment T qSlice (p i) hMonoSlice (ℝ × ℝ) μ₂ σ hStab).2 (b i)).2.2.2.2.2
  have hCF := (cor_5_7_linear_closed_form_with_platform n T b₀ hb₀ p₀).2.2 i b p
  exact ⟨μ₂, hProb, σ, hμ₂, hStab, hPay.trans hCF⟩

/-! ## Remark 5.8: Comparison Between Forward-KL VCG & Second-Price Payments -/

/-- Remark 5.8 (`rmk:payment-comparison`, supplementary zero-payment comparison): Under full support,
    both `forwardKLVCGPayment` and `linearSecondPriceClosedFormWithPlatform` equal `0` if and only if
    agent `i` does not move the aggregate distribution (`q_KL(b, p) = q^*_{-i}`). -/
theorem rem_5_8_zero_payment_iff (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
    (i : Fin n) (b : BidProfile n) (p : DistProfile n T)
    (hp₀ : HasFullSupport p₀) (_hp : ∀ j : Fin n, HasFullSupport (p j)) :
    (forwardKLVCGPayment b₀ hb₀ p₀ i b p = 0 ↔
        linearAggRule b₀ hb₀ p₀ b p = linearAggWithout b₀ hb₀ p₀ i b p) ∧
    (linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ i b p = 0 ↔
        linearAggRule b₀ hb₀ p₀ b p = linearAggWithout b₀ hb₀ p₀ i b p) := by
  set qOut := linearAggRule b₀ hb₀ p₀ b p
  set qWithout := linearAggWithout b₀ hb₀ p₀ i b p
  set Bminus := opposingBidWithPlatform b₀ i b
  have hb₀_pos : (0 : ℝ) < (b₀ : ℝ) := by exact_mod_cast hb₀
  have hBminus_pos : 0 < Bminus := by
    dsimp only [Bminus, opposingBidWithPlatform]
    have : 0 ≤ opposingStrategicBidSum i b := Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have h_lin_pos : ∀ (bProf : BidProfile n) (t : T), 0 < (linearAggRule b₀ hb₀ p₀ bProf p).prob t := by
    intro bProf t
    unfold linearAggRule
    dsimp only
    apply div_pos _ (totalBidWithPlatform_pos hb₀ bProf)
    have h1 : 0 < (b₀ : ℝ) * p₀.prob t := mul_pos hb₀_pos (hp₀ t)
    have h2 : 0 ≤ ∑ j : Fin n, (bProf j : ℝ) * (p j).prob t :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) ((p j).nonneg t))
    linarith
  have hqOut_pos : ∀ t : T, 0 < qOut.prob t := h_lin_pos b
  have hqWithout_pos : ∀ t : T, 0 < qWithout.prob t := h_lin_pos (joinBid i 0 (restrictBids i b))
  refine ⟨?_, ?_⟩
  · change Bminus * klDiv qWithout qOut = 0 ↔ qOut = qWithout
    rw [mul_eq_zero]
    simp only [ne_of_gt hBminus_pos, false_or]
    rw [(lem_gibbs_inequality T qWithout qOut hqOut_pos).2.2, eq_comm]
  · unfold linearSecondPriceClosedFormWithPlatform
    by_cases hbi : (b i : ℝ) > 0
    · rw [if_pos hbi]
      set B := totalBidWithPlatform b₀ b
      have hB_split : B = (b i : ℝ) + Bminus := h_total_split b₀ i b
      have hB_pos : 0 < B := by linarith
      set Φ := (B / (2 * (b i : ℝ))) * Real.log (B / Bminus) - (1 / 2 : ℝ)
      have hΦ_pos : 0 < Φ := by
        have hy_pos : 0 < Bminus / B := div_pos hBminus_pos hB_pos
        have hy_ne1 : Bminus / B ≠ 1 := by
          intro h1
          have := (div_eq_one_iff_eq (ne_of_gt hB_pos)).mp h1
          linarith
        have hlt := Real.log_lt_sub_one_of_pos hy_pos hy_ne1
        have hlog_inv : Real.log (Bminus / B) = -Real.log (B / Bminus) := by
          rw [Real.log_div (ne_of_gt hBminus_pos) (ne_of_gt hB_pos),
            Real.log_div (ne_of_gt hB_pos) (ne_of_gt hBminus_pos)]
          ring
        have hrhs : Bminus / B - 1 = -((b i : ℝ) / B) := by
          have hB_ne : B ≠ 0 := ne_of_gt hB_pos
          field_simp [hB_ne]
          linarith
        rw [hlog_inv, hrhs] at hlt
        have hlog_gt : (b i : ℝ) / B < Real.log (B / Bminus) := by linarith
        have hfac_pos : 0 < B / (2 * (b i : ℝ)) := div_pos hB_pos (by linarith)
        have hmul := mul_lt_mul_of_pos_left hlog_gt hfac_pos
        have hcancel : (B / (2 * (b i : ℝ))) * ((b i : ℝ) / B) = (1 / 2 : ℝ) := by
          have hB_ne : B ≠ 0 := ne_of_gt hB_pos
          have hbi_ne : (b i : ℝ) ≠ 0 := ne_of_gt hbi
          field_simp [hB_ne, hbi_ne]
        rw [hcancel] at hmul
        dsimp only [Φ]
        linarith
      constructor
      · intro hprod0
        have hl1_0 : l1Dist qWithout qOut = 0 := by
          rcases mul_eq_zero.mp hprod0 with h1 | h2
          · rcases mul_eq_zero.mp h1 with hB0 | hl0
            · exact absurd hB0 (ne_of_gt hBminus_pos)
            · exact hl0
          · exact absurd h2 (ne_of_gt hΦ_pos)
        ext t
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => abs_nonneg _)).mp hl1_0 t (Finset.mem_univ t)
        have := sub_eq_zero.mp (abs_eq_zero.mp h0)
        exact this.symm
      · intro heq
        dsimp only [qOut, qWithout] at heq
        have hl1_0 : l1Dist qWithout qOut = 0 := by
          dsimp only [qOut, qWithout]
          rw [heq]
          simp [l1Dist]
        dsimp only [B, Bminus, qOut, qWithout, Φ] at hl1_0 ⊢
        rw [hl1_0, mul_zero, zero_mul]
    · rw [if_neg hbi]
      have hbi0 : b i = 0 := by
        have hle : (b i : ℝ) ≤ 0 := not_lt.mp hbi
        have heq : (b i : ℝ) = ((0 : Bid) : ℝ) := by simpa using le_antisymm hle (by positivity)
        exact_mod_cast heq
      have heq_q : qOut = qWithout := by
        dsimp only [qOut, qWithout, linearAggWithout]
        rw [← hbi0, joinBid_restrictBids]
      exact ⟨fun _ => heq_q, fun _ => rfl⟩

/-- Remark 5.8 (`rmk:payment-comparison`, non-coincidence): Forward-KL VCG payments and linear
    second-price payments do not coincide in general (`forwardKLVCGPayment ≠
    linearSecondPriceClosedFormWithPlatform` on a full-support binary-token instance). -/
theorem rem_5_8_vcg_ne_second_price :
    ∃ (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist (Fin 2))
      (b : BidProfile 1) (p : DistProfile 1 (Fin 2)),
      HasFullSupport p₀ ∧ (∀ j : Fin 1, HasFullSupport (p j)) ∧
      forwardKLVCGPayment b₀ hb₀ p₀ 0 b p ≠
        linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ 0 b p := by
  let b₀ : Bid := 1
  have hb₀ : (0 : Bid) < b₀ := by decide
  let p₀ : TokenDist (Fin 2) :=
    { prob := fun _ => 1 / 2
      nonneg := fun _ => by norm_num
      sum_eq_one := by rw [Fin.sum_univ_two]; norm_num }
  let p₁ : TokenDist (Fin 2) :=
    { prob := fun t => if t = 0 then 3 / 4 else 1 / 4
      nonneg := fun t => by fin_cases t <;> norm_num
      sum_eq_one := by rw [Fin.sum_univ_two]; norm_num }
  let b : BidProfile 1 := fun _ => 1
  let p : DistProfile 1 (Fin 2) := fun _ => p₁
  refine ⟨b₀, hb₀, p₀, b, p, ?_, ?_, ?_⟩
  · intro t; dsimp [p₀]; norm_num
  · intro j t; fin_cases t <;> dsimp [p, p₁] <;> norm_num
  · have hBminus : opposingBidWithPlatform b₀ 0 b = 1 := by
      simp [opposingBidWithPlatform, opposingStrategicBidSum, b₀]
    have hB : totalBidWithPlatform b₀ b = 2 := by
      simp [totalBidWithPlatform, strategicBidSum, b₀, b]
      norm_num
    have hqW0 : (linearAggWithout b₀ hb₀ p₀ 0 b p).prob 0 = 1 / 2 := by
      unfold linearAggWithout linearAggRule
      dsimp only
      have htot0 : totalBidWithPlatform b₀ (joinBid 0 0 (restrictBids 0 b)) = 1 := by
        simp [totalBidWithPlatform, strategicBidSum, joinBid, b₀]
      rw [htot0]
      simp [joinBid, b₀, p₀]
    have hqW1 : (linearAggWithout b₀ hb₀ p₀ 0 b p).prob 1 = 1 / 2 := by
      unfold linearAggWithout linearAggRule
      dsimp only
      have htot0 : totalBidWithPlatform b₀ (joinBid 0 0 (restrictBids 0 b)) = 1 := by
        simp [totalBidWithPlatform, strategicBidSum, joinBid, b₀]
      rw [htot0]
      simp [joinBid, b₀, p₀]
    have hqO0 : (linearAggRule b₀ hb₀ p₀ b p).prob 0 = 5 / 8 := by
      unfold linearAggRule
      dsimp only
      rw [hB]
      simp [b₀, b, p₀, p, p₁]
      norm_num
    have hqO1 : (linearAggRule b₀ hb₀ p₀ b p).prob 1 = 3 / 8 := by
      unfold linearAggRule
      dsimp only
      rw [hB]
      simp [b₀, b, p₀, p, p₁]
      norm_num
    have hv_eq : forwardKLVCGPayment b₀ hb₀ p₀ 0 b p = (1 / 2 : ℝ) * Real.log (16 / 15) := by
      unfold forwardKLVCGPayment klDiv
      rw [hBminus, Fin.sum_univ_two, hqW0, hqW1, hqO0, hqO1]
      have hdiv1 : (1 / 2 : ℝ) / (5 / 8) = 4 / 5 := by norm_num
      have hdiv2 : (1 / 2 : ℝ) / (3 / 8) = 4 / 3 := by norm_num
      rw [hdiv1, hdiv2]
      have hlog_add : Real.log (4 / 5) + Real.log (4 / 3) = Real.log (16 / 15) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      linarith
    have hsp_eq : linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ 0 b p =
        (1 / 4 : ℝ) * (Real.log 2 - 1 / 2) := by
      unfold linearSecondPriceClosedFormWithPlatform
      have hb0_pos : (b 0 : ℝ) > 0 := by simp [b]
      rw [if_pos hb0_pos]
      dsimp only
      have hl1 : l1Dist (linearAggWithout b₀ hb₀ p₀ 0 b p) (linearAggRule b₀ hb₀ p₀ b p) = 1 / 4 := by
        unfold l1Dist
        rw [Fin.sum_univ_two, hqW0, hqW1, hqO0, hqO1]
        norm_num
      have hb0_val : (b 0 : ℝ) = 1 := by simp [b]
      rw [hBminus, hB, hl1, hb0_val]
      norm_num
    have hv_le : forwardKLVCGPayment b₀ hb₀ p₀ 0 b p ≤ 1 / 30 := by
      rw [hv_eq]
      have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16 / 15)
      linarith
    have hsp_gt : (1 / 30 : ℝ) < linearSecondPriceClosedFormWithPlatform b₀ hb₀ p₀ 0 b p := by
      rw [hsp_eq]
      have hlog2 := Real.log_two_gt_d9
      linarith
    exact ne_of_lt (lt_of_le_of_lt hv_le hsp_gt)

end

end TokenAuctions
