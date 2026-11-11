import TokenAuctions.Defs

set_option maxHeartbeats 4000000

/-!
# Idealized KL-Divergence Benchmark: Forward-KL & Reverse-KL VCG Mechanisms

This module formalizes Section 2.1 (`appendTrim` validity), Section 3 (Lemma 3.1, Theorem 3.2,
Remark 3.3), Appendix A, Appendix B (Lemma B.1, Theorem B.2), and Section 6.2 (perplexity and
Footnote 9) of *Mechanism Design for Large Language Models: Token Auctions with Proxy Bidders*.

## Main Results
- `sec_2_1_appendTrim_valid`: Model sanity lemma — appending a token and trimming to context window
  `K` preserves `1 ≤ |s| ≤ K` (Section 2.1).
- `lem_gibbs_inequality`: Cross-entropy decomposition `D_KL(p ‖ q) = H(p, q) - H(p)` and Gibbs'
  inequality (`0 ≤ D_KL(p ‖ q)`, with equality iff `p = q`).
- `lem_3_1_kl_linear_rule`: Forward-KL social welfare decomposition and unique maximization over
  full-support distributions `q ∈ Δ(T)` by the linear aggregation rule `q_KL` (Lemma 3.1 &
  Appendix A).
- `thm_3_2_kl_vcg`: Forward-KL VCG mechanism `𝓜_KL = ⟨q_KL, z⟩` — payment admissibility,
  closed-form Clarke pivot identity `z_i(b, p) = B_{-i} D_KL(q^*_{-i} ‖ q_KL(b, p))`, Ex-Post
  Individual Rationality, and joint Dominant-Strategy Incentive Compatibility in `(b_i, p_i)` over
  admissible full-support reports (Theorem 3.2).
- `lem_B_1_reverse_kl_rule`: Log-linear (geometric) aggregation rule `q̄_KL`, reverse-KL
  Pythagorean identity, and unique maximization of reverse-KL social welfare on all of `Δ(T)`
  (Remark 3.3 & Lemma B.1).
- `thm_B_2_reverse_kl_vcg`: Reverse-KL VCG mechanism `𝓜̄_KL = ⟨q̄_KL, z̄⟩` — payment admissibility,
  Clarke pivot identity `z̄_i(b, p) = B_{-i} D_KL(q̄_KL(b, p) ‖ q̄^*_{-i})`, Ex-Post IR, and joint
  DSIC over admissible full-support reports (Theorem B.2).
- `sec_6_2_perplexity_pos` and `fn_9_perplexity_cross_entropy`: Positivity sanity lemma for sequence
  perplexity `PPL_i(s_m) > 0` (Section 6.2) and cross-entropy / reverse-KL decomposition
  `H(q, p_i) = D_KL(q ‖ p_i) + H(q)` (Footnote 9).
-/

namespace TokenAuctions

open scoped BigOperators
open Classical MeasureTheory

noncomputable section

/-! ## Section 2.1: Context-Window Sequence Update -/

/-- Section 2.1 (model sanity lemma): Autoregressive `appendTrim` preserves `1 ≤ |s| ≤ K`. -/
theorem sec_2_1_appendTrim_valid (T : Type) (K : ℕ) (s : List T) (τ : T)
    (hK : 1 ≤ K) (hs : IsValidContextSeq K s) :
    IsValidContextSeq K (appendTrim K s τ) := by
  rcases hs with ⟨hs1, hs2⟩
  dsimp [IsValidContextSeq, appendTrim]
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  omega

/-! ## Gibbs' Inequality & Cross-Entropy Decomposition -/

/-- Cross-entropy decomposition `D_KL(p ‖ q) = H(p, q) - H(p)` and Gibbs' inequality on `Δ(T)`. -/
theorem lem_gibbs_inequality (T : Type) [Fintype T] [DecidableEq T] (p q : TokenDist T)
    (hq : HasFullSupport q) :
    klDiv p q = crossEntropy p q - shannonEntropy p ∧
    0 ≤ klDiv p q ∧
    (klDiv p q = 0 ↔ p = q) := by
  have h_decomp : klDiv p q = crossEntropy p q - shannonEntropy p := by
    unfold klDiv crossEntropy shannonEntropy
    have h_rhs : - ∑ t : T, p.prob t * Real.log (q.prob t) - - ∑ t : T, p.prob t * Real.log (p.prob t) =
        ∑ t : T, (p.prob t * Real.log (p.prob t) - p.prob t * Real.log (q.prob t)) := by
      rw [Finset.sum_sub_distrib]
      ring
    rw [h_rhs]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hpt : p.prob t = 0
    · simp [hpt]
    · rw [Real.log_div hpt (ne_of_gt (hq t))]
      ring
  let f : T → ℝ := fun t => p.prob t * Real.log (p.prob t / q.prob t) - (p.prob t - q.prob t)
  have hf_sum : ∑ t : T, f t = klDiv p q := by
    dsimp [f]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, p.sum_eq_one, q.sum_eq_one]
    unfold klDiv
    ring
  have hf_nonneg : ∀ t : T, 0 ≤ f t := by
    intro t
    dsimp [f]
    by_cases hpt : p.prob t = 0
    · simp [hpt, le_of_lt (hq t)]
    · have hp_pos : 0 < p.prob t := lt_of_le_of_ne (p.nonneg t) (Ne.symm hpt)
      have hq_pos : 0 < q.prob t := hq t
      set r : ℝ := q.prob t / p.prob t
      have hr_pos : 0 < r := div_pos hq_pos hp_pos
      have h_log : Real.log (p.prob t / q.prob t) = - Real.log r := by
        have h_inv : p.prob t / q.prob t = r⁻¹ := by
          dsimp [r]
          rw [inv_div]
        rw [h_inv, Real.log_inv]
      have h_pr : p.prob t * r = q.prob t := mul_div_cancel₀ (q.prob t) hpt
      have h_alg : p.prob t * Real.log (p.prob t / q.prob t) - (p.prob t - q.prob t) =
          p.prob t * ((r - 1) - Real.log r) := by
        rw [h_log, ← h_pr]
        ring
      rw [h_alg]
      have h_le : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr_pos
      exact mul_nonneg (le_of_lt hp_pos) (sub_nonneg.mpr h_le)
  have hf_eq_zero : ∀ t : T, f t = 0 ↔ p.prob t = q.prob t := by
    intro t
    dsimp [f]
    by_cases hpt : p.prob t = 0
    · have hq_ne : q.prob t ≠ 0 := ne_of_gt (hq t)
      simp [hpt, hq_ne, Ne.symm hq_ne]
    · have hp_pos : 0 < p.prob t := lt_of_le_of_ne (p.nonneg t) (Ne.symm hpt)
      have hq_pos : 0 < q.prob t := hq t
      constructor
      · intro hft
        set r : ℝ := q.prob t / p.prob t
        have hr_pos : 0 < r := div_pos hq_pos hp_pos
        have h_log : Real.log (p.prob t / q.prob t) = - Real.log r := by
          have h_inv : p.prob t / q.prob t = r⁻¹ := by
            dsimp [r]
            rw [inv_div]
          rw [h_inv, Real.log_inv]
        have h_pr : p.prob t * r = q.prob t := mul_div_cancel₀ (q.prob t) hpt
        have h_alg : p.prob t * ((r - 1) - Real.log r) = 0 := by
          calc p.prob t * ((r - 1) - Real.log r)
              = p.prob t * (- Real.log r) - (p.prob t - p.prob t * r) := by ring
            _ = p.prob t * Real.log (p.prob t / q.prob t) - (p.prob t - q.prob t) := by rw [h_log, h_pr]
            _ = 0 := hft
        have h_sub_zero : (r - 1) - Real.log r = 0 :=
          (mul_eq_zero.mp h_alg).resolve_left hpt
        have hr_eq_one : r = 1 := by
          by_contra hr_ne
          have h_lt : Real.log r < r - 1 := Real.log_lt_sub_one_of_pos hr_pos hr_ne
          linarith
        have hqp : q.prob t = p.prob t := by
          calc q.prob t = p.prob t * r := h_pr.symm
            _ = p.prob t * 1 := by rw [hr_eq_one]
            _ = p.prob t := mul_one _
        exact hqp.symm
      · intro hpq
        rw [hpq, div_self (ne_of_gt hq_pos), Real.log_one]
        ring
  have h_kl_nonneg : 0 ≤ klDiv p q := by
    rw [← hf_sum]
    exact Finset.sum_nonneg (fun t _ => hf_nonneg t)
  have h_kl_zero : klDiv p q = 0 ↔ p = q := by
    rw [← hf_sum, Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hf_nonneg t)]
    simp only [Finset.mem_univ, forall_true_left, hf_eq_zero]
    exact ⟨fun h => TokenDist.ext (funext h), fun h t => by rw [h]⟩
  exact ⟨h_decomp, h_kl_nonneg, h_kl_zero⟩

/-! ## Internal Algebraic Helpers for Forward-KL and Reverse-KL VCG -/

private lemma forwardKL_welfare_decomp (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
    (b : BidProfile n) (p : DistProfile n T) (hp₀ : HasFullSupport p₀) :
    let qKL := linearAggRule b₀ hb₀ p₀ b p
    HasFullSupport qKL ∧
    (∀ q : TokenDist T, HasFullSupport q →
      forwardKLSocialWelfare b₀ p₀ b p q =
        - totalBidWithPlatform b₀ b * crossEntropy qKL q +
          ((b₀ : ℝ) * shannonEntropy p₀ + ∑ i : Fin n, (b i : ℝ) * shannonEntropy (p i)) ∧
      forwardKLSocialWelfare b₀ p₀ b p qKL - forwardKLSocialWelfare b₀ p₀ b p q =
        totalBidWithPlatform b₀ b * klDiv qKL q) := by
  set qKL := linearAggRule b₀ hb₀ p₀ b p
  set B := totalBidWithPlatform b₀ b
  have hB_pos : 0 < B := totalBidWithPlatform_pos hb₀ b
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have hqKL_supp : HasFullSupport qKL := by
    intro t
    dsimp [qKL, linearAggRule]
    have hb₀' : (0 : ℝ) < (b₀ : ℝ) := by exact_mod_cast hb₀
    have h1 : 0 < (b₀ : ℝ) * p₀.prob t := mul_pos hb₀' (hp₀ t)
    have h2 : 0 ≤ ∑ i : Fin n, (b i : ℝ) * (p i).prob t :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) ((p i).nonneg t))
    exact div_pos (add_pos_of_pos_of_nonneg h1 h2) hB_pos
  have h_ce_exp : ∀ q : TokenDist T, HasFullSupport q →
      forwardKLSocialWelfare b₀ p₀ b p q =
        - B * crossEntropy qKL q +
          ((b₀ : ℝ) * shannonEntropy p₀ + ∑ i : Fin n, (b i : ℝ) * shannonEntropy (p i)) := by
    intro q hq
    have hd0 : klDiv p₀ q = crossEntropy p₀ q - shannonEntropy p₀ :=
      (lem_gibbs_inequality T p₀ q hq).1
    have hdi : ∀ i : Fin n, klDiv (p i) q = crossEntropy (p i) q - shannonEntropy (p i) :=
      fun i => (lem_gibbs_inequality T (p i) q hq).1
    have h_ce_sum : (b₀ : ℝ) * crossEntropy p₀ q + ∑ i : Fin n, (b i : ℝ) * crossEntropy (p i) q =
        B * crossEntropy qKL q := by
      unfold crossEntropy
      have h_lhs : (b₀ : ℝ) * (- ∑ t : T, p₀.prob t * Real.log (q.prob t)) +
          ∑ i : Fin n, (b i : ℝ) * (- ∑ t : T, (p i).prob t * Real.log (q.prob t)) =
          - ∑ t : T, (((b₀ : ℝ) * p₀.prob t + ∑ i : Fin n, (b i : ℝ) * (p i).prob t) * Real.log (q.prob t)) := by
        have h_term0 : (b₀ : ℝ) * (- ∑ t : T, p₀.prob t * Real.log (q.prob t)) =
            - ∑ t : T, (b₀ : ℝ) * p₀.prob t * Real.log (q.prob t) := by
          rw [mul_neg, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro t _; ring
        have h_termi : ∑ i : Fin n, (b i : ℝ) * (- ∑ t : T, (p i).prob t * Real.log (q.prob t)) =
            - ∑ t : T, (∑ i : Fin n, (b i : ℝ) * (p i).prob t) * Real.log (q.prob t) := by
          trans (- ∑ i : Fin n, ∑ t : T, (b i : ℝ) * (p i).prob t * Real.log (q.prob t))
          · rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i _
            rw [mul_neg, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro t _; ring
          · rw [Finset.sum_comm]
            congr 1
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.sum_mul]
        rw [h_term0, h_termi, ← neg_add, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro t _; ring
      have h_rhs : B * (- ∑ t : T, qKL.prob t * Real.log (q.prob t)) =
          - ∑ t : T, (((b₀ : ℝ) * p₀.prob t + ∑ i : Fin n, (b i : ℝ) * (p i).prob t) * Real.log (q.prob t)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        have hqKL_t : B * qKL.prob t = (b₀ : ℝ) * p₀.prob t + ∑ i : Fin n, (b i : ℝ) * (p i).prob t := by
          dsimp [qKL, linearAggRule]
          exact mul_div_cancel₀ _ hB_ne
        calc B * (qKL.prob t * Real.log (q.prob t))
            = (B * qKL.prob t) * Real.log (q.prob t) := by ring
          _ = ((b₀ : ℝ) * p₀.prob t + ∑ i : Fin n, (b i : ℝ) * (p i).prob t) * Real.log (q.prob t) := by
              rw [hqKL_t]
      rw [h_lhs, h_rhs]
    unfold forwardKLSocialWelfare
    have h_split : ∑ i : Fin n, (b i : ℝ) * klDiv (p i) q =
        (∑ i : Fin n, (b i : ℝ) * crossEntropy (p i) q) -
        (∑ i : Fin n, (b i : ℝ) * shannonEntropy (p i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hdi i]; ring
    rw [hd0, h_split]
    linarith [h_ce_sum]
  refine ⟨hqKL_supp, fun q hq => ⟨h_ce_exp q hq, ?_⟩⟩
  have h1 := h_ce_exp q hq
  have h2 := h_ce_exp qKL hqKL_supp
  have h_self : crossEntropy qKL qKL = shannonEntropy qKL := rfl
  have h_kl : klDiv qKL q = crossEntropy qKL q - shannonEntropy qKL :=
    (lem_gibbs_inequality T qKL q hq).1
  rw [h_self] at h2
  rw [h1, h2, h_kl]
  ring

private lemma reverseKL_pythagorean_gen (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
    (b : BidProfile n) (p : DistProfile n T) :
    let qBar := logLinearAggRule b₀ hb₀ p₀ b p
    HasFullSupport qBar ∧
    (∀ t : T, Real.log (qBar.prob t) = logLinearScore b₀ p₀ b p t - logLinearNormConst b₀ p₀ b p) ∧
    (HasFullSupport p₀ → (∀ i : Fin n, (b i : ℝ) ≠ 0 → HasFullSupport (p i)) →
      ∀ q : TokenDist T,
        ((b₀ : ℝ) * klDiv q p₀ + ∑ i : Fin n, (b i : ℝ) * klDiv q (p i)) =
          totalBidWithPlatform b₀ b * klDiv q qBar +
            ((b₀ : ℝ) * klDiv qBar p₀ + ∑ i : Fin n, (b i : ℝ) * klDiv qBar (p i))) := by
  set qBar := logLinearAggRule b₀ hb₀ p₀ b p
  set B := totalBidWithPlatform b₀ b
  set u := logLinearScore b₀ p₀ b p
  set C := logLinearNormConst b₀ p₀ b p
  have hqBar_supp : HasFullSupport qBar := by
    intro t
    dsimp [qBar, logLinearAggRule]
    exact Real.exp_pos _
  have hqBar_log : ∀ t : T, Real.log (qBar.prob t) = u t - C := by
    intro t
    dsimp [qBar, logLinearAggRule, u, C, logLinearNormConst]
    exact Real.log_exp _
  refine ⟨hqBar_supp, hqBar_log, ?_⟩
  intro hp₀ hp q
  have hB_pos : 0 < B := totalBidWithPlatform_pos hb₀ b
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have h_phi : ∀ r : TokenDist T,
      (b₀ : ℝ) * klDiv r p₀ + ∑ i : Fin n, (b i : ℝ) * klDiv r (p i) =
        B * klDiv r qBar - B * C := by
    intro r
    have h_lhs : (b₀ : ℝ) * klDiv r p₀ + ∑ i : Fin n, (b i : ℝ) * klDiv r (p i) =
        ∑ t : T, ((b₀ : ℝ) * (r.prob t * Real.log (r.prob t / p₀.prob t)) +
          ∑ i : Fin n, (b i : ℝ) * (r.prob t * Real.log (r.prob t / (p i).prob t))) := by
      unfold klDiv
      rw [Finset.mul_sum]
      have h_sum_i : ∑ i : Fin n, (b i : ℝ) * ∑ t : T, r.prob t * Real.log (r.prob t / (p i).prob t) =
          ∑ t : T, ∑ i : Fin n, (b i : ℝ) * (r.prob t * Real.log (r.prob t / (p i).prob t)) := by
        trans (∑ i : Fin n, ∑ t : T, (b i : ℝ) * (r.prob t * Real.log (r.prob t / (p i).prob t)))
        · apply Finset.sum_congr rfl
          intro i _; rw [Finset.mul_sum]
        · rw [Finset.sum_comm]
      rw [h_sum_i, ← Finset.sum_add_distrib]
    have h_rhs : B * klDiv r qBar - B * C =
        ∑ t : T, (B * (r.prob t * Real.log (r.prob t / qBar.prob t)) - B * C * r.prob t) := by
      unfold klDiv
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, r.sum_eq_one, mul_one]
    rw [h_lhs, h_rhs]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hrt : r.prob t = 0
    · simp [hrt]
    · have h0_div : (b₀ : ℝ) * Real.log (r.prob t / p₀.prob t) =
          (b₀ : ℝ) * Real.log (r.prob t) - (b₀ : ℝ) * Real.log (p₀.prob t) := by
        rw [Real.log_div hrt (ne_of_gt (hp₀ t))]; ring
      have hi_div : ∀ i : Fin n, (b i : ℝ) * Real.log (r.prob t / (p i).prob t) =
          (b i : ℝ) * Real.log (r.prob t) - (b i : ℝ) * Real.log ((p i).prob t) := by
        intro i
        by_cases hbi : (b i : ℝ) = 0
        · simp [hbi]
        · rw [Real.log_div hrt (ne_of_gt (hp i hbi t))]; ring
      have h_sum_div : ∑ i : Fin n, (b i : ℝ) * Real.log (r.prob t / (p i).prob t) =
          (∑ i : Fin n, (b i : ℝ)) * Real.log (r.prob t) -
          ∑ i : Fin n, (b i : ℝ) * Real.log ((p i).prob t) := by
        trans (∑ i : Fin n, ((b i : ℝ) * Real.log (r.prob t) - (b i : ℝ) * Real.log ((p i).prob t)))
        · apply Finset.sum_congr rfl; intro i _; exact hi_div i
        · rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      have h_Bu : B * u t = (b₀ : ℝ) * Real.log (p₀.prob t) + ∑ i : Fin n, (b i : ℝ) * Real.log ((p i).prob t) := by
        dsimp [u, logLinearScore]
        exact mul_div_cancel₀ _ hB_ne
      have h_B_def : (b₀ : ℝ) + ∑ i : Fin n, (b i : ℝ) = B := rfl
      have h_u_eq : u t = Real.log (qBar.prob t) + C := by linarith [hqBar_log t]
      have h_qbar_div : Real.log (r.prob t / qBar.prob t) = Real.log (r.prob t) - Real.log (qBar.prob t) :=
        Real.log_div hrt (ne_of_gt (hqBar_supp t))
      have h_pull : (b₀ : ℝ) * (r.prob t * Real.log (r.prob t / p₀.prob t)) +
          ∑ i : Fin n, (b i : ℝ) * (r.prob t * Real.log (r.prob t / (p i).prob t)) =
          r.prob t * ((b₀ : ℝ) * Real.log (r.prob t / p₀.prob t) +
            ∑ i : Fin n, (b i : ℝ) * Real.log (r.prob t / (p i).prob t)) := by
        have h_s : ∑ i : Fin n, (b i : ℝ) * (r.prob t * Real.log (r.prob t / (p i).prob t)) =
            r.prob t * ∑ i : Fin n, (b i : ℝ) * Real.log (r.prob t / (p i).prob t) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [h_s]; ring
      rw [h_pull, h0_div, h_sum_div]
      have h_core : (b₀ : ℝ) * Real.log (r.prob t) - (b₀ : ℝ) * Real.log (p₀.prob t) +
          ((∑ i : Fin n, (b i : ℝ)) * Real.log (r.prob t) -
            ∑ i : Fin n, (b i : ℝ) * Real.log ((p i).prob t)) =
          B * Real.log (r.prob t / qBar.prob t) - B * C := by
        calc (b₀ : ℝ) * Real.log (r.prob t) - (b₀ : ℝ) * Real.log (p₀.prob t) +
            ((∑ i : Fin n, (b i : ℝ)) * Real.log (r.prob t) -
              ∑ i : Fin n, (b i : ℝ) * Real.log ((p i).prob t))
            = ((b₀ : ℝ) + ∑ i : Fin n, (b i : ℝ)) * Real.log (r.prob t) -
              ((b₀ : ℝ) * Real.log (p₀.prob t) + ∑ i : Fin n, (b i : ℝ) * Real.log ((p i).prob t)) := by ring
          _ = B * Real.log (r.prob t) - B * u t := by rw [h_B_def, h_Bu]
          _ = B * Real.log (r.prob t) - B * (Real.log (qBar.prob t) + C) := by rw [h_u_eq]
          _ = B * (Real.log (r.prob t) - Real.log (qBar.prob t)) - B * C := by ring
          _ = B * Real.log (r.prob t / qBar.prob t) - B * C := by rw [← h_qbar_div]
      rw [h_core]
      ring
  have h_phi_q := h_phi q
  have h_phi_qBar := h_phi qBar
  have h_kl_self : klDiv qBar qBar = 0 :=
    (lem_gibbs_inequality T qBar qBar hqBar_supp).2.2.mpr rfl
  rw [h_kl_self, mul_zero, zero_sub] at h_phi_qBar
  linarith

private lemma zero_bid_sum_eq_erase {n : ℕ} (i : Fin n) (b : BidProfile n) (f : Fin n → ℝ) :
    ∑ j : Fin n, ((joinBid i 0 (restrictBids i b) j : Bid) : ℝ) * f j =
      ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * f j := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have h_self : ((joinBid i 0 (restrictBids i b) i : Bid) : ℝ) * f i = 0 := by
    simp [joinBid]
  rw [h_self, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  simp [joinBid, restrictBids, hji]

private lemma opposingBidWithPlatform_pos {n : ℕ} {b₀ : Bid} (hb₀ : 0 < b₀)
    (i : Fin n) (b : BidProfile n) :
    0 < opposingBidWithPlatform b₀ i b := by
  unfold opposingBidWithPlatform opposingStrategicBidSum
  have hb₀' : (0 : ℝ) < (b₀ : ℝ) := by exact_mod_cast hb₀
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.univ.erase i, (b j : ℝ) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  linarith

private lemma totalBid_joinBid_zero {n : ℕ} (b₀ : Bid) (i : Fin n) (b : BidProfile n) :
    totalBidWithPlatform b₀ (joinBid i 0 (restrictBids i b)) = opposingBidWithPlatform b₀ i b := by
  unfold totalBidWithPlatform opposingBidWithPlatform strategicBidSum opposingStrategicBidSum
  congr 1
  simpa using zero_bid_sum_eq_erase i b (fun _ => 1)

private lemma bzero_dist_sum_inv {n : ℕ} {T : Type} [Fintype T] (i : Fin n)
    (bOthers : OpposingBids n i) (p₁ p₂ : TokenDist T) (pOthers : OpposingDists n T i)
    (g : TokenDist T → ℝ) :
    ∑ j : Fin n, ((joinBid i 0 bOthers j : Bid) : ℝ) * g (joinDist i p₁ pOthers j) =
      ∑ j : Fin n, ((joinBid i 0 bOthers j : Bid) : ℝ) * g (joinDist i p₂ pOthers j) := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst hj; simp [joinBid]
  · simp [joinBid, joinDist, hj]

private lemma linearAggWithout_inv {n : ℕ} {T : Type} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) (i : Fin n)
    (b₁ b₂ : Bid) (p₁ p₂ : TokenDist T)
    (bOthers : OpposingBids n i) (pOthers : OpposingDists n T i) :
    linearAggWithout b₀ hb₀ p₀ i (joinBid i b₁ bOthers) (joinDist i p₁ pOthers) =
      linearAggWithout b₀ hb₀ p₀ i (joinBid i b₂ bOthers) (joinDist i p₂ pOthers) := by
  unfold linearAggWithout
  simp only [restrictBids_joinBid]
  ext t
  simp only [linearAggRule]
  congr 2
  exact bzero_dist_sum_inv i bOthers p₁ p₂ pOthers (fun d => d.prob t)

private lemma logLinearAggWithout_inv {n : ℕ} {T : Type} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) (i : Fin n)
    (b₁ b₂ : Bid) (p₁ p₂ : TokenDist T)
    (bOthers : OpposingBids n i) (pOthers : OpposingDists n T i) :
    logLinearAggWithout b₀ hb₀ p₀ i (joinBid i b₁ bOthers) (joinDist i p₁ pOthers) =
      logLinearAggWithout b₀ hb₀ p₀ i (joinBid i b₂ bOthers) (joinDist i p₂ pOthers) := by
  unfold logLinearAggWithout
  simp only [restrictBids_joinBid]
  have h_score : logLinearScore b₀ p₀ (joinBid i 0 bOthers) (joinDist i p₁ pOthers) =
      logLinearScore b₀ p₀ (joinBid i 0 bOthers) (joinDist i p₂ pOthers) := by
    funext s
    unfold logLinearScore
    congr 2
    exact bzero_dist_sum_inv i bOthers p₁ p₂ pOthers (fun d => Real.log (d.prob s))
  ext t
  simp only [logLinearAggRule, h_score]

private lemma erase_join_inv {n : ℕ} {T : Type} [Fintype T] (i : Fin n)
    (b₁ b₂ : Bid) (p₁ p₂ : TokenDist T)
    (bOthers : OpposingBids n i) (pOthers : OpposingDists n T i)
    (g : TokenDist T → ℝ) :
    ∑ j ∈ Finset.univ.erase i, ((joinBid i b₁ bOthers j : Bid) : ℝ) * g (joinDist i p₁ pOthers j) =
      ∑ j ∈ Finset.univ.erase i, ((joinBid i b₂ bOthers j : Bid) : ℝ) * g (joinDist i p₂ pOthers j) := by
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  simp [joinBid, joinDist, hji]

private lemma split_join_sum {n : ℕ} {T : Type} [Fintype T] (i : Fin n)
    (v_i : Bid) (p_i : TokenDist T)
    (bOthers : OpposingBids n i) (pOthers : OpposingDists n T i)
    (g : TokenDist T → ℝ) :
    ∑ j : Fin n, ((joinBid i v_i bOthers j : Bid) : ℝ) * g (joinDist i p_i pOthers j) =
      (v_i : ℝ) * g p_i +
        ∑ j ∈ Finset.univ.erase i, ((joinBid i v_i bOthers j : Bid) : ℝ) * g (joinDist i p_i pOthers j) := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  simp [joinBid, joinDist]

private lemma joinDist_fullSupport {n : ℕ} {T : Type} [Fintype T] (i : Fin n)
    (p_i : TokenDist T) (pOthers : OpposingDists n T i)
    (hp_i : HasFullSupport p_i) (hpOthers : ∀ j : {j : Fin n // j ≠ i}, HasFullSupport (pOthers j)) :
    ∀ j : Fin n, HasFullSupport (joinDist i p_i pOthers j) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa [joinDist] using hp_i
  · simpa [joinDist, hj] using hpOthers ⟨j, hj⟩

/-! ## Section 3 & Appendix A: Forward-KL Linear Rule & VCG Mechanism -/

/-- Lemma 3.1 (`lem:KL-linear-rule`) & Appendix A: Forward-KL social welfare is uniquely maximized
    by the linear aggregation rule `q_KL`. -/
theorem lem_3_1_kl_linear_rule (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
    (b : BidProfile n) (p : DistProfile n T)
    (hp₀ : HasFullSupport p₀) (_hp : ∀ i : Fin n, HasFullSupport (p i)) :
    let qKL := linearAggRule b₀ hb₀ p₀ b p
    HasFullSupport qKL ∧
    (∀ q : TokenDist T, HasFullSupport q →
      forwardKLSocialWelfare b₀ p₀ b p q =
        - totalBidWithPlatform b₀ b * crossEntropy qKL q +
          ((b₀ : ℝ) * shannonEntropy p₀ + ∑ i : Fin n, (b i : ℝ) * shannonEntropy (p i)) ∧
      forwardKLSocialWelfare b₀ p₀ b p q ≤ forwardKLSocialWelfare b₀ p₀ b p qKL ∧
      (forwardKLSocialWelfare b₀ p₀ b p q = forwardKLSocialWelfare b₀ p₀ b p qKL ↔ q = qKL)) := by
  obtain ⟨hqKL_supp, hqKL_ident⟩ := forwardKL_welfare_decomp n T b₀ hb₀ p₀ b p hp₀
  have hB_pos : 0 < totalBidWithPlatform b₀ b := totalBidWithPlatform_pos hb₀ b
  have hB_ne : totalBidWithPlatform b₀ b ≠ 0 := ne_of_gt hB_pos
  refine ⟨hqKL_supp, fun q hq => ?_⟩
  obtain ⟨h_ce, h_diff⟩ := hqKL_ident q hq
  obtain ⟨_, h_kl_nonneg, h_kl_zero⟩ := lem_gibbs_inequality T (linearAggRule b₀ hb₀ p₀ b p) q hq
  have h_le : forwardKLSocialWelfare b₀ p₀ b p q ≤
      forwardKLSocialWelfare b₀ p₀ b p (linearAggRule b₀ hb₀ p₀ b p) := by
    have h_prod : 0 ≤ totalBidWithPlatform b₀ b * klDiv (linearAggRule b₀ hb₀ p₀ b p) q :=
      mul_nonneg (le_of_lt hB_pos) h_kl_nonneg
    linarith
  have h_eq_iff : forwardKLSocialWelfare b₀ p₀ b p q =
      forwardKLSocialWelfare b₀ p₀ b p (linearAggRule b₀ hb₀ p₀ b p) ↔
      q = linearAggRule b₀ hb₀ p₀ b p := by
    have h_sub_iff : forwardKLSocialWelfare b₀ p₀ b p q =
        forwardKLSocialWelfare b₀ p₀ b p (linearAggRule b₀ hb₀ p₀ b p) ↔
        totalBidWithPlatform b₀ b * klDiv (linearAggRule b₀ hb₀ p₀ b p) q = 0 := by
      constructor <;> intro h <;> linarith
    rw [h_sub_iff, mul_eq_zero, or_iff_right hB_ne, h_kl_zero, eq_comm]
  exact ⟨h_ce, h_le, h_eq_iff⟩

/-- Theorem 3.2 (`thm:kl-vcg`): The forward-KL VCG mechanism `𝓜_KL = ⟨q_KL, z⟩` satisfies payment
    admissibility, the closed-form Clarke pivot identity
    `z_i(b, p) = B_{-i} D_KL(q^*_{-i} ‖ q_KL(b, p))`, Ex-Post Individual Rationality, and joint
    Dominant-Strategy Incentive Compatibility in `(b_i, p_i)`. -/
theorem thm_3_2_kl_vcg (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) (hp₀ : HasFullSupport p₀) :
    IsAdmissiblePayment (forwardKLVCGPayment b₀ hb₀ p₀ : PaymentRule n T) ∧
    (∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      (∀ j : Fin n, HasFullSupport (p j)) →
      let qKL := linearAggRule b₀ hb₀ p₀ b p
      let qWithout := linearAggWithout b₀ hb₀ p₀ i b p
      forwardKLVCGPayment b₀ hb₀ p₀ i b p =
        (- ((b₀ : ℝ) * klDiv p₀ qWithout +
            ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * klDiv (p j) qWithout)) -
        (- ((b₀ : ℝ) * klDiv p₀ qKL +
            ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * klDiv (p j) qKL))) ∧
    (∀ (i : Fin n) (v_i : Bid) (p_i_true : TokenDist T)
       (bOthers : OpposingBids n i) (pOthers : OpposingDists n T i),
      HasFullSupport p_i_true → (∀ j : {j : Fin n // j ≠ i}, HasFullSupport (pOthers j)) →
      let bTruth := joinBid i v_i bOthers;
      let pTruth := joinDist i p_i_true pOthers;
      let qTruth := linearAggRule b₀ hb₀ p₀ bTruth pTruth;
      let qOut := linearAggWithout b₀ hb₀ p₀ i bTruth pTruth;
      let uTruth := - (v_i : ℝ) * klDiv p_i_true qTruth - forwardKLVCGPayment b₀ hb₀ p₀ i bTruth pTruth;
      (- (v_i : ℝ) * klDiv p_i_true qOut ≤ uTruth) ∧
      (∀ (b'_i : Bid) (p'_i : TokenDist T), HasFullSupport p'_i →
        let bMis := joinBid i b'_i bOthers;
        let pMis := joinDist i p'_i pOthers;
        let qMis := linearAggRule b₀ hb₀ p₀ bMis pMis;
        (- (v_i : ℝ) * klDiv p_i_true qMis - forwardKLVCGPayment b₀ hb₀ p₀ i bMis pMis ≤ uTruth))) := by
  have h_adm : IsAdmissiblePayment (forwardKLVCGPayment b₀ hb₀ p₀ : PaymentRule n T) := by
    constructor
    · intro i b p
      unfold forwardKLVCGPayment
      have hqKL_supp : HasFullSupport (linearAggRule b₀ hb₀ p₀ b p) :=
        (forwardKL_welfare_decomp n T b₀ hb₀ p₀ b p hp₀).1
      have h_kl_nonneg : 0 ≤ klDiv (linearAggWithout b₀ hb₀ p₀ i b p) (linearAggRule b₀ hb₀ p₀ b p) :=
        (lem_gibbs_inequality T _ _ hqKL_supp).2.1
      exact mul_nonneg (le_of_lt (opposingBidWithPlatform_pos hb₀ i b)) h_kl_nonneg
    · intro i bOthers p
      unfold forwardKLVCGPayment linearAggWithout
      rw [restrictBids_joinBid]
      have hqKL_supp : HasFullSupport (linearAggRule b₀ hb₀ p₀ (joinBid i 0 bOthers) p) :=
        (forwardKL_welfare_decomp n T b₀ hb₀ p₀ (joinBid i 0 bOthers) p hp₀).1
      have h_kl_zero : klDiv (linearAggRule b₀ hb₀ p₀ (joinBid i 0 bOthers) p)
          (linearAggRule b₀ hb₀ p₀ (joinBid i 0 bOthers) p) = 0 :=
        (lem_gibbs_inequality T _ _ hqKL_supp).2.2.mpr rfl
      rw [h_kl_zero, mul_zero]
  have h_clarke : ∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      (∀ j : Fin n, HasFullSupport (p j)) →
      let qKL := linearAggRule b₀ hb₀ p₀ b p
      let qWithout := linearAggWithout b₀ hb₀ p₀ i b p
      forwardKLVCGPayment b₀ hb₀ p₀ i b p =
        (- ((b₀ : ℝ) * klDiv p₀ qWithout +
            ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * klDiv (p j) qWithout)) -
        (- ((b₀ : ℝ) * klDiv p₀ qKL +
            ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * klDiv (p j) qKL)) := by
    intro i b p _hp
    set qKL := linearAggRule b₀ hb₀ p₀ b p
    set bZero := joinBid i 0 (restrictBids i b)
    set qWithout := linearAggWithout b₀ hb₀ p₀ i b p
    have hqKL_supp : HasFullSupport qKL := (forwardKL_welfare_decomp n T b₀ hb₀ p₀ b p hp₀).1
    have h_diff := ((forwardKL_welfare_decomp n T b₀ hb₀ p₀ bZero p hp₀).2 qKL hqKL_supp).2
    have h_qWithout_def : linearAggRule b₀ hb₀ p₀ bZero p = qWithout := rfl
    rw [h_qWithout_def, totalBid_joinBid_zero b₀ i b] at h_diff
    unfold forwardKLSocialWelfare at h_diff
    rw [zero_bid_sum_eq_erase i b (fun j => klDiv (p j) qWithout),
        zero_bid_sum_eq_erase i b (fun j => klDiv (p j) qKL)] at h_diff
    unfold forwardKLVCGPayment
    linarith
  refine ⟨h_adm, h_clarke, ?_⟩
  intro i v_i p_i_true bOthers pOthers hp_i_true hpOthers
  set bTruth := joinBid i v_i bOthers
  set pTruth := joinDist i p_i_true pOthers
  set qTruth := linearAggRule b₀ hb₀ p₀ bTruth pTruth
  set qOut := linearAggWithout b₀ hb₀ p₀ i bTruth pTruth
  have hpTruth_supp : ∀ j : Fin n, HasFullSupport (pTruth j) :=
    joinDist_fullSupport i p_i_true pOthers hp_i_true hpOthers
  have h_sw_split : ∀ q : TokenDist T,
      forwardKLSocialWelfare b₀ p₀ bTruth pTruth q =
        - (v_i : ℝ) * klDiv p_i_true q +
        (- ((b₀ : ℝ) * klDiv p₀ q +
            ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv (pTruth j) q)) := by
    intro q
    unfold forwardKLSocialWelfare
    rw [split_join_sum i v_i p_i_true bOthers pOthers (fun d => klDiv d q)]
    ring
  have h_pay_truth := h_clarke i bTruth pTruth hpTruth_supp
  have hqOut_supp : HasFullSupport qOut :=
    (forwardKL_welfare_decomp n T b₀ hb₀ p₀ (joinBid i 0 (restrictBids i bTruth)) pTruth hp₀).1
  have h_opt_out : forwardKLSocialWelfare b₀ p₀ bTruth pTruth qOut ≤
      forwardKLSocialWelfare b₀ p₀ bTruth pTruth qTruth :=
    ((lem_3_1_kl_linear_rule n T b₀ hb₀ p₀ bTruth pTruth hp₀ hpTruth_supp).2 qOut hqOut_supp).2.1
  constructor
  · have hs1 := h_sw_split qTruth
    have hs2 := h_sw_split qOut
    linarith
  · intro b'_i p'_i hp'_i
    set bMis := joinBid i b'_i bOthers
    set pMis := joinDist i p'_i pOthers
    set qMis := linearAggRule b₀ hb₀ p₀ bMis pMis
    have hpMis_supp : ∀ j : Fin n, HasFullSupport (pMis j) :=
      joinDist_fullSupport i p'_i pOthers hp'_i hpOthers
    have hqMis_supp : HasFullSupport qMis :=
      (forwardKL_welfare_decomp n T b₀ hb₀ p₀ bMis pMis hp₀).1
    have h_pay_mis := h_clarke i bMis pMis hpMis_supp
    have h_qout_eq : linearAggWithout b₀ hb₀ p₀ i bMis pMis = qOut :=
      linearAggWithout_inv b₀ hb₀ p₀ i b'_i v_i p'_i p_i_true bOthers pOthers
    have h_sum_out_eq : ∑ j ∈ Finset.univ.erase i, (bMis j : ℝ) * klDiv (pMis j) qOut =
        ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv (pTruth j) qOut :=
      erase_join_inv i b'_i v_i p'_i p_i_true bOthers pOthers (fun d => klDiv d qOut)
    have h_sum_mis_eq : ∑ j ∈ Finset.univ.erase i, (bMis j : ℝ) * klDiv (pMis j) qMis =
        ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv (pTruth j) qMis :=
      erase_join_inv i b'_i v_i p'_i p_i_true bOthers pOthers (fun d => klDiv d qMis)
    have h_pay_mis' : forwardKLVCGPayment b₀ hb₀ p₀ i bMis pMis =
        (- ((b₀ : ℝ) * klDiv p₀ qOut +
            ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv (pTruth j) qOut)) -
        (- ((b₀ : ℝ) * klDiv p₀ qMis +
            ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv (pTruth j) qMis)) := by
      dsimp only at h_pay_mis
      rw [h_qout_eq, h_sum_out_eq, h_sum_mis_eq] at h_pay_mis
      exact h_pay_mis
    have h_opt_mis : forwardKLSocialWelfare b₀ p₀ bTruth pTruth qMis ≤
        forwardKLSocialWelfare b₀ p₀ bTruth pTruth qTruth :=
      ((lem_3_1_kl_linear_rule n T b₀ hb₀ p₀ bTruth pTruth hp₀ hpTruth_supp).2 qMis hqMis_supp).2.1
    have hs1 := h_sw_split qTruth
    have hs2 := h_sw_split qMis
    linarith

/-! ## Remark 3.3 & Appendix B: Reverse-KL Log-Linear Rule & VCG Mechanism -/

/-- Remark 3.3 & Lemma B.1 (`lem:reverse-KL-rule`): The log-linear aggregation rule `q̄_KL`
    satisfies the reverse-KL Pythagorean identity and uniquely maximizes reverse-KL social
    welfare across `Δ(T)`. -/
theorem lem_B_1_reverse_kl_rule (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
    (b : BidProfile n) (p : DistProfile n T)
    (hp₀ : HasFullSupport p₀) (hp : ∀ i : Fin n, HasFullSupport (p i)) :
    let qBar := logLinearAggRule b₀ hb₀ p₀ b p
    HasFullSupport qBar ∧
    (∀ t : T, Real.log (qBar.prob t) = logLinearScore b₀ p₀ b p t - logLinearNormConst b₀ p₀ b p) ∧
    (∀ q : TokenDist T,
      ((b₀ : ℝ) * klDiv q p₀ + ∑ i : Fin n, (b i : ℝ) * klDiv q (p i)) =
        totalBidWithPlatform b₀ b * klDiv q qBar +
          ((b₀ : ℝ) * klDiv qBar p₀ + ∑ i : Fin n, (b i : ℝ) * klDiv qBar (p i)) ∧
      reverseKLSocialWelfare b₀ p₀ b p q ≤ reverseKLSocialWelfare b₀ p₀ b p qBar ∧
      (reverseKLSocialWelfare b₀ p₀ b p q = reverseKLSocialWelfare b₀ p₀ b p qBar ↔ q = qBar)) := by
  obtain ⟨hqBar_supp, hqBar_log, hqBar_pyth_gen⟩ := reverseKL_pythagorean_gen n T b₀ hb₀ p₀ b p
  have hqBar_pyth := hqBar_pyth_gen hp₀ (fun i _ => hp i)
  have hB_pos : 0 < totalBidWithPlatform b₀ b := totalBidWithPlatform_pos hb₀ b
  have hB_ne : totalBidWithPlatform b₀ b ≠ 0 := ne_of_gt hB_pos
  refine ⟨hqBar_supp, hqBar_log, fun q => ?_⟩
  have h_pyth := hqBar_pyth q
  obtain ⟨_, h_kl_nonneg, h_kl_zero⟩ :=
    lem_gibbs_inequality T q (logLinearAggRule b₀ hb₀ p₀ b p) hqBar_supp
  have h_sw_diff : reverseKLSocialWelfare b₀ p₀ b p (logLinearAggRule b₀ hb₀ p₀ b p) -
      reverseKLSocialWelfare b₀ p₀ b p q =
      totalBidWithPlatform b₀ b * klDiv q (logLinearAggRule b₀ hb₀ p₀ b p) := by
    unfold reverseKLSocialWelfare
    linarith
  have h_le : reverseKLSocialWelfare b₀ p₀ b p q ≤
      reverseKLSocialWelfare b₀ p₀ b p (logLinearAggRule b₀ hb₀ p₀ b p) := by
    have h_prod : 0 ≤ totalBidWithPlatform b₀ b * klDiv q (logLinearAggRule b₀ hb₀ p₀ b p) :=
      mul_nonneg (le_of_lt hB_pos) h_kl_nonneg
    linarith
  have h_eq_iff : reverseKLSocialWelfare b₀ p₀ b p q =
      reverseKLSocialWelfare b₀ p₀ b p (logLinearAggRule b₀ hb₀ p₀ b p) ↔
      q = logLinearAggRule b₀ hb₀ p₀ b p := by
    have h_sub_iff : reverseKLSocialWelfare b₀ p₀ b p q =
        reverseKLSocialWelfare b₀ p₀ b p (logLinearAggRule b₀ hb₀ p₀ b p) ↔
        totalBidWithPlatform b₀ b * klDiv q (logLinearAggRule b₀ hb₀ p₀ b p) = 0 := by
      constructor <;> intro h <;> linarith
    rw [h_sub_iff, mul_eq_zero, or_iff_right hB_ne, h_kl_zero]
  exact ⟨h_pyth, h_le, h_eq_iff⟩

/-- Theorem B.2 (`thm:reverse-kl-vcg`): The reverse-KL VCG mechanism `𝓜̄_KL = ⟨q̄_KL, z̄⟩`
    satisfies payment admissibility, the closed-form Clarke pivot identity
    `z̄_i(b, p) = B_{-i} D_KL(q̄_KL(b, p) ‖ q̄^*_{-i})`, Ex-Post Individual Rationality, and joint
    Dominant-Strategy Incentive Compatibility. -/
theorem thm_B_2_reverse_kl_vcg (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) (hp₀ : HasFullSupport p₀) :
    IsAdmissiblePayment (reverseKLVCGPayment b₀ hb₀ p₀ : PaymentRule n T) ∧
    (∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      (∀ j : Fin n, HasFullSupport (p j)) →
      let qBar := logLinearAggRule b₀ hb₀ p₀ b p
      let qBarWithout := logLinearAggWithout b₀ hb₀ p₀ i b p
      reverseKLVCGPayment b₀ hb₀ p₀ i b p =
        (- ((b₀ : ℝ) * klDiv qBarWithout p₀ +
            ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * klDiv qBarWithout (p j))) -
        (- ((b₀ : ℝ) * klDiv qBar p₀ +
            ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * klDiv qBar (p j)))) ∧
    (∀ (i : Fin n) (v_i : Bid) (p_i_true : TokenDist T)
       (bOthers : OpposingBids n i) (pOthers : OpposingDists n T i),
      HasFullSupport p_i_true → (∀ j : {j : Fin n // j ≠ i}, HasFullSupport (pOthers j)) →
      let bTruth := joinBid i v_i bOthers;
      let pTruth := joinDist i p_i_true pOthers;
      let qTruth := logLinearAggRule b₀ hb₀ p₀ bTruth pTruth;
      let qOut := logLinearAggWithout b₀ hb₀ p₀ i bTruth pTruth;
      let uTruth := - (v_i : ℝ) * klDiv qTruth p_i_true - reverseKLVCGPayment b₀ hb₀ p₀ i bTruth pTruth;
      (- (v_i : ℝ) * klDiv qOut p_i_true ≤ uTruth) ∧
      (∀ (b'_i : Bid) (p'_i : TokenDist T), HasFullSupport p'_i →
        let bMis := joinBid i b'_i bOthers;
        let pMis := joinDist i p'_i pOthers;
        let qMis := logLinearAggRule b₀ hb₀ p₀ bMis pMis;
        (- (v_i : ℝ) * klDiv qMis p_i_true - reverseKLVCGPayment b₀ hb₀ p₀ i bMis pMis ≤ uTruth))) := by
  have h_adm : IsAdmissiblePayment (reverseKLVCGPayment b₀ hb₀ p₀ : PaymentRule n T) := by
    constructor
    · intro i b p
      unfold reverseKLVCGPayment
      have hqBarW_supp : HasFullSupport (logLinearAggWithout b₀ hb₀ p₀ i b p) :=
        (reverseKL_pythagorean_gen n T b₀ hb₀ p₀ (joinBid i 0 (restrictBids i b)) p).1
      have h_kl_nonneg : 0 ≤ klDiv (logLinearAggRule b₀ hb₀ p₀ b p) (logLinearAggWithout b₀ hb₀ p₀ i b p) :=
        (lem_gibbs_inequality T _ _ hqBarW_supp).2.1
      exact mul_nonneg (le_of_lt (opposingBidWithPlatform_pos hb₀ i b)) h_kl_nonneg
    · intro i bOthers p
      unfold reverseKLVCGPayment logLinearAggWithout
      rw [restrictBids_joinBid]
      have hqBar_supp : HasFullSupport (logLinearAggRule b₀ hb₀ p₀ (joinBid i 0 bOthers) p) :=
        (reverseKL_pythagorean_gen n T b₀ hb₀ p₀ (joinBid i 0 bOthers) p).1
      have h_kl_zero : klDiv (logLinearAggRule b₀ hb₀ p₀ (joinBid i 0 bOthers) p)
          (logLinearAggRule b₀ hb₀ p₀ (joinBid i 0 bOthers) p) = 0 :=
        (lem_gibbs_inequality T _ _ hqBar_supp).2.2.mpr rfl
      rw [h_kl_zero, mul_zero]
  have h_clarke : ∀ (i : Fin n) (b : BidProfile n) (p : DistProfile n T),
      (∀ j : Fin n, HasFullSupport (p j)) →
      let qBar := logLinearAggRule b₀ hb₀ p₀ b p
      let qBarWithout := logLinearAggWithout b₀ hb₀ p₀ i b p
      reverseKLVCGPayment b₀ hb₀ p₀ i b p =
        (- ((b₀ : ℝ) * klDiv qBarWithout p₀ +
            ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * klDiv qBarWithout (p j))) -
        (- ((b₀ : ℝ) * klDiv qBar p₀ +
            ∑ j ∈ Finset.univ.erase i, (b j : ℝ) * klDiv qBar (p j))) := by
    intro i b p hp
    set qBar := logLinearAggRule b₀ hb₀ p₀ b p
    set bZero := joinBid i 0 (restrictBids i b)
    set qBarWithout := logLinearAggWithout b₀ hb₀ p₀ i b p
    have h_pyth := (reverseKL_pythagorean_gen n T b₀ hb₀ p₀ bZero p).2.2 hp₀ (fun j _ => hp j) qBar
    have h_qBarW_def : logLinearAggRule b₀ hb₀ p₀ bZero p = qBarWithout := rfl
    rw [h_qBarW_def, totalBid_joinBid_zero b₀ i b] at h_pyth
    rw [zero_bid_sum_eq_erase i b (fun j => klDiv qBar (p j)),
        zero_bid_sum_eq_erase i b (fun j => klDiv qBarWithout (p j))] at h_pyth
    unfold reverseKLVCGPayment
    linarith
  refine ⟨h_adm, h_clarke, ?_⟩
  intro i v_i p_i_true bOthers pOthers hp_i_true hpOthers
  set bTruth := joinBid i v_i bOthers
  set pTruth := joinDist i p_i_true pOthers
  set qTruth := logLinearAggRule b₀ hb₀ p₀ bTruth pTruth
  set qOut := logLinearAggWithout b₀ hb₀ p₀ i bTruth pTruth
  have hpTruth_supp : ∀ j : Fin n, HasFullSupport (pTruth j) :=
    joinDist_fullSupport i p_i_true pOthers hp_i_true hpOthers
  have h_sw_split : ∀ q : TokenDist T,
      reverseKLSocialWelfare b₀ p₀ bTruth pTruth q =
        - (v_i : ℝ) * klDiv q p_i_true +
        (- ((b₀ : ℝ) * klDiv q p₀ +
            ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv q (pTruth j))) := by
    intro q
    unfold reverseKLSocialWelfare
    rw [split_join_sum i v_i p_i_true bOthers pOthers (fun d => klDiv q d)]
    ring
  have h_pay_truth := h_clarke i bTruth pTruth hpTruth_supp
  have h_opt_out : reverseKLSocialWelfare b₀ p₀ bTruth pTruth qOut ≤
      reverseKLSocialWelfare b₀ p₀ bTruth pTruth qTruth :=
    ((lem_B_1_reverse_kl_rule n T b₀ hb₀ p₀ bTruth pTruth hp₀ hpTruth_supp).2.2 qOut).2.1
  constructor
  · have hs1 := h_sw_split qTruth
    have hs2 := h_sw_split qOut
    linarith
  · intro b'_i p'_i hp'_i
    set bMis := joinBid i b'_i bOthers
    set pMis := joinDist i p'_i pOthers
    set qMis := logLinearAggRule b₀ hb₀ p₀ bMis pMis
    have hpMis_supp : ∀ j : Fin n, HasFullSupport (pMis j) :=
      joinDist_fullSupport i p'_i pOthers hp'_i hpOthers
    have h_pay_mis := h_clarke i bMis pMis hpMis_supp
    have h_qout_eq : logLinearAggWithout b₀ hb₀ p₀ i bMis pMis = qOut :=
      logLinearAggWithout_inv b₀ hb₀ p₀ i b'_i v_i p'_i p_i_true bOthers pOthers
    have h_sum_out_eq : ∑ j ∈ Finset.univ.erase i, (bMis j : ℝ) * klDiv qOut (pMis j) =
        ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv qOut (pTruth j) :=
      erase_join_inv i b'_i v_i p'_i p_i_true bOthers pOthers (fun d => klDiv qOut d)
    have h_sum_mis_eq : ∑ j ∈ Finset.univ.erase i, (bMis j : ℝ) * klDiv qMis (pMis j) =
        ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv qMis (pTruth j) :=
      erase_join_inv i b'_i v_i p'_i p_i_true bOthers pOthers (fun d => klDiv qMis d)
    have h_pay_mis' : reverseKLVCGPayment b₀ hb₀ p₀ i bMis pMis =
        (- ((b₀ : ℝ) * klDiv qOut p₀ +
            ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv qOut (pTruth j))) -
        (- ((b₀ : ℝ) * klDiv qMis p₀ +
            ∑ j ∈ Finset.univ.erase i, (bTruth j : ℝ) * klDiv qMis (pTruth j))) := by
      dsimp only at h_pay_mis
      rw [h_qout_eq, h_sum_out_eq, h_sum_mis_eq] at h_pay_mis
      exact h_pay_mis
    have h_opt_mis : reverseKLSocialWelfare b₀ p₀ bTruth pTruth qMis ≤
        reverseKLSocialWelfare b₀ p₀ bTruth pTruth qTruth :=
      ((lem_B_1_reverse_kl_rule n T b₀ hb₀ p₀ bTruth pTruth hp₀ hpTruth_supp).2.2 qMis).2.1
    have hs1 := h_sw_split qTruth
    have hs2 := h_sw_split qMis
    linarith

/-! ## Section 6.2 & Footnote 9: Perplexity & Cross-Entropy Identity -/

/-- Section 6.2 (model sanity lemma): Sequence perplexity `PPL_i(s_m)` is strictly positive. -/
theorem sec_6_2_perplexity_pos (T : Type) [Fintype T] [DecidableEq T] (m : ℕ)
    (pSeq : Fin m → TokenDist T) (τ : Fin m → T) :
    0 < sequencePerplexity pSeq τ := by
  unfold sequencePerplexity
  exact Real.exp_pos _

/-- Footnote 9 (Section 6.2): Expected log-perplexity / cross-entropy decomposes into reverse
    KL-divergence plus output entropy: `H(q, p_i) = D_KL(q ‖ p_i) + H(q)`. -/
theorem fn_9_perplexity_cross_entropy (T : Type) [Fintype T] [DecidableEq T]
    (q p_i : TokenDist T) (hp_i : HasFullSupport p_i) :
    crossEntropy q p_i = klDiv q p_i + shannonEntropy q := by
  have h_eq := (lem_gibbs_inequality T q p_i hp_i).1
  linarith

end

end TokenAuctions
