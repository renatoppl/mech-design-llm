import TokenAuctions.Defs

set_option maxHeartbeats 4000000

/-!
# Robust Preferences, Stable Sampling & Universal Stability Impossibility

This module formalizes Section 5.1 (Definition 5.1, Remark 5.2, Lemma 5.3, the two-token
illustrative sampler, Definition 5.4, Theorem 5.5), Appendix B (Example B.3), Appendix D.1, and
Appendix E (Examples E.1 and E.2) of *Mechanism Design for Large Language Models: Token Auctions
with Proxy Bidders*.

## Main Results
- `def_5_1_robust_pref_partial_order`: Robust preference `⪰_i` (Definition 5.1) is a topologically
  closed partial order on `Δ(T)` whose asymmetric strict part coincides with `RobustStrictPref`.
- `rem_5_2_linear_monotone_consistent`: The linear aggregation rule `q_KL` is both monotone and
  consistent under robust preferences, scaling deviations `(q_KL - p_i)` uniformly across tokens
  (Remark 5.2).
- `ex_B_3_log_linear_nonmonotone`: The log-linear aggregation rule `q̄_KL` violates robust
  monotonicity on a full-support 3-token, 2-bidder instance, both with `b_0 = 0` and with any
  positive platform bid `b_0 > 0` (Remark 5.2 & Example B.3).
- `lem_5_3_monotone_coord_iff` and `lem_5_3_monotone_agg_iff`: Single-agent slice and `n`-agent
  coordinatewise characterizations of robust monotonicity in terms of nondecreasing undersampled
  token probabilities (`T⁺`) and nonincreasing oversampled token probabilities (`T⁻`) (Lemma 5.3).
- `sec_5_1_two_token_stable_sampler`: Explicit threshold sampler on `[0, 1]` for two-token
  vocabularies (Section 5.1).
- `thm_5_5_stable_sampling_exists`: Every robust-monotone single-agent aggregation curve admits a
  stable sampling implementation `σ : ℚ₊ × [0, 1]² → T` (Theorem 5.5 & Appendix D.1).
- `ex_E_1_four_token_no_universal_stable`: Four-token, two-bidder monotone rule with identical
  targets admitting no universally stable sampler on any probability space (Example E.1).
- `ex_E_2_three_token_no_universal_stable`: Three-token, two-bidder monotone rule with
  heterogeneous targets admitting no universally stable sampler on any probability space
  (Example E.2).
-/

namespace TokenAuctions

open scoped BigOperators
open Classical MeasureTheory

noncomputable section

/-! ## Internal Helpers -/

private lemma hRobustCoord : ∀ a b : ℝ,
    (|a| ≤ |b| ∧ 0 ≤ a * b) ↔ ((0 ≤ a ∧ a ≤ b) ∨ (b ≤ a ∧ a ≤ 0)) := by
  intro a b
  constructor
  · rintro ⟨habs, hmul⟩
    rcases lt_trichotomy a 0 with ha | rfl | ha
    · right
      have hb : b ≤ 0 := by
        by_contra hb'
        push_neg at hb'
        have : a * b < 0 := mul_neg_of_neg_of_pos ha hb'
        linarith
      rw [abs_of_neg ha, abs_of_nonpos hb] at habs
      exact ⟨by linarith, le_of_lt ha⟩
    · rcases le_or_gt 0 b with hb | hb
      · left; exact ⟨le_rfl, hb⟩
      · right; exact ⟨le_of_lt hb, le_rfl⟩
    · left
      have hb : 0 ≤ b := by
        by_contra hb'
        push_neg at hb'
        have : a * b < 0 := mul_neg_of_pos_of_neg ha hb'
        linarith
      rw [abs_of_pos ha, abs_of_nonneg hb] at habs
      exact ⟨le_of_lt ha, habs⟩
  · rintro (⟨ha, hab⟩ | ⟨hab, ha⟩)
    · have hb : 0 ≤ b := le_trans ha hab
      rw [abs_of_nonneg ha, abs_of_nonneg hb]
      exact ⟨hab, mul_nonneg ha hb⟩
    · have hb : b ≤ 0 := le_trans hab ha
      rw [abs_of_nonpos ha, abs_of_nonpos hb]
      exact ⟨by linarith, mul_nonneg_of_nonpos_of_nonpos ha hb⟩

/-! ## Section 5.1: Robust Preferences & Monotonicity Characterization -/

/-- Definition 5.1 (`def:obvious-prefer`): `RobustPref target` is reflexive, antisymmetric,
    transitive, has strict part equal to `RobustStrictPref target`, and is topologically closed
    in `Δ(T) × Δ(T)`. -/
theorem def_5_1_robust_pref_partial_order (T : Type) [Fintype T] [DecidableEq T]
    (target : TokenDist T) :
    (∀ q : TokenDist T, RobustPref target q q) ∧
    (∀ q₁ q₂ : TokenDist T, RobustPref target q₁ q₂ → RobustPref target q₂ q₁ → q₁ = q₂) ∧
    (∀ q₁ q₂ q₃ : TokenDist T,
      RobustPref target q₁ q₂ → RobustPref target q₂ q₃ → RobustPref target q₁ q₃) ∧
    (∀ q₁ q₂ : TokenDist T,
      RobustStrictPref target q₁ q₂ ↔ strictPref (RobustPref target) q₁ q₂) ∧
    IsClosed {pair : TokenDist T × TokenDist T | RobustPref target pair.1 pair.2} := by
  have hRefl : ∀ q : TokenDist T, RobustPref target q q := by
    intro q
    exact ⟨fun _ => le_rfl, fun t => mul_self_nonneg _⟩
  have hAntisymm : ∀ q₁ q₂ : TokenDist T,
      RobustPref target q₁ q₂ → RobustPref target q₂ q₁ → q₁ = q₂ := by
    intro q₁ q₂ h12 h21
    ext t
    have c1 := (hRobustCoord (q₁.prob t - target.prob t) (q₂.prob t - target.prob t)).mp
      ⟨h12.1 t, h12.2 t⟩
    have c2 := (hRobustCoord (q₂.prob t - target.prob t) (q₁.prob t - target.prob t)).mp
      ⟨h21.1 t, h21.2 t⟩
    rcases c1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases c2 with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  have hTrans : ∀ q₁ q₂ q₃ : TokenDist T,
      RobustPref target q₁ q₂ → RobustPref target q₂ q₃ → RobustPref target q₁ q₃ := by
    intro q₁ q₂ q₃ h12 h23
    have hCoord : ∀ t : T,
        |q₁.prob t - target.prob t| ≤ |q₃.prob t - target.prob t| ∧
        0 ≤ (q₁.prob t - target.prob t) * (q₃.prob t - target.prob t) := by
      intro t
      rw [hRobustCoord]
      have c1 := (hRobustCoord (q₁.prob t - target.prob t) (q₂.prob t - target.prob t)).mp
        ⟨h12.1 t, h12.2 t⟩
      have c2 := (hRobustCoord (q₂.prob t - target.prob t) (q₃.prob t - target.prob t)).mp
        ⟨h23.1 t, h23.2 t⟩
      rcases c1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases c2 with ⟨_, _⟩ | ⟨_, _⟩
      · left; constructor <;> linarith
      · right; constructor <;> linarith
      · left; constructor <;> linarith
      · right; constructor <;> linarith
    exact ⟨fun t => (hCoord t).1, fun t => (hCoord t).2⟩
  have hStrict : ∀ q₁ q₂ : TokenDist T,
      RobustStrictPref target q₁ q₂ ↔ strictPref (RobustPref target) q₁ q₂ := by
    intro q₁ q₂
    unfold RobustStrictPref strictPref
    constructor
    · rintro ⟨h12, hne⟩
      exact ⟨h12, fun h21 => hne (hAntisymm q₁ q₂ h12 h21)⟩
    · rintro ⟨h12, hn21⟩
      refine ⟨h12, ?_⟩
      rintro rfl
      exact hn21 (hRefl q₁)
  have hClosed : IsClosed {pair : TokenDist T × TokenDist T | RobustPref target pair.1 pair.2} := by
    have hContProb : Continuous (TokenDist.prob : TokenDist T → (T → ℝ)) :=
      continuous_induced_dom
    have hSetEq : {pair : TokenDist T × TokenDist T | RobustPref target pair.1 pair.2} =
        (⋂ t : T, {pair : TokenDist T × TokenDist T |
          |pair.1.prob t - target.prob t| ≤ |pair.2.prob t - target.prob t|}) ∩
        (⋂ t : T, {pair : TokenDist T × TokenDist T |
          0 ≤ (pair.1.prob t - target.prob t) * (pair.2.prob t - target.prob t)}) := by
      ext pair
      simp [RobustPref]
    rw [hSetEq]
    refine IsClosed.inter (isClosed_iInter (fun t => ?_)) (isClosed_iInter (fun t => ?_))
    · have hc1 : Continuous (fun pair : TokenDist T × TokenDist T =>
          |pair.1.prob t - target.prob t|) :=
        (((continuous_apply t).comp (hContProb.comp continuous_fst)).sub continuous_const).abs
      have hc2 : Continuous (fun pair : TokenDist T × TokenDist T =>
          |pair.2.prob t - target.prob t|) :=
        (((continuous_apply t).comp (hContProb.comp continuous_snd)).sub continuous_const).abs
      exact isClosed_le hc1 hc2
    · have hc1 : Continuous (fun pair : TokenDist T × TokenDist T =>
          pair.1.prob t - target.prob t) :=
        ((continuous_apply t).comp (hContProb.comp continuous_fst)).sub continuous_const
      have hc2 : Continuous (fun pair : TokenDist T × TokenDist T =>
          pair.2.prob t - target.prob t) :=
        ((continuous_apply t).comp (hContProb.comp continuous_snd)).sub continuous_const
      exact isClosed_le continuous_const (hc1.mul hc2)
  exact ⟨hRefl, hAntisymm, hTrans, hStrict, hClosed⟩

/-- Remark 5.2: The linear aggregation rule `q_KL` is monotone and consistent under robust
    preferences, scaling every coordinate deviation `(q_KL - p_i)` by `B_old / B_new`. -/
theorem rem_5_2_linear_monotone_consistent (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) :
    IsMonotoneAgg (robustAgentPrefs n T) (linearAggRule b₀ hb₀ p₀) ∧
    IsConsistentAgg (robustAgentPrefs n T) (linearAggRule b₀ hb₀ p₀) ∧
    (∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i) (b_i b'_i : Bid) (t : T),
      b'_i ≤ b_i →
        let qNew := linearAggRule b₀ hb₀ p₀ (joinBid i b_i bOthers) p
        let qOld := linearAggRule b₀ hb₀ p₀ (joinBid i b'_i bOthers) p
        let BNew := totalBidWithPlatform b₀ (joinBid i b_i bOthers)
        let BOld := totalBidWithPlatform b₀ (joinBid i b'_i bOthers)
        qNew.prob t - (p i).prob t = (BOld / BNew) * (qOld.prob t - (p i).prob t)) := by
  have hScaleAll : ∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i)
      (b_i b'_i : Bid) (t : T),
      (linearAggRule b₀ hb₀ p₀ (joinBid i b_i bOthers) p).prob t - (p i).prob t =
        (totalBidWithPlatform b₀ (joinBid i b'_i bOthers) /
          totalBidWithPlatform b₀ (joinBid i b_i bOthers)) *
          ((linearAggRule b₀ hb₀ p₀ (joinBid i b'_i bOthers) p).prob t - (p i).prob t) := by
    intro i p bOthers b_i b'_i t
    let bZero := joinBid i 0 bOthers
    let Brem : ℝ := (b₀ : ℝ) + ∑ j ∈ Finset.univ.erase i, (bZero j : ℝ)
    let Srem : ℝ := (b₀ : ℝ) * p₀.prob t +
      ∑ j ∈ Finset.univ.erase i, (bZero j : ℝ) * (p j).prob t
    have hInv : ∀ x : Bid,
        totalBidWithPlatform b₀ (joinBid i x bOthers) *
          ((linearAggRule b₀ hb₀ p₀ (joinBid i x bOthers) p).prob t - (p i).prob t) =
        Srem - Brem * (p i).prob t := by
      intro x
      have hBxPos : 0 < totalBidWithPlatform b₀ (joinBid i x bOthers) :=
        totalBidWithPlatform_pos hb₀ (joinBid i x bOthers)
      have hBxNe : totalBidWithPlatform b₀ (joinBid i x bOthers) ≠ 0 := ne_of_gt hBxPos
      have hBsplit : totalBidWithPlatform b₀ (joinBid i x bOthers) = (x : ℝ) + Brem := by
        unfold totalBidWithPlatform strategicBidSum
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), joinBid_self]
        have hsumEq : ∑ j ∈ Finset.univ.erase i, (joinBid i x bOthers j : ℝ) =
            ∑ j ∈ Finset.univ.erase i, (bZero j : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          simp [bZero, joinBid, hji]
        rw [hsumEq]
        dsimp [Brem]
        ring
      have hSsplit : (b₀ : ℝ) * p₀.prob t +
          ∑ j : Fin n, (joinBid i x bOthers j : ℝ) * (p j).prob t =
          (x : ℝ) * (p i).prob t + Srem := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), joinBid_self]
        have hsumEq : ∑ j ∈ Finset.univ.erase i, (joinBid i x bOthers j : ℝ) * (p j).prob t =
            ∑ j ∈ Finset.univ.erase i, (bZero j : ℝ) * (p j).prob t := by
          apply Finset.sum_congr rfl
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          simp [bZero, joinBid, hji]
        rw [hsumEq]
        dsimp [Srem]
        ring
      change totalBidWithPlatform b₀ (joinBid i x bOthers) *
        (((b₀ : ℝ) * p₀.prob t + ∑ j : Fin n, (joinBid i x bOthers j : ℝ) * (p j).prob t) /
          totalBidWithPlatform b₀ (joinBid i x bOthers) - (p i).prob t) =
        Srem - Brem * (p i).prob t
      rw [mul_sub, mul_div_cancel₀ _ hBxNe, hSsplit, hBsplit]
      ring
    have hNewPos : 0 < totalBidWithPlatform b₀ (joinBid i b_i bOthers) :=
      totalBidWithPlatform_pos hb₀ _
    have hNewNe : totalBidWithPlatform b₀ (joinBid i b_i bOthers) ≠ 0 := ne_of_gt hNewPos
    have hEqProd : totalBidWithPlatform b₀ (joinBid i b_i bOthers) *
        ((linearAggRule b₀ hb₀ p₀ (joinBid i b_i bOthers) p).prob t - (p i).prob t) =
      totalBidWithPlatform b₀ (joinBid i b'_i bOthers) *
        ((linearAggRule b₀ hb₀ p₀ (joinBid i b'_i bOthers) p).prob t - (p i).prob t) := by
      rw [hInv b_i, hInv b'_i]
    calc
      (linearAggRule b₀ hb₀ p₀ (joinBid i b_i bOthers) p).prob t - (p i).prob t
          = (totalBidWithPlatform b₀ (joinBid i b_i bOthers) *
              ((linearAggRule b₀ hb₀ p₀ (joinBid i b_i bOthers) p).prob t - (p i).prob t)) /
            totalBidWithPlatform b₀ (joinBid i b_i bOthers) := by
            rw [mul_div_cancel_left₀ _ hNewNe]
      _ = (totalBidWithPlatform b₀ (joinBid i b'_i bOthers) *
            ((linearAggRule b₀ hb₀ p₀ (joinBid i b'_i bOthers) p).prob t - (p i).prob t)) /
            totalBidWithPlatform b₀ (joinBid i b_i bOthers) := by
            rw [hEqProd]
      _ = (totalBidWithPlatform b₀ (joinBid i b'_i bOthers) /
            totalBidWithPlatform b₀ (joinBid i b_i bOthers)) *
            ((linearAggRule b₀ hb₀ p₀ (joinBid i b'_i bOthers) p).prob t - (p i).prob t) := by
            ring
  have hMono : IsMonotoneAgg (robustAgentPrefs n T) (linearAggRule b₀ hb₀ p₀) := by
    intro i p bOthers b_i b'_i hle
    have hOldPos : 0 < totalBidWithPlatform b₀ (joinBid i b'_i bOthers) :=
      totalBidWithPlatform_pos hb₀ _
    have hNewPos : 0 < totalBidWithPlatform b₀ (joinBid i b_i bOthers) :=
      totalBidWithPlatform_pos hb₀ _
    have hBOldLeBNew : totalBidWithPlatform b₀ (joinBid i b'_i bOthers) ≤
        totalBidWithPlatform b₀ (joinBid i b_i bOthers) := by
      unfold totalBidWithPlatform strategicBidSum
      gcongr with j _
      by_cases hji : j = i
      · subst hji; simp [joinBid]; exact_mod_cast hle
      · simp [joinBid, hji]
    let α : ℝ := totalBidWithPlatform b₀ (joinBid i b'_i bOthers) /
      totalBidWithPlatform b₀ (joinBid i b_i bOthers)
    have hα0 : 0 ≤ α := div_nonneg (le_of_lt hOldPos) (le_of_lt hNewPos)
    have hα1 : α ≤ 1 := (div_le_one hNewPos).mpr hBOldLeBNew
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [hScaleAll i p bOthers b_i b'_i t]
      change |α * _| ≤ _
      rw [abs_mul, abs_of_nonneg hα0]
      exact mul_le_of_le_one_left (abs_nonneg _) hα1
    · rw [hScaleAll i p bOthers b_i b'_i t]
      change 0 ≤ (α * _) * _
      have : (α * ((linearAggRule b₀ hb₀ p₀ (joinBid i b'_i bOthers) p).prob t - (p i).prob t)) *
          ((linearAggRule b₀ hb₀ p₀ (joinBid i b'_i bOthers) p).prob t - (p i).prob t) =
        α * (((linearAggRule b₀ hb₀ p₀ (joinBid i b'_i bOthers) p).prob t - (p i).prob t) *
          ((linearAggRule b₀ hb₀ p₀ (joinBid i b'_i bOthers) p).prob t - (p i).prob t)) := by ring
      rw [this]
      exact mul_nonneg hα0 (mul_self_nonneg _)
  have hCons : IsConsistentAgg (robustAgentPrefs n T) (linearAggRule b₀ hb₀ p₀) := by
    intro i p b_i b'_i ⟨bOthers, _, hnot⟩ b'Others
    rcases le_total b'_i b_i with hle | hle
    · exact hMono i p b'Others b_i b'_i hle
    · exact False.elim (hnot (hMono i p bOthers b'_i b_i hle))
  exact ⟨hMono, hCons, fun i p bOthers b_i b'_i t _ => hScaleAll i p bOthers b_i b'_i t⟩

/-- Remark 5.2 & Example B.3 (`exmpl:log-linear`): On `T = Fin 3` with full-support targets
    `p_1 = (1/2, 2/5, 1/10)` and `p_2 = (1/2, 1/10, 2/5)`, the log-linear rule produces
    `q̄_KL((1, 1), p) = (5/9, 2/9, 2/9)` and fails robust monotonicity both without a platform
    bidder (`b_0 = 0`) and with any positive platform bid `b_0 > 0`. -/
theorem ex_B_3_log_linear_nonmonotone :
    ∃ (p₁ p₂ : TokenDist (Fin 3)),
      p₁.prob 0 = 1 / 2 ∧ p₁.prob 1 = 2 / 5 ∧ p₁.prob 2 = 1 / 10 ∧
      p₂.prob 0 = 1 / 2 ∧ p₂.prob 1 = 1 / 10 ∧ p₂.prob 2 = 2 / 5 ∧
      HasFullSupport p₁ ∧ HasFullSupport p₂ ∧
      (let pProf : DistProfile 2 (Fin 3) := ![p₁, p₂]
       let bEq : BidProfile 2 := ![1, 1]
       let qMid := logLinearAggNoPlatform p₂ bEq pProf
       qMid.prob 0 = 5 / 9 ∧ qMid.prob 1 = 2 / 9 ∧ qMid.prob 2 = 2 / 9 ∧
       ¬ IsMonotoneAgg (robustAgentPrefs 2 (Fin 3)) (logLinearAggNoPlatform p₂) ∧
       ∀ (b₀ : Bid) (hb₀ : 0 < b₀),
         ¬ IsMonotoneAgg (robustAgentPrefs 2 (Fin 3)) (logLinearAggRule b₀ hb₀ p₂)) := by
  let fp₁ : ℕ → ℝ := fun n => if n = 0 then 1 / 2 else if n = 1 then 2 / 5 else 1 / 10
  let p₁ : TokenDist (Fin 3) :=
    { prob := fun t => fp₁ t.val
      nonneg := fun t => by dsimp [fp₁]; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_three]
        change fp₁ 0 + fp₁ 1 + fp₁ 2 = 1
        norm_num [fp₁] }
  let fp₂ : ℕ → ℝ := fun n => if n = 0 then 1 / 2 else if n = 1 then 1 / 10 else 2 / 5
  let p₂ : TokenDist (Fin 3) :=
    { prob := fun t => fp₂ t.val
      nonneg := fun t => by dsimp [fp₂]; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_three]
        change fp₂ 0 + fp₂ 1 + fp₂ 2 = 1
        norm_num [fp₂] }
  have hp₁0 : p₁.prob 0 = 1 / 2 := by change fp₁ 0 = 1 / 2; norm_num [fp₁]
  have hp₁1 : p₁.prob 1 = 2 / 5 := by change fp₁ 1 = 2 / 5; norm_num [fp₁]
  have hp₁2 : p₁.prob 2 = 1 / 10 := by change fp₁ 2 = 1 / 10; norm_num [fp₁]
  have hp₂0 : p₂.prob 0 = 1 / 2 := by change fp₂ 0 = 1 / 2; norm_num [fp₂]
  have hp₂1 : p₂.prob 1 = 1 / 10 := by change fp₂ 1 = 1 / 10; norm_num [fp₂]
  have hp₂2 : p₂.prob 2 = 2 / 5 := by change fp₂ 2 = 2 / 5; norm_num [fp₂]
  have hp₁Full : HasFullSupport p₁ := fun t => by
    change 0 < fp₁ t.val; dsimp [fp₁]; split_ifs <;> norm_num
  have hp₂Full : HasFullSupport p₂ := fun t => by
    change 0 < fp₂ t.val; dsimp [fp₂]; split_ifs <;> norm_num
  refine ⟨p₁, p₂, hp₁0, hp₁1, hp₁2, hp₂0, hp₂1, hp₂2, hp₁Full, hp₂Full, ?_⟩
  dsimp only
  let pProf : DistProfile 2 (Fin 3) := ![p₁, p₂]
  let bEq : BidProfile 2 := ![1, 1]
  have hExp1 : Real.exp ((Real.log (2 / 5) + Real.log (1 / 10)) / 2) = 1 / 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    have hsq : (2 / 5 : ℝ) * (1 / 10) = (1 / 5 : ℝ) ^ 2 := by norm_num
    rw [hsq, Real.log_pow]
    have hdiv : ((2 : ℕ) : ℝ) * Real.log (1 / 5) / 2 = Real.log (1 / 5) := by ring
    rw [hdiv, Real.exp_log (by norm_num)]
  have hExp2 : Real.exp ((Real.log (1 / 10) + Real.log (2 / 5)) / 2) = 1 / 5 := by
    rw [add_comm]
    exact hExp1
  have hbEqSum : strategicBidSum bEq = 2 := by
    unfold strategicBidSum
    rw [Fin.sum_univ_two]
    norm_num [bEq]
  have hbEqPos : 0 < strategicBidSum bEq := by linarith
  let uMid : Fin 3 → ℝ := fun t =>
    (∑ i : Fin 2, (bEq i : ℝ) * Real.log ((pProf i).prob t)) / strategicBidSum bEq
  have hu0 : Real.exp (uMid 0) = 1 / 2 := by
    dsimp [uMid]; rw [Fin.sum_univ_two, hbEqSum]
    simp only [bEq, pProf, Matrix.cons_val_zero, Matrix.cons_val_one, hp₁0, hp₂0]
    norm_num
    exact Real.exp_log (by norm_num)
  have hu1 : Real.exp (uMid 1) = 1 / 5 := by
    dsimp [uMid]; rw [Fin.sum_univ_two, hbEqSum]
    simp only [bEq, pProf, Matrix.cons_val_zero, Matrix.cons_val_one, hp₁1, hp₂1]
    norm_num
    exact hExp1
  have hu2 : Real.exp (uMid 2) = 1 / 5 := by
    dsimp [uMid]; rw [Fin.sum_univ_two, hbEqSum]
    simp only [bEq, pProf, Matrix.cons_val_zero, Matrix.cons_val_one, hp₁2, hp₂2]
    norm_num
    exact hExp2
  have hZMid : ∑ s : Fin 3, Real.exp (uMid s) = 9 / 10 := by
    rw [Fin.sum_univ_three, hu0, hu1, hu2]; norm_num
  have hqMidProb : ∀ t : Fin 3,
      (logLinearAggNoPlatform p₂ bEq pProf).prob t = Real.exp (uMid t) / (9 / 10) := by
    intro t
    unfold logLinearAggNoPlatform
    rw [dif_pos hbEqPos]
    dsimp only
    change Real.exp (uMid t - Real.log (∑ s : Fin 3, Real.exp (uMid s))) = _
    rw [hZMid, Real.exp_sub, Real.exp_log (by norm_num)]
  have hqMid0 : (logLinearAggNoPlatform p₂ bEq pProf).prob 0 = 5 / 9 := by
    rw [hqMidProb 0, hu0]; norm_num
  have hqMid1 : (logLinearAggNoPlatform p₂ bEq pProf).prob 1 = 2 / 9 := by
    rw [hqMidProb 1, hu1]; norm_num
  have hqMid2 : (logLinearAggNoPlatform p₂ bEq pProf).prob 2 = 2 / 9 := by
    rw [hqMidProb 2, hu2]; norm_num
  refine ⟨hqMid0, hqMid1, hqMid2, ?_, ?_⟩
  · intro hMono
    let bOthers : OpposingBids 2 0 := fun _ => 1
    have hJoin1 : joinBid (0 : Fin 2) 1 bOthers = bEq := by
      ext j; fin_cases j <;> simp [joinBid, bOthers, bEq]
    let bZero := joinBid (0 : Fin 2) 0 bOthers
    have hbZeroSum : strategicBidSum bZero = 1 := by
      unfold strategicBidSum
      rw [Fin.sum_univ_two]
      simp [bZero, joinBid, bOthers]
    have hbZeroPos : 0 < strategicBidSum bZero := by linarith
    have hqZero0 : (logLinearAggNoPlatform p₂ bZero pProf).prob 0 = 1 / 2 := by
      unfold logLinearAggNoPlatform
      rw [dif_pos hbZeroPos]
      dsimp only
      have huZ : ∀ s : Fin 3,
          (∑ i : Fin 2, (bZero i : ℝ) * Real.log ((pProf i).prob s)) / strategicBidSum bZero =
            Real.log (p₂.prob s) := by
        intro s
        rw [Fin.sum_univ_two, hbZeroSum]
        simp [bZero, joinBid, bOthers, pProf]
      have hExpZ : ∀ s : Fin 3,
          Real.exp ((∑ i : Fin 2, (bZero i : ℝ) * Real.log ((pProf i).prob s)) /
            strategicBidSum bZero) = p₂.prob s := by
        intro s
        rw [huZ s, Real.exp_log (hp₂Full s)]
      have hSumZ : ∑ s : Fin 3,
          Real.exp ((∑ i : Fin 2, (bZero i : ℝ) * Real.log ((pProf i).prob s)) /
            strategicBidSum bZero) = 1 := by
        simp_rw [hExpZ]
        exact p₂.sum_eq_one
      rw [hSumZ, Real.log_one, sub_zero, hExpZ 0, hp₂0]
    have hPref := hMono 0 pProf bOthers 1 0 (by norm_num)
    rw [hJoin1] at hPref
    have hAbs := hPref.1 0
    change |(logLinearAggNoPlatform p₂ bEq pProf).prob 0 - p₁.prob 0| ≤
      |(logLinearAggNoPlatform p₂ bZero pProf).prob 0 - p₁.prob 0| at hAbs
    rw [hqMid0, hqZero0, hp₁0] at hAbs
    norm_num at hAbs
  · intro b₀ hb₀ hMono
    have hb₀' : (0 : ℝ) < (b₀ : ℝ) := by exact_mod_cast hb₀
    let bOthers : OpposingBids 2 0 := fun _ => 1
    let bHigh := joinBid (0 : Fin 2) (1 + b₀) bOthers
    let bLow := joinBid (0 : Fin 2) 0 bOthers
    have hScoreHigh : ∀ s : Fin 3, logLinearScore b₀ p₂ bHigh pProf s = uMid s := by
      intro s
      unfold logLinearScore totalBidWithPlatform strategicBidSum
      dsimp [uMid]
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, hbEqSum]
      simp only [bHigh, bOthers, bEq, joinBid, Fin.isValue, ↓reduceDIte,
        one_ne_zero, Matrix.cons_val_zero, Matrix.cons_val_one, pProf,
        NNRat.cast_add, NNRat.cast_one]
      have hden : (1 : ℝ) + (b₀ : ℝ) ≠ 0 := by linarith
      field_simp [hden]
      ring
    have hqHigh0 : (logLinearAggRule b₀ hb₀ p₂ bHigh pProf).prob 0 = 5 / 9 := by
      unfold logLinearAggRule
      dsimp only
      simp_rw [hScoreHigh]
      rw [hZMid, Real.exp_sub, Real.exp_log (by norm_num), hu0]
      norm_num
    have hScoreLow : ∀ s : Fin 3, logLinearScore b₀ p₂ bLow pProf s = Real.log (p₂.prob s) := by
      intro s
      unfold logLinearScore totalBidWithPlatform strategicBidSum
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [bLow, bOthers, joinBid, Fin.isValue, ↓reduceDIte,
        one_ne_zero, Matrix.cons_val_zero, Matrix.cons_val_one, pProf,
        NNRat.cast_zero, NNRat.cast_one]
      have hden : (b₀ : ℝ) + 1 ≠ 0 := by linarith
      field_simp [hden]
      ring
    have hqLow0 : (logLinearAggRule b₀ hb₀ p₂ bLow pProf).prob 0 = 1 / 2 := by
      unfold logLinearAggRule
      dsimp only
      simp_rw [hScoreLow]
      have hExpL : ∀ s : Fin 3, Real.exp (Real.log (p₂.prob s)) = p₂.prob s :=
        fun s => Real.exp_log (hp₂Full s)
      simp_rw [hExpL]
      rw [p₂.sum_eq_one, Real.log_one, sub_zero, hExpL 0, hp₂0]
    have hPref := hMono 0 pProf bOthers (1 + b₀) 0 (zero_le _)
    have hAbs := hPref.1 0
    change |(logLinearAggRule b₀ hb₀ p₂ bHigh pProf).prob 0 - p₁.prob 0| ≤
      |(logLinearAggRule b₀ hb₀ p₂ bLow pProf).prob 0 - p₁.prob 0| at hAbs
    rw [hqHigh0, hqLow0, hp₁0] at hAbs
    norm_num at hAbs

/-- Lemma 5.3 (`lemma:monotone-alter`): Single-agent robust monotonicity holds if and only if
    undersampled token probabilities (`t ∈ T⁺`) stay `≤ p_i(t)` and are nondecreasing in `b_i`,
    while oversampled token probabilities (`t ∈ T⁻`) stay `≥ p_i(t)` and are nonincreasing in `b_i`. -/
theorem lem_5_3_monotone_coord_iff (T : Type) [Fintype T] [DecidableEq T]
    (q : Bid → TokenDist T) (target : TokenDist T) :
    IsSingleAgentRobustMonotone q target ↔
      ((∀ t ∈ undersampledTokens q target,
          (∀ b_i : Bid, (q b_i).prob t ≤ target.prob t) ∧ Monotone (fun b_i : Bid => (q b_i).prob t)) ∧
       (∀ t ∈ oversampledTokens q target,
          (∀ b_i : Bid, target.prob t ≤ (q b_i).prob t) ∧ Antitone (fun b_i : Bid => (q b_i).prob t))) := by
  constructor
  · intro hMono
    refine ⟨?_, ?_⟩
    · intro t ht
      have hd0 : (q 0).prob t - target.prob t ≤ 0 := by
        have : (q 0).prob t ≤ target.prob t := ht
        linarith
      have hBound : ∀ b_i : Bid, (q b_i).prob t ≤ target.prob t := by
        intro b_i
        have h0 := hMono b_i 0 (zero_le b_i)
        have hc := (hRobustCoord ((q b_i).prob t - target.prob t)
          ((q 0).prob t - target.prob t)).mp ⟨h0.1 t, h0.2 t⟩
        rcases hc with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
      refine ⟨hBound, ?_⟩
      intro b'_i b_i hle
      have hbb' := hMono b_i b'_i hle
      have hc := (hRobustCoord ((q b_i).prob t - target.prob t)
        ((q b'_i).prob t - target.prob t)).mp ⟨hbb'.1 t, hbb'.2 t⟩
      have hb1 := hBound b_i
      have hb2 := hBound b'_i
      rcases hc with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
    · intro t ht
      have hd0 : 0 < (q 0).prob t - target.prob t := by
        have : target.prob t < (q 0).prob t := ht
        linarith
      have hBound : ∀ b_i : Bid, target.prob t ≤ (q b_i).prob t := by
        intro b_i
        have h0 := hMono b_i 0 (zero_le b_i)
        have hc := (hRobustCoord ((q b_i).prob t - target.prob t)
          ((q 0).prob t - target.prob t)).mp ⟨h0.1 t, h0.2 t⟩
        rcases hc with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
      refine ⟨hBound, ?_⟩
      intro b'_i b_i hle
      have hbb' := hMono b_i b'_i hle
      have hc := (hRobustCoord ((q b_i).prob t - target.prob t)
        ((q b'_i).prob t - target.prob t)).mp ⟨hbb'.1 t, hbb'.2 t⟩
      have hb1 := hBound b_i
      have hb2 := hBound b'_i
      rcases hc with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · rintro ⟨hUnder, hOver⟩ b_i b'_i hle
    have hCoord : ∀ t : T,
        |(q b_i).prob t - target.prob t| ≤ |(q b'_i).prob t - target.prob t| ∧
        0 ≤ ((q b_i).prob t - target.prob t) * ((q b'_i).prob t - target.prob t) := by
      intro t
      rw [hRobustCoord]
      rcases le_or_gt ((q 0).prob t) (target.prob t) with ht | ht
      · have ⟨hB, hM⟩ := hUnder t ht
        have h1 := hM hle
        have h2 := hB b_i
        right; constructor <;> linarith
      · have ⟨hB, hA⟩ := hOver t ht
        have h1 := hA hle
        have h2 := hB b_i
        left; constructor <;> linarith
    exact ⟨fun t => (hCoord t).1, fun t => (hCoord t).2⟩

/-- Lemma 5.3 (`lemma:monotone-alter`, `n`-agent form): Under robust preferences, a distribution
    aggregation function `q : ℚ₊ⁿ × Δ(T)ⁿ → Δ(T)` is monotone if and only if for every strategic
    agent `i`, target profile `p`, and opposing bid profile `b_{-i}`, undersampled token
    probabilities (`T⁺`) stay at most `p_i(t)` and are nondecreasing in `b_i`, while oversampled
    token probabilities (`T⁻`) stay at least `p_i(t)` and are nonincreasing in `b_i`. -/
theorem lem_5_3_monotone_agg_iff (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (q : AggRule n T) :
    IsMonotoneAgg (robustAgentPrefs n T) q ↔
      ∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i),
        let qSlice : Bid → TokenDist T := fun b_i => q (joinBid i b_i bOthers) p
        (∀ t ∈ undersampledTokens qSlice (p i),
          (∀ b_i : Bid, (qSlice b_i).prob t ≤ (p i).prob t) ∧
          Monotone (fun b_i : Bid => (qSlice b_i).prob t)) ∧
        (∀ t ∈ oversampledTokens qSlice (p i),
          (∀ b_i : Bid, (p i).prob t ≤ (qSlice b_i).prob t) ∧
          Antitone (fun b_i : Bid => (qSlice b_i).prob t)) := by
  constructor
  · intro hMono i p bOthers
    exact (lem_5_3_monotone_coord_iff T (fun b_i => q (joinBid i b_i bOthers) p) (p i)).mp
      (fun b_i b'_i hle => hMono i p bOthers b_i b'_i hle)
  · intro hCoord i p bOthers b_i b'_i hle
    exact (lem_5_3_monotone_coord_iff T (fun y => q (joinBid i y bOthers) p) (p i)).mpr
      (hCoord i p bOthers) b_i b'_i hle

/-! ## Section 5.1 & Appendix D.1: Stable Sampling Existence -/

/-- Section 5.1 Two-Token Illustrative Sampler: When `T = Fin 2` with `0 ∈ T⁺` and `1 ∈ T⁻`,
    the threshold sampler `σ(b_i, r) = 1` if `r < q_1(b_i)` else `0` on `([0, 1], Leb)` is a
    stable sampling implementation. -/
theorem sec_5_1_two_token_stable_sampler
    (q : Bid → TokenDist (Fin 2)) (target : TokenDist (Fin 2))
    (hMono : IsSingleAgentRobustMonotone q target)
    (h0 : (0 : Fin 2) ∈ undersampledTokens q target)
    (h1 : (1 : Fin 2) ∈ oversampledTokens q target) :
    ∃ (μ₁ : Measure ℝ) (_ : IsProbabilityMeasure μ₁),
      μ₁ = volume.restrict (Set.Icc (0 : ℝ) 1) ∧
      IsStableSampler μ₁ q target
        (fun (b_i : Bid) (r : ℝ) => if r < (q b_i).prob 1 then (1 : Fin 2) else (0 : Fin 2)) := by
  let μ₁ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hProbμ₁ : IsProbabilityMeasure μ₁ := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    norm_num
  refine ⟨μ₁, hProbμ₁, rfl, ?_⟩
  let σ : Bid → ℝ → Fin 2 := fun b_i r => if r < (q b_i).prob 1 then 1 else 0
  change IsStableSampler μ₁ q target σ
  have hAnti1 : Antitone (fun b_i : Bid => (q b_i).prob 1) :=
    (((lem_5_3_monotone_coord_iff (Fin 2) q target).mp hMono).2 1 h1).2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro b_i t
    fin_cases t
    · change MeasurableSet {r : ℝ | σ b_i r = 0}
      have hSet : {r : ℝ | σ b_i r = 0} = Set.Ici ((q b_i).prob 1) := by
        ext r; simp [σ]
      rw [hSet]
      exact measurableSet_Ici
    · change MeasurableSet {r : ℝ | σ b_i r = 1}
      have hSet : {r : ℝ | σ b_i r = 1} = Set.Iio ((q b_i).prob 1) := by
        ext r; simp [σ]
      rw [hSet]
      exact measurableSet_Iio
  · intro b_i t
    have hp0_nonneg : 0 ≤ (q b_i).prob 0 := (q b_i).nonneg 0
    have hp1_nonneg : 0 ≤ (q b_i).prob 1 := (q b_i).nonneg 1
    have hsum : (q b_i).prob 0 + (q b_i).prob 1 = 1 := by
      have h := (q b_i).sum_eq_one
      rw [Fin.sum_univ_two] at h
      exact h
    have hp1_le_one : (q b_i).prob 1 ≤ 1 := by linarith
    fin_cases t
    · change μ₁.real {r : ℝ | σ b_i r = 0} = (q b_i).prob 0
      have hSet : {r : ℝ | σ b_i r = 0} = Set.Ici ((q b_i).prob 1) := by
        ext r; simp [σ]
      rw [hSet, measureReal_def]
      dsimp [μ₁]
      rw [Measure.restrict_apply measurableSet_Ici]
      have hInter : Set.Ici ((q b_i).prob 1) ∩ Set.Icc (0 : ℝ) 1 =
          Set.Icc ((q b_i).prob 1) 1 := by
        ext r; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
        constructor
        · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
      rw [hInter, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      linarith
    · change μ₁.real {r : ℝ | σ b_i r = 1} = (q b_i).prob 1
      have hSet : {r : ℝ | σ b_i r = 1} = Set.Iio ((q b_i).prob 1) := by
        ext r; simp [σ]
      rw [hSet, measureReal_def]
      dsimp [μ₁]
      rw [Measure.restrict_apply measurableSet_Iio]
      have hInter : Set.Iio ((q b_i).prob 1) ∩ Set.Icc (0 : ℝ) 1 =
          Set.Ico (0 : ℝ) ((q b_i).prob 1) := by
        ext r; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
      rw [hInter, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal hp1_nonneg]
  · intro r
    let W_r : Set Bid := {b_i : Bid | (q b_i).prob 1 ≤ r}
    have hUpper : IsUpperSet W_r := by
      intro a b hab ha
      exact le_trans (hAnti1 hab) ha
    have hFormula : ∀ b_i : Bid, σ b_i r = if b_i ∈ W_r then (0 : Fin 2) else (1 : Fin 2) := by
      intro b_i
      dsimp [σ, W_r]
      by_cases hlt : r < (q b_i).prob 1
      · have hnle : ¬ (q b_i).prob 1 ≤ r := not_le.mpr hlt
        simp [hlt, hnle]
      · have hle : (q b_i).prob 1 ≤ r := not_lt.mp hlt
        simp [hlt, hle]
    by_cases hNe : W_r.Nonempty
    · by_cases hUniv : W_r = Set.univ
      · left
        refine ⟨0, fun b_i => ?_⟩
        have hmem : b_i ∈ W_r := by rw [hUniv]; trivial
        rw [hFormula b_i, if_pos hmem]
      · right
        exact ⟨0, h0, 1, h1, W_r, hUpper, hNe, hUniv, hFormula⟩
    · left
      refine ⟨1, fun b_i => ?_⟩
      have hnot : b_i ∉ W_r := fun hb => hNe ⟨b_i, hb⟩
      rw [hFormula b_i, if_neg hnot]

/-- Theorem 5.5 (`thm:stable`): Every robust-monotone single-agent aggregation function
    `q : ℚ₊ → Δ(T)` admits a stable sampling implementation `σ : ℚ₊ × [0, 1]² → T` under the
    uniform Lebesgue measure on `[0, 1]²`. -/
theorem thm_5_5_stable_sampling_exists (T : Type) [Fintype T] [DecidableEq T]
    (q : Bid → TokenDist T) (target : TokenDist T)
    (hMono : IsSingleAgentRobustMonotone q target) :
    ∃ (μ₂ : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure μ₂) (σ : Bid → (ℝ × ℝ) → T),
      μ₂ = (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      IsStableSampler μ₂ q target σ := by
  haveI hNonemptyT : Nonempty T := tokenDist_nonempty target
  let μ₁ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  haveI hProbμ₁ : IsProbabilityMeasure μ₁ := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    norm_num
  let μ₂ : Measure (ℝ × ℝ) := μ₁.prod μ₁
  haveI hProbμ₂ : IsProbabilityMeasure μ₂ := inferInstance
  
  let K : ℕ := Fintype.card T
  have hKpos : 0 < K := Fintype.card_pos
  let eT : Fin K ≃ T := (Fintype.equivFin T).symm
  let tDef : T := eT ⟨0, hKpos⟩
  let cw : (T → ℝ) → Fin K → ℝ := fun w i =>
    ∑ j ∈ Finset.univ.filter (· < i), w (eT j)
  let dw : (T → ℝ) → Fin K → ℝ := fun w i => cw w i + w (eT i)
  let cdfPick : (T → ℝ) → ℝ → T := fun w rB =>
    if h : ∃ i : Fin K, rB ∈ Set.Ico (cw w i) (dw w i) then eT (Classical.choose h) else tDef
  have h_dw_eq : ∀ (w : T → ℝ) (i : Fin K),
      dw w i = ∑ j ∈ Finset.univ.filter (· ≤ i), w (eT j) := by
    intro w i
    dsimp [dw, cw]
    have hSub : Finset.univ.filter (· ≤ i) = insert i (Finset.univ.filter (· < i)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      exact le_iff_eq_or_lt
    have hNotMem : i ∉ Finset.univ.filter (· < i) := by simp
    rw [hSub, Finset.sum_insert hNotMem, add_comm]
  have h_cdf_disj : ∀ (w : T → ℝ), (∀ t, 0 ≤ w t) →
      ∀ (i j : Fin K) (rB : ℝ),
        rB ∈ Set.Ico (cw w i) (dw w i) → rB ∈ Set.Ico (cw w j) (dw w j) → i = j := by
    intro w hw i j rB hi hj
    rcases lt_trichotomy i j with hij | rfl | hji
    · exfalso
      have hle : dw w i ≤ cw w j := by
        rw [h_dw_eq]
        dsimp [cw]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
          exact lt_of_le_of_lt hl hij
        · intro l _ _; exact hw (eT l)
      linarith [hi.2, hj.1]
    · rfl
    · exfalso
      have hle : dw w j ≤ cw w i := by
        rw [h_dw_eq]
        dsimp [cw]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
          exact lt_of_le_of_lt hl hji
        · intro l _ _; exact hw (eT l)
      linarith [hj.2, hi.1]
  have h_cdf_cover : ∀ (w : T → ℝ), (∀ t, 0 ≤ w t) → ∑ t : T, w t = 1 →
      ∀ rB ∈ Set.Ico (0 : ℝ) 1, ∃ i : Fin K, rB ∈ Set.Ico (cw w i) (dw w i) := by
    intro w hw hsum rB hrB
    let P : ℕ → ℝ := fun n => ∑ j ∈ Finset.univ.filter (fun j : Fin K => j.1 < n), w (eT j)
    have hP0 : P 0 = 0 := by simp [P]
    have hPK : P K = 1 := by
      have hUniv : Finset.univ.filter (fun j : Fin K => j.1 < K) = Finset.univ := by
        ext j; simp
      dsimp [P]
      rw [hUniv, Equiv.sum_comp eT w, hsum]
    have hInd : ∀ n : ℕ, n ≤ K → rB ∈ Set.Ico 0 (P n) →
        ∃ i : Fin K, rB ∈ Set.Ico (cw w i) (dw w i) := by
      intro n
      induction n with
      | zero =>
        intro _ hr
        rw [hP0] at hr
        simp at hr
      | succ n ih =>
        intro hn hr
        have hnlt : n < K := Nat.lt_of_succ_le hn
        let inat : Fin K := ⟨n, hnlt⟩
        have hSplit : Finset.univ.filter (fun j : Fin K => j.1 < n + 1) =
            insert inat (Finset.univ.filter (fun j : Fin K => j.1 < n)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Fin.ext_iff, inat]
          omega
        have hNotMem : inat ∉ Finset.univ.filter (fun j : Fin K => j.1 < n) := by
          simp [inat]
        have hPsucc : P (n + 1) = P n + w (eT inat) := by
          dsimp [P]
          rw [hSplit, Finset.sum_insert hNotMem, add_comm]
        have hcw_eq : cw w inat = P n := by
          dsimp [cw, P, inat]
          rfl
        have hdw_eq : dw w inat = P (n + 1) := by
          dsimp [dw]
          rw [hcw_eq, hPsucc]
        rcases lt_or_ge rB (P n) with hlt | hge
        · exact ih (Nat.le_of_succ_le hn) ⟨hr.1, hlt⟩
        · exact ⟨inat, ⟨by rw [hcw_eq]; exact hge, by rw [hdw_eq]; exact hr.2⟩⟩
    rw [← hPK] at hrB
    exact hInd K le_rfl hrB
  have h_cdf_iff : ∀ (w : T → ℝ), (∀ t, 0 ≤ w t) → ∑ t : T, w t = 1 →
      ∀ rB ∈ Set.Ico (0 : ℝ) 1, ∀ t : T,
        cdfPick w rB = t ↔ rB ∈ Set.Ico (cw w (eT.symm t)) (dw w (eT.symm t)) := by
    intro w hw hsum rB hrB t
    have hex : ∃ i : Fin K, rB ∈ Set.Ico (cw w i) (dw w i) := h_cdf_cover w hw hsum rB hrB
    have hSpec := Classical.choose_spec hex
    constructor
    · intro hEq
      dsimp [cdfPick] at hEq
      rw [dif_pos hex] at hEq
      have hChoose : Classical.choose hex = eT.symm t := by
        apply eT.injective
        rw [hEq, Equiv.apply_symm_apply]
      rwa [← hChoose]
    · intro hr
      dsimp [cdfPick]
      rw [dif_pos hex]
      have hChoose : Classical.choose hex = eT.symm t :=
        h_cdf_disj w hw (Classical.choose hex) (eT.symm t) rB hSpec hr
      rw [hChoose, Equiv.apply_symm_apply]
  have h_cdf_bounds : ∀ (w : T → ℝ), (∀ t, 0 ≤ w t) → ∑ t : T, w t = 1 →
      ∀ i : Fin K, 0 ≤ cw w i ∧ cw w i ≤ dw w i ∧ dw w i ≤ 1 := by
    intro w hw hsum i
    have h1 : 0 ≤ cw w i := Finset.sum_nonneg (fun j _ => hw (eT j))
    have h2 : cw w i ≤ dw w i := by dsimp [dw]; linarith [hw (eT i)]
    have h3 : dw w i ≤ 1 := by
      rw [h_dw_eq, ← hsum, ← Equiv.sum_comp eT w]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hw (eT j))
    exact ⟨h1, h2, h3⟩
  have h_cdf_pos : ∀ (w : T → ℝ), (∀ t, 0 ≤ w t) → ∑ t : T, w t = 1 →
      ∀ rB ∈ Set.Ico (0 : ℝ) 1, 0 < w (cdfPick w rB) := by
    intro w hw hsum rB hrB
    let t := cdfPick w rB
    have hr := (h_cdf_iff w hw hsum rB hrB t).mp rfl
    have hlt : cw w (eT.symm t) < cw w (eT.symm t) + w (eT (eT.symm t)) :=
      lt_of_le_of_lt hr.1 hr.2
    rw [Equiv.apply_symm_apply] at hlt
    linarith
  have h_cdf_meas1D : ∀ (w : T → ℝ), (∀ t, 0 ≤ w t) → ∑ t : T, w t = 1 →
      ∀ t : T, μ₁ {rB : ℝ | rB ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick w rB = t} = ENNReal.ofReal (w t) := by
    intro w hw hsum t
    let i := eT.symm t
    have ⟨hb0, _, hb1⟩ := h_cdf_bounds w hw hsum i
    have hSetEq : {rB : ℝ | rB ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick w rB = t} =
        Set.Ico (cw w i) (dw w i) := by
      ext rB
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hrB, hEq⟩
        exact (h_cdf_iff w hw hsum rB hrB t).mp hEq
      · intro hr
        have hrB : rB ∈ Set.Ico (0 : ℝ) 1 := ⟨le_trans hb0 hr.1, lt_of_lt_of_le hr.2 hb1⟩
        exact ⟨hrB, (h_cdf_iff w hw hsum rB hrB t).mpr hr⟩
    rw [hSetEq]
    dsimp [μ₁]
    rw [Measure.restrict_apply measurableSet_Ico]
    have hInter : Set.Ico (cw w i) (dw w i) ∩ Set.Icc (0 : ℝ) 1 = Set.Ico (cw w i) (dw w i) := by
      apply Set.inter_eq_left.mpr
      intro rB hr
      exact ⟨le_trans hb0 hr.1, le_trans (le_of_lt hr.2) hb1⟩
    rw [hInter, Real.volume_Ico]
    have hdiff : dw w i - cw w i = w t := by
      dsimp [dw, i]
      rw [Equiv.apply_symm_apply]
      ring
    rw [hdiff]
  have h_cdf_meas2D : ∀ (A : Set ℝ) (W : ℝ → T → ℝ) (t : T),
      MeasurableSet A →
      (∀ s : T, Measurable (fun rA => W rA s)) →
      (∀ rA ∈ A, (∀ s : T, 0 ≤ W rA s) ∧ ∑ s : T, W rA s = 1) →
      MeasurableSet {r : ℝ × ℝ | r.1 ∈ A ∧ r.2 ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick (W r.1) r.2 = t} := by
    intro A W t hMeasA hMeasW hValidW
    let i := eT.symm t
    have hEq : {r : ℝ × ℝ | r.1 ∈ A ∧ r.2 ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick (W r.1) r.2 = t} =
        (A ×ˢ Set.Ico (0 : ℝ) 1) ∩
        {r : ℝ × ℝ | cw (W r.1) i ≤ r.2} ∩
        {r : ℝ × ℝ | r.2 < dw (W r.1) i} := by
      ext ⟨rA, rB⟩
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ico]
      constructor
      · rintro ⟨hrA, hrB, hEq⟩
        have ⟨hw1, hw2⟩ := hValidW rA hrA
        have hIco := (h_cdf_iff (W rA) hw1 hw2 rB hrB t).mp hEq
        exact ⟨⟨⟨hrA, hrB⟩, hIco.1⟩, hIco.2⟩
      · rintro ⟨⟨⟨hrA, hrB⟩, hle⟩, hlt⟩
        have ⟨hw1, hw2⟩ := hValidW rA hrA
        exact ⟨hrA, hrB, (h_cdf_iff (W rA) hw1 hw2 rB hrB t).mpr ⟨hle, hlt⟩⟩
    rw [hEq]
    have hmcw : Measurable (fun r : ℝ × ℝ => cw (W r.1) i) := by
      dsimp [cw]
      exact Finset.measurable_sum _ (fun j _ => (hMeasW (eT j)).comp measurable_fst)
    have hmdw : Measurable (fun r : ℝ × ℝ => dw (W r.1) i) := by
      dsimp [dw]
      exact hmcw.add ((hMeasW (eT i)).comp measurable_fst)
    exact ((hMeasA.prod measurableSet_Ico).inter (measurableSet_le hmcw measurable_snd)).inter
      (measurableSet_lt measurable_snd hmdw)

  
  let TplusF : Finset T := Finset.univ.filter (fun t => (q 0).prob t ≤ target.prob t)
  let TminusF : Finset T := Finset.univ.filter (fun t => ¬ (q 0).prob t ≤ target.prob t)
  have hCoord := (lem_5_3_monotone_coord_iff T q target).mp hMono
  have hMonoPlus : ∀ t ∈ TplusF, Monotone (fun b : Bid => (q b).prob t) := by
    intro t ht
    simp only [TplusF, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact (hCoord.1 t ht).2
  have hAntiMinus : ∀ t ∈ TminusF, Antitone (fun b : Bid => (q b).prob t) := by
    intro t ht
    simp only [TminusF, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at ht
    exact (hCoord.2 t ht).2
  let Qplus : Bid → ℝ := fun b => ∑ t ∈ TplusF, (q b).prob t
  have hQplusMono : Monotone Qplus := fun b₁ b₂ hle =>
    Finset.sum_le_sum (fun t ht => hMonoPlus t ht hle)
  have hQplusNonneg : ∀ b : Bid, 0 ≤ Qplus b := fun b =>
    Finset.sum_nonneg (fun t _ => (q b).nonneg t)
  have hSumMinus : ∀ b : Bid, ∑ t ∈ TminusF, (q b).prob t = 1 - Qplus b := by
    intro b
    have hpart := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun t : T => (q 0).prob t ≤ target.prob t) (f := fun t => (q b).prob t)
    change Qplus b + ∑ t ∈ TminusF, (q b).prob t = ∑ t : T, (q b).prob t at hpart
    rw [(q b).sum_eq_one] at hpart
    linarith
  have hQplusLeOne : ∀ b : Bid, Qplus b ≤ 1 := by
    intro b
    have hnn : 0 ≤ ∑ t ∈ TminusF, (q b).prob t := Finset.sum_nonneg (fun t _ => (q b).nonneg t)
    linarith [hSumMinus b]
  have hLipBid : ∀ (b₁ b₂ : Bid) (t : T),
      |(q b₁).prob t - (q b₂).prob t| ≤ |Qplus b₁ - Qplus b₂| := by
    have hHalf : ∀ (b₁ b₂ : Bid) (t : T), b₁ ≤ b₂ →
        |(q b₁).prob t - (q b₂).prob t| ≤ |Qplus b₁ - Qplus b₂| := by
      intro b₁ b₂ t hle
      have hQle : Qplus b₁ ≤ Qplus b₂ := hQplusMono hle
      rw [abs_sub_comm (Qplus b₁), abs_of_nonneg (sub_nonneg.mpr hQle)]
      by_cases ht : t ∈ TplusF
      · have htle : (q b₁).prob t ≤ (q b₂).prob t := hMonoPlus t ht hle
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htle)]
        have hDiff : Qplus b₂ - Qplus b₁ = ∑ s ∈ TplusF, ((q b₂).prob s - (q b₁).prob s) := by
          dsimp [Qplus]; rw [← Finset.sum_sub_distrib]
        rw [hDiff]
        exact Finset.single_le_sum (fun s hs => sub_nonneg.mpr (hMonoPlus s hs hle)) ht
      · have ht' : t ∈ TminusF := by
          simp only [TplusF, TminusF, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          exact ht
        have htle : (q b₂).prob t ≤ (q b₁).prob t := hAntiMinus t ht' hle
        rw [abs_of_nonneg (sub_nonneg.mpr htle)]
        have hDiff : Qplus b₂ - Qplus b₁ = ∑ s ∈ TminusF, ((q b₁).prob s - (q b₂).prob s) := by
          have h1 := hSumMinus b₁
          have h2 := hSumMinus b₂
          rw [Finset.sum_sub_distrib]
          linarith
        rw [hDiff]
        exact Finset.single_le_sum (fun s hs => sub_nonneg.mpr (hAntiMinus s hs hle)) ht'
    intro b₁ b₂ t
    rcases le_total b₁ b₂ with hle | hle
    · exact hHalf b₁ b₂ t hle
    · rw [abs_sub_comm ((q b₁).prob t), abs_sub_comm (Qplus b₁)]
      exact hHalf b₂ b₁ t hle

  let m : ℝ := Qplus 0
  let M : ℝ := sSup (Set.range Qplus)
  have hBddQplus : BddAbove (Set.range Qplus) := ⟨1, by rintro _ ⟨b, rfl⟩; exact hQplusLeOne b⟩
  have hm_le_Qplus : ∀ b : Bid, m ≤ Qplus b := fun b => hQplusMono (zero_le b)
  have hQplus_le_M : ∀ b : Bid, Qplus b ≤ M := fun b => le_csSup hBddQplus ⟨b, rfl⟩
  have hm_le_M : m ≤ M := hQplus_le_M 0
  have hM_le_one : M ≤ 1 := csSup_le ⟨Qplus 0, ⟨0, rfl⟩⟩ (by rintro _ ⟨b, rfl⟩; exact hQplusLeOne b)
  have hm_nonneg : 0 ≤ m := hQplusNonneg 0
  let qInf : T → ℝ := fun t =>
    if t ∈ TplusF then sSup (Set.range (fun b : Bid => (q b).prob t))
    else sInf (Set.range (fun b : Bid => (q b).prob t))
  have hTendstoQplus : Filter.Tendsto Qplus Filter.atTop (nhds M) := by
    dsimp [M]
    rw [sSup_range]
    exact tendsto_atTop_ciSup hQplusMono hBddQplus
  have hTendstoCoord : ∀ t : T,
      Filter.Tendsto (fun b : Bid => (q b).prob t) Filter.atTop (nhds (qInf t)) := by
    intro t
    dsimp [qInf]
    split_ifs with ht
    · rw [sSup_range]
      refine tendsto_atTop_ciSup (hMonoPlus t ht) ⟨1, ?_⟩
      rintro _ ⟨b, rfl⟩
      have hsum := (q b).sum_eq_one
      rw [← hsum]
      exact Finset.single_le_sum (fun s _ => (q b).nonneg s) (Finset.mem_univ t)
    · have ht' : t ∈ TminusF := by
        simp only [TplusF, TminusF, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        exact ht
      rw [sInf_range]
      refine tendsto_atTop_ciInf (hAntiMinus t ht') ⟨0, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact (q b).nonneg t
  have hSumQInfPlus : ∑ t ∈ TplusF, qInf t = M := by
    have h1 : Filter.Tendsto (fun b : Bid => ∑ t ∈ TplusF, (q b).prob t) Filter.atTop
        (nhds (∑ t ∈ TplusF, qInf t)) :=
      tendsto_finset_sum TplusF (fun t _ => hTendstoCoord t)
    exact tendsto_nhds_unique h1 hTendstoQplus
  have hSumQInfMinus : ∑ t ∈ TminusF, qInf t = 1 - M := by
    have h1 : Filter.Tendsto (fun b : Bid => ∑ t ∈ TminusF, (q b).prob t) Filter.atTop
        (nhds (∑ t ∈ TminusF, qInf t)) :=
      tendsto_finset_sum TminusF (fun t _ => hTendstoCoord t)
    have h2 : Filter.Tendsto (fun b : Bid => ∑ t ∈ TminusF, (q b).prob t) Filter.atTop
        (nhds (1 - M)) := by
      simp_rw [hSumMinus]
      exact tendsto_const_nhds.sub hTendstoQplus
    exact tendsto_nhds_unique h1 h2
  have hQInfNonneg : ∀ t : T, 0 ≤ qInf t := by
    intro t
    exact ge_of_tendsto (hTendstoCoord t) (Filter.Eventually.of_forall (fun b => (q b).nonneg t))
  have hQInfLeMinus : ∀ t ∈ TminusF, ∀ b : Bid, qInf t ≤ (q b).prob t := by
    intro t ht b
    have htnot : t ∉ TplusF := by
      simp only [TplusF, TminusF, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ht
    dsimp [qInf]
    rw [if_neg htnot]
    exact csInf_le ⟨0, by rintro _ ⟨b', rfl⟩; exact (q b').nonneg t⟩ ⟨b, rfl⟩

  
  have hIcoComplNull : μ₁ (Set.Ico (0 : ℝ) 1)ᶜ = 0 := by
    dsimp [μ₁]
    rw [Measure.restrict_apply measurableSet_Ico.compl]
    have hSub : (Set.Ico (0 : ℝ) 1)ᶜ ∩ Set.Icc (0 : ℝ) 1 ⊆ {(1 : ℝ)} := by
      rintro x ⟨hx1, hx2⟩
      simp only [Set.mem_compl_iff, Set.mem_Ico] at hx1
      simp only [Set.mem_Icc] at hx2
      simp only [Set.mem_singleton_iff]
      by_contra hne
      exact hx1 ⟨hx2.1, lt_of_le_of_ne hx2.2 hne⟩
    exact measure_mono_null hSub Real.volume_singleton
  have hμ_union_null : ∀ {α : Type} [MeasurableSpace α] (ν : Measure α) (A B : Set α),
      ν B = 0 → ν (A ∪ B) = ν A :=
    fun ν A B hB => le_antisymm ((measure_union_le A B).trans (by rw [hB, add_zero]))
      (measure_mono Set.subset_union_left)

  
  rcases eq_or_lt_of_le hm_le_M with hm_eq_M | hm_lt_M
  · 
    have hqConst : ∀ (b : Bid) (t : T), (q b).prob t = (q 0).prob t := by
      intro b t
      have hQb : Qplus b = m := le_antisymm (by rw [hm_eq_M]; exact hQplus_le_M b) (hm_le_Qplus b)
      have hlip := hLipBid b 0 t
      have hQ0 : Qplus 0 = m := rfl
      rw [hQb, hQ0, sub_self, abs_zero] at hlip
      have hzero : |(q b).prob t - (q 0).prob t| = 0 :=
        le_antisymm hlip (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
    let σ : Bid → (ℝ × ℝ) → T := fun _ r =>
      if r.2 ∈ Set.Ico (0 : ℝ) 1 then cdfPick (q 0).prob r.2 else tDef
    let S1 (t : T) : Set (ℝ × ℝ) := {r : ℝ × ℝ | r.1 ∈ (Set.univ : Set ℝ) ∧
      r.2 ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick (q 0).prob r.2 = t}
    let S2 (t : T) : Set (ℝ × ℝ) :=
      if tDef = t then (Set.univ : Set ℝ) ×ˢ (Set.Ico (0 : ℝ) 1)ᶜ else ∅
    have hDecompC1 : ∀ (b_i : Bid) (t : T), {r : ℝ × ℝ | σ b_i r = t} = S1 t ∪ S2 t := by
      intro b_i t
      ext ⟨rA, rB⟩
      dsimp only [σ, S1, S2, Set.mem_setOf_eq, Set.mem_union]
      by_cases hrB : rB ∈ Set.Ico (0 : ℝ) 1
      · rw [if_pos hrB]
        by_cases ht : tDef = t
        · rw [if_pos ht]
          exact ⟨fun h => Or.inl ⟨trivial, hrB, h⟩,
            fun h => h.elim (fun h1 => h1.2.2) (fun h2 => (h2.2 hrB).elim)⟩
        · rw [if_neg ht]
          exact ⟨fun h => Or.inl ⟨trivial, hrB, h⟩,
            fun h => h.elim (fun h1 => h1.2.2) False.elim⟩
      · rw [if_neg hrB]
        by_cases ht : tDef = t
        · rw [if_pos ht]
          exact ⟨fun _ => Or.inr ⟨trivial, hrB⟩, fun _ => ht⟩
        · rw [if_neg ht]
          exact ⟨fun h => (ht h).elim,
            fun h => h.elim (fun h1 => (hrB h1.2.1).elim) False.elim⟩
    have hMeasS1 : ∀ t : T, MeasurableSet (S1 t) := fun t =>
      h_cdf_meas2D Set.univ (fun _ => (q 0).prob) t MeasurableSet.univ
        (fun _ => measurable_const) (fun _ _ => ⟨(q 0).nonneg, (q 0).sum_eq_one⟩)
    refine ⟨μ₂, hProbμ₂, σ, rfl, ⟨?_, ?_⟩, ?_⟩
    · intro b_i t
      rw [hDecompC1 b_i t]
      refine (hMeasS1 t).union ?_
      dsimp [S2]
      split_ifs
      · exact MeasurableSet.univ.prod measurableSet_Ico.compl
      · exact MeasurableSet.empty
    · intro b_i t
      have hS2Null : μ₂ (S2 t) = 0 := by
        dsimp [S2]
        split_ifs
        · dsimp [μ₂]
          rw [Measure.prod_prod, hIcoComplNull, mul_zero]
        · exact measure_empty
      have hS1Meas : μ₂ (S1 t) = ENNReal.ofReal ((q 0).prob t) := by
        dsimp [μ₂]
        rw [Measure.prod_apply (hMeasS1 t)]
        have hSliceEq : ∀ rA : ℝ, μ₁ (Prod.mk rA ⁻¹' S1 t) = ENNReal.ofReal ((q 0).prob t) := by
          intro rA
          have hPre : Prod.mk rA ⁻¹' S1 t =
              {rB : ℝ | rB ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick (q 0).prob rB = t} := by
            ext rB
            dsimp only [S1, Set.mem_preimage, Set.mem_setOf_eq]
            exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
          rw [hPre]
          exact h_cdf_meas1D (q 0).prob (q 0).nonneg (q 0).sum_eq_one t
        rw [lintegral_congr hSliceEq, lintegral_const, measure_univ, mul_one]
      rw [measureReal_def, hDecompC1 b_i t, hμ_union_null μ₂ (S1 t) (S2 t) hS2Null,
        hS1Meas, ENNReal.toReal_ofReal ((q 0).nonneg t), hqConst b_i t]
    · intro r
      left
      exact ⟨σ 0 r, fun _ => rfl⟩

  · 
    
    let S : Set ℝ := Set.range Qplus
    let clS : Set ℝ := closure S
    have hm_clS : m ∈ clS := subset_closure ⟨0, rfl⟩
    have hM_clS : M ∈ clS :=
      mem_closure_of_tendsto hTendstoQplus (Filter.Eventually.of_forall (fun b => ⟨b, rfl⟩))
    let g_cl : T → ℝ → ℝ := fun t x =>
      sInf (Set.range (fun b : Bid => (q b).prob t + |x - Qplus b|))
    have hg_cl_bdd : ∀ (t : T) (x : ℝ),
        BddBelow (Set.range (fun b : Bid => (q b).prob t + |x - Qplus b|)) := by
      intro t x
      refine ⟨0, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact add_nonneg ((q b).nonneg t) (abs_nonneg _)
    have hg_cl_approx : ∀ (t : T) (x : ℝ) (b₀ : Bid),
        |g_cl t x - (q b₀).prob t| ≤ |x - Qplus b₀| := by
      intro t x b₀
      rw [abs_le]
      constructor
      · have hle : (q b₀).prob t - |x - Qplus b₀| ≤ g_cl t x := by
          refine le_csInf ⟨(q 0).prob t + |x - Qplus 0|, ⟨0, rfl⟩⟩ ?_
          rintro _ ⟨b, rfl⟩
          have h1 : (q b₀).prob t - (q b).prob t ≤ |Qplus b₀ - Qplus b| :=
            le_trans (le_abs_self _) (hLipBid b₀ b t)
          have h2 : |Qplus b₀ - Qplus b| ≤ |Qplus b₀ - x| + |x - Qplus b| :=
            abs_sub_le (Qplus b₀) x (Qplus b)
          rw [abs_sub_comm (Qplus b₀) x] at h2
          linarith
        linarith
      · have hle : g_cl t x ≤ (q b₀).prob t + |x - Qplus b₀| :=
          csInf_le (hg_cl_bdd t x) ⟨b₀, rfl⟩
        linarith
    have hg_cl_lip : ∀ (t : T) (x y : ℝ), |g_cl t x - g_cl t y| ≤ |x - y| := by
      intro t x y
      rw [abs_le]
      constructor
      · have hle : g_cl t y - |x - y| ≤ g_cl t x := by
          refine le_csInf ⟨(q 0).prob t + |x - Qplus 0|, ⟨0, rfl⟩⟩ ?_
          rintro _ ⟨b, rfl⟩
          have hb : g_cl t y ≤ (q b).prob t + |y - Qplus b| :=
            csInf_le (hg_cl_bdd t y) ⟨b, rfl⟩
          have htri : |y - Qplus b| ≤ |y - x| + |x - Qplus b| := abs_sub_le y x (Qplus b)
          rw [abs_sub_comm y x] at htri
          linarith
        linarith
      · have hle : g_cl t x - |x - y| ≤ g_cl t y := by
          refine le_csInf ⟨(q 0).prob t + |y - Qplus 0|, ⟨0, rfl⟩⟩ ?_
          rintro _ ⟨b, rfl⟩
          have hb : g_cl t x ≤ (q b).prob t + |x - Qplus b| :=
            csInf_le (hg_cl_bdd t x) ⟨b, rfl⟩
          have htri : |x - Qplus b| ≤ |x - y| + |y - Qplus b| := abs_sub_le x y (Qplus b)
          linarith
        linarith
    have hg_cl_cont : ∀ t : T, Continuous (g_cl t) := by
      intro t
      rw [Metric.continuous_iff]
      intro x ε hε
      refine ⟨ε, hε, fun y hy => ?_⟩
      rw [Real.dist_eq] at hy ⊢
      exact lt_of_le_of_lt (hg_cl_lip t y x) hy
    have hg_cl_eval : ∀ (t : T) (b : Bid), g_cl t (Qplus b) = (q b).prob t := by
      intro t b
      have h := hg_cl_approx t (Qplus b) b
      rw [sub_self, abs_zero] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    have hg_cl_m : ∀ t : T, g_cl t m = (q 0).prob t := fun t => hg_cl_eval t 0
    have hg_cl_M : ∀ t : T, g_cl t M = qInf t := by
      intro t
      have h1 : Filter.Tendsto (fun b : Bid => g_cl t (Qplus b)) Filter.atTop
          (nhds (g_cl t M)) :=
        (hg_cl_cont t).continuousAt.tendsto.comp hTendstoQplus
      simp_rw [hg_cl_eval t] at h1
      exact tendsto_nhds_unique h1 (hTendstoCoord t)
    have hg_cl_sumPlus : ∀ x ∈ clS, ∑ t ∈ TplusF, g_cl t x = x := by
      have hEqS : Set.EqOn (fun x => ∑ t ∈ TplusF, g_cl t x) id S := by
        rintro _ ⟨b, rfl⟩
        simp [hg_cl_eval, Qplus]
      exact hEqS.closure (continuous_finset_sum _ (fun t _ => hg_cl_cont t)) continuous_id
    have hg_cl_sumMinus : ∀ x ∈ clS, ∑ t ∈ TminusF, g_cl t x = 1 - x := by
      have hEqS : Set.EqOn (fun x => ∑ t ∈ TminusF, g_cl t x) (fun x => 1 - x) S := by
        rintro _ ⟨b, rfl⟩
        simp [hg_cl_eval, hSumMinus]
      exact hEqS.closure (continuous_finset_sum _ (fun t _ => hg_cl_cont t))
        (continuous_const.sub continuous_id)
    have hg_cl_monoPlus : ∀ t ∈ TplusF, ∀ x₁ ∈ clS, ∀ x₂ ∈ clS, x₁ ≤ x₂ →
        g_cl t x₁ ≤ g_cl t x₂ := by
      intro t ht x₁ hx₁ x₂ hx₂ hle
      apply le_of_forall_pos_le_add
      intro ε hε
      have hε4 : 0 < ε / 4 := by linarith
      rcases (Metric.mem_closure_iff.mp hx₁) (ε / 4) hε4 with ⟨_, ⟨b₁, rfl⟩, hb₁⟩
      rcases (Metric.mem_closure_iff.mp hx₂) (ε / 4) hε4 with ⟨_, ⟨b₂, rfl⟩, hb₂⟩
      rw [Real.dist_eq, abs_lt] at hb₁ hb₂
      have hb₁_abs : |x₁ - Qplus b₁| < ε / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
      have hb₂_abs : |x₂ - Qplus b₂| < ε / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
      have ha1 := abs_lt.mp (lt_of_le_of_lt (hg_cl_approx t x₁ b₁) hb₁_abs)
      have ha2 := abs_lt.mp (lt_of_le_of_lt (hg_cl_approx t x₂ b₂) hb₂_abs)
      rcases le_total b₁ b₂ with hbb | hbb
      · have hm12 : (q b₁).prob t ≤ (q b₂).prob t := hMonoPlus t ht hbb
        linarith
      · have hQle : Qplus b₂ ≤ Qplus b₁ := hQplusMono hbb
        have hQdiff : Qplus b₁ - Qplus b₂ < ε / 2 := by linarith
        have hlip := hLipBid b₁ b₂ t
        rw [abs_of_nonneg (sub_nonneg.mpr hQle)] at hlip
        have hqlip := (abs_le.mp hlip).2
        linarith
    have hg_cl_antiMinus : ∀ t ∈ TminusF, ∀ x₁ ∈ clS, ∀ x₂ ∈ clS, x₁ ≤ x₂ →
        g_cl t x₂ ≤ g_cl t x₁ := by
      intro t ht x₁ hx₁ x₂ hx₂ hle
      apply le_of_forall_pos_le_add
      intro ε hε
      have hε4 : 0 < ε / 4 := by linarith
      rcases (Metric.mem_closure_iff.mp hx₁) (ε / 4) hε4 with ⟨_, ⟨b₁, rfl⟩, hb₁⟩
      rcases (Metric.mem_closure_iff.mp hx₂) (ε / 4) hε4 with ⟨_, ⟨b₂, rfl⟩, hb₂⟩
      rw [Real.dist_eq, abs_lt] at hb₁ hb₂
      have hb₁_abs : |x₁ - Qplus b₁| < ε / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
      have hb₂_abs : |x₂ - Qplus b₂| < ε / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
      have ha1 := abs_lt.mp (lt_of_le_of_lt (hg_cl_approx t x₁ b₁) hb₁_abs)
      have ha2 := abs_lt.mp (lt_of_le_of_lt (hg_cl_approx t x₂ b₂) hb₂_abs)
      rcases le_total b₁ b₂ with hbb | hbb
      · have hm12 : (q b₂).prob t ≤ (q b₁).prob t := hAntiMinus t ht hbb
        linarith
      · have hQle : Qplus b₂ ≤ Qplus b₁ := hQplusMono hbb
        have hQdiff : Qplus b₁ - Qplus b₂ < ε / 2 := by linarith
        have hlip := hLipBid b₂ b₁ t
        rw [abs_sub_comm (Qplus b₂), abs_of_nonneg (sub_nonneg.mpr hQle)] at hlip
        have hqlip := (abs_le.mp hlip).2
        linarith
    
    let xL : ℝ → ℝ := fun x => sSup (clS ∩ Set.Iic x)
    let xR : ℝ → ℝ := fun x => sInf (clS ∩ Set.Ici x)
    have hxL_props : ∀ x ∈ Set.Icc m M,
        xL x ∈ clS ∧ m ≤ xL x ∧ xL x ≤ x ∧ (∀ z ∈ clS, z ≤ x → z ≤ xL x) := by
      intro x hx
      have hClosed : IsClosed (clS ∩ Set.Iic x) := isClosed_closure.inter isClosed_Iic
      have hNe : (clS ∩ Set.Iic x).Nonempty := ⟨m, hm_clS, hx.1⟩
      have hBdd : BddAbove (clS ∩ Set.Iic x) := ⟨x, fun _ hz => hz.2⟩
      have hMem := hClosed.csSup_mem hNe hBdd
      exact ⟨hMem.1, le_csSup hBdd ⟨hm_clS, hx.1⟩, hMem.2,
        fun z hz hzx => le_csSup hBdd ⟨hz, hzx⟩⟩
    have hxR_props : ∀ x ∈ Set.Icc m M,
        xR x ∈ clS ∧ x ≤ xR x ∧ xR x ≤ M ∧ (∀ z ∈ clS, x ≤ z → xR x ≤ z) := by
      intro x hx
      have hClosed : IsClosed (clS ∩ Set.Ici x) := isClosed_closure.inter isClosed_Ici
      have hNe : (clS ∩ Set.Ici x).Nonempty := ⟨M, hM_clS, hx.2⟩
      have hBdd : BddBelow (clS ∩ Set.Ici x) := ⟨x, fun _ hz => hz.2⟩
      have hMem := hClosed.csInf_mem hNe hBdd
      exact ⟨hMem.1, hMem.2, csInf_le hBdd ⟨hM_clS, hx.2⟩,
        fun z hz hxz => csInf_le hBdd ⟨hz, hxz⟩⟩

    let qHat : T → ℝ → ℝ := fun t x =>
      if x < m then (q 0).prob t
      else if M < x then qInf t
      else if x ∈ clS then g_cl t x
      else ((xR x - x) / (xR x - xL x)) * g_cl t (xL x) +
           ((x - xL x) / (xR x - xL x)) * g_cl t (xR x)

    have hqHat_clS : ∀ (t : T) (x : ℝ), x ∈ Set.Icc m M → x ∈ clS → qHat t x = g_cl t x := by
      intro t x hx hxcl
      dsimp [qHat]
      rw [if_neg (not_lt.mpr hx.1), if_neg (not_lt.mpr hx.2), if_pos hxcl]
    have hqHat_eval : ∀ (t : T) (b : Bid), qHat t (Qplus b) = (q b).prob t := by
      intro t b
      rw [hqHat_clS t (Qplus b) ⟨hm_le_Qplus b, hQplus_le_M b⟩ (subset_closure ⟨b, rfl⟩),
        hg_cl_eval]
    have hqHat_m : ∀ t : T, qHat t m = (q 0).prob t := fun t => hqHat_eval t 0
    have hqHat_M : ∀ t : T, qHat t M = qInf t := by
      intro t
      rw [hqHat_clS t M ⟨hm_le_M, le_rfl⟩ hM_clS, hg_cl_M]
    have hqHat_clamp : ∀ (t : T) (x : ℝ), qHat t x = qHat t (max m (min M x)) := by
      intro t x
      rcases lt_or_ge x m with hxm | hmx
      · have hmin : min M x = x := min_eq_right (le_of_lt (lt_of_lt_of_le hxm hm_le_M))
        have hmax : max m x = m := max_eq_left (le_of_lt hxm)
        rw [hmin, hmax, hqHat_m]
        dsimp [qHat]
        rw [if_pos hxm]
      · rcases lt_or_ge M x with hMx | hxM
        · have hmin : min M x = M := min_eq_left (le_of_lt hMx)
          have hmax : max m M = M := max_eq_right hm_le_M
          rw [hmin, hmax, hqHat_M]
          dsimp [qHat]
          rw [if_neg (not_lt.mpr hmx), if_pos hMx]
        · have hmin : min M x = x := min_eq_right hxM
          have hmax : max m x = x := max_eq_right hmx
          rw [hmin, hmax]
    have hqHat_sumPlus : ∀ x ∈ Set.Icc m M, ∑ t ∈ TplusF, qHat t x = x := by
      intro x hx
      by_cases hxcl : x ∈ clS
      · simp_rw [hqHat_clS _ x hx hxcl]
        exact hg_cl_sumPlus x hxcl
      · have ⟨hxL_cl, _, hxL_le, _⟩ := hxL_props x hx
        have ⟨hxR_cl, hxR_ge, _, _⟩ := hxR_props x hx
        have hxL_lt : xL x < x := lt_of_le_of_ne hxL_le (fun h => hxcl (h ▸ hxL_cl))
        have hxR_gt : x < xR x := lt_of_le_of_ne hxR_ge (fun h => hxcl (h ▸ hxR_cl))
        have hden : xR x - xL x ≠ 0 := by linarith
        have hFormula : ∀ t ∈ TplusF, qHat t x =
            ((xR x - x) / (xR x - xL x)) * g_cl t (xL x) +
            ((x - xL x) / (xR x - xL x)) * g_cl t (xR x) := by
          intro t _
          dsimp [qHat]
          rw [if_neg (not_lt.mpr hx.1), if_neg (not_lt.mpr hx.2), if_neg hxcl]
        calc
          ∑ t ∈ TplusF, qHat t x
              = ∑ t ∈ TplusF, (((xR x - x) / (xR x - xL x)) * g_cl t (xL x) +
                  ((x - xL x) / (xR x - xL x)) * g_cl t (xR x)) :=
                Finset.sum_congr rfl hFormula
          _ = ((xR x - x) / (xR x - xL x)) * (∑ t ∈ TplusF, g_cl t (xL x)) +
              ((x - xL x) / (xR x - xL x)) * (∑ t ∈ TplusF, g_cl t (xR x)) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = ((xR x - x) / (xR x - xL x)) * xL x +
              ((x - xL x) / (xR x - xL x)) * xR x := by
                rw [hg_cl_sumPlus (xL x) hxL_cl, hg_cl_sumPlus (xR x) hxR_cl]
          _ = x := by field_simp [hden]; ring
    have hqHat_sumMinus : ∀ x ∈ Set.Icc m M, ∑ t ∈ TminusF, qHat t x = 1 - x := by
      intro x hx
      by_cases hxcl : x ∈ clS
      · simp_rw [hqHat_clS _ x hx hxcl]
        exact hg_cl_sumMinus x hxcl
      · have ⟨hxL_cl, _, hxL_le, _⟩ := hxL_props x hx
        have ⟨hxR_cl, hxR_ge, _, _⟩ := hxR_props x hx
        have hxL_lt : xL x < x := lt_of_le_of_ne hxL_le (fun h => hxcl (h ▸ hxL_cl))
        have hxR_gt : x < xR x := lt_of_le_of_ne hxR_ge (fun h => hxcl (h ▸ hxR_cl))
        have hden : xR x - xL x ≠ 0 := by linarith
        have hFormula : ∀ t ∈ TminusF, qHat t x =
            ((xR x - x) / (xR x - xL x)) * g_cl t (xL x) +
            ((x - xL x) / (xR x - xL x)) * g_cl t (xR x) := by
          intro t _
          dsimp [qHat]
          rw [if_neg (not_lt.mpr hx.1), if_neg (not_lt.mpr hx.2), if_neg hxcl]
        calc
          ∑ t ∈ TminusF, qHat t x
              = ∑ t ∈ TminusF, (((xR x - x) / (xR x - xL x)) * g_cl t (xL x) +
                  ((x - xL x) / (xR x - xL x)) * g_cl t (xR x)) :=
                Finset.sum_congr rfl hFormula
          _ = ((xR x - x) / (xR x - xL x)) * (∑ t ∈ TminusF, g_cl t (xL x)) +
              ((x - xL x) / (xR x - xL x)) * (∑ t ∈ TminusF, g_cl t (xR x)) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = ((xR x - x) / (xR x - xL x)) * (1 - xL x) +
              ((x - xL x) / (xR x - xL x)) * (1 - xR x) := by
                rw [hg_cl_sumMinus (xL x) hxL_cl, hg_cl_sumMinus (xR x) hxR_cl]
          _ = 1 - x := by field_simp [hden]; ring

    
    have hqHat_monoPlus : ∀ t ∈ TplusF, Monotone (qHat t) := by
      intro t ht
      have hMonoIcc : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc m M → y ∈ Set.Icc m M → x ≤ y →
          qHat t x ≤ qHat t y := by
        have hBracket : ∀ z ∈ Set.Icc m M,
            g_cl t (xL z) ≤ qHat t z ∧ qHat t z ≤ g_cl t (xR z) := by
          intro z hz
          have ⟨hzL_cl, _, hzL_le, hzL_max⟩ := hxL_props z hz
          have ⟨hzR_cl, hzR_ge, _, hzR_min⟩ := hxR_props z hz
          by_cases hzcl : z ∈ clS
          · have hLz : xL z = z := le_antisymm hzL_le (hzL_max z hzcl le_rfl)
            have hRz : xR z = z := le_antisymm (hzR_min z hzcl le_rfl) hzR_ge
            rw [hqHat_clS t z hz hzcl, hLz, hRz]
            exact ⟨le_rfl, le_rfl⟩
          · have hzL_lt : xL z < z := lt_of_le_of_ne hzL_le (fun h => hzcl (h ▸ hzL_cl))
            have hzR_gt : z < xR z := lt_of_le_of_ne hzR_ge (fun h => hzcl (h ▸ hzR_cl))
            have hdenPos : 0 < xR z - xL z := by linarith
            have hgLR : g_cl t (xL z) ≤ g_cl t (xR z) :=
              hg_cl_monoPlus t ht (xL z) hzL_cl (xR z) hzR_cl (le_trans hzL_le hzR_ge)
            let α : ℝ := (xR z - z) / (xR z - xL z)
            let β : ℝ := (z - xL z) / (xR z - xL z)
            have hα0 : 0 ≤ α := div_nonneg (by linarith) (le_of_lt hdenPos)
            have hβ0 : 0 ≤ β := div_nonneg (by linarith) (le_of_lt hdenPos)
            have hαβ : α + β = 1 := by dsimp [α, β]; field_simp [ne_of_gt hdenPos]; ring
            have hqVal : qHat t z = α * g_cl t (xL z) + β * g_cl t (xR z) := by
              dsimp [qHat, α, β]
              rw [if_neg (not_lt.mpr hz.1), if_neg (not_lt.mpr hz.2), if_neg hzcl]
            rw [hqVal]
            constructor
            · have hmul : 0 ≤ β * (g_cl t (xR z) - g_cl t (xL z)) :=
                mul_nonneg hβ0 (sub_nonneg.mpr hgLR)
              have hid : α * g_cl t (xL z) + β * g_cl t (xR z) - g_cl t (xL z) =
                  β * (g_cl t (xR z) - g_cl t (xL z)) := by
                calc
                  α * g_cl t (xL z) + β * g_cl t (xR z) - g_cl t (xL z) =
                      α * g_cl t (xL z) + β * g_cl t (xR z) - (α + β) * g_cl t (xL z) := by
                    rw [hαβ, one_mul]
                  _ = β * (g_cl t (xR z) - g_cl t (xL z)) := by ring
              linarith
            · have hmul : 0 ≤ α * (g_cl t (xR z) - g_cl t (xL z)) :=
                mul_nonneg hα0 (sub_nonneg.mpr hgLR)
              have hid : g_cl t (xR z) - (α * g_cl t (xL z) + β * g_cl t (xR z)) =
                  α * (g_cl t (xR z) - g_cl t (xL z)) := by
                calc
                  g_cl t (xR z) - (α * g_cl t (xL z) + β * g_cl t (xR z)) =
                      (α + β) * g_cl t (xR z) - (α * g_cl t (xL z) + β * g_cl t (xR z)) := by
                    rw [hαβ, one_mul]
                  _ = α * (g_cl t (xR z) - g_cl t (xL z)) := by ring
              linarith
        intro x y hx hy hxy
        by_cases hMid : ∃ w ∈ clS, x ≤ w ∧ w ≤ y
        · rcases hMid with ⟨w, hw_cl, hxw, hwy⟩
          have hxR_w : xR x ≤ w := (hxR_props x hx).2.2.2 w hw_cl hxw
          have hw_yL : w ≤ xL y := (hxL_props y hy).2.2.2 w hw_cl hwy
          have hgRx_Ly : g_cl t (xR x) ≤ g_cl t (xL y) :=
            hg_cl_monoPlus t ht (xR x) (hxR_props x hx).1 (xL y) (hxL_props y hy).1
              (le_trans hxR_w hw_yL)
          exact le_trans (hBracket x hx).2 (le_trans hgRx_Ly (hBracket y hy).1)
        · have hx_ncl : x ∉ clS := fun hc => hMid ⟨x, hc, le_rfl, hxy⟩
          have hy_ncl : y ∉ clS := fun hc => hMid ⟨y, hc, hxy, le_rfl⟩
          have hxL_eq : xL y = xL x := by
            dsimp [xL]
            congr 1
            ext w
            simp only [Set.mem_inter_iff, Set.mem_Iic]
            constructor
            · rintro ⟨hw_cl, hwy⟩
              refine ⟨hw_cl, ?_⟩
              by_contra hwx; push_neg at hwx
              exact hMid ⟨w, hw_cl, le_of_lt hwx, hwy⟩
            · rintro ⟨hw_cl, hwx⟩
              exact ⟨hw_cl, le_trans hwx hxy⟩
          have hxR_eq : xR y = xR x := by
            dsimp [xR]
            congr 1
            ext w
            simp only [Set.mem_inter_iff, Set.mem_Ici]
            constructor
            · rintro ⟨hw_cl, hyw⟩
              exact ⟨hw_cl, le_trans hxy hyw⟩
            · rintro ⟨hw_cl, hxw⟩
              refine ⟨hw_cl, ?_⟩
              by_contra hyw; push_neg at hyw
              exact hMid ⟨w, hw_cl, hxw, le_of_lt hyw⟩
          have ⟨hxL_cl, _, hxL_le, _⟩ := hxL_props x hx
          have ⟨hxR_cl, hxR_ge, _, _⟩ := hxR_props x hx
          have hxL_lt : xL x < x := lt_of_le_of_ne hxL_le (fun h => hx_ncl (h ▸ hxL_cl))
          have hxR_gt : x < xR x := lt_of_le_of_ne hxR_ge (fun h => hx_ncl (h ▸ hxR_cl))
          have hdenPos : 0 < xR x - xL x := by linarith
          have hgLR : g_cl t (xL x) ≤ g_cl t (xR x) :=
            hg_cl_monoPlus t ht (xL x) hxL_cl (xR x) hxR_cl (le_trans hxL_le hxR_ge)
          have hqx : qHat t x =
              ((xR x - x) / (xR x - xL x)) * g_cl t (xL x) +
              ((x - xL x) / (xR x - xL x)) * g_cl t (xR x) := by
            dsimp [qHat]; rw [if_neg (not_lt.mpr hx.1), if_neg (not_lt.mpr hx.2), if_neg hx_ncl]
          have hqy : qHat t y =
              ((xR x - y) / (xR x - xL x)) * g_cl t (xL x) +
              ((y - xL x) / (xR x - xL x)) * g_cl t (xR x) := by
            dsimp [qHat]
            rw [if_neg (not_lt.mpr hy.1), if_neg (not_lt.mpr hy.2), if_neg hy_ncl,
              hxL_eq, hxR_eq]
          have hDiff : qHat t y - qHat t x =
              ((y - x) / (xR x - xL x)) * (g_cl t (xR x) - g_cl t (xL x)) := by
            rw [hqx, hqy]; field_simp [ne_of_gt hdenPos]; ring
          have hNonneg : 0 ≤ qHat t y - qHat t x := by
            rw [hDiff]
            exact mul_nonneg (div_nonneg (by linarith) (le_of_lt hdenPos)) (by linarith)
          linarith
      intro x y hxy
      rw [hqHat_clamp t x, hqHat_clamp t y]
      have hcIcc : ∀ z : ℝ, max m (min M z) ∈ Set.Icc m M := fun z =>
        ⟨le_max_left m _, max_le hm_le_M (min_le_left M z)⟩
      exact hMonoIcc (hcIcc x) (hcIcc y) (max_le_max le_rfl (min_le_min le_rfl hxy))

    have hqHat_antiMinus : ∀ t ∈ TminusF, Antitone (qHat t) := by
      intro t ht
      have hAntiIcc : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc m M → y ∈ Set.Icc m M → x ≤ y →
          qHat t y ≤ qHat t x := by
        have hBracket : ∀ z ∈ Set.Icc m M,
            g_cl t (xR z) ≤ qHat t z ∧ qHat t z ≤ g_cl t (xL z) := by
          intro z hz
          have ⟨hzL_cl, _, hzL_le, hzL_max⟩ := hxL_props z hz
          have ⟨hzR_cl, hzR_ge, _, hzR_min⟩ := hxR_props z hz
          by_cases hzcl : z ∈ clS
          · have hLz : xL z = z := le_antisymm hzL_le (hzL_max z hzcl le_rfl)
            have hRz : xR z = z := le_antisymm (hzR_min z hzcl le_rfl) hzR_ge
            rw [hqHat_clS t z hz hzcl, hLz, hRz]
            exact ⟨le_rfl, le_rfl⟩
          · have hzL_lt : xL z < z := lt_of_le_of_ne hzL_le (fun h => hzcl (h ▸ hzL_cl))
            have hzR_gt : z < xR z := lt_of_le_of_ne hzR_ge (fun h => hzcl (h ▸ hzR_cl))
            have hdenPos : 0 < xR z - xL z := by linarith
            have hgRL : g_cl t (xR z) ≤ g_cl t (xL z) :=
              hg_cl_antiMinus t ht (xL z) hzL_cl (xR z) hzR_cl (le_trans hzL_le hzR_ge)
            let α : ℝ := (xR z - z) / (xR z - xL z)
            let β : ℝ := (z - xL z) / (xR z - xL z)
            have hα0 : 0 ≤ α := div_nonneg (by linarith) (le_of_lt hdenPos)
            have hβ0 : 0 ≤ β := div_nonneg (by linarith) (le_of_lt hdenPos)
            have hαβ : α + β = 1 := by dsimp [α, β]; field_simp [ne_of_gt hdenPos]; ring
            have hqVal : qHat t z = α * g_cl t (xL z) + β * g_cl t (xR z) := by
              dsimp [qHat, α, β]
              rw [if_neg (not_lt.mpr hz.1), if_neg (not_lt.mpr hz.2), if_neg hzcl]
            rw [hqVal]
            constructor
            · have hmul : 0 ≤ α * (g_cl t (xL z) - g_cl t (xR z)) :=
                mul_nonneg hα0 (sub_nonneg.mpr hgRL)
              have hid : α * g_cl t (xL z) + β * g_cl t (xR z) - g_cl t (xR z) =
                  α * (g_cl t (xL z) - g_cl t (xR z)) := by
                calc
                  α * g_cl t (xL z) + β * g_cl t (xR z) - g_cl t (xR z) =
                      α * g_cl t (xL z) + β * g_cl t (xR z) - (α + β) * g_cl t (xR z) := by
                    rw [hαβ, one_mul]
                  _ = α * (g_cl t (xL z) - g_cl t (xR z)) := by ring
              linarith
            · have hmul : 0 ≤ β * (g_cl t (xL z) - g_cl t (xR z)) :=
                mul_nonneg hβ0 (sub_nonneg.mpr hgRL)
              have hid : g_cl t (xL z) - (α * g_cl t (xL z) + β * g_cl t (xR z)) =
                  β * (g_cl t (xL z) - g_cl t (xR z)) := by
                calc
                  g_cl t (xL z) - (α * g_cl t (xL z) + β * g_cl t (xR z)) =
                      (α + β) * g_cl t (xL z) - (α * g_cl t (xL z) + β * g_cl t (xR z)) := by
                    rw [hαβ, one_mul]
                  _ = β * (g_cl t (xL z) - g_cl t (xR z)) := by ring
              linarith
        intro x y hx hy hxy
        by_cases hMid : ∃ w ∈ clS, x ≤ w ∧ w ≤ y
        · rcases hMid with ⟨w, hw_cl, hxw, hwy⟩
          have hxR_w : xR x ≤ w := (hxR_props x hx).2.2.2 w hw_cl hxw
          have hw_yL : w ≤ xL y := (hxL_props y hy).2.2.2 w hw_cl hwy
          have hgLy_Rx : g_cl t (xL y) ≤ g_cl t (xR x) :=
            hg_cl_antiMinus t ht (xR x) (hxR_props x hx).1 (xL y) (hxL_props y hy).1
              (le_trans hxR_w hw_yL)
          exact le_trans (hBracket y hy).2 (le_trans hgLy_Rx (hBracket x hx).1)
        · have hx_ncl : x ∉ clS := fun hc => hMid ⟨x, hc, le_rfl, hxy⟩
          have hy_ncl : y ∉ clS := fun hc => hMid ⟨y, hc, hxy, le_rfl⟩
          have hxL_eq : xL y = xL x := by
            dsimp [xL]; congr 1; ext w
            simp only [Set.mem_inter_iff, Set.mem_Iic]
            constructor
            · rintro ⟨hw_cl, hwy⟩
              refine ⟨hw_cl, ?_⟩
              by_contra hwx; push_neg at hwx
              exact hMid ⟨w, hw_cl, le_of_lt hwx, hwy⟩
            · rintro ⟨hw_cl, hwx⟩; exact ⟨hw_cl, le_trans hwx hxy⟩
          have hxR_eq : xR y = xR x := by
            dsimp [xR]; congr 1; ext w
            simp only [Set.mem_inter_iff, Set.mem_Ici]
            constructor
            · rintro ⟨hw_cl, hyw⟩; exact ⟨hw_cl, le_trans hxy hyw⟩
            · rintro ⟨hw_cl, hxw⟩
              refine ⟨hw_cl, ?_⟩
              by_contra hyw; push_neg at hyw
              exact hMid ⟨w, hw_cl, hxw, le_of_lt hyw⟩
          have ⟨hxL_cl, _, hxL_le, _⟩ := hxL_props x hx
          have ⟨hxR_cl, hxR_ge, _, _⟩ := hxR_props x hx
          have hxL_lt : xL x < x := lt_of_le_of_ne hxL_le (fun h => hx_ncl (h ▸ hxL_cl))
          have hxR_gt : x < xR x := lt_of_le_of_ne hxR_ge (fun h => hx_ncl (h ▸ hxR_cl))
          have hdenPos : 0 < xR x - xL x := by linarith
          have hgRL : g_cl t (xR x) ≤ g_cl t (xL x) :=
            hg_cl_antiMinus t ht (xL x) hxL_cl (xR x) hxR_cl (le_trans hxL_le hxR_ge)
          have hqx : qHat t x =
              ((xR x - x) / (xR x - xL x)) * g_cl t (xL x) +
              ((x - xL x) / (xR x - xL x)) * g_cl t (xR x) := by
            dsimp [qHat]; rw [if_neg (not_lt.mpr hx.1), if_neg (not_lt.mpr hx.2), if_neg hx_ncl]
          have hqy : qHat t y =
              ((xR x - y) / (xR x - xL x)) * g_cl t (xL x) +
              ((y - xL x) / (xR x - xL x)) * g_cl t (xR x) := by
            dsimp [qHat]
            rw [if_neg (not_lt.mpr hy.1), if_neg (not_lt.mpr hy.2), if_neg hy_ncl,
              hxL_eq, hxR_eq]
          have hDiff : qHat t x - qHat t y =
              ((y - x) / (xR x - xL x)) * (g_cl t (xL x) - g_cl t (xR x)) := by
            rw [hqx, hqy]; field_simp [ne_of_gt hdenPos]; ring
          have hNonneg : 0 ≤ qHat t x - qHat t y := by
            rw [hDiff]
            exact mul_nonneg (div_nonneg (by linarith) (le_of_lt hdenPos)) (by linarith)
          linarith
      intro x y hxy
      rw [hqHat_clamp t x, hqHat_clamp t y]
      have hcIcc : ∀ z : ℝ, max m (min M z) ∈ Set.Icc m M := fun z =>
        ⟨le_max_left m _, max_le hm_le_M (min_le_left M z)⟩
      exact hAntiIcc (hcIcc x) (hcIcc y) (max_le_max le_rfl (min_le_min le_rfl hxy))

    
    have hDerivPlusNonneg : ∀ t ∈ TplusF, ∀ x : ℝ, 0 ≤ deriv (qHat t) x :=
      fun t ht _ => (hqHat_monoPlus t ht).deriv_nonneg
    have hMonoNegMinus : ∀ t ∈ TminusF, Monotone (- qHat t) :=
      fun t ht _ _ hxy => neg_le_neg (hqHat_antiMinus t ht hxy)
    have hDerivMinusNonneg : ∀ t ∈ TminusF, ∀ x : ℝ, 0 ≤ - deriv (qHat t) x := by
      intro t ht x
      have h := (hMonoNegMinus t ht).deriv_nonneg (x := x)
      rwa [deriv.neg] at h

    let G : Set ℝ := {rA : ℝ | rA ∈ Set.Ioo m M ∧
      (∑ t ∈ TplusF, deriv (qHat t) rA = 1) ∧
      (∑ t ∈ TminusF, (- deriv (qHat t) rA) = 1)}
    have hMeasG : MeasurableSet G := by
      have hm1 : Measurable (fun rA : ℝ => ∑ t ∈ TplusF, deriv (qHat t) rA) :=
        Finset.measurable_sum TplusF (fun t _ => measurable_deriv (qHat t))
      have hm2 : Measurable (fun rA : ℝ => ∑ t ∈ TminusF, (- deriv (qHat t) rA)) :=
        Finset.measurable_sum TminusF (fun t _ => (measurable_deriv (qHat t)).neg)
      have hSetEq : G = Set.Ioo m M ∩
          {rA : ℝ | ∑ t ∈ TplusF, deriv (qHat t) rA = 1} ∩
          {rA : ℝ | ∑ t ∈ TminusF, (- deriv (qHat t) rA) = 1} := by
        ext rA
        simp only [G, Set.mem_setOf_eq, Set.mem_inter_iff]
        tauto
      rw [hSetEq]
      exact (measurableSet_Ioo.inter (measurableSet_eq_fun hm1 measurable_const)).inter
        (measurableSet_eq_fun hm2 measurable_const)

    have hG_aeImp : ∀ᵐ rA : ℝ ∂volume, rA ∈ Set.Ioo m M → rA ∈ G := by
      have hAeAll : ∀ᵐ rA : ℝ ∂volume, ∀ t : T, DifferentiableAt ℝ (qHat t) rA := by
        rw [ae_all_iff]
        intro t
        by_cases ht : t ∈ TplusF
        · exact (hqHat_monoPlus t ht).ae_differentiableAt
        · have ht' : t ∈ TminusF := by
            simp only [TplusF, TminusF, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
            exact ht
          filter_upwards [(hMonoNegMinus t ht').ae_differentiableAt] with rA hdiff
          have := hdiff.neg
          simpa using this
      filter_upwards [hAeAll] with rA hDiff hrA_Ioo
      refine ⟨hrA_Ioo, ?_, ?_⟩
      · have hNhds : Set.Icc m M ∈ nhds rA :=
          Filter.mem_of_superset (isOpen_Ioo.mem_nhds hrA_Ioo) Set.Ioo_subset_Icc_self
        have hEv : (fun x => ∑ t ∈ TplusF, qHat t x) =ᶠ[nhds rA] id := by
          filter_upwards [hNhds] with x hx
          exact hqHat_sumPlus x hx
        have hEqFn : (∑ t ∈ TplusF, fun x => qHat t x) = (fun x => ∑ t ∈ TplusF, qHat t x) := by
          ext x; simp
        have hSumDeriv : HasDerivAt (fun x => ∑ t ∈ TplusF, qHat t x)
            (∑ t ∈ TplusF, deriv (qHat t) rA) rA := by
          rw [← hEqFn]
          exact HasDerivAt.sum (fun t _ => (hDiff t).hasDerivAt)
        have hIdDeriv : HasDerivAt (fun x => ∑ t ∈ TplusF, qHat t x) 1 rA :=
          (hasDerivAt_id rA).congr_of_eventuallyEq hEv
        exact hSumDeriv.unique hIdDeriv
      · have hNhds : Set.Icc m M ∈ nhds rA :=
          Filter.mem_of_superset (isOpen_Ioo.mem_nhds hrA_Ioo) Set.Ioo_subset_Icc_self
        have hEv : (fun x => ∑ t ∈ TminusF, (- qHat t x)) =ᶠ[nhds rA] (fun x => x - 1) := by
          filter_upwards [hNhds] with x hx
          simp only [Finset.sum_neg_distrib, hqHat_sumMinus x hx]
          ring
        have hEqFn : (∑ t ∈ TminusF, fun x => - qHat t x) = (fun x => ∑ t ∈ TminusF, (- qHat t x)) := by
          ext x; simp
        have hSumDeriv : HasDerivAt (fun x => ∑ t ∈ TminusF, (- qHat t x))
            (∑ t ∈ TminusF, (- deriv (qHat t) rA)) rA := by
          rw [← hEqFn]
          exact HasDerivAt.sum (fun t _ => (hDiff t).hasDerivAt.neg)
        have hLinDeriv : HasDerivAt (fun x : ℝ => x - 1) 1 rA := by
          simpa using (hasDerivAt_id rA).sub_const (1 : ℝ)
        exact hSumDeriv.unique (hLinDeriv.congr_of_eventuallyEq hEv)

    have hG_ae : volume (Set.Ioo m M \ G) = 0 := by
      have hSubNull : Set.Ioo m M \ G ⊆ {rA : ℝ | ¬ (rA ∈ Set.Ioo m M → rA ∈ G)} :=
        fun rA hr hImp => hr.2 (hImp hr.1)
      exact measure_mono_null hSubNull (ae_iff.mp hG_aeImp)

    
    have hFTC_plus : ∀ (a b : ℝ), m ≤ a → a ≤ b → b ≤ M →
        ∀ t ∈ TplusF, ∫ x in a..b, deriv (qHat t) x = qHat t b - qHat t a := by
      intro a b hma hab hbM t ht
      rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      · have hIntAll : ∀ s ∈ TplusF, IntervalIntegrable (deriv (qHat s)) volume a b :=
          fun s hs => ((hqHat_monoPlus s hs).monotoneOn _).intervalIntegrable_deriv
        have hLeAll : ∀ s ∈ TplusF, ∫ x in a..b, deriv (qHat s) x ≤ qHat s b - qHat s a := by
          intro s hs
          have hmem := ((hqHat_monoPlus s hs).monotoneOn (Set.uIcc a b)).intervalIntegral_deriv_mem_uIcc
          rw [Set.uIcc_of_le (sub_nonneg.mpr (hqHat_monoPlus s hs hab))] at hmem
          exact hmem.2
        have hSumInt : ∑ s ∈ TplusF, (∫ x in a..b, deriv (qHat s) x) =
            ∑ s ∈ TplusF, (qHat s b - qHat s a) := by
          rw [← intervalIntegral.integral_finset_sum hIntAll,
            intervalIntegral.integral_of_le hab]
          have hAeOne : ∀ᵐ x ∂volume, x ∈ Set.Ioc a b →
              ∑ s ∈ TplusF, deriv (qHat s) x = (1 : ℝ) := by
            have hne_b : ∀ᵐ x : ℝ ∂volume, x ≠ b := by
              rw [ae_iff]
              have hEq : {x : ℝ | ¬ x ≠ b} = {b} := by ext x; simp
              rw [hEq]
              exact Real.volume_singleton
            filter_upwards [hne_b, hG_aeImp] with x hxb hxImp hxIoc
            have hxImM : x ∈ Set.Ioo m M :=
              ⟨lt_of_le_of_lt hma hxIoc.1, lt_of_lt_of_le (lt_of_le_of_ne hxIoc.2 hxb) hbM⟩
            exact (hxImp hxImM).2.1
          rw [setIntegral_congr_ae measurableSet_Ioc hAeOne,
            ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const,
            smul_eq_mul, mul_one, Finset.sum_sub_distrib,
            hqHat_sumPlus b ⟨le_trans hma hab, hbM⟩,
            hqHat_sumPlus a ⟨hma, le_trans hab hbM⟩]
        exact (Finset.sum_eq_sum_iff_of_le hLeAll).mp hSumInt t ht

    have hFTC_minus : ∀ (a b : ℝ), m ≤ a → a ≤ b → b ≤ M →
        ∀ t ∈ TminusF, ∫ x in a..b, (- deriv (qHat t) x) = qHat t a - qHat t b := by
      intro a b hma hab hbM t ht
      rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      · have hIntAll : ∀ s ∈ TminusF,
            IntervalIntegrable (fun x => - deriv (qHat s) x) volume a b := by
          intro s hs
          have h := ((hMonoNegMinus s hs).monotoneOn (Set.uIcc a b)).intervalIntegrable_deriv
          simpa [deriv.neg] using h
        have hLeAll : ∀ s ∈ TminusF,
            ∫ x in a..b, (- deriv (qHat s) x) ≤ qHat s a - qHat s b := by
          intro s hs
          have hmem := ((hMonoNegMinus s hs).monotoneOn (Set.uIcc a b)).intervalIntegral_deriv_mem_uIcc
          have hdiff : (- qHat s) b - (- qHat s) a = qHat s a - qHat s b := by dsimp; ring
          rw [hdiff, Set.uIcc_of_le (sub_nonneg.mpr (hqHat_antiMinus s hs hab))] at hmem
          simpa [deriv.neg] using hmem.2
        have hSumInt : ∑ s ∈ TminusF, (∫ x in a..b, (- deriv (qHat s) x)) =
            ∑ s ∈ TminusF, (qHat s a - qHat s b) := by
          rw [← intervalIntegral.integral_finset_sum hIntAll,
            intervalIntegral.integral_of_le hab]
          have hAeOne : ∀ᵐ x ∂volume, x ∈ Set.Ioc a b →
              ∑ s ∈ TminusF, (- deriv (qHat s) x) = (1 : ℝ) := by
            have hne_b : ∀ᵐ x : ℝ ∂volume, x ≠ b := by
              rw [ae_iff]
              have hEq : {x : ℝ | ¬ x ≠ b} = {b} := by ext x; simp
              rw [hEq]
              exact Real.volume_singleton
            filter_upwards [hne_b, hG_aeImp] with x hxb hxImp hxIoc
            have hxImM : x ∈ Set.Ioo m M :=
              ⟨lt_of_le_of_lt hma hxIoc.1, lt_of_lt_of_le (lt_of_le_of_ne hxIoc.2 hxb) hbM⟩
            exact (hxImp hxImM).2.2
          rw [setIntegral_congr_ae measurableSet_Ioc hAeOne,
            ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const,
            smul_eq_mul, mul_one, Finset.sum_sub_distrib,
            hqHat_sumMinus a ⟨hma, le_trans hab hbM⟩,
            hqHat_sumMinus b ⟨le_trans hma hab, hbM⟩]
          ring
        exact (Finset.sum_eq_sum_iff_of_le hLeAll).mp hSumInt t ht

    
    let I1 : Set ℝ := Set.Ioo 0 m
    let I3 : Set ℝ := Set.Ioo M 1
    let wI1 : T → ℝ := fun s => if s ∈ TplusF then (q 0).prob s / m else 0
    let wPlus : ℝ → T → ℝ := fun rA s => if s ∈ TplusF then deriv (qHat s) rA else 0
    let wMinus : ℝ → T → ℝ := fun rA s => if s ∈ TminusF then - deriv (qHat s) rA else 0
    let wI3 : T → ℝ := fun s => if s ∈ TminusF then qInf s / (1 - M) else 0

    have hwI1_valid : 0 < m → (∀ s : T, 0 ≤ wI1 s) ∧ ∑ s : T, wI1 s = 1 := by
      intro hmPos
      refine ⟨fun s => ?_, ?_⟩
      · dsimp [wI1]
        split_ifs
        · exact div_nonneg ((q 0).nonneg s) (le_of_lt hmPos)
        · exact le_rfl
      · dsimp [wI1]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div]
        exact div_self (ne_of_gt hmPos)
    have hwPlus_valid : ∀ rA ∈ G, (∀ s : T, 0 ≤ wPlus rA s) ∧ ∑ s : T, wPlus rA s = 1 := by
      intro rA hrA
      refine ⟨fun s => ?_, ?_⟩
      · dsimp [wPlus]
        split_ifs with hs
        · exact hDerivPlusNonneg s hs rA
        · exact le_rfl
      · dsimp [wPlus]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact hrA.2.1
    have hwMinus_valid : ∀ rA ∈ G, (∀ s : T, 0 ≤ wMinus rA s) ∧ ∑ s : T, wMinus rA s = 1 := by
      intro rA hrA
      refine ⟨fun s => ?_, ?_⟩
      · dsimp [wMinus]
        split_ifs with hs
        · exact hDerivMinusNonneg s hs rA
        · exact le_rfl
      · dsimp [wMinus]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact hrA.2.2
    have hwI3_valid : M < 1 → (∀ s : T, 0 ≤ wI3 s) ∧ ∑ s : T, wI3 s = 1 := by
      intro hMlt1
      have h1M : 0 < 1 - M := by linarith
      refine ⟨fun s => ?_, ?_⟩
      · dsimp [wI3]
        split_ifs
        · exact div_nonneg (hQInfNonneg s) (le_of_lt h1M)
        · exact le_rfl
      · dsimp [wI3]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          ← Finset.sum_div, hSumQInfMinus]
        exact div_self (ne_of_gt h1M)

    let σ : Bid → (ℝ × ℝ) → T := fun b_i r =>
      if r.2 ∈ Set.Ico (0 : ℝ) 1 then
        if r.1 ∈ I1 then cdfPick wI1 r.2
        else if r.1 ∈ G then
          if r.1 ≤ Qplus b_i then cdfPick (wPlus r.1) r.2
          else cdfPick (wMinus r.1) r.2
        else if r.1 ∈ I3 then cdfPick wI3 r.2
        else tDef
      else tDef

    have hDisj_I1_G : Disjoint I1 G :=
      Set.disjoint_left.mpr (fun _ h1 hG => by linarith [h1.2, hG.1.1])
    have hDisj_I1_I3 : Disjoint I1 I3 :=
      Set.disjoint_left.mpr (fun _ h1 h3 => by linarith [h1.2, hm_lt_M, h3.1])
    have hDisj_G_I3 : Disjoint G I3 :=
      Set.disjoint_left.mpr (fun _ hG h3 => by linarith [hG.1.2, h3.1])

    
    let E : Set (ℝ × ℝ) := ((I1 ∪ G ∪ I3) ×ˢ Set.Ico (0 : ℝ) 1)ᶜ
    have hMeasE : MeasurableSet E :=
      ((measurableSet_Ioo.union hMeasG).union measurableSet_Ioo).prod measurableSet_Ico |>.compl
    have hENull : μ₂ E = 0 := by
      have hμ1_I1 : μ₁ I1 = ENNReal.ofReal m := by
        dsimp [μ₁, I1]
        rw [Measure.restrict_apply measurableSet_Ioo]
        have hSub : Set.Ioo 0 m ∩ Set.Icc (0 : ℝ) 1 = Set.Ioo 0 m := by
          apply Set.inter_eq_left.mpr
          intro x hx; exact ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) (le_trans hm_le_M hM_le_one)⟩
        rw [hSub, Real.volume_Ioo, sub_zero]
      have hμ1_G : μ₁ G = ENNReal.ofReal (M - m) := by
        dsimp [μ₁]
        rw [Measure.restrict_apply hMeasG]
        have hSub : G ∩ Set.Icc (0 : ℝ) 1 = G := by
          apply Set.inter_eq_left.mpr
          intro x hx
          exact ⟨le_trans hm_nonneg (le_of_lt hx.1.1), le_trans (le_of_lt hx.1.2) hM_le_one⟩
        rw [hSub]
        have hUnionG : G ∪ (Set.Ioo m M \ G) = Set.Ioo m M :=
          Set.union_diff_cancel (fun _ hx => hx.1)
        have hVolG : volume G = volume (Set.Ioo m M) := by
          rw [← hUnionG, hμ_union_null volume G (Set.Ioo m M \ G) hG_ae]
        rw [hVolG, Real.volume_Ioo]
      have hμ1_I3 : μ₁ I3 = ENNReal.ofReal (1 - M) := by
        dsimp [μ₁, I3]
        rw [Measure.restrict_apply measurableSet_Ioo]
        have hSub : Set.Ioo M 1 ∩ Set.Icc (0 : ℝ) 1 = Set.Ioo M 1 := by
          apply Set.inter_eq_left.mpr
          intro x hx; exact ⟨le_trans (le_trans hm_nonneg hm_le_M) (le_of_lt hx.1), le_of_lt hx.2⟩
        rw [hSub, Real.volume_Ioo]
      have hμ1_Union : μ₁ (I1 ∪ G ∪ I3) = 1 := by
        rw [measure_union (Disjoint.union_left hDisj_I1_I3 hDisj_G_I3) measurableSet_Ioo,
          measure_union hDisj_I1_G hMeasG, hμ1_I1, hμ1_G, hμ1_I3,
          ← ENNReal.ofReal_add hm_nonneg (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf
        exact ENNReal.ofReal_one
      have hμ1_Ico : μ₁ (Set.Ico (0 : ℝ) 1) = 1 := by
        dsimp [μ₁]
        rw [Measure.restrict_apply measurableSet_Ico,
          Set.inter_eq_left.mpr Set.Ico_subset_Icc_self, Real.volume_Ico]
        norm_num
      have hProdOne : μ₂ ((I1 ∪ G ∪ I3) ×ˢ Set.Ico (0 : ℝ) 1) = 1 := by
        dsimp [μ₂]
        rw [Measure.prod_prod, hμ1_Union, hμ1_Ico, mul_one]
      dsimp [E]
      rw [measure_compl (hMeasE.of_compl) (measure_ne_top μ₂ _), measure_univ, hProdOne, tsub_self]

    
    let R1 (t : T) : Set (ℝ × ℝ) :=
      {r | r.1 ∈ I1 ∧ r.2 ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick wI1 r.2 = t}
    let R2 (b_i : Bid) (t : T) : Set (ℝ × ℝ) :=
      {r | r.1 ∈ G ∩ Set.Iic (Qplus b_i) ∧ r.2 ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick (wPlus r.1) r.2 = t}
    let R3 (b_i : Bid) (t : T) : Set (ℝ × ℝ) :=
      {r | r.1 ∈ G ∩ Set.Ioi (Qplus b_i) ∧ r.2 ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick (wMinus r.1) r.2 = t}
    let R4 (t : T) : Set (ℝ × ℝ) :=
      {r | r.1 ∈ I3 ∧ r.2 ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick wI3 r.2 = t}
    let R5 (t : T) : Set (ℝ × ℝ) := if tDef = t then E else ∅

    have hFiberEq : ∀ (b_i : Bid) (t : T),
        {r : ℝ × ℝ | σ b_i r = t} = R1 t ∪ R2 b_i t ∪ R3 b_i t ∪ R4 t ∪ R5 t := by
      intro b_i t
      ext ⟨rA, rB⟩
      dsimp only [σ, Set.mem_setOf_eq, Set.mem_union]
      by_cases hrB : rB ∈ Set.Ico (0 : ℝ) 1
      · rw [if_pos hrB]
        by_cases h1 : rA ∈ I1
        · rw [if_pos h1]
          have hnG : rA ∉ G := Set.disjoint_left.mp hDisj_I1_G h1
          have hn3 : rA ∉ I3 := Set.disjoint_left.mp hDisj_I1_I3 h1
          have hnE : (rA, rB) ∉ E := fun hE => hE ⟨Or.inl (Or.inl h1), hrB⟩
          have hnR5 : (rA, rB) ∉ R5 t := by dsimp [R5]; split_ifs <;> simp [hnE]
          constructor
          · intro hEq; exact Or.inl (Or.inl (Or.inl (Or.inl ⟨h1, hrB, hEq⟩)))
          · rintro ((((hr1 | hr2) | hr3) | hr4) | hr5)
            · exact hr1.2.2
            · exact (hnG hr2.1.1).elim
            · exact (hnG hr3.1.1).elim
            · exact (hn3 hr4.1).elim
            · exact (hnR5 hr5).elim
        · rw [if_neg h1]
          by_cases hG : rA ∈ G
          · rw [if_pos hG]
            have hn3 : rA ∉ I3 := Set.disjoint_left.mp hDisj_G_I3 hG
            have hnE : (rA, rB) ∉ E := fun hE => hE ⟨Or.inl (Or.inr hG), hrB⟩
            have hnR5 : (rA, rB) ∉ R5 t := by dsimp [R5]; split_ifs <;> simp [hnE]
            by_cases hle : rA ≤ Qplus b_i
            · rw [if_pos hle]
              constructor
              · intro hEq; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hG, hle⟩, hrB, hEq⟩)))
              · rintro ((((hr1 | hr2) | hr3) | hr4) | hr5)
                · exact (h1 hr1.1).elim
                · exact hr2.2.2
                · have hgt : Qplus b_i < rA := hr3.1.2
                  linarith
                · exact (hn3 hr4.1).elim
                · exact (hnR5 hr5).elim
            · rw [if_neg hle]
              have hgt : Qplus b_i < rA := not_le.mp hle
              constructor
              · intro hEq; exact Or.inl (Or.inl (Or.inr ⟨⟨hG, hgt⟩, hrB, hEq⟩))
              · rintro ((((hr1 | hr2) | hr3) | hr4) | hr5)
                · exact (h1 hr1.1).elim
                · exact (hle hr2.1.2).elim
                · exact hr3.2.2
                · exact (hn3 hr4.1).elim
                · exact (hnR5 hr5).elim
          · rw [if_neg hG]
            by_cases h3 : rA ∈ I3
            · rw [if_pos h3]
              have hnE : (rA, rB) ∉ E := fun hE => hE ⟨Or.inr h3, hrB⟩
              have hnR5 : (rA, rB) ∉ R5 t := by dsimp [R5]; split_ifs <;> simp [hnE]
              constructor
              · intro hEq; exact Or.inl (Or.inr ⟨h3, hrB, hEq⟩)
              · rintro ((((hr1 | hr2) | hr3) | hr4) | hr5)
                · exact (h1 hr1.1).elim
                · exact (hG hr2.1.1).elim
                · exact (hG hr3.1.1).elim
                · exact hr4.2.2
                · exact (hnR5 hr5).elim
            · rw [if_neg h3]
              have hE : (rA, rB) ∈ E := by
                rintro ⟨(h1' | hG') | h3', _⟩
                · exact h1 h1'
                · exact hG hG'
                · exact h3 h3'
              by_cases ht : tDef = t
              · have hR5 : (rA, rB) ∈ R5 t := by dsimp [R5]; rw [if_pos ht]; exact hE
                exact ⟨fun _ => Or.inr hR5, fun _ => ht⟩
              · have hnR5 : (rA, rB) ∉ R5 t := by dsimp [R5]; rw [if_neg ht]; exact False.elim
                constructor
                · intro hEq; exact (ht hEq).elim
                · rintro ((((hr1 | hr2) | hr3) | hr4) | hr5)
                  · exact (h1 hr1.1).elim
                  · exact (hG hr2.1.1).elim
                  · exact (hG hr3.1.1).elim
                  · exact (h3 hr4.1).elim
                  · exact (hnR5 hr5).elim
      · rw [if_neg hrB]
        have hE : (rA, rB) ∈ E := fun h => hrB h.2
        by_cases ht : tDef = t
        · have hR5 : (rA, rB) ∈ R5 t := by dsimp [R5]; rw [if_pos ht]; exact hE
          exact ⟨fun _ => Or.inr hR5, fun _ => ht⟩
        · have hnR5 : (rA, rB) ∉ R5 t := by dsimp [R5]; rw [if_neg ht]; exact False.elim
          constructor
          · intro hEq; exact (ht hEq).elim
          · rintro ((((hr1 | hr2) | hr3) | hr4) | hr5)
            · exact (hrB hr1.2.1).elim
            · exact (hrB hr2.2.1).elim
            · exact (hrB hr3.2.1).elim
            · exact (hrB hr4.2.1).elim
            · exact (hnR5 hr5).elim

    have hMeasR1 : ∀ t : T, MeasurableSet (R1 t) := by
      intro t
      exact h_cdf_meas2D I1 (fun _ => wI1) t measurableSet_Ioo (fun _ => measurable_const)
        (fun rA hrA => hwI1_valid (lt_trans hrA.1 hrA.2))
    have hMeasR2 : ∀ (b_i : Bid) (t : T), MeasurableSet (R2 b_i t) := by
      intro b_i t
      refine h_cdf_meas2D (G ∩ Set.Iic (Qplus b_i)) wPlus t (hMeasG.inter measurableSet_Iic)
        (fun s => ?_) (fun rA hrA => hwPlus_valid rA hrA.1)
      dsimp [wPlus]
      split_ifs
      · exact measurable_deriv (qHat s)
      · exact measurable_const
    have hMeasR3 : ∀ (b_i : Bid) (t : T), MeasurableSet (R3 b_i t) := by
      intro b_i t
      refine h_cdf_meas2D (G ∩ Set.Ioi (Qplus b_i)) wMinus t (hMeasG.inter measurableSet_Ioi)
        (fun s => ?_) (fun rA hrA => hwMinus_valid rA hrA.1)
      dsimp [wMinus]
      split_ifs
      · exact (measurable_deriv (qHat s)).neg
      · exact measurable_const
    have hMeasR4 : ∀ t : T, MeasurableSet (R4 t) := by
      intro t
      exact h_cdf_meas2D I3 (fun _ => wI3) t measurableSet_Ioo (fun _ => measurable_const)
        (fun rA hrA => hwI3_valid (lt_trans hrA.1 hrA.2))
    have hMeasR5 : ∀ t : T, MeasurableSet (R5 t) := by
      intro t
      dsimp [R5]
      split_ifs
      · exact hMeasE
      · exact MeasurableSet.empty

    refine ⟨μ₂, hProbμ₂, σ, rfl, ⟨?_, ?_⟩, ?_⟩
    · 
      intro b_i t
      rw [hFiberEq b_i t]
      exact ((((hMeasR1 t).union (hMeasR2 b_i t)).union (hMeasR3 b_i t)).union
        (hMeasR4 t)).union (hMeasR5 t)
    · 
      intro b_i t
      have hR5Null : μ₂ (R5 t) = 0 := by
        dsimp [R5]
        split_ifs
        · exact hENull
        · exact measure_empty
      have hDisj12 : Disjoint (R1 t) (R2 b_i t) :=
        Set.disjoint_left.mpr (fun _ h1 h2 => Set.disjoint_left.mp hDisj_I1_G h1.1 h2.1.1)
      have hDisj12_3 : Disjoint (R1 t ∪ R2 b_i t) (R3 b_i t) := by
        refine Set.disjoint_left.mpr (fun r hr12 hr3 => ?_)
        rcases hr12 with hr1 | hr2
        · exact Set.disjoint_left.mp hDisj_I1_G hr1.1 hr3.1.1
        · have hle : r.1 ≤ Qplus b_i := hr2.1.2
          have hgt : Qplus b_i < r.1 := hr3.1.2
          linarith
      have hDisj123_4 : Disjoint (R1 t ∪ R2 b_i t ∪ R3 b_i t) (R4 t) := by
        refine Set.disjoint_left.mpr (fun r hr123 hr4 => ?_)
        rcases hr123 with (hr1 | hr2) | hr3
        · exact Set.disjoint_left.mp hDisj_I1_I3 hr1.1 hr4.1
        · exact Set.disjoint_left.mp hDisj_G_I3 hr2.1.1 hr4.1
        · exact Set.disjoint_left.mp hDisj_G_I3 hr3.1.1 hr4.1
      have hSumMeas : μ₂ {r : ℝ × ℝ | σ b_i r = t} =
          μ₂ (R1 t) + μ₂ (R2 b_i t) + μ₂ (R3 b_i t) + μ₂ (R4 t) := by
        rw [hFiberEq b_i t, hμ_union_null μ₂ _ (R5 t) hR5Null,
          measure_union hDisj123_4 (hMeasR4 t),
          measure_union hDisj12_3 (hMeasR3 b_i t),
          measure_union hDisj12 (hMeasR2 b_i t)]
      
      have hValR1 : μ₂ (R1 t) = if t ∈ TplusF then ENNReal.ofReal ((q 0).prob t) else 0 := by
        rcases eq_or_lt_of_le hm_nonneg with hm0 | hmPos
        · have hI1Empty : I1 = ∅ := by dsimp [I1]; rw [← hm0]; simp
          have hR1Empty : R1 t = ∅ := by ext r; simp [R1, hI1Empty]
          rw [hR1Empty, measure_empty]
          split_ifs with ht
          · have hSum0 : ∑ s ∈ TplusF, (q 0).prob s = 0 := hm0.symm
            have hq0t : (q 0).prob t = 0 :=
              le_antisymm (by rw [← hSum0]; exact Finset.single_le_sum (fun s _ => (q 0).nonneg s) ht)
                ((q 0).nonneg t)
            simp [hq0t]
          · rfl
        · dsimp [μ₂]
          rw [Measure.prod_apply (hMeasR1 t)]
          have hSlice : ∀ rA : ℝ, μ₁ (Prod.mk rA ⁻¹' R1 t) =
              Set.indicator I1 (fun _ => ENNReal.ofReal (wI1 t)) rA := by
            intro rA
            by_cases hrA : rA ∈ I1
            · rw [Set.indicator_of_mem hrA]
              have hPre : Prod.mk rA ⁻¹' R1 t =
                  {rB : ℝ | rB ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick wI1 rB = t} := by
                ext rB
                dsimp only [R1, Set.mem_preimage, Set.mem_setOf_eq]
                exact ⟨fun h => h.2, fun h => ⟨hrA, h⟩⟩
              rw [hPre]
              exact h_cdf_meas1D wI1 (hwI1_valid hmPos).1 (hwI1_valid hmPos).2 t
            · rw [Set.indicator_of_notMem hrA]
              have hPre : Prod.mk rA ⁻¹' R1 t = ∅ := by
                ext rB
                simp only [R1, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
                exact fun h => hrA h.1
              simp [hPre]
          simp_rw [hSlice]
          rw [lintegral_indicator measurableSet_Ioo, lintegral_const, Measure.restrict_apply_univ]
          have hμ1_I1 : μ₁ I1 = ENNReal.ofReal m := by
            dsimp [μ₁, I1]
            rw [Measure.restrict_apply measurableSet_Ioo]
            have hSub : Set.Ioo 0 m ∩ Set.Icc (0 : ℝ) 1 = Set.Ioo 0 m := by
              apply Set.inter_eq_left.mpr
              intro x hx; exact ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) (le_trans hm_le_M hM_le_one)⟩
            rw [hSub, Real.volume_Ioo, sub_zero]
          rw [hμ1_I1]
          dsimp [wI1]
          split_ifs with ht
          · rw [← ENNReal.ofReal_mul (div_nonneg ((q 0).nonneg t) (le_of_lt hmPos)),
              div_mul_cancel₀ _ (ne_of_gt hmPos)]
          · simp
      
      have hValR4 : μ₂ (R4 t) = if t ∈ TminusF then ENNReal.ofReal (qInf t) else 0 := by
        rcases eq_or_lt_of_le hM_le_one with hM1 | hMlt1
        · have hI3Empty : I3 = ∅ := by dsimp [I3]; rw [hM1]; simp
          have hR4Empty : R4 t = ∅ := by ext r; simp [R4, hI3Empty]
          rw [hR4Empty, measure_empty]
          split_ifs with ht
          · have hSum0 : ∑ s ∈ TminusF, qInf s = 0 := by rw [hSumQInfMinus, hM1, sub_self]
            have hqIt : qInf t = 0 :=
              le_antisymm (by rw [← hSum0]; exact Finset.single_le_sum (fun s _ => hQInfNonneg s) ht)
                (hQInfNonneg t)
            simp [hqIt]
          · rfl
        · dsimp [μ₂]
          rw [Measure.prod_apply (hMeasR4 t)]
          have hSlice : ∀ rA : ℝ, μ₁ (Prod.mk rA ⁻¹' R4 t) =
              Set.indicator I3 (fun _ => ENNReal.ofReal (wI3 t)) rA := by
            intro rA
            by_cases hrA : rA ∈ I3
            · rw [Set.indicator_of_mem hrA]
              have hPre : Prod.mk rA ⁻¹' R4 t =
                  {rB : ℝ | rB ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick wI3 rB = t} := by
                ext rB
                dsimp only [R4, Set.mem_preimage, Set.mem_setOf_eq]
                exact ⟨fun h => h.2, fun h => ⟨hrA, h⟩⟩
              rw [hPre]
              exact h_cdf_meas1D wI3 (hwI3_valid hMlt1).1 (hwI3_valid hMlt1).2 t
            · rw [Set.indicator_of_notMem hrA]
              have hPre : Prod.mk rA ⁻¹' R4 t = ∅ := by
                ext rB
                simp only [R4, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
                exact fun h => hrA h.1
              simp [hPre]
          simp_rw [hSlice]
          rw [lintegral_indicator measurableSet_Ioo, lintegral_const, Measure.restrict_apply_univ]
          have hμ1_I3 : μ₁ I3 = ENNReal.ofReal (1 - M) := by
            dsimp [μ₁, I3]
            rw [Measure.restrict_apply measurableSet_Ioo]
            have hSub : Set.Ioo M 1 ∩ Set.Icc (0 : ℝ) 1 = Set.Ioo M 1 := by
              apply Set.inter_eq_left.mpr
              intro x hx; exact ⟨le_trans (le_trans hm_nonneg hm_le_M) (le_of_lt hx.1), le_of_lt hx.2⟩
            rw [hSub, Real.volume_Ioo]
          rw [hμ1_I3]
          dsimp [wI3]
          split_ifs with ht
          · have h1M : 0 < 1 - M := by linarith
            rw [← ENNReal.ofReal_mul (div_nonneg (hQInfNonneg t) (le_of_lt h1M)),
              div_mul_cancel₀ _ (ne_of_gt h1M)]
          · simp
      
      have hValR2 : μ₂ (R2 b_i t) =
          if t ∈ TplusF then ENNReal.ofReal ((q b_i).prob t - (q 0).prob t) else 0 := by
        let Gle : Set ℝ := G ∩ Set.Iic (Qplus b_i)
        have hMeasGle : MeasurableSet Gle := hMeasG.inter measurableSet_Iic
        dsimp [μ₂]
        rw [Measure.prod_apply (hMeasR2 b_i t)]
        have hSlice : ∀ rA : ℝ, μ₁ (Prod.mk rA ⁻¹' R2 b_i t) =
            Set.indicator Gle (fun x => ENNReal.ofReal (wPlus x t)) rA := by
          intro rA
          by_cases hrA : rA ∈ Gle
          · rw [Set.indicator_of_mem hrA]
            have hPre : Prod.mk rA ⁻¹' R2 b_i t =
                {rB : ℝ | rB ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick (wPlus rA) rB = t} := by
              ext rB
              dsimp only [R2, Set.mem_preimage, Set.mem_setOf_eq]
              exact ⟨fun h => h.2, fun h => ⟨hrA, h⟩⟩
            rw [hPre]
            exact h_cdf_meas1D (wPlus rA) (hwPlus_valid rA hrA.1).1
              (hwPlus_valid rA hrA.1).2 t
          · rw [Set.indicator_of_notMem hrA]
            have hPre : Prod.mk rA ⁻¹' R2 b_i t = ∅ := by
              ext rB
              simp only [R2, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              exact fun h => hrA h.1
            simp [hPre]
        simp_rw [hSlice]
        rw [lintegral_indicator hMeasGle]
        split_ifs with ht
        · have hwEq : (fun x => ENNReal.ofReal (wPlus x t)) =
              (fun x => ENNReal.ofReal (deriv (qHat t) x)) := by
            ext x; simp [wPlus, ht]
          rw [hwEq]
          have hGleSubIcc : Gle ⊆ Set.Icc (0 : ℝ) 1 := by
            rintro x ⟨hxG, _⟩
            exact ⟨le_trans hm_nonneg (le_of_lt hxG.1.1), le_trans (le_of_lt hxG.1.2) hM_le_one⟩
          have hRestr1 : μ₁.restrict Gle = volume.restrict Gle := by
            dsimp [μ₁]
            rw [Measure.restrict_restrict hMeasGle, Set.inter_eq_left.mpr hGleSubIcc]
          have hGleAe : Gle =ᵐ[volume] Set.Ioc m (Qplus b_i) := by
            rw [ae_eq_set]
            constructor
            · have hSub : Gle \ Set.Ioc m (Qplus b_i) = ∅ := by
                ext x
                simp only [Set.mem_diff, Set.mem_empty_iff_false, iff_false]
                rintro ⟨⟨hxG, hxle⟩, hnot⟩
                exact hnot ⟨hxG.1.1, hxle⟩
              simp [hSub]
            · have hSub : Set.Ioc m (Qplus b_i) \ Gle ⊆ {M} ∪ (Set.Ioo m M \ G) := by
                rintro x ⟨⟨hxm, hxle⟩, hnot⟩
                by_cases hxM : x = M
                · exact Or.inl hxM
                · have hltM : x < M := lt_of_le_of_ne (le_trans hxle (hQplus_le_M b_i)) hxM
                  exact Or.inr ⟨⟨hxm, hltM⟩, fun hxG => hnot ⟨hxG, hxle⟩⟩
              exact measure_mono_null hSub (measure_union_null Real.volume_singleton hG_ae)
          rw [hRestr1, Measure.restrict_congr_set hGleAe]
          have hIntIoc : IntegrableOn (deriv (qHat t)) (Set.Ioc m (Qplus b_i)) volume :=
            (((hqHat_monoPlus t ht).monotoneOn (Set.uIcc m (Qplus b_i))).intervalIntegrable_deriv).1
          have hNnAe : 0 ≤ᵐ[volume.restrict (Set.Ioc m (Qplus b_i))] deriv (qHat t) :=
            Filter.Eventually.of_forall (fun x => hDerivPlusNonneg t ht x)
          rw [← ofReal_integral_eq_lintegral_ofReal hIntIoc hNnAe,
            ← intervalIntegral.integral_of_le (hm_le_Qplus b_i),
            hFTC_plus m (Qplus b_i) le_rfl (hm_le_Qplus b_i) (hQplus_le_M b_i) t ht,
            hqHat_eval, hqHat_m]
        · have hwEq : (fun x => ENNReal.ofReal (wPlus x t)) = (fun _ => 0) := by
            ext x; simp [wPlus, ht]
          simp [hwEq]
      
      have hValR3 : μ₂ (R3 b_i t) =
          if t ∈ TminusF then ENNReal.ofReal ((q b_i).prob t - qInf t) else 0 := by
        let Ggt : Set ℝ := G ∩ Set.Ioi (Qplus b_i)
        have hMeasGgt : MeasurableSet Ggt := hMeasG.inter measurableSet_Ioi
        dsimp [μ₂]
        rw [Measure.prod_apply (hMeasR3 b_i t)]
        have hSlice : ∀ rA : ℝ, μ₁ (Prod.mk rA ⁻¹' R3 b_i t) =
            Set.indicator Ggt (fun x => ENNReal.ofReal (wMinus x t)) rA := by
          intro rA
          by_cases hrA : rA ∈ Ggt
          · rw [Set.indicator_of_mem hrA]
            have hPre : Prod.mk rA ⁻¹' R3 b_i t =
                {rB : ℝ | rB ∈ Set.Ico (0 : ℝ) 1 ∧ cdfPick (wMinus rA) rB = t} := by
              ext rB
              dsimp only [R3, Set.mem_preimage, Set.mem_setOf_eq]
              exact ⟨fun h => h.2, fun h => ⟨hrA, h⟩⟩
            rw [hPre]
            exact h_cdf_meas1D (wMinus rA) (hwMinus_valid rA hrA.1).1
              (hwMinus_valid rA hrA.1).2 t
          · rw [Set.indicator_of_notMem hrA]
            have hPre : Prod.mk rA ⁻¹' R3 b_i t = ∅ := by
              ext rB
              simp only [R3, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              exact fun h => hrA h.1
            simp [hPre]
        simp_rw [hSlice]
        rw [lintegral_indicator hMeasGgt]
        split_ifs with ht
        · have hwEq : (fun x => ENNReal.ofReal (wMinus x t)) =
              (fun x => ENNReal.ofReal (- deriv (qHat t) x)) := by
            ext x; simp [wMinus, ht]
          rw [hwEq]
          have hGgtSubIcc : Ggt ⊆ Set.Icc (0 : ℝ) 1 := by
            rintro x ⟨hxG, _⟩
            exact ⟨le_trans hm_nonneg (le_of_lt hxG.1.1), le_trans (le_of_lt hxG.1.2) hM_le_one⟩
          have hRestr1 : μ₁.restrict Ggt = volume.restrict Ggt := by
            dsimp [μ₁]
            rw [Measure.restrict_restrict hMeasGgt, Set.inter_eq_left.mpr hGgtSubIcc]
          have hGgtAe : Ggt =ᵐ[volume] Set.Ioc (Qplus b_i) M := by
            rw [ae_eq_set]
            constructor
            · have hSub : Ggt \ Set.Ioc (Qplus b_i) M = ∅ := by
                ext x
                simp only [Set.mem_diff, Set.mem_empty_iff_false, iff_false]
                rintro ⟨⟨hxG, hxgt⟩, hnot⟩
                exact hnot ⟨hxgt, le_of_lt hxG.1.2⟩
              simp [hSub]
            · have hSub : Set.Ioc (Qplus b_i) M \ Ggt ⊆ {M} ∪ (Set.Ioo m M \ G) := by
                rintro x ⟨⟨hxgt, hxle⟩, hnot⟩
                by_cases hxM : x = M
                · exact Or.inl hxM
                · have hltM : x < M := lt_of_le_of_ne hxle hxM
                  have hgt_m : m < x := lt_of_le_of_lt (hm_le_Qplus b_i) hxgt
                  exact Or.inr ⟨⟨hgt_m, hltM⟩, fun hxG => hnot ⟨hxG, hxgt⟩⟩
              exact measure_mono_null hSub (measure_union_null Real.volume_singleton hG_ae)
          rw [hRestr1, Measure.restrict_congr_set hGgtAe]
          have hIntIoc : IntegrableOn (fun x => - deriv (qHat t) x)
              (Set.Ioc (Qplus b_i) M) volume := by
            have h := (((hMonoNegMinus t ht).monotoneOn (Set.uIcc (Qplus b_i) M)).intervalIntegrable_deriv).1
            simpa [deriv.neg] using h
          have hNnAe : 0 ≤ᵐ[volume.restrict (Set.Ioc (Qplus b_i) M)]
              (fun x => - deriv (qHat t) x) :=
            Filter.Eventually.of_forall (fun x => hDerivMinusNonneg t ht x)
          rw [← ofReal_integral_eq_lintegral_ofReal hIntIoc hNnAe,
            ← intervalIntegral.integral_of_le (hQplus_le_M b_i),
            hFTC_minus (Qplus b_i) M (hm_le_Qplus b_i) (hQplus_le_M b_i) le_rfl t ht,
            hqHat_eval, hqHat_M]
        · have hwEq : (fun x => ENNReal.ofReal (wMinus x t)) = (fun _ => 0) := by
            ext x; simp [wMinus, ht]
          simp [hwEq]

      
      rw [measureReal_def, hSumMeas, hValR1, hValR2, hValR3, hValR4]
      by_cases ht : t ∈ TplusF
      · have hnot : t ∉ TminusF := by
          simp only [TplusF, TminusF, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          exact not_not.mpr ht
        rw [if_pos ht, if_pos ht, if_neg hnot, if_neg hnot, add_zero, add_zero]
        have hdiffNn : 0 ≤ (q b_i).prob t - (q 0).prob t :=
          sub_nonneg.mpr (hMonoPlus t ht (zero_le b_i))
        rw [← ENNReal.ofReal_add ((q 0).nonneg t) hdiffNn]
        ring_nf
        exact ENNReal.toReal_ofReal ((q b_i).nonneg t)
      · have ht' : t ∈ TminusF := by
          simp only [TplusF, TminusF, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          exact ht
        rw [if_neg ht, if_neg ht, if_pos ht', if_pos ht', zero_add, zero_add]
        have hdiffNn : 0 ≤ (q b_i).prob t - qInf t :=
          sub_nonneg.mpr (hQInfLeMinus t ht' b_i)
        rw [← ENNReal.ofReal_add hdiffNn (hQInfNonneg t)]
        ring_nf
        exact ENNReal.toReal_ofReal ((q b_i).nonneg t)
    · 
      intro ⟨rA, rB⟩
      by_cases hrB : rB ∈ Set.Ico (0 : ℝ) 1
      · by_cases h1 : rA ∈ I1
        · left
          refine ⟨cdfPick wI1 rB, fun b_i => ?_⟩
          dsimp only [σ]
          rw [if_pos hrB, if_pos h1]
        · by_cases hG : rA ∈ G
          · right
            let u_r := cdfPick (wPlus rA) rB
            let o_r := cdfPick (wMinus rA) rB
            let W_r : Set Bid := {b : Bid | rA ≤ Qplus b}
            have hu_mem : u_r ∈ undersampledTokens q target := by
              have hpos := h_cdf_pos (wPlus rA) (hwPlus_valid rA hG).1
                (hwPlus_valid rA hG).2 rB hrB
              change 0 < wPlus rA u_r at hpos
              dsimp [wPlus] at hpos
              by_cases huF : u_r ∈ TplusF
              · simp only [TplusF, Finset.mem_filter, Finset.mem_univ, true_and] at huF
                exact huF
              · rw [if_neg huF] at hpos; linarith
            have ho_mem : o_r ∈ oversampledTokens q target := by
              have hpos := h_cdf_pos (wMinus rA) (hwMinus_valid rA hG).1
                (hwMinus_valid rA hG).2 rB hrB
              change 0 < wMinus rA o_r at hpos
              dsimp [wMinus] at hpos
              by_cases hoF : o_r ∈ TminusF
              · simp only [TminusF, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hoF
                exact hoF
              · rw [if_neg hoF] at hpos; linarith
            have hUpper : IsUpperSet W_r := fun a b hab ha => le_trans ha (hQplusMono hab)
            have hNe : W_r.Nonempty := by
              have hrA_lt_M : rA < M := hG.1.2
              rcases (lt_csSup_iff hBddQplus ⟨Qplus 0, ⟨0, rfl⟩⟩).mp hrA_lt_M with ⟨_, ⟨b, rfl⟩, hb⟩
              exact ⟨b, le_of_lt hb⟩
            have hNotUniv : W_r ≠ Set.univ := by
              intro hUniv
              have h0in : (0 : Bid) ∈ W_r := by rw [hUniv]; trivial
              have : rA ≤ m := h0in
              linarith [hG.1.1]
            refine ⟨u_r, hu_mem, o_r, ho_mem, W_r, hUpper, hNe, hNotUniv, fun b_i => ?_⟩
            dsimp [σ, W_r, u_r, o_r]
            rw [if_pos hrB, if_neg h1, if_pos hG]
          · by_cases h3 : rA ∈ I3
            · left
              refine ⟨cdfPick wI3 rB, fun b_i => ?_⟩
              dsimp only [σ]
              rw [if_pos hrB, if_neg h1, if_neg hG, if_pos h3]
            · left
              refine ⟨tDef, fun b_i => ?_⟩
              dsimp only [σ]
              rw [if_pos hrB, if_neg h1, if_neg hG, if_neg h3]
      · left
        refine ⟨tDef, fun b_i => ?_⟩
        dsimp only [σ]
        rw [if_neg hrB]

/-! ## Appendix E: Impossibility of Universally Stable Sampling -/

private lemma hUnderRetain : ∀ {T : Type} [Fintype T] {R : Type} [MeasurableSpace R]
    (μ : Measure R) [IsProbabilityMeasure μ]
    (qSlice : Bid → TokenDist T) (target : TokenDist T) (σSlice : Bid → R → T),
    IsStableSampler μ qSlice target σSlice →
    ∀ (t : T) (b : Bid), t ∈ undersampledTokens qSlice target →
      {r : R | σSlice 0 r = t} ⊆ {r : R | σSlice b r = t} := by
  intro T _ R _ μ _ qSlice target σSlice hStab t b ht r hr
  rcases hStab.2 r with ⟨t₀, ht₀⟩ | ⟨u_r, hu, o_r, ho, W_r, hUpper, _, hNotUniv, hPath⟩
  · change σSlice b r = t
    rw [ht₀ b, ← ht₀ 0]
    exact hr
  · have h0not : (0 : Bid) ∉ W_r := by
      intro h0in
      apply hNotUniv
      ext x
      simp only [Set.mem_univ, iff_true]
      exact hUpper (zero_le x) h0in
    have h0eq : σSlice 0 r = o_r := by
      rw [hPath 0, if_neg h0not]
    have hto : o_r = t := h0eq.symm.trans hr
    subst hto
    have h1 : (qSlice 0).prob o_r ≤ target.prob o_r := ht
    have h2 : target.prob o_r < (qSlice 0).prob o_r := ho
    linarith
private lemma hOverShrink : ∀ {T : Type} [Fintype T] {R : Type} [MeasurableSpace R]
    (μ : Measure R) [IsProbabilityMeasure μ]
    (qSlice : Bid → TokenDist T) (target : TokenDist T) (σSlice : Bid → R → T),
    IsStableSampler μ qSlice target σSlice →
    ∀ (t : T) (b : Bid), t ∈ oversampledTokens qSlice target →
      {r : R | σSlice b r = t} ⊆ {r : R | σSlice 0 r = t} := by
  intro T _ R _ μ _ qSlice target σSlice hStab t b ht r hr
  rcases hStab.2 r with ⟨t₀, ht₀⟩ | ⟨u_r, hu, o_r, ho, W_r, hUpper, _, hNotUniv, hPath⟩
  · change σSlice 0 r = t
    rw [ht₀ 0, ← ht₀ b]
    exact hr
  · have h0not : (0 : Bid) ∉ W_r := by
      intro h0in
      apply hNotUniv
      ext x
      simp only [Set.mem_univ, iff_true]
      exact hUpper (zero_le x) h0in
    have hbnot : b ∉ W_r := by
      intro hbin
      have hbeq : σSlice b r = u_r := by rw [hPath b, if_pos hbin]
      have htu : u_r = t := hbeq.symm.trans hr
      subst htu
      have h1 : (qSlice 0).prob u_r ≤ target.prob u_r := hu
      have h2 : target.prob u_r < (qSlice 0).prob u_r := ht
      linarith
    change σSlice 0 r = t
    have hbeq : σSlice b r = o_r := by rw [hPath b, if_neg hbnot]
    rw [hPath 0, if_neg h0not, ← hbeq]
    exact hr
private lemma hDisjNull : ∀ {R : Type} [MeasurableSpace R] (μ : Measure R) [IsProbabilityMeasure μ]
    {A B C : Set R},
    A ⊆ B → MeasurableSet A → μ.real A = μ.real B → Disjoint C A →
    μ.real (C ∩ B) = 0 := by
  intro R _ μ _ A B C hAB hMeasA hEqMeas hDisj
  have hDiffZero : μ.real (B \ A) = 0 := by
    rw [measureReal_diff hAB hMeasA, hEqMeas, sub_self]
  have hSub : C ∩ B ⊆ B \ A := by
    rintro r ⟨hrC, hrB⟩
    exact ⟨hrB, fun hrA => Set.disjoint_left.mp hDisj hrC hrA⟩
  have hle : μ.real (C ∩ B) ≤ μ.real (B \ A) := measureReal_mono hSub
  have hnn : 0 ≤ μ.real (C ∩ B) := measureReal_nonneg
  linarith
private lemma hJoin00 : joinBid (0 : Fin 2) 0 (fun _ => 0) = ![0, 0] := by
  ext j; fin_cases j <;> simp [joinBid]
private lemma hJoin01_0 : joinBid (0 : Fin 2) 1 (fun _ => 0) = ![1, 0] := by
  ext j; fin_cases j <;> simp [joinBid]
private lemma hJoin00_1 : joinBid (0 : Fin 2) 0 (fun _ => 1) = ![0, 1] := by
  ext j; fin_cases j <;> simp [joinBid]
private lemma hJoin01_1 : joinBid (0 : Fin 2) 1 (fun _ => 1) = ![1, 1] := by
  ext j; fin_cases j <;> simp [joinBid]
private lemma hJoin10_0 : joinBid (1 : Fin 2) 0 (fun _ => 0) = ![0, 0] := by
  ext j; fin_cases j <;> simp [joinBid]
private lemma hJoin11_0 : joinBid (1 : Fin 2) 1 (fun _ => 0) = ![0, 1] := by
  ext j; fin_cases j <;> simp [joinBid]
private lemma hJoin10_1 : joinBid (1 : Fin 2) 0 (fun _ => 1) = ![1, 0] := by
  ext j; fin_cases j <;> simp [joinBid]
private lemma hJoin11_1 : joinBid (1 : Fin 2) 1 (fun _ => 1) = ![1, 1] := by
  ext j; fin_cases j <;> simp [joinBid]
private lemma hReflPref : ∀ {T : Type} [Fintype T] (target d : TokenDist T), RobustPref target d d :=
  fun _ _ => ⟨fun _ => le_rfl, fun _ => mul_self_nonneg _⟩
private lemma hTargetPref : ∀ {T : Type} [Fintype T] (target d : TokenDist T),
    RobustPref target target d := by
  intro T _ target d
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp [abs_nonneg]
  · simp

/-- Example E.1 (`exmpl:4-token`): Four-token, two-bidder robust-monotone aggregation rule with
    identical target distributions `p_1 = p_2 = (0, 0, 1/2, 1/2)` that admits no universally
    stable sampling implementation on any probability space `(R, μ)`. -/
theorem ex_E_1_four_token_no_universal_stable :
    ∃ (q : AggRule 2 (Fin 4)) (pCommon : TokenDist (Fin 4)),
      pCommon.prob 0 = 0 ∧ pCommon.prob 1 = 0 ∧ pCommon.prob 2 = 1 / 2 ∧ pCommon.prob 3 = 1 / 2 ∧
      IsMonotoneAgg (robustAgentPrefs 2 (Fin 4)) q ∧
      (let pProf : DistProfile 2 (Fin 4) := ![pCommon, pCommon]
       ∀ (R : Type) [MeasurableSpace R] (μ : Measure R) [IsProbabilityMeasure μ]
         (σUniv : BidProfile 2 → R → Fin 4),
         ¬ IsUniversallyStableSampler μ q pProf σUniv) := by
  let fpC : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then 0 else 1 / 2
  let pCommon : TokenDist (Fin 4) :=
    { prob := fun t => fpC t.val
      nonneg := fun t => by dsimp [fpC]; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_four]
        change fpC 0 + fpC 1 + fpC 2 + fpC 3 = 1
        norm_num [fpC] }
  let fd00 : ℕ → ℝ := fun n => if n = 0 then 1 / 2 else if n = 1 then 1 / 2 else 0
  let d00 : TokenDist (Fin 4) :=
    { prob := fun t => fd00 t.val
      nonneg := fun t => by dsimp [fd00]; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_four]
        change fd00 0 + fd00 1 + fd00 2 + fd00 3 = 1
        norm_num [fd00] }
  let fd10 : ℕ → ℝ := fun n => if n = 1 then 1 / 2 else if n = 2 then 1 / 2 else 0
  let d10 : TokenDist (Fin 4) :=
    { prob := fun t => fd10 t.val
      nonneg := fun t => by dsimp [fd10]; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_four]
        change fd10 0 + fd10 1 + fd10 2 + fd10 3 = 1
        norm_num [fd10] }
  let fd01 : ℕ → ℝ := fun n => if n = 0 then 1 / 2 else if n = 2 then 1 / 2 else 0
  let d01 : TokenDist (Fin 4) :=
    { prob := fun t => fd01 t.val
      nonneg := fun t => by dsimp [fd01]; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_four]
        change fd01 0 + fd01 1 + fd01 2 + fd01 3 = 1
        norm_num [fd01] }
  have hpC0 : pCommon.prob 0 = 0 := by change fpC 0 = 0; norm_num [fpC]
  have hpC1 : pCommon.prob 1 = 0 := by change fpC 1 = 0; norm_num [fpC]
  have hpC2 : pCommon.prob 2 = 1 / 2 := by change fpC 2 = 1 / 2; norm_num [fpC]
  have hpC3 : pCommon.prob 3 = 1 / 2 := by change fpC 3 = 1 / 2; norm_num [fpC]
  have hd00_0 : d00.prob 0 = 1 / 2 := by change fd00 0 = 1 / 2; norm_num [fd00]
  have hd00_1 : d00.prob 1 = 1 / 2 := by change fd00 1 = 1 / 2; norm_num [fd00]
  have hd00_2 : d00.prob 2 = 0 := by change fd00 2 = 0; norm_num [fd00]
  have hd00_3 : d00.prob 3 = 0 := by change fd00 3 = 0; norm_num [fd00]
  have hd10_1 : d10.prob 1 = 1 / 2 := by change fd10 1 = 1 / 2; norm_num [fd10]
  have hd10_2 : d10.prob 2 = 1 / 2 := by change fd10 2 = 1 / 2; norm_num [fd10]
  have hd01_0 : d01.prob 0 = 1 / 2 := by change fd01 0 = 1 / 2; norm_num [fd01]
  have hd01_2 : d01.prob 2 = 1 / 2 := by change fd01 2 = 1 / 2; norm_num [fd01]
  let pProf : DistProfile 2 (Fin 4) := ![pCommon, pCommon]
  let qE1 : BidProfile 2 → TokenDist (Fin 4) := fun b =>
    if 1 ≤ b 0 then (if 1 ≤ b 1 then pCommon else d10)
    else (if 1 ≤ b 1 then d01 else d00)
  let q : AggRule 2 (Fin 4) := fun b p => if p = pProf then qE1 b else p 0
  have hMonoQ : IsMonotoneAgg (robustAgentPrefs 2 (Fin 4)) q := by
    intro i p bOthers b_i b'_i hle
    dsimp [robustAgentPrefs, q]
    split_ifs with hp
    · subst hp
      have hp_i : pProf i = pCommon := by fin_cases i <;> rfl
      rw [hp_i]
      fin_cases i
      · dsimp [qE1]
        simp only [joinBid_self]
        have hOther1 : joinBid 0 b_i bOthers 1 = joinBid 0 b'_i bOthers 1 := by
          simp [joinBid]
        rw [hOther1]
        by_cases hb1 : 1 ≤ joinBid 0 b'_i bOthers 1
        · rw [if_pos hb1, if_pos hb1]
          by_cases hbi' : 1 ≤ b'_i
          · have hbi : 1 ≤ b_i := le_trans hbi' hle
            rw [if_pos hbi, if_pos hbi']
            exact hReflPref pCommon pCommon
          · rw [if_neg hbi']
            by_cases hbi : 1 ≤ b_i
            · rw [if_pos hbi]
              exact hTargetPref pCommon d01
            · rw [if_neg hbi]
              exact hReflPref pCommon d01
        · rw [if_neg hb1, if_neg hb1]
          by_cases hbi' : 1 ≤ b'_i
          · have hbi : 1 ≤ b_i := le_trans hbi' hle
            rw [if_pos hbi, if_pos hbi']
            exact hReflPref pCommon d10
          · rw [if_neg hbi']
            by_cases hbi : 1 ≤ b_i
            · rw [if_pos hbi]
              refine ⟨fun t => ?_, fun t => ?_⟩ <;>
                (rcases (by have := t.isLt; omega : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3)
                  with h | h | h | h <;>
                  simp only [pCommon, d10, d00, fpC, fd10, fd00, h] <;> norm_num)
            · rw [if_neg hbi]
              exact hReflPref pCommon d00
      · dsimp [qE1]
        simp only [joinBid_self]
        have hOther0 : joinBid 1 b_i bOthers 0 = joinBid 1 b'_i bOthers 0 := by
          simp [joinBid]
        rw [hOther0]
        by_cases hb0 : 1 ≤ joinBid 1 b'_i bOthers 0
        · rw [if_pos hb0, if_pos hb0]
          by_cases hbi' : 1 ≤ b'_i
          · have hbi : 1 ≤ b_i := le_trans hbi' hle
            rw [if_pos hbi, if_pos hbi']
            exact hReflPref pCommon pCommon
          · rw [if_neg hbi']
            by_cases hbi : 1 ≤ b_i
            · rw [if_pos hbi]
              exact hTargetPref pCommon d10
            · rw [if_neg hbi]
              exact hReflPref pCommon d10
        · rw [if_neg hb0, if_neg hb0]
          by_cases hbi' : 1 ≤ b'_i
          · have hbi : 1 ≤ b_i := le_trans hbi' hle
            rw [if_pos hbi, if_pos hbi']
            exact hReflPref pCommon d01
          · rw [if_neg hbi']
            by_cases hbi : 1 ≤ b_i
            · rw [if_pos hbi]
              refine ⟨fun t => ?_, fun t => ?_⟩ <;>
                (rcases (by have := t.isLt; omega : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3)
                  with h | h | h | h <;>
                  simp only [pCommon, d01, d00, fpC, fd01, fd00, h] <;> norm_num)
            · rw [if_neg hbi]
              exact hReflPref pCommon d00
    · exact hReflPref (p i) (p 0)
  refine ⟨q, pCommon, hpC0, hpC1, hpC2, hpC3, hMonoQ, ?_⟩
  dsimp only
  intro R _ μ _ σUniv hUniv
  rcases hUniv with ⟨hMeas, hProb, hSlice⟩
  let E : BidProfile 2 → Fin 4 → Set R := fun b t => {r : R | σUniv b r = t}
  have hq00 : q ![0, 0] pProf = d00 := by simp [q, qE1]
  have hq10 : q ![1, 0] pProf = d10 := by simp [q, qE1]
  have hq01 : q ![0, 1] pProf = d01 := by simp [q, qE1]
  have hq11 : q ![1, 1] pProf = pCommon := by simp [q, qE1]
  
  have hSub1 : E ![1, 0] 1 ⊆ E ![0, 0] 1 := by
    have hs := hOverShrink μ (fun b_i => q (joinBid 0 b_i (fun _ => 0)) pProf)
      (pProf 0) (fun b_i r => σUniv (joinBid 0 b_i (fun _ => 0)) r)
      (hSlice 0 (fun _ => 0)) 1 1
    rw [hJoin00, hJoin01_0] at hs
    apply hs
    change pCommon.prob 1 < (q ![0, 0] pProf).prob 1
    rw [hq00, hpC1, hd00_1]; norm_num
  have hNull1 : μ.real (E ![1, 0] 2 ∩ E ![0, 0] 1) = 0 := by
    apply hDisjNull μ hSub1 (hMeas ![1, 0] 1)
    · rw [hProb ![1, 0] 1, hProb ![0, 0] 1, hq10, hq00, hd10_1, hd00_1]
    · refine Set.disjoint_left.mpr (fun r hr2 hr1 => ?_)
      change σUniv ![1, 0] r = 2 at hr2
      change σUniv ![1, 0] r = 1 at hr1
      omega
  
  have hSub0 : E ![0, 1] 0 ⊆ E ![0, 0] 0 := by
    have hs := hOverShrink μ (fun b_i => q (joinBid 1 b_i (fun _ => 0)) pProf)
      (pProf 1) (fun b_i r => σUniv (joinBid 1 b_i (fun _ => 0)) r)
      (hSlice 1 (fun _ => 0)) 0 1
    rw [hJoin10_0, hJoin11_0] at hs
    apply hs
    change pCommon.prob 0 < (q ![0, 0] pProf).prob 0
    rw [hq00, hpC0, hd00_0]; norm_num
  have hNull0 : μ.real (E ![0, 1] 2 ∩ E ![0, 0] 0) = 0 := by
    apply hDisjNull μ hSub0 (hMeas ![0, 1] 0)
    · rw [hProb ![0, 1] 0, hProb ![0, 0] 0, hq01, hq00, hd01_0, hd00_0]
    · refine Set.disjoint_left.mpr (fun r hr2 hr0 => ?_)
      change σUniv ![0, 1] r = 2 at hr2
      change σUniv ![0, 1] r = 0 at hr0
      omega
  
  let I : Set R := E ![1, 0] 2 ∩ E ![0, 1] 2
  have hICover : I ⊆ (E ![0, 1] 2 ∩ E ![0, 0] 0) ∪ (E ![1, 0] 2 ∩ E ![0, 0] 1) ∪
      E ![0, 0] 2 ∪ E ![0, 0] 3 := by
    rintro r ⟨hr10, hr01⟩
    have ht : σUniv ![0, 0] r = 0 ∨ σUniv ![0, 0] r = 1 ∨
        σUniv ![0, 0] r = 2 ∨ σUniv ![0, 0] r = 3 := by
      rcases (by have := (σUniv ![0, 0] r).isLt; omega :
        (σUniv ![0, 0] r).val = 0 ∨ (σUniv ![0, 0] r).val = 1 ∨
        (σUniv ![0, 0] r).val = 2 ∨ (σUniv ![0, 0] r).val = 3) with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    rcases ht with h0 | h1 | h2 | h3
    · exact Or.inl (Or.inl (Or.inl ⟨hr01, h0⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hr10, h1⟩))
    · exact Or.inl (Or.inr h2)
    · exact Or.inr h3
  have hINull : μ.real I = 0 := by
    have hle : μ.real I ≤
        μ.real (E ![0, 1] 2 ∩ E ![0, 0] 0) + μ.real (E ![1, 0] 2 ∩ E ![0, 0] 1) +
        μ.real (E ![0, 0] 2) + μ.real (E ![0, 0] 3) := by
      calc
        μ.real I ≤ μ.real ((E ![0, 1] 2 ∩ E ![0, 0] 0) ∪ (E ![1, 0] 2 ∩ E ![0, 0] 1) ∪
            E ![0, 0] 2 ∪ E ![0, 0] 3) := measureReal_mono hICover
        _ ≤ μ.real ((E ![0, 1] 2 ∩ E ![0, 0] 0) ∪ (E ![1, 0] 2 ∩ E ![0, 0] 1) ∪
            E ![0, 0] 2) + μ.real (E ![0, 0] 3) := measureReal_union_le _ _
        _ ≤ μ.real ((E ![0, 1] 2 ∩ E ![0, 0] 0) ∪ (E ![1, 0] 2 ∩ E ![0, 0] 1)) +
            μ.real (E ![0, 0] 2) + μ.real (E ![0, 0] 3) := by
          linarith [measureReal_union_le (μ := μ) ((E ![0, 1] 2 ∩ E ![0, 0] 0) ∪
            (E ![1, 0] 2 ∩ E ![0, 0] 1)) (E ![0, 0] 2)]
        _ ≤ μ.real (E ![0, 1] 2 ∩ E ![0, 0] 0) + μ.real (E ![1, 0] 2 ∩ E ![0, 0] 1) +
            μ.real (E ![0, 0] 2) + μ.real (E ![0, 0] 3) := by
          linarith [measureReal_union_le (μ := μ) (E ![0, 1] 2 ∩ E ![0, 0] 0)
            (E ![1, 0] 2 ∩ E ![0, 0] 1)]
    have h00_2 : μ.real (E ![0, 0] 2) = 0 := by
      rw [hProb ![0, 0] 2, hq00, hd00_2]
    have h00_3 : μ.real (E ![0, 0] 3) = 0 := by
      rw [hProb ![0, 0] 3, hq00, hd00_3]
    have hnn : 0 ≤ μ.real I := measureReal_nonneg
    linarith
  
  have hRet10 : E ![1, 0] 2 ⊆ E ![1, 1] 2 := by
    have hs := hUnderRetain μ (fun b_i => q (joinBid 1 b_i (fun _ => 1)) pProf)
      (pProf 1) (fun b_i r => σUniv (joinBid 1 b_i (fun _ => 1)) r)
      (hSlice 1 (fun _ => 1)) 2 1
    rw [hJoin10_1, hJoin11_1] at hs
    apply hs
    change (q ![1, 0] pProf).prob 2 ≤ pCommon.prob 2
    rw [hq10, hd10_2, hpC2]
  have hRet01 : E ![0, 1] 2 ⊆ E ![1, 1] 2 := by
    have hs := hUnderRetain μ (fun b_i => q (joinBid 0 b_i (fun _ => 1)) pProf)
      (pProf 0) (fun b_i r => σUniv (joinBid 0 b_i (fun _ => 1)) r)
      (hSlice 0 (fun _ => 1)) 2 1
    rw [hJoin00_1, hJoin01_1] at hs
    apply hs
    change (q ![0, 1] pProf).prob 2 ≤ pCommon.prob 2
    rw [hq01, hd01_2, hpC2]
  have hUnionSub : E ![1, 0] 2 ∪ E ![0, 1] 2 ⊆ E ![1, 1] 2 :=
    Set.union_subset hRet10 hRet01
  have hUnionLe : μ.real (E ![1, 0] 2 ∪ E ![0, 1] 2) ≤ μ.real (E ![1, 1] 2) :=
    measureReal_mono hUnionSub
  have hAddInter := measureReal_union_add_inter (μ := μ) (s := E ![1, 0] 2)
    (hMeas ![0, 1] 2)
  have hm10 : μ.real (E ![1, 0] 2) = 1 / 2 := by
    rw [hProb ![1, 0] 2, hq10, hd10_2]
  have hm01 : μ.real (E ![0, 1] 2) = 1 / 2 := by
    rw [hProb ![0, 1] 2, hq01, hd01_2]
  have hm11 : μ.real (E ![1, 1] 2) = 1 / 2 := by
    rw [hProb ![1, 1] 2, hq11, hpC2]
  change μ.real (E ![1, 0] 2 ∩ E ![0, 1] 2) = 0 at hINull
  linarith

/-- Example E.2 (`exmpl:3-token`): Three-token, two-bidder robust-monotone aggregation rule with
    heterogeneous targets `p_1 = (1/2, 0, 1/2)` and `p_2 = (0, 0, 1)` that admits no universally
    stable sampling implementation on any probability space `(R, μ)`. -/
theorem ex_E_2_three_token_no_universal_stable :
    ∃ (q : AggRule 2 (Fin 3)) (p₁ p₂ : TokenDist (Fin 3)),
      p₁.prob 0 = 1 / 2 ∧ p₁.prob 1 = 0 ∧ p₁.prob 2 = 1 / 2 ∧
      p₂.prob 0 = 0 ∧ p₂.prob 1 = 0 ∧ p₂.prob 2 = 1 ∧
      IsMonotoneAgg (robustAgentPrefs 2 (Fin 3)) q ∧
      (let pProf : DistProfile 2 (Fin 3) := ![p₁, p₂]
       ∀ (R : Type) [MeasurableSpace R] (μ : Measure R) [IsProbabilityMeasure μ]
         (σUniv : BidProfile 2 → R → Fin 3),
         ¬ IsUniversallyStableSampler μ q pProf σUniv) := by
  let fp₁ : ℕ → ℝ := fun n => if n = 0 then 1 / 2 else if n = 1 then 0 else 1 / 2
  let p₁ : TokenDist (Fin 3) :=
    { prob := fun t => fp₁ t.val
      nonneg := fun t => by dsimp [fp₁]; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_three]
        change fp₁ 0 + fp₁ 1 + fp₁ 2 = 1
        norm_num [fp₁] }
  let fp₂ : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then 0 else 1
  let p₂ : TokenDist (Fin 3) :=
    { prob := fun t => fp₂ t.val
      nonneg := fun t => by dsimp [fp₂]; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_three]
        change fp₂ 0 + fp₂ 1 + fp₂ 2 = 1
        norm_num [fp₂] }
  let fd00' : ℕ → ℝ := fun n => if n = 0 then 1 / 2 else if n = 1 then 1 / 2 else 0
  let d00 : TokenDist (Fin 3) :=
    { prob := fun t => fd00' t.val
      nonneg := fun t => by dsimp [fd00']; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_three]
        change fd00' 0 + fd00' 1 + fd00' 2 = 1
        norm_num [fd00'] }
  let fd01' : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then 1 / 2 else 1 / 2
  let d01 : TokenDist (Fin 3) :=
    { prob := fun t => fd01' t.val
      nonneg := fun t => by dsimp [fd01']; split_ifs <;> norm_num
      sum_eq_one := by
        rw [Fin.sum_univ_three]
        change fd01' 0 + fd01' 1 + fd01' 2 = 1
        norm_num [fd01'] }
  have hp₁_0 : p₁.prob 0 = 1 / 2 := by change fp₁ 0 = 1 / 2; norm_num [fp₁]
  have hp₁_1 : p₁.prob 1 = 0 := by change fp₁ 1 = 0; norm_num [fp₁]
  have hp₁_2 : p₁.prob 2 = 1 / 2 := by change fp₁ 2 = 1 / 2; norm_num [fp₁]
  have hp₂_0 : p₂.prob 0 = 0 := by change fp₂ 0 = 0; norm_num [fp₂]
  have hp₂_1 : p₂.prob 1 = 0 := by change fp₂ 1 = 0; norm_num [fp₂]
  have hp₂_2 : p₂.prob 2 = 1 := by change fp₂ 2 = 1; norm_num [fp₂]
  have hd00'_0 : d00.prob 0 = 1 / 2 := by change fd00' 0 = 1 / 2; norm_num [fd00']
  have hd00'_1 : d00.prob 1 = 1 / 2 := by change fd00' 1 = 1 / 2; norm_num [fd00']
  have hd00'_2 : d00.prob 2 = 0 := by change fd00' 2 = 0; norm_num [fd00']
  have hd01'_1 : d01.prob 1 = 1 / 2 := by change fd01' 1 = 1 / 2; norm_num [fd01']
  have hd01'_2 : d01.prob 2 = 1 / 2 := by change fd01' 2 = 1 / 2; norm_num [fd01']
  let pProf : DistProfile 2 (Fin 3) := ![p₁, p₂]
  let qE2 : BidProfile 2 → TokenDist (Fin 3) := fun b =>
    if 1 ≤ b 0 then p₁ else (if 1 ≤ b 1 then d01 else d00)
  let q : AggRule 2 (Fin 3) := fun b p => if p = pProf then qE2 b else p 0
  have hMonoQ : IsMonotoneAgg (robustAgentPrefs 2 (Fin 3)) q := by
    intro i p bOthers b_i b'_i hle
    dsimp [robustAgentPrefs, q]
    split_ifs with hp
    · subst hp
      fin_cases i
      · change RobustPref p₁ (qE2 (joinBid 0 b_i bOthers)) (qE2 (joinBid 0 b'_i bOthers))
        dsimp [qE2]
        simp only [joinBid_self]
        have hOther1 : joinBid 0 b_i bOthers 1 = joinBid 0 b'_i bOthers 1 := by
          simp [joinBid]
        rw [hOther1]
        by_cases hbi : 1 ≤ b_i
        · rw [if_pos hbi]
          exact hTargetPref p₁ _
        · have hbi' : ¬ 1 ≤ b'_i := fun h => hbi (le_trans h hle)
          rw [if_neg hbi, if_neg hbi']
          exact hReflPref p₁ _
      · change RobustPref p₂ (qE2 (joinBid 1 b_i bOthers)) (qE2 (joinBid 1 b'_i bOthers))
        dsimp [qE2]
        simp only [joinBid_self]
        have hOther0 : joinBid 1 b_i bOthers 0 = joinBid 1 b'_i bOthers 0 := by
          simp [joinBid]
        rw [hOther0]
        by_cases hb0 : 1 ≤ joinBid 1 b'_i bOthers 0
        · rw [if_pos hb0, if_pos hb0]
          exact hReflPref p₂ p₁
        · rw [if_neg hb0, if_neg hb0]
          by_cases hbi' : 1 ≤ b'_i
          · have hbi : 1 ≤ b_i := le_trans hbi' hle
            rw [if_pos hbi, if_pos hbi']
            exact hReflPref p₂ d01
          · rw [if_neg hbi']
            by_cases hbi : 1 ≤ b_i
            · rw [if_pos hbi]
              refine ⟨fun t => ?_, fun t => ?_⟩ <;>
                (rcases (by have := t.isLt; omega : t.val = 0 ∨ t.val = 1 ∨ t.val = 2)
                  with h | h | h <;>
                  simp only [p₂, d01, d00, fp₂, fd01', fd00', h] <;> norm_num)
            · rw [if_neg hbi]
              exact hReflPref p₂ d00
    · exact hReflPref (p i) (p 0)
  refine ⟨q, p₁, p₂, hp₁_0, hp₁_1, hp₁_2, hp₂_0, hp₂_1, hp₂_2, hMonoQ, ?_⟩
  dsimp only
  intro R _ μ _ σUniv hUniv
  rcases hUniv with ⟨hMeas, hProb, hSlice⟩
  let E : BidProfile 2 → Fin 3 → Set R := fun b t => {r : R | σUniv b r = t}
  have hq00 : q ![0, 0] pProf = d00 := by simp [q, qE2]
  have hq10 : q ![1, 0] pProf = p₁ := by simp [q, qE2]
  have hq01 : q ![0, 1] pProf = d01 := by simp [q, qE2]
  have hq11 : q ![1, 1] pProf = p₁ := by simp [q, qE2]
  
  have hSub0 : E ![0, 0] 0 ⊆ E ![1, 0] 0 := by
    have hs := hUnderRetain μ (fun b_i => q (joinBid 0 b_i (fun _ => 0)) pProf)
      (pProf 0) (fun b_i r => σUniv (joinBid 0 b_i (fun _ => 0)) r)
      (hSlice 0 (fun _ => 0)) 0 1
    rw [hJoin00, hJoin01_0] at hs
    apply hs
    change (q ![0, 0] pProf).prob 0 ≤ p₁.prob 0
    rw [hq00, hd00'_0, hp₁_0]
  have hEmpty0 : E ![1, 0] 2 ∩ E ![0, 0] 0 = ∅ := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hr2 hr0
    have hr10_0 : r ∈ E ![1, 0] 0 := hSub0 hr0
    change σUniv ![1, 0] r = 2 at hr2
    change σUniv ![1, 0] r = 0 at hr10_0
    omega
  
  have hSub1 : E ![0, 1] 1 ⊆ E ![0, 0] 1 := by
    have hs := hOverShrink μ (fun b_i => q (joinBid 1 b_i (fun _ => 0)) pProf)
      (pProf 1) (fun b_i r => σUniv (joinBid 1 b_i (fun _ => 0)) r)
      (hSlice 1 (fun _ => 0)) 1 1
    rw [hJoin10_0, hJoin11_0] at hs
    apply hs
    change p₂.prob 1 < (q ![0, 0] pProf).prob 1
    rw [hq00, hp₂_1, hd00'_1]; norm_num
  have hNull1 : μ.real (E ![0, 1] 2 ∩ E ![0, 0] 1) = 0 := by
    apply hDisjNull μ hSub1 (hMeas ![0, 1] 1)
    · rw [hProb ![0, 1] 1, hProb ![0, 0] 1, hq01, hq00, hd01'_1, hd00'_1]
    · refine Set.disjoint_left.mpr (fun r hr2 hr1 => ?_)
      change σUniv ![0, 1] r = 2 at hr2
      change σUniv ![0, 1] r = 1 at hr1
      omega
  
  let I : Set R := E ![1, 0] 2 ∩ E ![0, 1] 2
  have hICover : I ⊆ (E ![1, 0] 2 ∩ E ![0, 0] 0) ∪ (E ![0, 1] 2 ∩ E ![0, 0] 1) ∪
      E ![0, 0] 2 := by
    rintro r ⟨hr10, hr01⟩
    have ht : σUniv ![0, 0] r = 0 ∨ σUniv ![0, 0] r = 1 ∨ σUniv ![0, 0] r = 2 := by
      rcases (by have := (σUniv ![0, 0] r).isLt; omega :
        (σUniv ![0, 0] r).val = 0 ∨ (σUniv ![0, 0] r).val = 1 ∨
        (σUniv ![0, 0] r).val = 2) with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases ht with h0 | h1 | h2
    · exact Or.inl (Or.inl ⟨hr10, h0⟩)
    · exact Or.inl (Or.inr ⟨hr01, h1⟩)
    · exact Or.inr h2
  have hINull : μ.real I = 0 := by
    have hle : μ.real I ≤
        μ.real (E ![1, 0] 2 ∩ E ![0, 0] 0) + μ.real (E ![0, 1] 2 ∩ E ![0, 0] 1) +
        μ.real (E ![0, 0] 2) := by
      calc
        μ.real I ≤ μ.real ((E ![1, 0] 2 ∩ E ![0, 0] 0) ∪ (E ![0, 1] 2 ∩ E ![0, 0] 1) ∪
            E ![0, 0] 2) := measureReal_mono hICover
        _ ≤ μ.real ((E ![1, 0] 2 ∩ E ![0, 0] 0) ∪ (E ![0, 1] 2 ∩ E ![0, 0] 1)) +
            μ.real (E ![0, 0] 2) := measureReal_union_le _ _
        _ ≤ μ.real (E ![1, 0] 2 ∩ E ![0, 0] 0) + μ.real (E ![0, 1] 2 ∩ E ![0, 0] 1) +
            μ.real (E ![0, 0] 2) := by
          linarith [measureReal_union_le (μ := μ) (E ![1, 0] 2 ∩ E ![0, 0] 0)
            (E ![0, 1] 2 ∩ E ![0, 0] 1)]
    have h00_0 : μ.real (E ![1, 0] 2 ∩ E ![0, 0] 0) = 0 := by
      rw [hEmpty0]; simp
    have h00_2 : μ.real (E ![0, 0] 2) = 0 := by
      rw [hProb ![0, 0] 2, hq00, hd00'_2]
    have hnn : 0 ≤ μ.real I := measureReal_nonneg
    linarith
  
  have hRet10 : E ![1, 0] 2 ⊆ E ![1, 1] 2 := by
    have hs := hUnderRetain μ (fun b_i => q (joinBid 1 b_i (fun _ => 1)) pProf)
      (pProf 1) (fun b_i r => σUniv (joinBid 1 b_i (fun _ => 1)) r)
      (hSlice 1 (fun _ => 1)) 2 1
    rw [hJoin10_1, hJoin11_1] at hs
    apply hs
    change (q ![1, 0] pProf).prob 2 ≤ p₂.prob 2
    rw [hq10, hp₁_2, hp₂_2]; norm_num
  have hRet01 : E ![0, 1] 2 ⊆ E ![1, 1] 2 := by
    have hs := hUnderRetain μ (fun b_i => q (joinBid 0 b_i (fun _ => 1)) pProf)
      (pProf 0) (fun b_i r => σUniv (joinBid 0 b_i (fun _ => 1)) r)
      (hSlice 0 (fun _ => 1)) 2 1
    rw [hJoin00_1, hJoin01_1] at hs
    apply hs
    change (q ![0, 1] pProf).prob 2 ≤ p₁.prob 2
    rw [hq01, hd01'_2, hp₁_2]
  have hUnionSub : E ![1, 0] 2 ∪ E ![0, 1] 2 ⊆ E ![1, 1] 2 :=
    Set.union_subset hRet10 hRet01
  have hUnionLe : μ.real (E ![1, 0] 2 ∪ E ![0, 1] 2) ≤ μ.real (E ![1, 1] 2) :=
    measureReal_mono hUnionSub
  have hAddInter := measureReal_union_add_inter (μ := μ) (s := E ![1, 0] 2)
    (hMeas ![0, 1] 2)
  have hm10 : μ.real (E ![1, 0] 2) = 1 / 2 := by
    rw [hProb ![1, 0] 2, hq10, hp₁_2]
  have hm01 : μ.real (E ![0, 1] 2) = 1 / 2 := by
    rw [hProb ![0, 1] 2, hq01, hd01'_2]
  have hm11 : μ.real (E ![1, 1] 2) = 1 / 2 := by
    rw [hProb ![1, 1] 2, hq11, hp₁_2]
  change μ.real (E ![1, 0] 2 ∩ E ![0, 1] 2) = 0 at hINull
  linarith

end

end TokenAuctions
