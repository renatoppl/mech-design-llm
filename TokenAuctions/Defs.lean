import Mathlib

/-!
# Shared Definitions: Mechanism Design for Large Language Models (Token Auctions with Proxy Bidders)

This module defines all foundational mathematical objects from Sections 2–6 and Appendices A–E of
*Mechanism Design for Large Language Models: Token Auctions with Proxy Bidders*:

- **Section 2.1**: Finite token vocabulary `T`, probability simplex `Δ(T)` (`TokenDist T`),
  context-window sequences `T*`, `appendTrim` (`⊕`), stateless LLMs `f : T* → Δ(T)`, and
  prompt-tuned proxy LLMs `f_i(s) = f(s_0^i ⊕ s)`.
- **Section 2.2**: Rational bid space `ℚ₊` (`Bid := NNRat`), bid and distribution profiles,
  distribution aggregation functions `q`, stage-independent token pricing functions `ζ_i`,
  induced expected payments `z_i`, token auction mechanisms `𝓜 = ⟨q, z⟩`, and payment admissibility
  (`z_i(0, b_{-i}, p) = 0 ≤ z_i(b, p)`).
- **Section 3 & Appendices A–B**: Shannon entropy `H(p)`, cross-entropy `H(p, q)`,
  KL-divergence `D_KL(p ‖ q)`, forward- and reverse-KL social welfare, the linear aggregation rule
  `q_KL`, the log-linear (geometric) aggregation rule `q̄_KL`, and their closed-form VCG payments.
- **Section 4 & Appendix C**: General partial preference orders `⪰_i`, multi-utility preferences,
  payment monotonicity (Definition 4.1), consistent aggregation (Definition 4.2), monotone
  aggregation (Definition 4.3), strategic equivalence (Definition 4.4), and achievable menus `Q_i`.
- **Section 5 & Appendices D–E**: Robust preferences over distributions (Definition 5.1),
  undersampled/oversampled token sets `T⁺`/`T⁻`, valid and stable sampling implementations
  (Definition 5.4), critical prices `θ_r` and ex-post/expected second-price payments, closed-form
  linear-rule second-price payments (Corollary 5.7), and universally stable sampling (`σ^univ`).
- **Section 6.2**: Sequence perplexity `PPL_i(s_m)`.
-/

namespace TokenAuctions

open scoped BigOperators
open Classical MeasureTheory

noncomputable section

/-! ## Section 2.1: Tokens, Simplex `Δ(T)`, and Stateless LLM Abstraction -/

/-- A probability distribution over a finite token vocabulary `T`, representing an element of
    the probability simplex `Δ(T)`. -/
@[ext]
structure TokenDist (T : Type*) [Fintype T] where
  /-- Probability assigned to each token `t ∈ T`. -/
  prob : T → ℝ
  /-- All token probabilities are nonnegative. -/
  nonneg : ∀ t : T, 0 ≤ prob t
  /-- Token probabilities sum to `1`. -/
  sum_eq_one : ∑ t : T, prob t = 1

instance {T : Type*} [Fintype T] : CoeFun (TokenDist T) (fun _ => T → ℝ) :=
  ⟨TokenDist.prob⟩

/-- Subspace topology on `Δ(T)` inherited from `ℝ^T` (`T → ℝ`). -/
instance {T : Type*} [Fintype T] : TopologicalSpace (TokenDist T) :=
  TopologicalSpace.induced TokenDist.prob inferInstance

/-- Full-support condition on `Δ(T)`: every token has strictly positive probability (`p(t) > 0`),
    as produced by an untruncated softmax with finite logits (Section 3). -/
def HasFullSupport {T : Type*} [Fintype T] (p : TokenDist T) : Prop :=
  ∀ t : T, 0 < p.prob t

/-- Any token vocabulary admitting a probability distribution is nonempty. -/
lemma tokenDist_nonempty {T : Type*} [Fintype T] (p : TokenDist T) : Nonempty T := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsum := p.sum_eq_one
  simp at hsum

/-- `L₁` distance `‖p - q‖₁ = ∑_{t ∈ T} |p(t) - q(t)|` on `Δ(T)`. -/
def l1Dist {T : Type*} [Fintype T] (p q : TokenDist T) : ℝ :=
  ∑ t : T, |p.prob t - q.prob t|

/-- Total variation distance `(1/2) ‖p - q‖₁` on `Δ(T)`. -/
def tvDist {T : Type*} [Fintype T] (p q : TokenDist T) : ℝ :=
  (1 / 2 : ℝ) * l1Dist p q

/-- Membership in `T* = ⋃_{k=1}^K T^k`: nonempty token sequence of length at most `K`. -/
def IsValidContextSeq {T : Type*} (K : ℕ) (s : List T) : Prop :=
  1 ≤ s.length ∧ s.length ≤ K

/-- Append token `τ` to sequence `s` (`s ⊕ τ`), trimming to the length-`K` suffix when `|s ⊕ τ| > K`
    (Section 2.1). -/
def appendTrim {T : Type*} (K : ℕ) (s : List T) (τ : T) : List T :=
  let s' := s ++ [τ]
  s'.drop (s'.length - K)

/-- Stateless LLM mapping a context sequence to a next-token distribution `f : T* → Δ(T)`. -/
abbrev StatelessLLM (T : Type*) [Fintype T] := List T → TokenDist T

/-- Prompt-tuned proxy LLM `f_i(s) = f(s_0^i ⊕ s)` (Section 6). -/
def promptTunedLLM {T : Type*} [Fintype T] (f : StatelessLLM T) (s₀ : List T) : StatelessLLM T :=
  fun s => f (s₀ ++ s)

/-! ## Section 2.2: Token Auctions, Aggregation Rules, and Payment Functions -/

/-- Space of allowable scalar bids `ℚ₊` (nonnegative rational numbers, Section 2.2). -/
abbrev Bid := NNRat

/-- Profile of bids `b = (b_1, …, b_n) ∈ ℚ₊ⁿ` of the `n` strategic bidders. -/
abbrev BidProfile (n : ℕ) := Fin n → Bid

/-- Opposing bid profile `b_{-i} ∈ ℚ₊^{n-1}` excluding bidder `i`. -/
abbrev OpposingBids (n : ℕ) (i : Fin n) := {j : Fin n // j ≠ i} → Bid

/-- Profile of target distributions `p = (p_1, …, p_n) ∈ Δ(T)ⁿ`. -/
abbrev DistProfile (n : ℕ) (T : Type*) [Fintype T] := Fin n → TokenDist T

/-- Opposing target distributions `p_{-i} ∈ Δ(T)^{n-1}` excluding bidder `i`. -/
abbrev OpposingDists (n : ℕ) (T : Type*) [Fintype T] (i : Fin n) :=
  {j : Fin n // j ≠ i} → TokenDist T

/-- Reconstruct full bid profile `(b_i, b_{-i})` from own bid `b_i` and opposing bids `b_{-i}`. -/
def joinBid {n : ℕ} (i : Fin n) (b_i : Bid) (bOthers : OpposingBids n i) : BidProfile n :=
  fun j => if h : j = i then b_i else bOthers ⟨j, h⟩

/-- Extract opposing bids `b_{-i}` from a full bid profile `b`. -/
def restrictBids {n : ℕ} (i : Fin n) (b : BidProfile n) : OpposingBids n i :=
  fun j => b j.1

/-- Reconstruct full distribution profile `(p_i, p_{-i})`. -/
def joinDist {n : ℕ} {T : Type*} [Fintype T] (i : Fin n)
    (p_i : TokenDist T) (pOthers : OpposingDists n T i) : DistProfile n T :=
  fun j => if h : j = i then p_i else pOthers ⟨j, h⟩

/-- Extract opposing distributions `p_{-i}` from a full distribution profile `p`. -/
def restrictDists {n : ℕ} {T : Type*} [Fintype T] (i : Fin n)
    (p : DistProfile n T) : OpposingDists n T i :=
  fun j => p j.1

@[simp]
lemma joinBid_self {n : ℕ} (i : Fin n) (b_i : Bid) (bOthers : OpposingBids n i) :
    joinBid i b_i bOthers i = b_i := by
  simp [joinBid]

@[simp]
lemma joinBid_other {n : ℕ} (i : Fin n) (b_i : Bid) (bOthers : OpposingBids n i)
    (j : {j : Fin n // j ≠ i}) :
    joinBid i b_i bOthers j.1 = bOthers j := by
  simp [joinBid, j.2]

@[simp]
lemma restrictBids_joinBid {n : ℕ} (i : Fin n) (b_i : Bid) (bOthers : OpposingBids n i) :
    restrictBids i (joinBid i b_i bOthers) = bOthers := by
  ext j
  simp [restrictBids, joinBid, j.2]

@[simp]
lemma joinBid_restrictBids {n : ℕ} (i : Fin n) (b : BidProfile n) :
    joinBid i (b i) (restrictBids i b) = b := by
  ext j
  by_cases h : j = i
  · subst h; simp [joinBid]
  · simp [joinBid, restrictBids, h]

/-- Distribution aggregation function `q : ℚ₊ⁿ × Δ(T)ⁿ → Δ(T)`. -/
abbrev AggRule (n : ℕ) (T : Type*) [Fintype T] :=
  BidProfile n → DistProfile n T → TokenDist T

/-- Stage-independent per-token conditional pricing function `ζ_i : ℚ₊ⁿ × Δ(T)ⁿ × T → ℝ`. -/
abbrev PricingRule (n : ℕ) (T : Type*) [Fintype T] :=
  Fin n → BidProfile n → DistProfile n T → T → ℝ

/-- Expected payment function `z_i : ℚ₊ⁿ × Δ(T)ⁿ → ℝ`. -/
abbrev PaymentRule (n : ℕ) (T : Type*) [Fintype T] :=
  Fin n → BidProfile n → DistProfile n T → ℝ

/-- Expected payment induced by a per-token pricing function:
    `z_i(b, p) = E_{t ~ q(b, p)}[ζ_i(b, p, t)]`. -/
def expectedPaymentOfPricing {n : ℕ} {T : Type*} [Fintype T]
    (q : AggRule n T) (ζ : PricingRule n T) : PaymentRule n T :=
  fun i b p => ∑ t : T, (q b p).prob t * ζ i b p t

/-- A token auction mechanism `𝓜 = ⟨q, z⟩`. -/
structure TokenMechanism (n : ℕ) (T : Type*) [Fintype T] where
  /-- Next-token distribution aggregation rule. -/
  q : AggRule n T
  /-- Expected payment rule for each strategic bidder `i ∈ [n]`. -/
  z : PaymentRule n T

/-- Admissible payment rule: nonnegative expected payments and free zero bidding,
    `z_i(0, b_{-i}, p) = 0 ≤ z_i(b, p)` (Section 2.2). -/
def IsAdmissiblePayment {n : ℕ} {T : Type*} [Fintype T] (z : PaymentRule n T) : Prop :=
  (∀ i b p, 0 ≤ z i b p) ∧
  (∀ i bOthers p, z i (joinBid i 0 bOthers) p = 0)

/-! ## Section 3 & Appendices A–B: Information Theory, Linear & Log-Linear VCG -/

/-- Shannon entropy `H(p) = - ∑_{t ∈ T} p(t) ln p(t)` (with `0 ln 0 = 0`). -/
def shannonEntropy {T : Type*} [Fintype T] (p : TokenDist T) : ℝ :=
  - ∑ t : T, p.prob t * Real.log (p.prob t)

/-- Cross-entropy `H(p, q) = - ∑_{t ∈ T} p(t) ln q(t)`. -/
def crossEntropy {T : Type*} [Fintype T] (p q : TokenDist T) : ℝ :=
  - ∑ t : T, p.prob t * Real.log (q.prob t)

/-- Kullback–Leibler divergence `D_KL(p ‖ q) = ∑_{t ∈ T} p(t) ln(p(t) / q(t))`
    (with `0 ln(0 / q(t)) = 0` via `Real.log 0 = 0`). -/
def klDiv {T : Type*} [Fintype T] (p q : TokenDist T) : ℝ :=
  ∑ t : T, p.prob t * Real.log (p.prob t / q.prob t)

/-- Sum of strategic bids `∑_{i=1}^n b_i`. -/
def strategicBidSum {n : ℕ} (b : BidProfile n) : ℝ :=
  ∑ i : Fin n, (b i : ℝ)

/-- Sum of opposing strategic bids `∑_{j ≠ i} b_j`. -/
def opposingStrategicBidSum {n : ℕ} (i : Fin n) (b : BidProfile n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, (b j : ℝ)

/-- Total bid `B = b_0 + ∑_{i=1}^n b_i` including the non-strategic platform bidder `0`
    with fixed positive rational bid `b_0 > 0` (Section 3). -/
def totalBidWithPlatform {n : ℕ} (b₀ : Bid) (b : BidProfile n) : ℝ :=
  (b₀ : ℝ) + strategicBidSum b

/-- Total bid excluding strategic agent `i`: `B_{-i} = b_0 + ∑_{j ≠ i} b_j = B - b_i`. -/
def opposingBidWithPlatform {n : ℕ} (b₀ : Bid) (i : Fin n) (b : BidProfile n) : ℝ :=
  (b₀ : ℝ) + opposingStrategicBidSum i b

lemma totalBidWithPlatform_pos {n : ℕ} {b₀ : Bid} (hb₀ : 0 < b₀) (b : BidProfile n) :
    0 < totalBidWithPlatform b₀ b := by
  unfold totalBidWithPlatform strategicBidSum
  have hb₀' : (0 : ℝ) < (b₀ : ℝ) := by exact_mod_cast hb₀
  have hsum : (0 : ℝ) ≤ ∑ i : Fin n, (b i : ℝ) :=
    Finset.sum_nonneg (fun i _ => by positivity)
  linarith

/-- Forward-KL reported social welfare `SW(q) = - ∑_{j ∈ ℐ} b_j D_KL(p_j ‖ q)` (Section 3.1). -/
def forwardKLSocialWelfare {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (p₀ : TokenDist T) (b : BidProfile n) (p : DistProfile n T) (q : TokenDist T) : ℝ :=
  - ((b₀ : ℝ) * klDiv p₀ q + ∑ i : Fin n, (b i : ℝ) * klDiv (p i) q)

/-- Reverse-KL reported social welfare `SW_rev(q) = - ∑_{j ∈ ℐ} b_j D_KL(q ‖ p_j)`
    (Remark 3.3 & Appendix B). -/
def reverseKLSocialWelfare {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (p₀ : TokenDist T) (b : BidProfile n) (p : DistProfile n T) (q : TokenDist T) : ℝ :=
  - ((b₀ : ℝ) * klDiv q p₀ + ∑ i : Fin n, (b i : ℝ) * klDiv q (p i))

/-- Linear distribution aggregation rule `q_KL(b, p)(t) = (1 / B) ∑_{j ∈ ℐ} b_j p_j(t)`
    with platform bidder `(b_0, p_0)` (Lemma 3.1). -/
def linearAggRule {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) : AggRule n T :=
  fun b p =>
    let B := totalBidWithPlatform b₀ b
    have hB : 0 < B := totalBidWithPlatform_pos hb₀ b
    { prob := fun t => ((b₀ : ℝ) * p₀.prob t + ∑ i : Fin n, (b i : ℝ) * (p i).prob t) / B
      nonneg := fun t =>
        div_nonneg
          (add_nonneg (mul_nonneg (by positivity) (p₀.nonneg t))
            (Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) ((p i).nonneg t))))
          (le_of_lt hB)
      sum_eq_one := by
        have hBne : B ≠ 0 := ne_of_gt hB
        calc
          ∑ t : T, ((b₀ : ℝ) * p₀.prob t + ∑ i : Fin n, (b i : ℝ) * (p i).prob t) / B
              = (∑ t : T, ((b₀ : ℝ) * p₀.prob t + ∑ i : Fin n, (b i : ℝ) * (p i).prob t)) / B := by
                rw [← Finset.sum_div]
          _ = ((b₀ : ℝ) * (∑ t : T, p₀.prob t) +
                ∑ i : Fin n, (b i : ℝ) * (∑ t : T, (p i).prob t)) / B := by
                congr 1
                rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                congr 1
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i _
                rw [← Finset.mul_sum]
          _ = B / B := by
                simp [B, totalBidWithPlatform, strategicBidSum, p₀.sum_eq_one,
                  (fun i => (p i).sum_eq_one)]
          _ = 1 := div_self hBne }

/-- Linear aggregation rule without a platform bidder (`b_0 = 0`), falling back to `pDefault`
    only when all strategic bids are zero (`∑_i b_i = 0`). -/
def linearAggNoPlatform {n : ℕ} {T : Type*} [Fintype T] (pDefault : TokenDist T) : AggRule n T :=
  fun b p =>
    let B := strategicBidSum b
    if hB : 0 < B then
      { prob := fun t => (∑ i : Fin n, (b i : ℝ) * (p i).prob t) / B
        nonneg := fun t =>
          div_nonneg
            (Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) ((p i).nonneg t)))
            (le_of_lt hB)
        sum_eq_one := by
          have hBne : B ≠ 0 := ne_of_gt hB
          calc
            ∑ t : T, (∑ i : Fin n, (b i : ℝ) * (p i).prob t) / B
                = (∑ i : Fin n, (b i : ℝ) * (∑ t : T, (p i).prob t)) / B := by
                  rw [← Finset.sum_div, Finset.sum_comm]
                  congr 1
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [← Finset.mul_sum]
            _ = B / B := by simp [B, strategicBidSum, (fun i => (p i).sum_eq_one)]
            _ = 1 := div_self hBne }
    else pDefault

/-- Leaving-out-`i` linear aggregate `q^*_{-i} = q_KL(0, b_{-i}, p)` (Theorem 3.2). -/
def linearAggWithout {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
    (i : Fin n) (b : BidProfile n) (p : DistProfile n T) : TokenDist T :=
  linearAggRule b₀ hb₀ p₀ (joinBid i 0 (restrictBids i b)) p

/-- Closed-form forward-KL VCG payment `z_i(b, p) = B_{-i} D_KL(q^*_{-i} ‖ q_KL(b, p))`
    (Theorem 3.2). -/
def forwardKLVCGPayment {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) : PaymentRule n T :=
  fun i b p =>
    opposingBidWithPlatform b₀ i b *
      klDiv (linearAggWithout b₀ hb₀ p₀ i b p) (linearAggRule b₀ hb₀ p₀ b p)

/-- Forward-KL VCG token auction mechanism `𝓜_KL = ⟨q_KL, z⟩` (Theorem 3.2). -/
def forwardKLVCGMechanism {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) : TokenMechanism n T :=
  { q := linearAggRule b₀ hb₀ p₀
    z := forwardKLVCGPayment b₀ hb₀ p₀ }

/-- Unnormalized log-linear score `(1 / B) ∑_{j ∈ ℐ} b_j ln p_j(t)` (Remark 3.3 & Lemma B.1). -/
def logLinearScore {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (p₀ : TokenDist T) (b : BidProfile n) (p : DistProfile n T) (t : T) : ℝ :=
  ((b₀ : ℝ) * Real.log (p₀.prob t) + ∑ i : Fin n, (b i : ℝ) * Real.log ((p i).prob t)) /
    totalBidWithPlatform b₀ b

/-- Log-partition normalization term `C(b, p) = ln ∑_{t ∈ T} exp((1 / B) ∑_{j ∈ ℐ} b_j ln p_j(t))`
    (Lemma B.1). -/
def logLinearNormConst {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (p₀ : TokenDist T) (b : BidProfile n) (p : DistProfile n T) : ℝ :=
  Real.log (∑ t : T, Real.exp (logLinearScore b₀ p₀ b p t))

/-- Log-linear (geometric) aggregation rule `q̄_KL(b, p)` with platform bidder `(b_0, p_0)`
    (Remark 3.3 & Lemma B.1). -/
def logLinearAggRule {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (_hb₀ : 0 < b₀) (p₀ : TokenDist T) : AggRule n T :=
  fun b p =>
    haveI : Nonempty T := tokenDist_nonempty p₀
    let u := logLinearScore b₀ p₀ b p
    let Z := ∑ s : T, Real.exp (u s)
    have hZ : 0 < Z := Finset.sum_pos (fun s _ => Real.exp_pos (u s)) Finset.univ_nonempty
    { prob := fun t => Real.exp (u t - Real.log Z)
      nonneg := fun t => le_of_lt (Real.exp_pos _)
      sum_eq_one := by
        have hZne : Z ≠ 0 := ne_of_gt hZ
        calc
          ∑ t : T, Real.exp (u t - Real.log Z)
              = ∑ t : T, Real.exp (u t) / Z := by
                apply Finset.sum_congr rfl
                intro t _
                rw [Real.exp_sub, Real.exp_log hZ]
          _ = Z / Z := by rw [← Finset.sum_div]
          _ = 1 := div_self hZne }

/-- Log-linear aggregation rule without a platform bidder (`b_0 = 0`), falling back to `pDefault`
    when `∑_i b_i = 0` (used in Example B.3). -/
def logLinearAggNoPlatform {n : ℕ} {T : Type*} [Fintype T] (pDefault : TokenDist T) : AggRule n T :=
  fun b p =>
    haveI : Nonempty T := tokenDist_nonempty pDefault
    let B := strategicBidSum b
    if hB : 0 < B then
      let u : T → ℝ := fun t => (∑ i : Fin n, (b i : ℝ) * Real.log ((p i).prob t)) / B
      let Z := ∑ s : T, Real.exp (u s)
      have hZ : 0 < Z := Finset.sum_pos (fun s _ => Real.exp_pos (u s)) Finset.univ_nonempty
      { prob := fun t => Real.exp (u t - Real.log Z)
        nonneg := fun t => le_of_lt (Real.exp_pos _)
        sum_eq_one := by
          have hZne : Z ≠ 0 := ne_of_gt hZ
          calc
            ∑ t : T, Real.exp (u t - Real.log Z)
                = ∑ t : T, Real.exp (u t) / Z := by
                  apply Finset.sum_congr rfl
                  intro t _
                  rw [Real.exp_sub, Real.exp_log hZ]
            _ = Z / Z := by rw [← Finset.sum_div]
            _ = 1 := div_self hZne }
    else pDefault

/-- Leaving-out-`i` log-linear aggregate `q̄^*_{-i} = q̄_KL(0, b_{-i}, p)` (Theorem B.2). -/
def logLinearAggWithout {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T)
    (i : Fin n) (b : BidProfile n) (p : DistProfile n T) : TokenDist T :=
  logLinearAggRule b₀ hb₀ p₀ (joinBid i 0 (restrictBids i b)) p

/-- Closed-form reverse-KL VCG payment `z_i(b, p) = B_{-i} D_KL(q̄_KL(b, p) ‖ q̄^*_{-i})`
    (Theorem B.2). -/
def reverseKLVCGPayment {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) : PaymentRule n T :=
  fun i b p =>
    opposingBidWithPlatform b₀ i b *
      klDiv (logLinearAggRule b₀ hb₀ p₀ b p) (logLinearAggWithout b₀ hb₀ p₀ i b p)

/-- Reverse-KL VCG token auction mechanism `𝓜̄_KL = ⟨q̄_KL, z̄⟩` (Theorem B.2). -/
def reverseKLVCGMechanism {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) : TokenMechanism n T :=
  { q := logLinearAggRule b₀ hb₀ p₀
    z := reverseKLVCGPayment b₀ hb₀ p₀ }

/-! ## Section 4 & Appendix C: Partial Orders, Monotonicity, Consistency & Strategic Equivalence -/

/-- Profile of agent partial preference relations `⪰_i` on `Δ(T)`. -/
abbrev AgentPrefs (n : ℕ) (T : Type*) [Fintype T] :=
  Fin n → DistProfile n T → TokenDist T → TokenDist T → Prop

/-- Asymmetric strict preference `q ≻ q'` induced by weak preference `⪰`: `q ⪰ q' ∧ ¬(q' ⪰ q)`. -/
def strictPref {α : Type*} (rel : α → α → Prop) (x y : α) : Prop :=
  rel x y ∧ ¬ rel y x

/-- Reflexivity and transitivity of every agent's preference relation `⪰_i`. -/
def IsPreorderPrefs {n : ℕ} {T : Type*} [Fintype T] (pref : AgentPrefs n T) : Prop :=
  ∀ (i : Fin n) (p : DistProfile n T),
    (∀ q : TokenDist T, pref i p q q) ∧
    (∀ q₁ q₂ q₃ : TokenDist T, pref i p q₁ q₂ → pref i p q₂ q₃ → pref i p q₁ q₃)

/-- Multi-utility preference relation induced by a family `V` of valuation functions on `Δ(T)`:
    `q ⪰ q' ↔ ∀ v ∈ V, v(q) ≥ v(q')` (Section 4). -/
def multiUtilityPref {T : Type*} [Fintype T]
    (V : Set (TokenDist T → ℝ)) (q q' : TokenDist T) : Prop :=
  ∀ v ∈ V, v q' ≤ v q

/-- Definition 4.1 (`def:mono-pay`): Payment Monotonicity. -/
def IsPaymentMonotone {n : ℕ} {T : Type*} [Fintype T]
    (pref : AgentPrefs n T) (M : TokenMechanism n T) : Prop :=
  ∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i) (b_i b'_i : Bid),
    M.z i (joinBid i b'_i bOthers) p ≤ M.z i (joinBid i b_i bOthers) p ↔
      pref i p (M.q (joinBid i b_i bOthers) p) (M.q (joinBid i b'_i bOthers) p)

/-- Definition 4.2 (`def:consistent-aggregate`): Consistent Aggregation. -/
def IsConsistentAgg {n : ℕ} {T : Type*} [Fintype T]
    (pref : AgentPrefs n T) (q : AggRule n T) : Prop :=
  ∀ (i : Fin n) (p : DistProfile n T) (b_i b'_i : Bid),
    (∃ bOthers : OpposingBids n i,
      strictPref (pref i p) (q (joinBid i b_i bOthers) p) (q (joinBid i b'_i bOthers) p)) →
    ∀ b'Others : OpposingBids n i,
      pref i p (q (joinBid i b_i b'Others) p) (q (joinBid i b'_i b'Others) p)

/-- Definition 4.3 (`def:mon-agg`): Monotone Aggregation Function. -/
def IsMonotoneAgg {n : ℕ} {T : Type*} [Fintype T]
    (pref : AgentPrefs n T) (q : AggRule n T) : Prop :=
  ∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i) (b_i b'_i : Bid),
    b'_i ≤ b_i →
      pref i p (q (joinBid i b_i bOthers) p) (q (joinBid i b'_i bOthers) p)

/-- Coordinatewise application `π(b) = (π_1(b_1), …, π_n(b_n))` of bid strategy mappings. -/
def applyStrategyProfile {n : ℕ} (π : Fin n → Bid → Bid) (b : BidProfile n) : BidProfile n :=
  fun i => π i (b i)

/-- Definition 4.4: Strategic Equivalence of mechanisms `𝓜 = ⟨q, z⟩` and `𝓜̃ = ⟨q̃, z̃⟩`. -/
def StrategicallyEquivalent {n : ℕ} {T : Type*} [Fintype T]
    (M Mtilde : TokenMechanism n T) : Prop :=
  ∀ p : DistProfile n T, ∃ π : Fin n → Bid → Bid,
    ∀ b : BidProfile n,
      M.q b p = Mtilde.q (applyStrategyProfile π b) p ∧
      (∀ i : Fin n, M.z i b p = Mtilde.z i (applyStrategyProfile π b) p)

/-- Achievable distribution menu `Q_i(b_{-i}, p) = {q(b_i, b_{-i}, p) : b_i ∈ ℚ₊}`
    (Lemmas 4.6 & 4.7). -/
def achievableMenu {n : ℕ} {T : Type*} [Fintype T]
    (q : AggRule n T) (i : Fin n) (bOthers : OpposingBids n i) (p : DistProfile n T) :
    Set (TokenDist T) :=
  Set.range (fun b_i : Bid => q (joinBid i b_i bOthers) p)

/-- Total comparability of `⪰_i` on `Q_i(b_{-i}, p)` with zero-bid outcome weakly least
    (Lemmas 4.6 & 4.7). -/
def MenuTotallyOrderedFromZero {n : ℕ} {T : Type*} [Fintype T]
    (pref : AgentPrefs n T) (q : AggRule n T) : Prop :=
  ∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i),
    (∀ q₁ ∈ achievableMenu q i bOthers p, ∀ q₂ ∈ achievableMenu q i bOthers p,
      pref i p q₁ q₂ ∨ pref i p q₂ q₁) ∧
    (∀ b_i : Bid, pref i p (q (joinBid i b_i bOthers) p) (q (joinBid i 0 bOthers) p))

/-! ## Section 5 & Appendices D–E: Robust Preferences, Stable Sampling & Second-Price Auctions -/

/-- Definition 5.1 (`def:obvious-prefer`): Robust Preferences over Distributions. -/
def RobustPref {T : Type*} [Fintype T] (target : TokenDist T) (q q' : TokenDist T) : Prop :=
  (∀ t : T, |q.prob t - target.prob t| ≤ |q'.prob t - target.prob t|) ∧
  (∀ t : T, 0 ≤ (q.prob t - target.prob t) * (q'.prob t - target.prob t))

/-- Strict robust preference `q ≻_i q'` (`q ⪰_i q'` and `q ≠ q'`, Definition 5.1). -/
def RobustStrictPref {T : Type*} [Fintype T] (target : TokenDist T) (q q' : TokenDist T) : Prop :=
  RobustPref target q q' ∧ q ≠ q'

/-- Private-values `AgentPrefs` where each agent `i` uses `RobustPref (p i)`. -/
def robustAgentPrefs (n : ℕ) (T : Type*) [Fintype T] : AgentPrefs n T :=
  fun i p q q' => RobustPref (p i) q q'

/-- Single-agent slice `b_i ↦ q(b_i)` monotone under `RobustPref target`. -/
def IsSingleAgentRobustMonotone {T : Type*} [Fintype T]
    (q : Bid → TokenDist T) (target : TokenDist T) : Prop :=
  ∀ b_i b'_i : Bid, b'_i ≤ b_i → RobustPref target (q b_i) (q b'_i)

/-- Undersampled tokens `T⁺ = {t ∈ T : q_t(0) ≤ p_i(t)}` (Section 5.1). -/
def undersampledTokens {T : Type*} [Fintype T]
    (q : Bid → TokenDist T) (target : TokenDist T) : Set T :=
  {t : T | (q 0).prob t ≤ target.prob t}

/-- Oversampled tokens `T⁻ = {t ∈ T : q_t(0) > p_i(t)}` (Section 5.1). -/
def oversampledTokens {T : Type*} [Fintype T]
    (q : Bid → TokenDist T) (target : TokenDist T) : Set T :=
  {t : T | target.prob t < (q 0).prob t}

/-- Valid randomized sampling implementation `σ : ℚ₊ × R → T` of `q : ℚ₊ → Δ(T)` (Section 5.1). -/
def IsValidSampler {T : Type*} [Fintype T] {R : Type*} [MeasurableSpace R]
    (μ : Measure R) [IsProbabilityMeasure μ]
    (q : Bid → TokenDist T) (σ : Bid → R → T) : Prop :=
  (∀ (b_i : Bid) (t : T), MeasurableSet {r : R | σ b_i r = t}) ∧
  (∀ (b_i : Bid) (t : T), μ.real {r : R | σ b_i r = t} = (q b_i).prob t)

/-- Definition 5.4 (`def:stable-sampler`): Stable Sampling implementation. -/
def IsStableSampler {T : Type*} [Fintype T] {R : Type*} [MeasurableSpace R]
    (μ : Measure R) [IsProbabilityMeasure μ]
    (q : Bid → TokenDist T) (target : TokenDist T) (σ : Bid → R → T) : Prop :=
  IsValidSampler μ q σ ∧
  ∀ r : R,
    (∃ t₀ : T, ∀ b_i : Bid, σ b_i r = t₀) ∨
    (∃ u_r ∈ undersampledTokens q target,
     ∃ o_r ∈ oversampledTokens q target,
     ∃ W_r : Set Bid,
       IsUpperSet W_r ∧ W_r.Nonempty ∧ W_r ≠ Set.univ ∧
       ∀ b_i : Bid, σ b_i r = if b_i ∈ W_r then u_r else o_r)

/-- Winning set `W_r = {b_i ∈ ℚ₊ : σ(b_i, r) ≠ σ(0, r)}` of seed `r` (Section 5.2). -/
def samplerWinningSet {T : Type*} {R : Type*} (σ : Bid → R → T) (r : R) : Set Bid :=
  {b_i : Bid | σ b_i r ≠ σ 0 r}

/-- Critical price `θ_r = inf_{ℝ} W_r` on switching paths, and `0` on constant paths (Section 5.2). -/
def criticalPrice {T : Type*} {R : Type*} (σ : Bid → R → T) (r : R) : ℝ :=
  if (samplerWinningSet σ r).Nonempty then
    sInf ((fun b : Bid => (b : ℝ)) '' samplerWinningSet σ r)
  else 0

/-- Ex-post second-price charge on seed `r` at bid `b_i`: `θ_r` if `b_i ∈ W_r`, else `0`
    (Section 5.2). -/
def secondPriceCharge {T : Type*} {R : Type*} (σ : Bid → R → T) (b_i : Bid) (r : R) : ℝ :=
  if b_i ∈ samplerWinningSet σ r then criticalPrice σ r else 0

/-- Expected second-price payment `E_r[secondPriceCharge(σ, b_i, r)]` (Section 5.2). -/
def secondPriceExpectedPayment {T : Type*} {R : Type*} [MeasurableSpace R]
    (μ : Measure R) (σ : Bid → R → T) (b_i : Bid) : ℝ :=
  ∫ r, secondPriceCharge σ b_i r ∂μ

/-- Canonical nonincreasing extension of `b' ↦ ‖q(b') - p_i‖₁` from `ℚ₊` to `ℝ`
    (Proposition 5.6 & Footnote 8). -/
def l1DistRealExt {T : Type*} [Fintype T] (q : Bid → TokenDist T) (target : TokenDist T) (x : ℝ) : ℝ :=
  if x < 0 then l1Dist (q 0) target
  else sInf ((fun b : Bid => l1Dist (q b) target) '' {b : Bid | (b : ℝ) ≤ x})

/-- Canonical nondecreasing extension of `b' ↦ q_t(b')` (for `t ∈ T⁺`) from `ℚ₊` to `ℝ`. -/
def tokenProbUnderExt {T : Type*} [Fintype T] (q : Bid → TokenDist T) (t : T) (x : ℝ) : ℝ :=
  if x < 0 then (q 0).prob t
  else sSup ((fun b : Bid => (q b).prob t) '' {b : Bid | (b : ℝ) ≤ x})

/-- Myerson-style total-variation integral formula from Proposition 5.6:
    `(1/2) ∫_0^{b_i} [‖q(b') - p_i‖₁ - ‖q(b_i) - p_i‖₁] db'`. -/
def myersonTVPayment {T : Type*} [Fintype T]
    (q : Bid → TokenDist T) (target : TokenDist T) (b_i : Bid) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..(b_i : ℝ), (l1DistRealExt q target x - l1Dist (q b_i) target)

/-- Canonical sampler-independent second-price conditional per-token pricing function
    `ζ_i : ℚ₊ⁿ × Δ(T)ⁿ × T → ℝ` (Section 2.2 & Proposition 5.6): for undersampled tokens `t ∈ T⁺`
    with `q_t(b, p) > 0`, `ζ_i(b, p, t) = (1 / q_t(b, p)) ∫_0^{b_i} [q_t(b, p) - q_t(b', b_{-i}, p)] db'`,
    and `0` otherwise (including all oversampled tokens `t ∈ T⁻` and zero-probability tokens). -/
def myersonTokenPricing {n : ℕ} {T : Type*} [Fintype T] (q : AggRule n T) : PricingRule n T :=
  fun i b p t =>
    let qSlice : Bid → TokenDist T := fun b' => q (joinBid i b' (restrictBids i b)) p
    if t ∈ undersampledTokens qSlice (p i) ∧ 0 < (q b p).prob t then
      (∫ x in (0 : ℝ)..(b i : ℝ), ((q b p).prob t - tokenProbUnderExt qSlice t x)) / (q b p).prob t
    else 0

/-- Closed-form expected second-price payment for the linear aggregation rule `q_KL`
    with platform bidder `(b_0, p_0)` (`B_{-i} > 0`, Corollary 5.7). -/
def linearSecondPriceClosedFormWithPlatform {n : ℕ} {T : Type*} [Fintype T]
    (b₀ : Bid) (hb₀ : 0 < b₀) (p₀ : TokenDist T) : PaymentRule n T :=
  fun i b p =>
    if (b i : ℝ) > 0 then
      let B := totalBidWithPlatform b₀ b
      let Bminus := opposingBidWithPlatform b₀ i b
      let qOut := linearAggRule b₀ hb₀ p₀ b p
      let qWithout := linearAggWithout b₀ hb₀ p₀ i b p
      Bminus * l1Dist qWithout qOut *
        ((B / (2 * (b i : ℝ))) * Real.log (B / Bminus) - (1 / 2 : ℝ))
    else 0

/-- Closed-form expected second-price payment for the general linear aggregation rule
    (covering both `B_{-i} > 0` and `B_{-i} = 0`, Corollary 5.7). -/
def linearSecondPriceClosedFormGeneral {n : ℕ} {T : Type*} [Fintype T]
    (pDefault : TokenDist T) : PaymentRule n T :=
  fun i b p =>
    let bi := (b i : ℝ)
    let Bminus := opposingStrategicBidSum i b
    if bi > 0 ∧ Bminus > 0 then
      let B := bi + Bminus
      let qOut := linearAggNoPlatform pDefault b p
      let qWithout := linearAggNoPlatform pDefault (joinBid i 0 (restrictBids i b)) p
      Bminus * l1Dist qWithout qOut *
        ((B / (2 * bi)) * Real.log (B / Bminus) - (1 / 2 : ℝ))
    else 0

/-- Universally stable sampling implementation `σ^univ : ℚ₊ⁿ × R → T` (Section 5.2 & Appendix E). -/
def IsUniversallyStableSampler {n : ℕ} {T : Type*} [Fintype T] {R : Type*} [MeasurableSpace R]
    (μ : Measure R) [IsProbabilityMeasure μ]
    (q : AggRule n T) (p : DistProfile n T) (σUniv : BidProfile n → R → T) : Prop :=
  (∀ (b : BidProfile n) (t : T), MeasurableSet {r : R | σUniv b r = t}) ∧
  (∀ (b : BidProfile n) (t : T), μ.real {r : R | σUniv b r = t} = (q b p).prob t) ∧
  (∀ (i : Fin n) (bOthers : OpposingBids n i),
    IsStableSampler μ (fun b_i => q (joinBid i b_i bOthers) p) (p i)
      (fun b_i r => σUniv (joinBid i b_i bOthers) r))

/-! ## Section 6.2: Perplexity of Generated Token Sequences -/

/-- Perplexity `PPL_i(s_m) = exp(- (1/m) ∑_{k=1}^m ln p_{i,k}(τ_k))` evaluated against
    agent `i`'s sequence of next-token distributions (Section 6.2). -/
def sequencePerplexity {T : Type*} [Fintype T] {m : ℕ}
    (pSeq : Fin m → TokenDist T) (τ : Fin m → T) : ℝ :=
  Real.exp (- (1 / (m : ℝ)) * ∑ k : Fin m, Real.log ((pSeq k).prob (τ k)))

end

end TokenAuctions
