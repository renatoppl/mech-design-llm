import TokenAuctions.Defs
import TokenAuctions.VCG
import TokenAuctions.RevelationPrinciple
import TokenAuctions.StableSampling
import TokenAuctions.SecondPrice

/-!
# Mechanism Design for Large Language Models: Token Auctions with Proxy Bidders

Root module importing the complete Lean 4 formalization:

- `TokenAuctions.Defs`: Shared definitions across Sections 2–6 and Appendices A–E.
- `TokenAuctions.VCG`: Section 2.1, Section 3, Appendices A–B (Lemma B.1, Theorem B.2), and
  Section 6.2 (Forward-KL and Reverse-KL VCG benchmarks and sequence perplexity).
- `TokenAuctions.RevelationPrinciple`: Section 4 and Appendix C (Partial preference orders,
  Debreu countable rational utility representation, lexicographic counterexample, payment
  monotonicity characterization, consistent realignment, and the Revelation Principle).
- `TokenAuctions.StableSampling`: Section 5.1, Example B.3, Appendix D.1, and Appendix E
  (Robust preferences, linear-rule monotonicity vs. log-linear non-monotonicity, coordinatewise
  characterization, stable sampling existence on `[0, 1]²`, and 4-token / 3-token impossibility
  of universally stable sampling).
- `TokenAuctions.SecondPrice`: Section 5.2 and Appendix D.2 (Second-price token auction expected
  payment integral formula, Footnotes 7 & 8, closed-form linear-rule second-price payments, and
  comparison with forward-KL VCG payments).
-/
