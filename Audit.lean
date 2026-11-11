import TokenAuctions

/-!
# Axiom Audit

Run from the package root after `lake build`:

    lake env lean Audit.lean

Each `#print axioms` line below reports the axioms that the declaration depends on. Every
declaration depends only on a subset of Lean's three standard classical axioms (`propext`,
`Classical.choice`, `Quot.sound`); in particular, `sorryAx` never appears.

This file is not part of the `TokenAuctions` library, so `lake build` does not compile it.
-/

open TokenAuctions

-- Section 2.1, Section 3, Appendices A–B & Section 6.2 (TokenAuctions.VCG)
#print axioms sec_2_1_appendTrim_valid
#print axioms lem_gibbs_inequality
#print axioms lem_3_1_kl_linear_rule
#print axioms thm_3_2_kl_vcg
#print axioms lem_B_1_reverse_kl_rule
#print axioms thm_B_2_reverse_kl_vcg
#print axioms sec_6_2_perplexity_pos
#print axioms fn_9_perplexity_cross_entropy

-- Section 4 & Appendix C (TokenAuctions.RevelationPrinciple)
#print axioms sec_4_multiUtility_closed_preorder
#print axioms def_4_1_equal_outcome_equal_payment
#print axioms lem_C_1_debreu_countable_utility
#print axioms rem_C_2_lexicographic_no_utility
#print axioms lem_4_6_payment_monotone_iff_total_order
#print axioms lem_4_7_consistent_realignment
#print axioms thm_4_5_revelation_principle

-- Section 5.1, Example B.3, Appendix D.1 & Appendix E (TokenAuctions.StableSampling)
#print axioms def_5_1_robust_pref_partial_order
#print axioms rem_5_2_linear_monotone_consistent
#print axioms ex_B_3_log_linear_nonmonotone
#print axioms lem_5_3_monotone_coord_iff
#print axioms lem_5_3_monotone_agg_iff
#print axioms sec_5_1_two_token_stable_sampler
#print axioms thm_5_5_stable_sampling_exists
#print axioms ex_E_1_four_token_no_universal_stable
#print axioms ex_E_2_three_token_no_universal_stable

-- Section 5.2 & Appendix D.2 (TokenAuctions.SecondPrice)
#print axioms prop_5_6_second_price_payment
#print axioms prop_5_6_token_pricing_decomp
#print axioms fn_7_second_price_payment_monotone
#print axioms cor_5_7_linear_closed_form_with_platform
#print axioms cor_5_7_linear_closed_form_general
#print axioms cor_5_7_right_continuity_at_zero
#print axioms cor_5_7_linear_stable_sampler_payment
#print axioms rem_5_8_zero_payment_iff
#print axioms rem_5_8_vcg_ne_second_price
