import FTPaper

/-! Run `lake env lean CheckAxioms.lean`: every theorem must depend only on the three
standard axioms `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`). -/

-- Lemma B (two-application repair), FTPaper/Repair.lean
#print axioms FTPaper.output_eq
#print axioms FTPaper.exists_table
#print axioms FTPaper.repair_correct
#print axioms FTPaper.separatesOn_vandermonde
#print axioms FTPaper.exists_table_vandermonde
-- Lemma A (window predictor, Horner), FTPaper/Predictor.lean
#print axioms FTPaper.parity
#print axioms FTPaper.count_eq
#print axioms FTPaper.exists_window_poly
#print axioms FTPaper.aeval_diag
#print axioms FTPaper.predictor_correct
#print axioms FTPaper.card_window_complement
#print axioms FTPaper.horner_eq
#print axioms FTPaper.horner_stages
-- Lemma C (feedback cost) and Theorem 1 (cost part), FTPaper/Feedback.lean
#print axioms FTPaper.feedbackCost_eq
#print axioms FTPaper.feedbackCost_div_le
#print axioms FTPaper.one_level_cost
-- Theorem 3(3) (charged rectangles), FTPaper/Limits.lean
#print axioms FTPaper.charged_card_ge
#print axioms FTPaper.charged_card_ge_pow
-- Theorem 1, step 2 (Hoeffding window) and explicit constant, FTPaper/Window.lean
#print axioms FTPaper.sum_exp_weight
#print axioms FTPaper.card_tail_le
#print axioms FTPaper.window_fraction
#print axioms FTPaper.mem_window_iff
#print axioms FTPaper.window_width_le
#print axioms FTPaper.log_eighty_le
#print axioms FTPaper.theorem1_bound
-- Corollary R2 (routing parameters), FTPaper/Routing.lean
#print axioms FTPaper.routing_alphabet
#print axioms FTPaper.routing_exponent_le
-- Theorem 3(2) (batching), FTPaper/Batching.lean, in OpenAI's circuit model
#print axioms FTPaper.split_step
#print axioms FTPaper.batching_sufficient
#print axioms FTPaper.batching_necessary
-- Lemma R1 against OpenAI's actual routing, FTPaper/RoutingOAI.lean
#print axioms FTPaper.routing_arith
#print axioms FTPaper.lemmaR1_pencil
#print axioms FTPaper.stageBound_le
#print axioms FTPaper.oai_template_cost
-- End-to-end template in OpenAI's routing (rational plans), FTPaper/Q*.lean
#print axioms FTPaper.QPlan.applyAt_horner
#print axioms FTPaper.QPlan.calls_horner
#print axioms FTPaper.QPlan.applyAt_twoPass
#print axioms FTPaper.QPlan.frequency_horner
#print axioms FTPaper.QPlan.frequency_spectralTable
#print axioms FTPaper.QPlan.frequency_batch
#print axioms FTPaper.QPlan.calls_batch
#print axioms FTPaper.QPlan.correct_of_product
#print axioms FTPaper.frequency_stage
#print axioms FTPaper.frequency_ourBatch
#print axioms FTPaper.template_correct
#print axioms FTPaper.template_calls
#print axioms FTPaper.template_end_to_end
#print axioms FTPaper.outside_card_le
#print axioms FTPaper.checks_le
#print axioms FTPaper.theorem1_direct
-- Feedback conversions inside the plan language (Lemma C at the plan level), FTPaper/QFeedback.lean
#print axioms FTPaper.QPlan.rowAction_of_correct
#print axioms FTPaper.QPlan.correct_restrict
#print axioms FTPaper.QPlan.frequency_spectralVia
#print axioms FTPaper.QPlan.frequency_batchWith
#print axioms FTPaper.QPlan.correct_wrapOuter
#print axioms FTPaper.frequency_batchVia
#print axioms FTPaper.calls_batchVia
#print axioms FTPaper.correct_fbPlan
#print axioms FTPaper.calls_fbPlan_succ
#print axioms FTPaper.calls_fbPlan_le
#print axioms FTPaper.outside_window
#print axioms FTPaper.window_width
#print axioms FTPaper.theorem1_feedback
#print axioms FTPaper.theorem1
#print axioms FTPaper.axes_eq
#print axioms FTPaper.theorem1_explicit
-- Theorem 1 with the routing parameters of Corollary R2, FTPaper/QRouted.lean
#print axioms FTPaper.rho_le_routed
#print axioms FTPaper.theorem1_routed
-- From plans to circuits, FTPaper/QCircuit.lean and FTPaper/QUpper.lean
#print axioms FTPaper.Circ.child_eq
#print axioms FTPaper.Circ.program_plan
#print axioms FTPaper.Circ.program_qplan
#print axioms FTPaper.Circ.target_eq
#print axioms FTPaper.Circ.program_batch
#print axioms FTPaper.Circ.kernelBatch_of_correct
#print axioms FTPaper.walsh_bound_of_plan
#print axioms FTPaper.saving_of_routing
#print axioms FTPaper.walsh_upper
-- Free endpoint plans and explicit local cost, FTPaper/Free/*.lean, LocalCost*.lean
#print axioms OAI.Computability.NearSquareRoot.KernelPass.RealizesF.partialChart
#print axioms OAI.Computability.NearSquareRoot.KernelPass.RealizesF.geometricEndpoints
#print axioms OAI.Computability.NearSquareRoot.KernelPass.normalizedFree_factorF
#print axioms OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary.block_geometricPencilF
#print axioms OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary.calls_geometricPencilF
#print axioms FTPaper.lemmaR1_pencilF
#print axioms FTPaper.Circ.planFree_pencil
#print axioms FTPaper.Circ.planFree_geometricPencilF
#print axioms FTPaper.Circ.card_free_le
#print axioms FTPaper.Circ.qfree_fbPlan_le
-- The explicit rate, FTPaper/ExplicitRecursion.lean and FTPaper/ExplicitRate.lean
#print axioms OAI.LinearAlgebra.FiniteFourier.primeTransform_bound_paddedX
#print axioms FTPaper.walsh_bound_explicit
#print axioms FTPaper.paddedX_le
#print axioms FTPaper.xT_le
#print axioms FTPaper.xsaving
#print axioms FTPaper.walsh_explicit_rate
#print axioms FTPaper.walsh_explicit_rate_k
#print axioms FTPaper.walsh_rate_asymptotic
-- The per-level floor, conditional on the lower bound, FTPaper/Floor.lean
#print axioms FTPaper.template_floor
-- No dyadic window predictor (paper: Proposition 7.3), FTPaper/Dyadic.lean
#print axioms FTPaper.six_dvd_third_diff
#print axioms FTPaper.no_dyadic_window
-- OpenAI's stage count (paper: Proposition 1.4), FTPaper/Compare.lean
#print axioms FTPaper.two_radius_le_degree
#print axioms FTPaper.oai_stages_ge
#print axioms FTPaper.oai_stages_ge_real
-- Theorem 1.5(3), pairing form, FTPaper/Limits.lean
#print axioms FTPaper.charged_card_ge_pairing
