-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Allocation
import Shield.Balance
import Shield.LimbBalance
import Shield.Emit
import Shield.Publics
import Shield.Sponge
import Shield.Budget
import Shield.Canon
import Shield.ClientData
import Shield.Codec
import Shield.Combine
import Shield.Cost
import Shield.Curve
import Shield.Deep
import Shield.Domain
import Shield.Field
import Shield.Fixture
import Shield.Fold
import Shield.FoldPoly
import Shield.Poly
import Shield.Tie
import Shield.Gas
import Shield.Grind
import Shield.Hash
import Shield.Header
import Shield.Horner
import Shield.Identity
import Shield.Imt
import Shield.Index
import Shield.Intent
import Shield.Key
import Shield.Ladder
import Shield.Layout
import Shield.Live
import Shield.Manifest
import Shield.Merkle
import Shield.Note
import Shield.Nullifier
import Shield.Params
import Shield.Phase
import Shield.Pieces
import Shield.Points
import Shield.Poseidon
import Shield.Proof
import Shield.Quad
import Shield.Radix
import Shield.Read.Shape
import Shield.Recursion
import Shield.Roots
import Shield.Rounds
import Shield.Search
import Shield.Session
import Shield.Settlement
import Shield.Soundness
import Shield.Spend
import Shield.Stack
import Shield.Stop
import Shield.Tokens
import Shield.Trace
import Shield.Transcript
import Shield.Walk
import Shield.Wire
import Shield.Wiring
import Shield.Wrap

/-!
What each headline theorem depends on.

`#print axioms` writes the dependency of a theorem into the build log.
`propext`, `Classical.choice` and `Quot.sound` are Lean's own foundation and
are expected. Any fourth name is an assumption nobody agreed to, and the
marker Lean emits for an admitted proof fails the build in CI rather than
being left to a reader to notice.
-/

#print axioms Shield.Hash.the_assumptions_are_satisfiable
#print axioms Shield.Note.the_leaf_binds_the_escrowed_value
#print axioms Shield.Note.a_payer_cannot_move_the_value
#print axioms Shield.Key.the_position_moves_the_nullifier
#print axioms Shield.Key.a_nullifier_names_its_note
#print axioms Shield.Merkle.a_root_binds_its_leaf
#print axioms Shield.Imt.excludes_is_exclusive
#print axioms Shield.Balance.a_transfer_conserves
#print axioms Shield.LimbBalance.limbwise_conservation
#print axioms Shield.LimbBalance.a_bounded_value_zero_mod_p_is_zero
#print axioms Shield.LimbBalance.modular_balance_alone_creates_value
#print axioms Shield.Params.provable_le_conjectured
#print axioms Shield.Stack.the_stack_clears_eighty
#print axioms Shield.Deep.shedding_seventy_one_halves_it
#print axioms Shield.Gas.the_settlement_proof_never_fits
#print axioms Shield.Gas.the_wrap_fits
#print axioms Shield.Gas.amortisation_falls
#print axioms Shield.Spend.a_moved_nullifier_moved_something
#print axioms Shield.Spend.an_opening_names_one_note
#print axioms Shield.Wrap.deep_is_the_larger_term
#print axioms Shield.Wrap.the_boundary_beats_both
#print axioms Shield.Proof.fri_is_the_larger_term
#print axioms Shield.Proof.the_spec_does_not_fit
#print axioms Shield.Proof.a_bigger_fold_inverts_without_it
#print axioms Shield.Live.a_dead_input_cannot_carry_value
#print axioms Shield.Live.one_note_can_pay
#print axioms Shield.Wiring.a_triple_is_one_cycle
#print axioms Shield.Wiring.a_redundant_class_drops_a_binding
#print axioms Shield.Rounds.a_drawn_challenge_refuses_the_pair
#print axioms Shield.Rounds.at_zero_the_gap_is_free

#print axioms Shield.Layout.shipped_closes
#print axioms Shield.Layout.fri_depth_step
#print axioms Shield.Quad.next_layer_selector
#print axioms Shield.Field.powMod_eq
#print axioms Shield.Field.seven_to_half_is_minus_one
#print axioms Shield.Budget.memory_superadditive
#print axioms Shield.Budget.doubling_more_than_doubles
#print axioms Shield.Transcript.before_means_both_occur
#print axioms Shield.Transcript.no_index_before_a_commitment
#print axioms Shield.Header.de64_le64
#print axioms Shield.Header.every_field_moves_the_preimage
#print axioms Shield.Stop.the_final_is_what_is_left
#print axioms Shield.Soundness.two_queries_buy_the_rate_exponent
#print axioms Shield.Index.attach_binds_the_index
#print axioms Shield.Index.the_root_and_index_name_one_leaf
#print axioms Shield.Search.the_shipped_point_is_admissible
#print axioms Shield.Search.stop_six_dominates_the_shipped_point
#print axioms Shield.Manifest.the_layers_fill_the_query
#print axioms Shield.Curve.rising_costs_exceed_the_first_line
#print axioms Shield.Combine.the_scalar_factors
#print axioms Shield.Phase.the_phases_add_up
#print axioms Shield.Fixture.the_size_is_the_layout
#print axioms Shield.Wire.a_trailing_byte_is_refused
#print axioms Shield.Horner.horner_is_the_power_sum
#print axioms Shield.Cost.query_monotone_in_nodes
#print axioms Shield.Ladder.descending_ladder
#print axioms Shield.Recursion.two_le_fanout_iff
#print axioms Shield.Domain.blowup_eleven_does_not_fit
#print axioms Shield.Radix.radix_four_is_smaller_per_query
#print axioms Shield.Codec.program_one_closes
#print axioms Shield.Identity.accepted_means_every_check_passed
#print axioms Shield.Settlement.per_spend_halves_as_spends_double
#print axioms Shield.Allocation.loop_superadditive
#print axioms Shield.Tokens.tokensOf_monotone
#print axioms Shield.Roots.omega29_has_order_two_to_the_twenty_nine
#print axioms Shield.Canon.readLE_bytesLE
#print axioms Shield.Grind.trials_times_passing_is_every_word
#print axioms Shield.Poseidon.blocks_cover_the_input
#print axioms Shield.Fold.fold_self
#print axioms Shield.Walk.walk_accepts
#print axioms Shield.Session.chunk_advances_by_count
#print axioms Shield.Intent.the_words_determine_the_intent
#print axioms Shield.Nullifier.a_respend_is_refused
#print axioms Shield.Trace.used_le_thousand
#print axioms Shield.Pieces.the_test_sends_the_whole_file
#print axioms Shield.Points.only_dev_is_under_the_floor
#print axioms Shield.Sponge.total_append
#print axioms Shield.Publics.every_public_precedes_the_trace_root
#print axioms Shield.Emit.the_emit_agrees_with_the_layout
#print axioms Shield.Poly.division
#print axioms Shield.Poly.deep_value_is_the_quotient
#print axioms Shield.FoldPoly.split
#print axioms Shield.FoldPoly.fold_eval
#print axioms Shield.FoldPoly.the_even_lane
#print axioms Shield.FoldPoly.the_odd_lane
#print axioms Shield.Tie.tied_names_one_value
#print axioms Shield.Tie.untied_pair_has_two_roots
#print axioms Shield.Read.capped_eq
#print axioms Shield.Read.readBody_exact
#print axioms Shield.Read.readLegacy_size
#print axioms Shield.Read.size_is_the_layout
#print axioms Shield.Read.an_accepted_shipped_file_is_112436_bytes
#print axioms Shield.Read.fitsB_sound
#print axioms Shield.Read.readFour_size
#print axioms Shield.Read.an_accepted_format_four_file_is_112476_bytes
#print axioms Shield.Layout.format_four_moves_no_shipped_offset
#print axioms Shield.Layout.format_five_saves
#print axioms Shield.Layout.cons_stride_closed_five
#print axioms Shield.Layout.shipped_four_closes
#print axioms Shield.Identity.one_query_set_moves_format_and_layout
#print axioms Shield.Tie.format_four_names_one_value
#print axioms Shield.Tie.leaf_and_slot_are_injective
#print axioms Shield.Identity.the_format_moved_alone_once
#print axioms Shield.ClientData.the_regions_tile_the_blob
#print axioms Shield.ClientData.opened_means_every_check
#print axioms Shield.ClientData.by_note_separates_notes
