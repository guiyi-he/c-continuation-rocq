
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

val eqb0 : bool -> bool -> bool

module Nat :
 sig
  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int * int

  val modulo : int -> int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

val repeat : 'a1 -> int -> 'a1 list

val nth : int -> 'a1 list -> 'a1 -> 'a1

val hd : 'a1 -> 'a1 list -> 'a1

val nth_error : 'a1 list -> int -> 'a1 option

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type 'a regex =
| Zero
| Eps
| Atom of 'a
| Plus of 'a regex * 'a regex
| Concat of 'a regex * 'a regex
| Star of 'a regex

val nullable : 'a1 regex -> bool

val alphabetic_width : 'a1 regex -> int

val regex_eqb : ('a1 -> 'a1 -> bool) -> 'a1 regex -> 'a1 regex -> bool

val is_zero : 'a1 regex -> bool

val smart_concat : 'a1 regex -> 'a1 regex -> 'a1 regex

type 'a position = int * 'a

val linearize_from : int -> 'a1 regex -> 'a1 position regex * int

val linearize : 'a1 regex -> 'a1 position regex

val erase : 'a1 position regex -> 'a1 regex

type 'a automaton = { state_count : int; initial : int;
                      finalb : (int -> bool); trans : (int -> 'a -> int list) }

val memb : int -> int list -> bool

val add0 : int -> int list -> int list

val union : int list -> int list -> int list

val step_from : 'a1 automaton -> int list -> 'a1 -> int list

val run : 'a1 automaton -> int list -> 'a1 list -> int list

val any_final : 'a1 automaton -> int list -> bool

val acceptb : 'a1 automaton -> 'a1 list -> bool

val mapi_from : int -> (int -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list

val mapi : (int -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list

type ('a, 'r) state_info = { info_id : int;
                             info_position : (int * 'a) option;
                             info_members : int list; info_continuation : 
                             'r; info_final : bool }

type ('a, 'r) built_automaton = { machine : 'a automaton;
                                  infos : ('a, 'r) state_info list }

val pos_eqb : ('a1 -> 'a1 -> bool) -> 'a1 position -> 'a1 position -> bool

val positions : 'a1 position regex -> 'a1 position list

val cderive :
  ('a1 -> 'a1 -> bool) -> 'a1 position -> 'a1 position regex -> 'a1 position
  regex

val ccontinuation :
  ('a1 -> 'a1 -> bool) -> 'a1 position -> 'a1 position regex -> 'a1 position
  regex

val nth_position : 'a1 position list -> int -> 'a1 position option

val continuation_at :
  ('a1 -> 'a1 -> bool) -> 'a1 position regex -> 'a1 position list -> int ->
  'a1 position regex

val targets :
  ('a1 -> 'a1 -> bool) -> 'a1 position list -> 'a1 position regex -> 'a1
  position regex -> 'a1 -> int list

val build_ce :
  ('a1 -> 'a1 -> bool) -> 'a1 regex -> ('a1, 'a1 position regex)
  built_automaton

val build_position :
  ('a1 -> 'a1 -> bool) -> 'a1 regex -> ('a1, 'a1 position regex)
  built_automaton

val erased_cont :
  ('a1 -> 'a1 -> bool) -> 'a1 position regex -> 'a1 position list -> int ->
  'a1 regex

val insert_class :
  ('a1 -> 'a1 -> bool) -> int -> int list list -> 'a1 position regex -> 'a1
  position list -> int list list

val classes_of : ('a1 -> 'a1 -> bool) -> 'a1 regex -> int list list

val class_index : int -> int list list -> int

val representative : int list -> int

val quotient_targets :
  'a1 automaton -> int list list -> int -> 'a1 -> int list

val quotient_targets_class :
  'a1 automaton -> int list list -> int list -> 'a1 -> int list

val build_quotient :
  ('a1 -> 'a1 -> bool) -> 'a1 regex -> ('a1, 'a1 position regex)
  built_automaton

type 'a word = 'a list

type 'a rewpla =
| WZero
| WEps
| WAtom of 'a
| WPlus of 'a rewpla * 'a rewpla
| WConcat of 'a rewpla * 'a rewpla
| WStar of 'a rewpla
| WLookahead of 'a rewpla

val rewpla_nullable : 'a1 rewpla -> bool

val rewpla_lambda : 'a1 rewpla -> 'a1 rewpla

val embed_regex : 'a1 regex -> 'a1 rewpla

type 'a derivative_pair = 'a rewpla * 'a rewpla

val derivative_merge : 'a1 derivative_pair -> 'a1 rewpla

val symbol_derivative_core :
  ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 rewpla -> 'a1 derivative_pair

val smart_plus : 'a1 rewpla -> 'a1 rewpla -> 'a1 rewpla

val smart_concat0 : 'a1 rewpla -> 'a1 rewpla -> 'a1 rewpla

val smart_star : 'a1 rewpla -> 'a1 rewpla

val smart_lookahead : 'a1 rewpla -> 'a1 rewpla

val rewpla_simplify : 'a1 rewpla -> 'a1 rewpla

val simplified_symbol_derivative :
  ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 rewpla -> 'a1 derivative_pair

val rewpla_eqb : ('a1 -> 'a1 -> bool) -> 'a1 rewpla -> 'a1 rewpla -> bool

val nodupb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

val rewpla_term_key : ('a1 -> int) -> 'a1 rewpla -> int list

val nat_list_ltb : int list -> int list -> bool

val rewpla_term_ltb : ('a1 -> int) -> 'a1 rewpla -> 'a1 rewpla -> bool

val aci_union_terms : 'a1 rewpla -> 'a1 rewpla list

val aci_insert_term :
  ('a1 -> int) -> 'a1 rewpla -> 'a1 rewpla list -> 'a1 rewpla list

val aci_sort_terms : ('a1 -> int) -> 'a1 rewpla list -> 'a1 rewpla list

val aci_union_build : 'a1 rewpla list -> 'a1 rewpla

val aci_union_normalize :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla -> 'a1 rewpla

val rewpla_aci_normalize :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla -> 'a1 rewpla

val rewpla_normalized_symbol_step :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 -> 'a1 rewpla -> 'a1 rewpla

val rewpla_normalized_word_step :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 word -> 'a1 rewpla -> 'a1 rewpla

val constraint_expressionb : 'a1 rewpla -> bool

val rewpla_lookahead_lift : ('a1 -> 'a1 -> bool) -> 'a1 rewpla -> 'a1 rewpla

val rewpla_paper_normalize : ('a1 -> 'a1 -> bool) -> 'a1 rewpla -> 'a1 rewpla

val rewpla_paper_symbol_step :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 -> 'a1 rewpla -> 'a1 rewpla

val rewpla_paper_word_step :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 word -> 'a1 rewpla -> 'a1 rewpla

val union_expression : 'a1 rewpla list -> 'a1 rewpla

val rewpla_states_closedb :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 list -> 'a1 rewpla list -> bool

val rewpla_paper_states_closedb :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 list -> 'a1 rewpla list -> bool

val add_fresh :
  ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list * 'a1 list

val add_successors :
  ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list * 'a1
  list

val explore :
  ('a1 -> 'a1 -> bool) -> 'a2 list -> ('a1 -> 'a2 -> 'a1) -> int -> 'a1 list
  -> 'a1 list -> 'a1 list

val derivative_states :
  ('a1 -> 'a1 -> bool) -> 'a2 list -> ('a1 -> 'a2 -> 'a1) -> int -> 'a1 ->
  'a1 list

type ('state, 'label) witnessed_state = { witnessed_value : 'state;
                                          witnessed_word : 'label list }

val witnessed_values : ('a1, 'a2) witnessed_state list -> 'a1 list

val add_witnessed :
  ('a1 -> 'a1 -> bool) -> ('a1, 'a2) witnessed_state -> ('a1, 'a2)
  witnessed_state list -> ('a1, 'a2) witnessed_state list -> ('a1, 'a2)
  witnessed_state list * ('a1, 'a2) witnessed_state list

val add_witnessed_successors :
  ('a1 -> 'a1 -> bool) -> ('a1, 'a2) witnessed_state list -> ('a1, 'a2)
  witnessed_state list -> ('a1, 'a2) witnessed_state list -> ('a1, 'a2)
  witnessed_state list * ('a1, 'a2) witnessed_state list

val witnessed_successors :
  'a2 list -> ('a1 -> 'a2 -> 'a1) -> ('a1, 'a2) witnessed_state -> ('a1, 'a2)
  witnessed_state list

val explore_witnessed :
  ('a1 -> 'a1 -> bool) -> 'a2 list -> ('a1 -> 'a2 -> 'a1) -> int -> ('a1,
  'a2) witnessed_state list -> ('a1, 'a2) witnessed_state list -> ('a1, 'a2)
  witnessed_state list

val derivative_states_with_witness :
  ('a1 -> 'a1 -> bool) -> 'a2 list -> ('a1 -> 'a2 -> 'a1) -> int -> 'a1 ->
  ('a1, 'a2) witnessed_state list

module Mod15Example :
 sig
  type bitvec = bool list

  val bitvec_eqb : bitvec -> bitvec -> bool

  val zeros15 : bitvec

  val base15 : bitvec

  val rotate15 : bitvec -> bitvec

  val bitvec_union : bitvec -> bitvec -> bitvec

  val residue_step : bitvec -> bool -> bitvec

  val residue_alphabet : bool list

  val residue_states : bitvec list

  val residue_state_count : int

  val residue_witnessed_states : (bitvec, bool) witnessed_state list

  val state_index_from : bitvec -> bitvec list -> int -> int option

  val state_index : bitvec -> bitvec list -> int option

  val true_indices_from : bitvec -> int -> int list

  val true_indices : bitvec -> int list

  type residue_debug_transition = { debug_symbol_is_a : bool;
                                    debug_main_keeps_suffix_language : 
                                    bool; debug_main_bits : bitvec;
                                    debug_context_bits : bitvec;
                                    debug_target : int }

  type residue_debug_state = { debug_id : int; debug_witness : bool list;
                               debug_accepting : bool;
                               debug_representative : bitvec;
                               debug_term_ids : int list;
                               debug_transitions : residue_debug_transition
                                                   list }

  val debug_witness : residue_debug_state -> bool list

  val debug_representative : residue_debug_state -> bitvec

  val residue_transition_debug :
    bitvec list -> bitvec -> bool -> residue_debug_transition

  val build_residue_debug_states_from :
    bitvec list -> (bitvec, bool) witnessed_state list -> int ->
    residue_debug_state list

  val residue_witnessed_values : bitvec list

  val requested_derivative_debug_states : residue_debug_state list

  val replay_witness : bool list -> bitvec

  val debug_state_replaysb : residue_debug_state -> bool

  val all_debug_states_replayb : bool
 end

module PeriodicFamily :
 sig
  type bitvec = bool list

  val zeros : int -> bitvec

  val base : int -> int list -> bitvec

  val rotate : bitvec -> bitvec

  val union : bitvec -> bitvec -> bitvec

  val step : ('a1 -> 'a1 -> bool) -> 'a1 -> bitvec -> bitvec -> 'a1 -> bitvec
 end

module RequestedCorrespondence :
 sig
  val sigma_regex : bool regex

  val positive_regex_power : bool regex -> int -> bool regex

  val wab_bool : bool rewpla

  val wthree_bool : bool rewpla

  val wfive_bool : bool rewpla

  val requested_rewpla_bool : bool rewpla

  val requested_context_product : bool rewpla

  val requested_after_a_display : bool rewpla

  val mod15_block_regex : bool regex

  val residue_class_regex : int -> bool regex

  val true_residue_ids : Mod15Example.bitvec -> int list

  val selected_residue_regex : Mod15Example.bitvec -> bool regex

  val mod15_representative : Mod15Example.bitvec -> bool rewpla

  val requested_debug_representative :
    bool list -> Mod15Example.bitvec -> bool rewpla
 end

val positive_factorb : 'a1 rewpla -> bool

val positive_insert_factor :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla -> 'a1 rewpla list ->
  'a1 rewpla list

val positive_word_normalize :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla list -> 'a1 rewpla list

val positive_word_build : 'a1 rewpla list -> 'a1 rewpla

val positive_sum_insert :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla -> 'a1 rewpla list ->
  'a1 rewpla list

val positive_sum_normalize :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla list -> 'a1 rewpla list

val positive_sum_build :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla list list -> 'a1 rewpla

val positive_logicalb : 'a1 rewpla -> bool

val positive_dnf :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla -> 'a1 rewpla list list

val rewpla_positive_normalize :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla -> 'a1 rewpla

val rewpla_positive_symbol_step :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 -> 'a1 rewpla -> 'a1 rewpla

val rewpla_positive_word_step :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 list -> 'a1 rewpla -> 'a1 rewpla

val rewpla_positive_states_closedb :
  ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 list -> 'a1 rewpla list -> bool

module PeriodicAutomaton :
 sig
  val parameters_validb : int -> int list -> bool

  val bitvec_eqb : PeriodicFamily.bitvec -> PeriodicFamily.bitvec -> bool

  val states_closedb :
    ('a1 -> 'a1 -> bool) -> 'a1 -> PeriodicFamily.bitvec -> 'a1 list ->
    PeriodicFamily.bitvec list -> bool

  val power : 'a1 regex -> int -> 'a1 regex

  val assertion : 'a1 regex -> int -> 'a1 rewpla

  val assertions : 'a1 regex -> int list -> 'a1 rewpla

  val residue_regex : 'a1 regex -> int -> int -> 'a1 regex
 end

module PeriodicDisplay :
 sig
  val shift_offset : int -> int -> int

  val trigger_offsets : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> int list

  val shifted_assertion : 'a1 regex -> int -> int -> 'a1 rewpla

  val derivation_terms : 'a1 rewpla list -> 'a1 rewpla list

  val shift_expression : 'a1 regex -> int list -> int -> 'a1 rewpla

  val history_expression :
    ('a1 -> 'a1 -> bool) -> 'a1 regex -> int list -> int list -> 'a1 rewpla

  val representative :
    ('a1 -> 'a1 -> bool) -> 'a1 regex -> 'a1 -> 'a1 rewpla -> int list -> 'a1
    list -> 'a1 rewpla
 end

module DerivationDisplay :
 sig
  val keep_lookahead : 'a1 rewpla -> 'a1 rewpla

  val normalize : 'a1 rewpla -> 'a1 rewpla

  val canonical :
    ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 rewpla -> 'a1 rewpla

  val symbol_step :
    ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 -> 'a1 rewpla -> 'a1 rewpla

  val word_step :
    ('a1 -> 'a1 -> bool) -> ('a1 -> int) -> 'a1 list -> 'a1 rewpla -> 'a1
    rewpla
 end

type tight_symbol =
| TLa
| TLb
| TLc
| TLd
| TLe
| TLx
| TLhash

module TightAutomaton :
 sig
  type bitvec = bool list

  type family = bitvec list

  val bitvec_eqb : bitvec -> bitvec -> bool

  val bitvec_subsetb : bitvec -> bitvec -> bool

  val bitvec_strict_subsetb : bitvec -> bitvec -> bool

  val all_bitvecs : int -> bitvec list

  val family_normalize : int -> family -> family

  val bitvec_update : int -> bool -> bitvec -> bitvec

  val bitvec_set : int -> bitvec -> bitvec

  val bitvec_clear : int -> bitvec -> bitvec

  val zero_bits : int -> bitvec

  val rotate_bits : bitvec -> bitvec

  val family_add : int -> bitvec -> bitvec list -> family

  val advance_obligations : tight_symbol -> bitvec -> bitvec

  val advance_family : int -> tight_symbol -> bitvec list -> family

  type partial_state =
  | PartialNone
  | PartialPadding
  | PartialBits of bitvec

  val partial_step : int -> partial_state -> tight_symbol -> partial_state

  val completion_obligation : int -> partial_state -> bitvec option

  val completed_step :
    int -> partial_state -> bitvec list -> tight_symbol -> family

  type state =
  | Running of partial_state * family
  | Accepting
  | Dead

  val initial : state

  val finalb : state -> bool

  val family_has_empty : int -> bitvec list -> bool

  val step_running :
    int -> partial_state -> bitvec list -> tight_symbol -> state

  val step : int -> state -> tight_symbol -> state

  val partial_state_eqb : partial_state -> partial_state -> bool

  val family_eqb : family -> family -> bool

  val state_eqb : state -> state -> bool

  val states_closedb : int -> tight_symbol list -> state list -> bool
 end

type char = int

val char_eqb : int -> int -> bool

val build_ce_char : char regex -> (int, int position regex) built_automaton

val build_position_char :
  char regex -> (int, int position regex) built_automaton

val build_quotient_char :
  char regex -> (int, int position regex) built_automaton

type rewpla_char = char rewpla

val rewpla_eqb_char : int rewpla -> int rewpla -> bool

val rewpla_nullable_char : char rewpla -> bool

val rewpla_simplify_char : char rewpla -> char rewpla

val rewpla_aci_normalize_char : rewpla_char -> int rewpla

val rewpla_symbol_components_char : char -> rewpla_char -> int derivative_pair

val rewpla_step_char : char -> rewpla_char -> int rewpla

val rewpla_normalized_symbol_step_char : char -> rewpla_char -> int rewpla

val rewpla_normalized_word_step_char : char list -> rewpla_char -> int rewpla

val rewpla_states_closedb_char : char list -> rewpla_char list -> bool

val rewpla_paper_normalize_char : rewpla_char -> int rewpla

val rewpla_paper_symbol_step_char : char -> rewpla_char -> int rewpla

val rewpla_paper_word_step_char : char list -> rewpla_char -> int rewpla

val rewpla_derivation_display_normalize_char : rewpla_char -> int rewpla

val rewpla_derivation_symbol_components_char :
  char -> rewpla_char -> int derivative_pair

val rewpla_derivation_word_display_char :
  char list -> rewpla_char -> int rewpla

val rewpla_paper_states_closedb_char : char list -> rewpla_char list -> bool

val rewpla_positive_normalize_char : rewpla_char -> int rewpla

val rewpla_positive_symbol_step_char : char -> rewpla_char -> int rewpla

val rewpla_positive_word_step_char : char list -> rewpla_char -> int rewpla

val rewpla_positive_states_closedb_char :
  char list -> rewpla_char list -> bool

val periodic_zeros_char : int -> PeriodicFamily.bitvec

val periodic_parameters_validb_char : int -> int list -> bool

val periodic_states_closedb_char :
  int -> PeriodicFamily.bitvec -> int list -> PeriodicFamily.bitvec list ->
  bool

val periodic_base_char : int -> int list -> PeriodicFamily.bitvec

val periodic_step_char :
  char -> PeriodicFamily.bitvec -> PeriodicFamily.bitvec -> char ->
  PeriodicFamily.bitvec

val periodic_history_representative_char :
  char regex -> char -> rewpla_char -> int list -> char list -> char rewpla

val tight_initial_char : TightAutomaton.state

val tight_step_char :
  int -> TightAutomaton.state -> tight_symbol -> TightAutomaton.state

val tight_finalb_char : TightAutomaton.state -> bool

val tight_state_eqb_char :
  TightAutomaton.state -> TightAutomaton.state -> bool

val tight_states_closedb_char :
  int -> tight_symbol list -> TightAutomaton.state list -> bool

val bool_rewpla_to_char : bool rewpla -> rewpla_char

val requested_representative_char : Mod15Example.bitvec -> rewpla_char

val requested_debug_representative_char :
  bool list -> Mod15Example.bitvec -> rewpla_char
