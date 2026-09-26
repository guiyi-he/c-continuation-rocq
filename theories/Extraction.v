From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From CCont Require Import Syntax Automaton Construction LookaheadSemantics
  LookaheadDerivatives LookaheadDecision PositiveCongruenceNormalization
  PeriodicAutomaton PeriodicDisplay TightAutomaton TightLowerBoundFamily.

Definition char := nat.
Definition char_eqb := Nat.eqb.

Definition build_ce_char (r : regex char) := build_ce char_eqb r.
Definition build_position_char (r : regex char) := build_position char_eqb r.
Definition build_quotient_char (r : regex char) := build_quotient char_eqb r.

Definition rewpla_char := rewpla char.
Definition rewpla_eqb_char := rewpla_eqb char_eqb.
Definition rewpla_nullable_char := @rewpla_nullable char.
Definition rewpla_simplify_char := @rewpla_simplify char.
Definition rewpla_aci_normalize_char (r : rewpla_char) :=
  rewpla_aci_normalize char_eqb (fun a : char => a) r.
Definition rewpla_symbol_components_char (a : char) (r : rewpla_char) :=
  simplified_symbol_derivative char_eqb a r.
Definition rewpla_step_char (a : char) (r : rewpla_char) :=
  rewpla_simplify
    (derivative_merge (simplified_symbol_derivative char_eqb a r)).
Definition rewpla_normalized_symbol_step_char (a : char) (r : rewpla_char) :=
  rewpla_normalized_symbol_step char_eqb (fun c : char => c) a r.
Definition rewpla_normalized_word_step_char (w : list char) (r : rewpla_char) :=
  rewpla_normalized_word_step char_eqb (fun c : char => c) w r.
Definition rewpla_states_closedb_char
    (alphabet : list char) (states : list rewpla_char) :=
  rewpla_states_closedb char_eqb (fun c : char => c) alphabet states.
Definition rewpla_paper_normalize_char (r : rewpla_char) :=
  rewpla_paper_normalize char_eqb r.
Definition rewpla_paper_symbol_step_char (a : char) (r : rewpla_char) :=
  rewpla_paper_symbol_step char_eqb (fun c : char => c) a r.
Definition rewpla_paper_word_step_char (w : list char) (r : rewpla_char) :=
  rewpla_paper_word_step char_eqb (fun c : char => c) w r.
Definition rewpla_derivation_display_normalize_char (r : rewpla_char) :=
  DerivationDisplay.canonical char_eqb (fun c : char => c) r.
Definition rewpla_derivation_symbol_components_char (a : char) (r : rewpla_char) :=
  symbol_derivative_core char_eqb a r.
Definition rewpla_derivation_word_display_char (w : list char) (r : rewpla_char) :=
  DerivationDisplay.word_step char_eqb (fun c : char => c) w r.
Definition rewpla_paper_states_closedb_char
    (alphabet : list char) (states : list rewpla_char) :=
  rewpla_paper_states_closedb char_eqb (fun c : char => c)
    alphabet states.
Definition rewpla_positive_normalize_char (r : rewpla_char) :=
  rewpla_positive_normalize char_eqb (fun c : char => c) r.
Definition rewpla_positive_symbol_step_char (a : char) (r : rewpla_char) :=
  rewpla_positive_symbol_step char_eqb (fun c : char => c) a r.
Definition rewpla_positive_word_step_char (w : list char) (r : rewpla_char) :=
  rewpla_positive_word_step char_eqb (fun c : char => c) w r.
Definition rewpla_positive_states_closedb_char
    (alphabet : list char) (states : list rewpla_char) :=
  rewpla_positive_states_closedb char_eqb (fun c : char => c)
    alphabet states.

(** Generic residue-vector kernel for the periodic-lookahead expression
    family.  All dimensions and periods are supplied by the parsed input. *)
Definition periodic_zeros_char := PeriodicFamily.zeros.
Definition periodic_parameters_validb_char := PeriodicAutomaton.parameters_validb.
Definition periodic_states_closedb_char trigger base_bits alphabet states :=
  PeriodicAutomaton.states_closedb char_eqb trigger base_bits alphabet states.
Definition periodic_base_char := PeriodicFamily.base.
Definition periodic_step_char (trigger : char)
    (base_bits s : PeriodicFamily.bitvec) (a : char) :=
  PeriodicFamily.step char_eqb trigger base_bits s a.

Definition periodic_history_representative_char (sigma : regex char)
    (trigger : char) (initial : rewpla_char) (periods : list nat)
    (w : list char) :=
  @PeriodicDisplay.representative char char_eqb sigma trigger initial periods w.

(** Certified phase/obligation kernel for the tight lower-bound witness. *)
Definition tight_initial_char := TightAutomaton.initial.
Definition tight_step_char := TightAutomaton.step.
Definition tight_finalb_char := TightAutomaton.finalb.
Definition tight_state_eqb_char := TightAutomaton.state_eqb.
Definition tight_states_closedb_char := TightAutomaton.states_closedb.

(** Certified modulo-15 representatives are proved over the finite two-letter
    type [bool].  Translate each atom to the corresponding CLI character;
    this changes only the symbol representation, not the REwPLA constructors. *)
Fixpoint bool_rewpla_to_char (r : rewpla bool) : rewpla_char :=
  match r with
  | WZero => WZero
  | WEps => WEps
  | WAtom a => WAtom (if a then 97 else 98)
  | WPlus p q => WPlus (bool_rewpla_to_char p) (bool_rewpla_to_char q)
  | WConcat p q => WConcat (bool_rewpla_to_char p) (bool_rewpla_to_char q)
  | WStar p => WStar (bool_rewpla_to_char p)
  | WLookahead p => WLookahead (bool_rewpla_to_char p)
  end.

Definition requested_representative_char (s : Mod15Example.bitvec) : rewpla_char :=
  bool_rewpla_to_char (RequestedCorrespondence.mod15_representative s).

Definition requested_debug_representative_char
    (w : list bool) (s : Mod15Example.bitvec) : rewpla_char :=
  bool_rewpla_to_char
    (RequestedCorrespondence.requested_debug_representative w s).

Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction Output Directory "extracted".
Extraction "ccont_core.ml"
  build_ce_char build_position_char build_quotient_char acceptb
  regex_eqb nullable alphabetic_width erase linearize
  rewpla_eqb_char rewpla_nullable_char rewpla_simplify_char
  rewpla_aci_normalize_char
  rewpla_symbol_components_char rewpla_step_char
  rewpla_normalized_symbol_step_char
  rewpla_normalized_word_step_char rewpla_states_closedb_char
  rewpla_paper_normalize_char rewpla_paper_symbol_step_char
  rewpla_paper_word_step_char rewpla_paper_states_closedb_char
  rewpla_positive_normalize_char rewpla_positive_symbol_step_char
  rewpla_positive_word_step_char rewpla_positive_states_closedb_char
  rewpla_derivation_display_normalize_char rewpla_derivation_word_display_char
  rewpla_derivation_symbol_components_char
  periodic_zeros_char periodic_base_char periodic_step_char
  periodic_parameters_validb_char periodic_states_closedb_char
  periodic_history_representative_char
  tight_initial_char tight_step_char tight_finalb_char tight_state_eqb_char
  tight_states_closedb_char
  requested_representative_char requested_debug_representative_char
  Mod15Example.requested_derivative_debug_states
  Mod15Example.residue_state_count
  Mod15Example.all_debug_states_replayb.
