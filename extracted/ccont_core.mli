
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val eqb : int -> int -> bool

module Nat :
 sig
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

val nth : int -> 'a1 list -> 'a1 -> 'a1

val hd : 'a1 -> 'a1 list -> 'a1

val nth_error : 'a1 list -> int -> 'a1 option

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

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

type char = int

val char_eqb : int -> int -> bool

val build_ce_char : char regex -> (int, int position regex) built_automaton

val build_position_char :
  char regex -> (int, int position regex) built_automaton

val build_quotient_char :
  char regex -> (int, int position regex) built_automaton
