From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From CCont Require Import Syntax Automaton Construction.

Definition char := nat.
Definition char_eqb := Nat.eqb.

Definition build_ce_char (r : regex char) := build_ce char_eqb r.
Definition build_position_char (r : regex char) := build_position char_eqb r.
Definition build_quotient_char (r : regex char) := build_quotient char_eqb r.

Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction Output Directory "extracted".
Extraction "ccont_core.ml"
  build_ce_char build_position_char build_quotient_char acceptb
  regex_eqb nullable alphabetic_width erase linearize.
