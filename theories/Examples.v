From Stdlib Require Import List Bool Arith.
From CCont Require Import Syntax Automaton Construction.
Import ListNotations.

Definition nat_eqb_spec : forall x y, Nat.eqb x y = true <-> x = y := Nat.eqb_eq.

Definition paper : regex nat :=
  Concat (Star (Atom 120))
    (Star (Plus (Concat (Atom 120) (Atom 120)) (Atom 121))).

Definition paper_ce := machine (build_ce Nat.eqb paper).
Definition paper_q := machine (build_quotient Nat.eqb paper).

Example paper_ce_states : state_count (machine (build_ce Nat.eqb paper)) = 5.
Proof. reflexivity. Qed.

Example paper_quotient_states :
  state_count (machine (build_quotient Nat.eqb paper)) = 3.
Proof. reflexivity. Qed.

Example paper_accepts_xxy :
  acceptb (machine (build_ce Nat.eqb paper)) [120;120;121] = true.
Proof. reflexivity. Qed.

Example paper_quotient_accepts_xxy :
  acceptb (machine (build_quotient Nat.eqb paper)) [120;120;121] = true.
Proof. reflexivity. Qed.

Example paper_ce_transitions :
  trans paper_ce 0 120 = [1;2] /\ trans paper_ce 0 121 = [4] /\
  trans paper_ce 1 120 = [1;2] /\ trans paper_ce 1 121 = [4] /\
  trans paper_ce 2 120 = [3] /\ trans paper_ce 2 121 = [] /\
  trans paper_ce 3 120 = [2] /\ trans paper_ce 3 121 = [4] /\
  trans paper_ce 4 120 = [2] /\ trans paper_ce 4 121 = [4].
Proof. repeat split; reflexivity. Qed.

Example paper_quotient_transitions :
  trans paper_q 0 120 = [0;1] /\ trans paper_q 0 121 = [2] /\
  trans paper_q 1 120 = [2] /\ trans paper_q 1 121 = [] /\
  trans paper_q 2 120 = [1] /\ trans paper_q 2 121 = [2].
Proof. repeat split; reflexivity. Qed.
