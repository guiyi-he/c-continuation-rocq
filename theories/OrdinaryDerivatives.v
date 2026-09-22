From Stdlib Require Import List Bool.
From CCont Require Import Syntax.
Import ListNotations.
Set Implicit Arguments.

(** * Classical Brzozowski derivatives (paper Section 2.2)

    This file records the preliminary construction literally on the ordinary
    [regex] syntax.  The later REwPLA development subsumes its semantics, but a
    separate definition makes Equations (2)--(3) directly auditable. *)

Fixpoint regex_derivative {A} (eqb : A -> A -> bool) (a : A)
    (r : regex A) : regex A :=
  match r with
  | Zero | Eps => Zero
  | Atom b => if eqb a b then Eps else Zero
  | Plus r s => Plus (regex_derivative eqb a r) (regex_derivative eqb a s)
  | Concat r s =>
      Plus (Concat (regex_derivative eqb a r) s)
        (if nullable r then regex_derivative eqb a s else Zero)
  | Star r => Concat (regex_derivative eqb a r) (Star r)
  end.

Fixpoint regex_word_derivative {A} (eqb : A -> A -> bool)
    (w : list A) (r : regex A) : regex A :=
  match w with
  | [] => r
  | a :: w' => regex_word_derivative eqb w' (regex_derivative eqb a r)
  end.

Section Correctness.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma cons_app_cases (a : A) w u v :
  a :: w = u ++ v ->
  (u = [] /\ v = a :: w) \/
  exists u', u = a :: u' /\ w = u' ++ v.
Proof.
  destruct u as [|b u']; simpl.
  - intro H. now left.
  - intro H. inversion H; subst. right. exists u'. now split.
Qed.

Lemma matches_star_cons_inv (r : regex A) a w :
  matches (Star r) (a :: w) ->
  exists u v, w = u ++ v /\ matches r (a :: u) /\ matches (Star r) v.
Proof.
  intro H. inversion H; subst.
  destruct u as [|b u']; [contradiction|].
  simpl in H1. inversion H1; subst b.
  exists u', v. repeat split; assumption.
Qed.

Theorem regex_derivative_correct (a : A) r w :
  matches (regex_derivative eqb a r) w <-> matches r (a :: w).
Proof.
  revert w. induction r as [| |b|r IHr s IHs|r IHr s IHs|r IHr]; intro w;
    simpl.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - destruct (eqb a b) eqn:Hab.
    + apply eqb_spec in Hab. subst b. split; intro H.
      * inversion H; constructor.
      * inversion H; constructor.
    + assert (a <> b) as Hneq.
      { intro H. subst b.
        assert (eqb a a = true) by (apply eqb_spec; reflexivity).
        congruence. }
      split; intro H; inversion H; subst; contradiction.
  - split.
    + intro H. inversion H; subst.
      * apply M_PlusL. now apply IHr.
      * apply M_PlusR. now apply IHs.
    + intro H. inversion H; subst.
      * apply M_PlusL. now apply IHr.
      * apply M_PlusR. now apply IHs.
  - destruct (nullable r) eqn:Hnull; simpl.
    + split.
      * intro H. inversion H; subst.
        -- match goal with Hm : matches (Concat _ _) _ |- _ => inversion Hm; subst end.
           match goal with Hd : matches (regex_derivative eqb a r) _ |- _ =>
             apply IHr in Hd
           end.
           change (matches (Concat r s) ((a :: u) ++ v)).
           apply M_Concat; assumption.
        -- match goal with Hd : matches (regex_derivative eqb a s) _ |- _ =>
             apply IHs in Hd
           end.
           change (matches (Concat r s) ([] ++ a :: w)).
           apply M_Concat; [now apply nullable_correct|assumption].
      * intro H. inversion H; subst.
        match goal with Heq : ?u ++ ?v = a :: w |- _ =>
          symmetry in Heq;
          apply cons_app_cases in Heq as [[-> ->]|[u' [-> ->]]]
        end.
        -- apply M_PlusR. now apply IHs.
        -- apply M_PlusL. apply M_Concat; [now apply IHr|assumption].
    + split.
      * intro H. inversion H; subst.
        -- match goal with Hm : matches (Concat _ _) _ |- _ => inversion Hm; subst end.
           match goal with Hd : matches (regex_derivative eqb a r) _ |- _ =>
             apply IHr in Hd
           end.
           change (matches (Concat r s) ((a :: u) ++ v)).
           apply M_Concat; assumption.
        -- match goal with Hz : matches Zero _ |- _ => inversion Hz end.
      * intro H. inversion H; subst.
        match goal with Heq : ?u ++ ?v = a :: w |- _ =>
          symmetry in Heq;
          apply cons_app_cases in Heq as [[-> ->]|[u' [-> ->]]]
        end.
        -- match goal with Hr : matches r [] |- _ =>
             apply nullable_correct in Hr; congruence
           end.
        -- apply M_PlusL. apply M_Concat; [now apply IHr|assumption].
  - split.
    + intro H. inversion H; subst.
      match goal with Hd : matches (regex_derivative eqb a r) _ |- _ =>
        apply IHr in Hd
      end.
      apply M_StarApp with (u := a :: u) (v := v); try assumption.
      discriminate.
    + intro H. apply matches_star_cons_inv in H as [u [v [-> [Hr Hstar]]]].
      apply M_Concat; [now apply IHr|exact Hstar].
Qed.

Theorem regex_word_derivative_correct w r z :
  matches (regex_word_derivative eqb w r) z <-> matches r (w ++ z).
Proof.
  revert r. induction w as [|a w IH]; intro r; simpl.
  - reflexivity.
  - rewrite IH, regex_derivative_correct. reflexivity.
Qed.

Corollary regex_word_derivative_acceptance w r :
  nullable (regex_word_derivative eqb w r) = true <-> matches r w.
Proof.
  rewrite nullable_correct, (regex_word_derivative_correct w r []).
  now rewrite app_nil_r.
Qed.

End Correctness.

Print Assumptions regex_derivative_correct.
Print Assumptions regex_word_derivative_correct.
Print Assumptions regex_word_derivative_acceptance.
