From Stdlib Require Import List Bool.
From CCont Require Import StringConstraints LookaheadSemantics
  LookaheadDerivatives.
Import ListNotations.
Set Implicit Arguments.

(** Eq. (19)'s lambda_1 at the language level, without postulating a
    Boolean decision procedure for nonemptiness. It is exactly the identity
    language when an empty-main pair exists, and empty otherwise. *)
Definition language_lambda1 {A} (R : constraint_language A)
    : constraint_language A :=
  fun p => p = ([], []) /\ exists v, R ([], v).

Lemma language_lambda1_nonempty {A} (R : constraint_language A) :
  (exists v, R ([], v)) -> lang_equiv (language_lambda1 R) lang_one.
Proof. intros HR p. unfold language_lambda1, lang_one. tauto. Qed.

Lemma language_lambda1_empty {A} (R : constraint_language A) :
  ~ (exists v, R ([], v)) -> lang_equiv (language_lambda1 R) lang_zero.
Proof. intros HR p. unfold language_lambda1, lang_zero. tauto. Qed.

Section Guards.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

(** Every context quotient witnesses lambda_1(R). The paper's guard can
    therefore be erased in this product without using excluded middle. *)
Theorem language_context_guard_redundant a (R : constraint_language A) :
  lang_equiv (lang_concat eqb (language_lambda1 R)
    (context_symbol_quotient a R)) (context_symbol_quotient a R).
Proof.
  intro out. unfold lang_concat, language_lambda1. split.
  - intros [p [q [[-> HR] [Hq Hout]]]].
    rewrite (constraint_concat_left_identity eqb eqb_spec q) in Hout.
    inversion Hout; subst. exact Hq.
  - intro Hout. exists ([], []), out. split.
    + split; [reflexivity|]. destruct out as [u v].
      destruct Hout as [-> HR]. exists (a :: v). exact HR.
    + split; [exact Hout|apply constraint_concat_left_identity; exact eqb_spec].
Qed.

Lemma epsilon_part_concat_comm (R S : constraint_language A) :
  lang_equiv (lang_concat eqb R (language_epsilon_part S))
    (lang_concat eqb (language_epsilon_part S) R).
Proof.
  intro out. unfold lang_concat, language_epsilon_part, epsilon_part. split.
  - intros [p [q [Hp [[HS ->] Hout]]]].
    rewrite (constraint_concat_right_identity eqb eqb_spec p) in Hout.
    inversion Hout; subst. exists ([], []), out. repeat split; try assumption.
    apply constraint_concat_left_identity. exact eqb_spec.
  - intros [p [q [[HS ->] [Hq Hout]]]].
    rewrite (constraint_concat_left_identity eqb eqb_spec q) in Hout.
    inversion Hout; subst. exists out, ([], []). repeat split; try assumption.
    apply constraint_concat_right_identity. exact eqb_spec.
Qed.

(** Literal guarded form of Eq. (20), for every pair language, and hence
    for every REwPLA denotation. The executable core implements the equal
    unguarded right side. No lambda1 Boolean oracle is a theorem premise. *)
Theorem paper_guarded_concat_main_quotient a (R S : constraint_language A) :
  lang_equiv (main_symbol_quotient a (lang_concat eqb R S))
    (lang_union
      (lang_union
        (lang_concat eqb (main_symbol_quotient a R) S)
        (lang_concat eqb
          (lang_concat eqb (language_lambda1 R) (context_symbol_quotient a R))
          (main_symbol_quotient a S)))
      (lang_concat eqb (language_epsilon_part R) (main_symbol_quotient a S))).
Proof.
  eapply lang_equiv_trans.
  - apply main_quotient_concat. exact eqb_spec.
  - apply lang_union_compat; [|apply lang_equiv_refl].
    apply lang_union_compat; [apply lang_equiv_refl|].
    apply lang_concat_compat; [|apply lang_equiv_refl].
    apply lang_equiv_sym, language_context_guard_redundant.
Qed.

Theorem paper_guarded_concat_context_quotient a (R S : constraint_language A) :
  lang_equiv (context_symbol_quotient a (lang_concat eqb R S))
    (lang_union
      (lang_union
        (lang_concat eqb
          (lang_concat eqb (language_lambda1 R) (context_symbol_quotient a R))
          (context_symbol_quotient a S))
        (lang_concat eqb
          (lang_concat eqb (language_lambda1 R) (language_epsilon_part S))
          (context_symbol_quotient a R)))
      (lang_concat eqb (language_epsilon_part R) (context_symbol_quotient a S))).
Proof.
  eapply lang_equiv_trans.
  - apply context_quotient_concat. exact eqb_spec.
  - apply lang_union_compat; [|apply lang_equiv_refl].
    apply lang_union_compat.
    + apply lang_concat_compat; [|apply lang_equiv_refl].
      apply lang_equiv_sym, language_context_guard_redundant.
    + eapply lang_equiv_trans.
      * apply lang_concat_compat; [|apply lang_equiv_refl].
        apply lang_equiv_sym, language_context_guard_redundant.
      * eapply lang_equiv_trans.
        -- apply lang_concat_assoc. exact eqb_spec.
        -- eapply lang_equiv_trans.
           ++ apply lang_concat_compat; [apply lang_equiv_refl|].
              apply epsilon_part_concat_comm.
           ++ apply lang_equiv_sym, lang_concat_assoc. exact eqb_spec.
Qed.
End Guards.

Print Assumptions paper_guarded_concat_main_quotient.
Print Assumptions paper_guarded_concat_context_quotient.
