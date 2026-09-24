From Stdlib Require Import List Bool RelationClasses.
From CCont Require Import StringConstraints LookaheadSemantics
  LookaheadDerivatives LookaheadDecision ConstraintExpansion.
Import ListNotations.

Set Implicit Arguments.

(** * The positive-lookahead congruence of Miyazaki--Minamide

    This file formalizes Definition 3.5, rules (1)--(11), of
    "Derivatives of Regular Expressions with Lookahead", restricted to
    the fragment without negative lookahead.  The side condition called
    "logical expression" is represented by [positive_logical].  The
    broader executable predicate [constraint_expressionb] is used only as
    a soundness bridge: every positive logical expression satisfies it.

    [positive_congruence] is the least equivalence and constructor
    congruence containing precisely those eleven algebraic rules. *)

(** Positive logical expressions are the negative-lookahead-free instance of
    the paper's grammar [l ::= 0 | 1 | l+l | ll | !e].  A primitive positive
    lookahead is the counterpart of the paper's logical lookahead form.  In
    particular, the grammar does not close logical expressions under star. *)
Inductive positive_logical {A : Type} : rewpla A -> Prop :=
| PL_zero : positive_logical WZero
| PL_eps : positive_logical WEps
| PL_plus r s :
    positive_logical r -> positive_logical s ->
    positive_logical (WPlus r s)
| PL_concat r s :
    positive_logical r -> positive_logical s ->
    positive_logical (WConcat r s)
| PL_lookahead r : positive_logical (WLookahead r).

Theorem positive_logical_constraint_expressionb {A} (r : rewpla A) :
  positive_logical r -> constraint_expressionb r = true.
Proof.
  induction 1; simpl; try reflexivity.
  - now rewrite IHpositive_logical1, IHpositive_logical2.
  - now rewrite IHpositive_logical1, IHpositive_logical2.
Qed.

Inductive positive_congruence {A : Type} : rewpla A -> rewpla A -> Prop :=
| PC_refl r : positive_congruence r r
| PC_sym r s :
    positive_congruence r s -> positive_congruence s r
| PC_trans r s t :
    positive_congruence r s ->
    positive_congruence s t ->
    positive_congruence r t
| PC_plus_congr r r' s s' :
    positive_congruence r r' ->
    positive_congruence s s' ->
    positive_congruence (WPlus r s) (WPlus r' s')
| PC_concat_congr r r' s s' :
    positive_congruence r r' ->
    positive_congruence s s' ->
    positive_congruence (WConcat r s) (WConcat r' s')
| PC_star_congr r s :
    positive_congruence r s ->
    positive_congruence (WStar r) (WStar s)
| PC_lookahead_congr r s :
    positive_congruence r s ->
    positive_congruence (WLookahead r) (WLookahead s)

(** Rules (1)--(3): associativity, commutativity and idempotence of union. *)
| PC_plus_assoc r s t :
    positive_congruence
      (WPlus r (WPlus s t)) (WPlus (WPlus r s) t)
| PC_plus_comm r s :
    positive_congruence (WPlus r s) (WPlus s r)
| PC_plus_idem r :
    positive_congruence (WPlus r r) r

(** Rule (4): [WZero] is the two-sided unit of union. *)
| PC_plus_zero_right r :
    positive_congruence (WPlus r WZero) r
| PC_plus_zero_left r :
    positive_congruence (WPlus WZero r) r

(** Rules (5)--(6): concatenation unit and zero. *)
| PC_concat_eps_right r :
    positive_congruence (WConcat r WEps) r
| PC_concat_eps_left r :
    positive_congruence (WConcat WEps r) r
| PC_concat_zero_right r :
    positive_congruence (WConcat r WZero) WZero
| PC_concat_zero_left r :
    positive_congruence (WConcat WZero r) WZero

(** Rules (7)--(8): right and left distributivity. *)
| PC_right_distrib r s t :
    positive_congruence
      (WConcat (WPlus r s) t)
      (WPlus (WConcat r t) (WConcat s t))
| PC_left_distrib r s t :
    positive_congruence
      (WConcat r (WPlus s t))
      (WPlus (WConcat r s) (WConcat r t))

(** Rule (9): associativity of concatenation. *)
| PC_concat_assoc r s t :
    positive_congruence
      (WConcat r (WConcat s t)) (WConcat (WConcat r s) t)

(** Rules (10)--(11): logical/constraint products are commutative and
    idempotent. *)
| PC_constraint_comm c d :
    positive_logical c ->
    positive_logical d ->
    positive_congruence (WConcat c d) (WConcat d c)
| PC_constraint_idem c :
    positive_logical c ->
    positive_congruence (WConcat c c) c.

Arguments positive_congruence {A} _ _.

Notation "r ==p s" := (positive_congruence r s)
  (at level 70, no associativity).

(** The relation is explicitly an equivalence. *)
Theorem positive_congruence_refl {A} (r : rewpla A) : r ==p r.
Proof. constructor. Qed.

Theorem positive_congruence_sym {A} (r s : rewpla A) :
  r ==p s -> s ==p r.
Proof. apply PC_sym. Qed.

Theorem positive_congruence_trans {A} (r s t : rewpla A) :
  r ==p s -> s ==p t -> r ==p t.
Proof. apply PC_trans. Qed.

Global Instance positive_congruence_equivalence {A} :
  Equivalence (@positive_congruence A).
Proof.
  constructor.
  - exact positive_congruence_refl.
  - exact positive_congruence_sym.
  - exact positive_congruence_trans.
Qed.

(** Constructor compatibility is part of the generated congruence. *)
Theorem positive_congruence_plus_compat {A}
    (r r' s s' : rewpla A) :
  r ==p r' -> s ==p s' -> WPlus r s ==p WPlus r' s'.
Proof. apply PC_plus_congr. Qed.

Theorem positive_congruence_concat_compat {A}
    (r r' s s' : rewpla A) :
  r ==p r' -> s ==p s' -> WConcat r s ==p WConcat r' s'.
Proof. apply PC_concat_congr. Qed.

Theorem positive_congruence_star_compat {A} (r s : rewpla A) :
  r ==p s -> WStar r ==p WStar s.
Proof. apply PC_star_congr. Qed.

Theorem positive_congruence_lookahead_compat {A} (r s : rewpla A) :
  r ==p s -> WLookahead r ==p WLookahead s.
Proof. apply PC_lookahead_congr. Qed.

(** A relation is a model of the positive-lookahead equations when it is an
    equivalence, is compatible with every constructor, and validates exactly
    rules (1)--(11).  Packaging these assumptions makes the universal
    (least-congruence) property below explicit. *)
Record positive_congruence_theory {A : Type}
    (R : rewpla A -> rewpla A -> Prop) : Prop := {
  pct_refl : forall r, R r r;
  pct_sym : forall r s, R r s -> R s r;
  pct_trans : forall r s t, R r s -> R s t -> R r t;
  pct_plus_congr : forall r r' s s',
    R r r' -> R s s' -> R (WPlus r s) (WPlus r' s');
  pct_concat_congr : forall r r' s s',
    R r r' -> R s s' -> R (WConcat r s) (WConcat r' s');
  pct_star_congr : forall r s, R r s -> R (WStar r) (WStar s);
  pct_lookahead_congr : forall r s,
    R r s -> R (WLookahead r) (WLookahead s);
  pct_plus_assoc : forall r s t,
    R (WPlus r (WPlus s t)) (WPlus (WPlus r s) t);
  pct_plus_comm : forall r s, R (WPlus r s) (WPlus s r);
  pct_plus_idem : forall r, R (WPlus r r) r;
  pct_plus_zero_right : forall r, R (WPlus r WZero) r;
  pct_plus_zero_left : forall r, R (WPlus WZero r) r;
  pct_concat_eps_right : forall r, R (WConcat r WEps) r;
  pct_concat_eps_left : forall r, R (WConcat WEps r) r;
  pct_concat_zero_right : forall r, R (WConcat r WZero) WZero;
  pct_concat_zero_left : forall r, R (WConcat WZero r) WZero;
  pct_right_distrib : forall r s t,
    R (WConcat (WPlus r s) t)
      (WPlus (WConcat r t) (WConcat s t));
  pct_left_distrib : forall r s t,
    R (WConcat r (WPlus s t))
      (WPlus (WConcat r s) (WConcat r t));
  pct_concat_assoc : forall r s t,
    R (WConcat r (WConcat s t)) (WConcat (WConcat r s) t);
  pct_constraint_comm : forall c d,
    positive_logical c -> positive_logical d ->
    R (WConcat c d) (WConcat d c);
  pct_constraint_idem : forall c,
    positive_logical c -> R (WConcat c c) c
}.

Theorem positive_congruence_is_theory {A} :
  positive_congruence_theory (@positive_congruence A).
Proof.
  constructor; intros; eauto using positive_congruence.
Qed.

(** Universal property: [positive_congruence] is contained in every
    constructor congruence satisfying rules (1)--(11), hence it really is the
    least such congruence rather than merely one sound relation. *)
Theorem positive_congruence_least {A}
    (R : rewpla A -> rewpla A -> Prop) :
  positive_congruence_theory R ->
  forall r s, r ==p s -> R r s.
Proof.
  intros T r s H.
  destruct T.
  induction H; eauto.
Qed.

(** The equivalence class represented by [r], kept predicate-valued so the
    development needs no quotient-type or extensionality axiom. *)
Definition positive_class {A} (r : rewpla A) : rewpla A -> Prop :=
  fun s => r ==p s.

Theorem positive_class_member_iff {A} (r s : rewpla A) :
  positive_class r s <-> r ==p s.
Proof. reflexivity. Qed.

Theorem positive_class_same_members {A} (r s : rewpla A) :
  r ==p s -> forall t, positive_class r t <-> positive_class s t.
Proof.
  intros Hrs t. unfold positive_class. split; intro H.
  - eapply PC_trans; [apply PC_sym; exact Hrs|exact H].
  - eapply PC_trans; eassumption.
Qed.

Section Soundness.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

(** The syntactic side condition has the semantic property required by
    rules (10)--(11): logical expressions contribute only empty-main pairs. *)
Theorem positive_logical_empty_main (r : rewpla A) :
  positive_logical r -> empty_main_language (rewpla_denote eqb r).
Proof.
  intro Hr.
  apply (constraint_expression_sound eqb eqb_spec).
  now apply positive_logical_constraint_expressionb.
Qed.

(** Every generating equation, and hence the generated congruence, is sound
    for the complete least-constraint pair semantics [M]. *)
Theorem positive_congruence_sound_M (r s : rewpla A) :
  r ==p s ->
  lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s).
Proof.
  intro H. induction H.
  - apply lang_equiv_refl.
  - now apply lang_equiv_sym.
  - eapply lang_equiv_trans; eassumption.
  - simpl. now apply lang_union_compat.
  - simpl. now apply lang_concat_compat.
  - simpl. now apply lang_star_compat.
  - simpl. now apply positive_lookahead_compat.
  - simpl. apply lang_equiv_sym, lang_union_assoc.
  - simpl. apply lang_union_comm.
  - simpl. apply lang_union_idempotent.
  - simpl. apply lang_union_zero_right.
  - simpl. apply lang_union_zero_left.
  - apply rewpla_concat_one_right_M. exact eqb_spec.
  - apply rewpla_concat_one_left_M. exact eqb_spec.
  - apply rewpla_concat_zero_right_M. exact eqb_spec.
  - apply rewpla_concat_zero_left_M. exact eqb_spec.
  - simpl. apply lang_concat_union_left.
  - simpl. apply lang_concat_union_right.
  - apply lang_equiv_sym, rewpla_concat_assoc_M. exact eqb_spec.
  - apply (rewpla_constraint_concat_comm eqb eqb_spec).
    + now apply positive_logical_empty_main.
    + now apply positive_logical_empty_main.
  - apply (rewpla_constraint_concat_idempotent eqb eqb_spec).
    now apply positive_logical_empty_main.
Qed.

(** Soundness for the expanded behavior semantics [B = Gamma o M]. *)
Theorem positive_congruence_sound_B (r s : rewpla A) :
  r ==p s ->
  lang_equiv
    (constraint_expansion (rewpla_denote eqb r))
    (constraint_expansion (rewpla_denote eqb s)).
Proof.
  intro Hrs. pose proof (positive_congruence_sound_M Hrs) as Hsem.
  intros [u z]. unfold constraint_expansion. simpl. split.
  - intros [v [Hr Hv]]. exists v. split;
      [apply (proj1 (Hsem (u, v))); exact Hr|exact Hv].
  - intros [v [Hs Hv]]. exists v. split;
      [apply (proj2 (Hsem (u, v))); exact Hs|exact Hv].
Qed.

(** The final-state/nullability observation is representative-independent. *)
Theorem positive_congruence_nullable (r s : rewpla A) :
  r ==p s -> rewpla_nullable r = rewpla_nullable s.
Proof.
  intro Hrs.
  pose proof (positive_congruence_sound_M Hrs ([], [])) as Hid.
  destruct (rewpla_nullable r) eqn:Hr,
           (rewpla_nullable s) eqn:Hs; try reflexivity.
  - exfalso.
    apply (proj1 (rewpla_nullable_correct eqb eqb_spec r)) in Hr.
    apply (proj1 Hid) in Hr.
    apply (proj2 (rewpla_nullable_correct eqb eqb_spec s)) in Hr.
    congruence.
  - exfalso.
    apply (proj1 (rewpla_nullable_correct eqb eqb_spec s)) in Hs.
    apply (proj2 Hid) in Hs.
    apply (proj2 (rewpla_nullable_correct eqb eqb_spec r)) in Hs.
    congruence.
Qed.

(** Projection to ordinary word languages also respects every class. *)
Theorem positive_congruence_projected (r s : rewpla A) :
  r ==p s ->
  forall w, rewpla_language eqb r w <-> rewpla_language eqb s w.
Proof.
  intros Hrs w. unfold rewpla_language, project_language.
  pose proof (positive_congruence_sound_M Hrs) as Hsem.
  split; intros [p [Hp Hproj]]; exists p; split; try exact Hproj.
  - apply (proj1 (Hsem p)); exact Hp.
  - apply (proj2 (Hsem p)); exact Hp.
Qed.

(** Even before the stronger syntactic derivative-congruence theorem, semantic
    derivative states are representative-independent: quotienting a sound
    class and differentiating commute at the complete [M] level. *)
Lemma pair_language_symbol_quotient_compat_positive a
    (R S : constraint_language A) :
  lang_equiv R S ->
  lang_equiv (pair_language_symbol_quotient eqb a R)
             (pair_language_symbol_quotient eqb a S).
Proof.
  intros H q. unfold pair_language_symbol_quotient. split.
  - intros [p [Hp Hstep]]. exists p. split;
      [apply (proj1 (H p)); exact Hp|exact Hstep].
  - intros [p [Hp Hstep]]. exists p. split;
      [apply (proj2 (H p)); exact Hp|exact Hstep].
Qed.

Theorem positive_congruence_symbol_derivative_M a (r s : rewpla A) :
  r ==p s ->
  lang_equiv
    (rewpla_denote eqb
      (derivative_merge (symbol_derivative_core eqb a r)))
    (rewpla_denote eqb
      (derivative_merge (symbol_derivative_core eqb a s))).
Proof.
  intro Hrs.
  eapply lang_equiv_trans.
  - apply symbol_derivative_core_merge_correct. exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply pair_language_symbol_quotient_compat_positive.
      apply positive_congruence_sound_M. exact Hrs.
    + apply lang_equiv_sym, symbol_derivative_core_merge_correct.
      exact eqb_spec.
Qed.

Theorem positive_congruence_word_derivative_M w (r s : rewpla A) :
  r ==p s ->
  lang_equiv
    (rewpla_denote eqb (word_derivative eqb w r))
    (rewpla_denote eqb (word_derivative eqb w s)).
Proof.
  intro Hrs. eapply lang_equiv_trans.
  - apply word_derivative_correct. exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply pair_language_word_quotient_compat.
      apply positive_congruence_sound_M. exact Hrs.
    + apply lang_equiv_sym, word_derivative_correct. exact eqb_spec.
Qed.

End Soundness.

Print Assumptions positive_congruence_sound_M.
Print Assumptions positive_congruence_sound_B.
Print Assumptions positive_congruence_least.
Print Assumptions positive_logical_empty_main.
Print Assumptions positive_congruence_nullable.
Print Assumptions positive_congruence_symbol_derivative_M.
Print Assumptions positive_congruence_word_derivative_M.
