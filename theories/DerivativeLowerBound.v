From Stdlib Require Import List Arith Lia.
From CCont Require Import StringConstraints LookaheadSemantics LookaheadDerivatives
  LookaheadDecision SemanticDFA.
Import ListNotations.
Set Implicit Arguments.

(** * The derivative-state lower-bound principle (paper Section 4.3)

    The paper's Myhill--Nerode argument only needs a finite list of prefixes
    with pairwise distinguishing suffixes.  This section proves directly, in
    the artifact's derivative semantics, that such prefixes yield the same
    number of distinct projected and full-pair derivative classes. *)

Definition language_separated {A} (L : list A -> Prop)
    (u v : list A) : Prop :=
  exists z, (L (u ++ z) /\ ~ L (v ++ z)) \/
            (~ L (u ++ z) /\ L (v ++ z)).

Fixpoint prefixes_separated {A} (L : list A -> Prop)
    (prefixes : list (list A)) : Prop :=
  match prefixes with
  | [] => True
  | u :: us =>
      (forall v, In v us -> language_separated L u v) /\
      prefixes_separated L us
  end.

Lemma language_separated_sym {A} (L : list A -> Prop) u v :
  language_separated L u v -> language_separated L v u.
Proof.
  intros [z [[Hu Hnv]|[Hnu Hv]]]; exists z;
    [right|left]; now split.
Qed.

(** A direct finite-state Myhill--Nerode counting principle.  It avoids any
    quotient construction: pairwise distinguishable prefixes must reach
    pairwise different states in every deterministic recognizer. *)
Fixpoint deterministic_run {A Q : Type} (step : Q -> A -> Q)
    (q : Q) (w : list A) : Q :=
  match w with
  | [] => q
  | a :: w' => deterministic_run step (step q a) w'
  end.

Lemma deterministic_run_app {A Q : Type} (step : Q -> A -> Q) q u v :
  deterministic_run step q (u ++ v) =
  deterministic_run step (deterministic_run step q u) v.
Proof.
  revert q. induction u as [|a u IH]; intro q; simpl; [reflexivity|].
  apply IH.
Qed.

Definition deterministic_recognizes {A Q : Type}
    (step : Q -> A -> Q) (initial : Q) (final : Q -> Prop)
    (L : list A -> Prop) : Prop :=
  forall w, final (deterministic_run step initial w) <-> L w.

Theorem separated_prefixes_reach_distinct_states {A Q : Type}
    (step : Q -> A -> Q) initial final (L : list A -> Prop) prefixes :
  deterministic_recognizes step initial final L ->
  prefixes_separated L prefixes ->
  NoDup (map (deterministic_run step initial) prefixes).
Proof.
  intros Hrecognizes Hsep. induction prefixes as [|u us IH]; simpl.
  - constructor.
  - destruct Hsep as [Hhead Htail]. constructor.
    + intro Hin. apply in_map_iff in Hin as [v [Heq Hv]].
      destruct (Hhead v Hv) as [z [[Hu Hnv]|[Hnu Hvz]]].
      * apply Hnv, (proj1 (Hrecognizes (v ++ z))).
        assert (Hsame :
            deterministic_run step initial (u ++ z) =
            deterministic_run step initial (v ++ z)).
        { rewrite !deterministic_run_app. now rewrite Heq. }
        rewrite <- Hsame.
        now apply (proj2 (Hrecognizes (u ++ z))).
      * apply Hnu, (proj1 (Hrecognizes (u ++ z))).
        assert (Hsame :
            deterministic_run step initial (u ++ z) =
            deterministic_run step initial (v ++ z)).
        { rewrite !deterministic_run_app. now rewrite Heq. }
        rewrite Hsame.
        now apply (proj2 (Hrecognizes (v ++ z))).
    + now apply IH.
Qed.

Theorem separated_prefixes_finite_dfa_lower_bound {A Q : Type}
    (step : Q -> A -> Q) initial final (L : list A -> Prop)
    prefixes states :
  deterministic_recognizes step initial final L ->
  (forall w, In (deterministic_run step initial w) states) ->
  prefixes_separated L prefixes ->
  length prefixes <= length states.
Proof.
  intros Hrecognizes Hstates Hsep.
  rewrite <- length_map with (f := deterministic_run step initial).
  apply NoDup_incl_length.
  - now apply separated_prefixes_reach_distinct_states with (final := final)
      (L := L).
  - intros q Hq. apply in_map_iff in Hq as [w [<- _]]. apply Hstates.
Qed.

Section DerivativePrinciple.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.
Variable initial : rewpla A.

Definition derivative_of_prefix (u : list A) : rewpla A :=
  word_derivative eqb u initial.

Theorem separated_prefixes_projected_distinct prefixes :
  prefixes_separated (rewpla_language eqb initial) prefixes ->
  projected_distinct eqb (map derivative_of_prefix prefixes).
Proof.
  induction prefixes as [|u us IH]; simpl; [tauto|].
  intros [Hhead Htail]. split; [|now apply IH].
  intros d Hd Hequiv.
  apply in_map_iff in Hd as [v [<- Hv]].
  destruct (Hhead v Hv) as [z [[Hu Hnv]|[Hnu Hvz]]].
  - assert (Hdu : rewpla_language eqb (derivative_of_prefix u) z).
    { apply (proj2 (word_derivative_projected_correct
        eqb eqb_spec u initial z)). exact Hu. }
    assert (Hdv : rewpla_language eqb (derivative_of_prefix v) z)
      by now apply (proj1 (Hequiv z)).
    apply Hnv. apply (proj1 (word_derivative_projected_correct
      eqb eqb_spec v initial z)) in Hdv. exact Hdv.
  - assert (Hdv : rewpla_language eqb (derivative_of_prefix v) z).
    { apply (proj2 (word_derivative_projected_correct
        eqb eqb_spec v initial z)). exact Hvz. }
    assert (Hdu : rewpla_language eqb (derivative_of_prefix u) z)
      by now apply (proj2 (Hequiv z)).
    apply Hnu. apply (proj1 (word_derivative_projected_correct
      eqb eqb_spec u initial z)) in Hdu. exact Hdu.
Qed.

Corollary separated_prefixes_semantic_distinct prefixes :
  prefixes_separated (rewpla_language eqb initial) prefixes ->
  semantic_distinct eqb (map derivative_of_prefix prefixes).
Proof.
  intro H. apply projected_distinct_semantic_distinct.
  now apply separated_prefixes_projected_distinct.
Qed.

Theorem separated_prefixes_derivative_count prefixes :
  prefixes_separated (rewpla_language eqb initial) prefixes ->
  exists derivatives : list (rewpla A),
    length derivatives = length prefixes /\
    projected_distinct eqb derivatives /\
    semantic_distinct eqb derivatives /\
    semantic_reachable eqb initial derivatives.
Proof.
  intro Hsep. exists (map derivative_of_prefix prefixes).
  split; [now rewrite length_map|].
  assert (Hproj : projected_distinct eqb (map derivative_of_prefix prefixes))
    by now apply separated_prefixes_projected_distinct.
  split; [exact Hproj|]. split.
  - now apply projected_distinct_semantic_distinct.
  - intros d Hd. apply in_map_iff in Hd as [u [<- Hu]].
    exists u. apply lang_equiv_refl.
Qed.

End DerivativePrinciple.

(** A self-contained binomial coefficient, chosen so its recurrence matches
    the combination enumerator below. *)
Fixpoint binomial (n k : nat) : nat :=
  match n, k with
  | _, 0 => 1
  | 0, S _ => 0
  | S n', S k' => binomial n' (S k') + binomial n' k'
  end.

Fixpoint combinations {X} (k : nat) (xs : list X) : list (list X) :=
  match k, xs with
  | 0, _ => [[]]
  | S _, [] => []
  | S k', x :: xs' =>
      combinations (S k') xs' ++ map (cons x) (combinations k' xs')
  end.

Theorem combinations_length {X} k (xs : list X) :
  length (combinations k xs) = binomial (length xs) k.
Proof.
  revert k. induction xs as [|x xs IH]; intros [|k]; simpl; try reflexivity.
  rewrite length_app, length_map, !IH. reflexivity.
Qed.

Lemma combinations_members_length {X} k (xs ys : list X) :
  In ys (combinations k xs) -> length ys = k.
Proof.
  revert k ys. induction xs as [|x xs IH]; intros [|k] ys H; simpl in *.
  - destruct H as [<-|[]]. reflexivity.
  - contradiction.
  - destruct H as [<-|[]]. reflexivity.
  - apply in_app_iff in H as [H|H].
    + now apply IH in H.
    + apply in_map_iff in H as [zs [<- Hzs]]. simpl. f_equal.
      now apply IH in Hzs.
Qed.

Lemma combinations_members_source {X} k (xs ys : list X) :
  In ys (combinations k xs) -> forall y, In y ys -> In y xs.
Proof.
  revert k ys. induction xs as [|x xs IH]; intros [|k] ys H y Hy; simpl in *.
  - destruct H as [<-|[]]. contradiction.
  - contradiction.
  - destruct H as [<-|[]]. contradiction.
  - apply in_app_iff in H as [H|H].
    + right. eapply IH; eauto.
    + apply in_map_iff in H as [zs [<- Hzs]].
      destruct Hy as [<-|Hy]; [now left|right; eapply IH; eauto].
Qed.

Definition middle_subsets (k : nat) : list (list nat) :=
  combinations (k / 2) (seq 0 k).

Theorem middle_subsets_length k :
  length (middle_subsets k) = binomial k (k / 2).
Proof.
  unfold middle_subsets. rewrite combinations_length, length_seq. reflexivity.
Qed.

Definition lower_bound_families (k : nat) : list (list (list nat)) :=
  subsets (middle_subsets k).

Theorem lower_bound_families_length k :
  length (lower_bound_families k) =
    2 ^ binomial k (k / 2).
Proof.
  unfold lower_bound_families. rewrite subsets_length, middle_subsets_length.
  reflexivity.
Qed.

Print Assumptions separated_prefixes_derivative_count.
Print Assumptions separated_prefixes_finite_dfa_lower_bound.
Print Assumptions lower_bound_families_length.
