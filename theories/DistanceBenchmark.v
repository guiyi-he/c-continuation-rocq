From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import StringConstraints Syntax LookaheadSemantics.
Import ListNotations.
Set Implicit Arguments.

(** * A native distance benchmark for the experimental solver

    This file fixes the semantic claim used by [cpp/bench/distance_bench.cpp].
    It does not participate in extraction and does not change the existing
    decision procedure. *)

Inductive distance_symbol := DistanceA | DistanceB.

Definition distance_symbol_eqb (x y : distance_symbol) : bool :=
  match x, y with
  | DistanceA, DistanceA | DistanceB, DistanceB => true
  | _, _ => false
  end.

Lemma distance_symbol_eqb_spec x y :
  distance_symbol_eqb x y = true <-> x = y.
Proof.
  destruct x, y; simpl; split; intro H; try reflexivity; discriminate.
Qed.

Definition distance_sigma : regex distance_symbol :=
  Plus (Atom DistanceA) (Atom DistanceB).

Fixpoint distance_repeat (n : nat) : regex distance_symbol :=
  match n with
  | 0 => Eps
  | S n' => Concat distance_sigma (distance_repeat n')
  end.

Definition distance_prefix : regex distance_symbol :=
  Concat (Star distance_sigma) (Atom DistanceA).

Definition distance_constraint n : regex distance_symbol :=
  Concat (distance_repeat n) (Atom DistanceB).

Definition distance_expression n : rewpla distance_symbol :=
  WConcat (embed_regex distance_prefix)
    (WLookahead (embed_regex (distance_constraint n))).

Definition distance_ordinary_expression n : rewpla distance_symbol :=
  embed_regex (Concat distance_prefix (distance_constraint n)).

Definition distance_alternating_regex : regex distance_symbol :=
  Star (Concat (Atom DistanceA) (Atom DistanceB)).

Lemma constraint_concat_plain_constraint u v :
  constraint_concat distance_symbol_eqb (u, []) ([], v) = Some (u, v).
Proof.
  unfold constraint_concat, join, residual. simpl.
  destruct v; simpl; now rewrite app_nil_r.
Qed.

(** An ordinary prefix followed by an ordinary positive assertion projects to
    ordinary concatenation.  This is the reusable semantic bridge behind the
    benchmark definition. *)
Lemma ordinary_lookahead_projected (r s : regex distance_symbol) w :
  rewpla_language distance_symbol_eqb
      (WConcat (embed_regex r) (WLookahead (embed_regex s))) w <->
  exists u v, matches r u /\ matches s v /\ w = u ++ v.
Proof.
  unfold rewpla_language, project_language. simpl. split.
  - intros [[m c] [Hden Hprojection]].
    destruct Hden as [[um cm] [[uq cq] [Hr [Hlook Hcat]]]].
    apply (proj1 (embed_regex_semantics distance_symbol_eqb
      distance_symbol_eqb_spec r (um, cm))) in Hr.
    destruct Hr as [u [Hpair Hu]]. inversion Hpair; subst um cm.
    destruct Hlook as [[vm vc] [Hs Hlook]].
    apply (proj1 (embed_regex_semantics distance_symbol_eqb
      distance_symbol_eqb_spec s (vm, vc))) in Hs.
    destruct Hs as [v [Hpair2 Hv]]. inversion Hpair2; subst vm vc.
    unfold constraint_projection in Hlook. simpl in Hlook.
    rewrite app_nil_r in Hlook. inversion Hlook; subst uq cq.
    rewrite constraint_concat_plain_constraint in Hcat.
    inversion Hcat; subst m c.
    unfold constraint_projection in Hprojection. simpl in Hprojection.
    exists u, v. repeat split; try assumption.
    symmetry. exact Hprojection.
  - intros [u [v [Hu [Hv ->]]]].
    exists (u, v). split.
    + exists (u, []), ([], v). repeat split.
      * apply (proj2 (embed_regex_semantics distance_symbol_eqb
          distance_symbol_eqb_spec r (u, []))).
        exists u. now split.
      * exists (v, []). split.
        -- apply (proj2 (embed_regex_semantics distance_symbol_eqb
             distance_symbol_eqb_spec s (v, []))).
           exists v. now split.
        -- unfold constraint_projection. simpl. now rewrite app_nil_r.
      * apply constraint_concat_plain_constraint.
    + unfold constraint_projection. simpl. reflexivity.
Qed.

Lemma embed_regex_projected (r : regex distance_symbol) w :
  rewpla_language distance_symbol_eqb (embed_regex r) w <-> matches r w.
Proof.
  unfold rewpla_language, project_language. split.
  - intros [[u v] [Hden Hprojection]].
    apply (proj1 (embed_regex_semantics distance_symbol_eqb
      distance_symbol_eqb_spec r (u, v))) in Hden.
    destruct Hden as [x [Hpair Hmatches]]. inversion Hpair; subst u v.
    unfold constraint_projection in Hprojection. simpl in Hprojection.
    rewrite app_nil_r in Hprojection. now subst w.
  - intro Hmatches. exists (w, []). split.
    + apply (proj2 (embed_regex_semantics distance_symbol_eqb
        distance_symbol_eqb_spec r (w, []))).
      exists w. now split.
    + unfold constraint_projection. simpl. now rewrite app_nil_r.
Qed.

Lemma matches_distance_sigma w :
  matches distance_sigma w <-> exists a, w = [a].
Proof.
  split.
  - intro H. inversion H; subst;
      match goal with
      | Ha : matches (Atom _) _ |- _ => inversion Ha; subst; eauto
      end.
  - intros [a ->]. destruct a; unfold distance_sigma.
    + apply M_PlusL. constructor.
    + apply M_PlusR. constructor.
Qed.

Lemma matches_distance_sigma_star w : matches (Star distance_sigma) w.
Proof.
  induction w as [|a w IH].
  - constructor.
  - change (matches (Star distance_sigma) ([a] ++ w)).
    apply M_StarApp.
    + discriminate.
    + apply matches_distance_sigma. now exists a.
    + exact IH.
Qed.

Lemma matches_distance_repeat n w :
  matches (distance_repeat n) w <-> length w = n.
Proof.
  revert w. induction n as [|n IH]; intro w; simpl.
  - split.
    + intro H. inversion H. reflexivity.
    + intro H. destruct w; [constructor|discriminate].
  - split.
    + intro H. inversion H; subst.
      match goal with
      | Hsigma : matches distance_sigma ?u,
        Hrest : matches (distance_repeat n) ?v |- _ =>
          apply matches_distance_sigma in Hsigma as [a ->];
          apply IH in Hrest; simpl; lia
      end.
    + intro Hlen. destruct w as [|a w]; [discriminate|].
      change (matches (Concat distance_sigma (distance_repeat n))
        ([a] ++ w)).
      apply M_Concat.
      * apply matches_distance_sigma. now exists a.
      * apply IH. simpl in Hlen. lia.
Qed.

Lemma matches_distance_prefix w :
  matches distance_prefix w <-> exists x, w = x ++ [DistanceA].
Proof.
  unfold distance_prefix. split.
  - intro H. inversion H; subst.
    match goal with
    | Hstar : matches (Star distance_sigma) ?u,
      Ha : matches (Atom DistanceA) ?v |- _ =>
        inversion Ha; subst; exists u; reflexivity
    end.
  - intros [x ->]. apply M_Concat.
    + apply matches_distance_sigma_star.
    + constructor.
Qed.

Lemma matches_distance_constraint n w :
  matches (distance_constraint n) w <->
  exists y, length y = n /\ w = y ++ [DistanceB].
Proof.
  unfold distance_constraint. split.
  - intro H. inversion H; subst.
    match goal with
    | Hrepeat : matches (distance_repeat n) ?u,
      Hb : matches (Atom DistanceB) ?v |- _ =>
        inversion Hb; subst; exists u; split;
          [now apply matches_distance_repeat|reflexivity]
    end.
  - intros [y [Hlen ->]]. apply M_Concat.
    + now apply matches_distance_repeat.
    + constructor.
Qed.

(** Exact projected language of the C++ [distance_n] expression. *)
Theorem distance_expression_projected_exact n w :
  rewpla_language distance_symbol_eqb (distance_expression n) w <->
  exists x y, length y = n /\
    w = x ++ DistanceA :: y ++ [DistanceB].
Proof.
  unfold distance_expression.
  rewrite ordinary_lookahead_projected. split.
  - intros [u [v [Hu [Hv ->]]]].
    apply matches_distance_prefix in Hu as [x ->].
    apply matches_distance_constraint in Hv as [y [Hlen ->]].
    exists x, y. split; [exact Hlen|].
    repeat rewrite <- app_assoc. reflexivity.
  - intros [x [y [Hlen ->]]].
    exists (x ++ [DistanceA]), (y ++ [DistanceB]). repeat split.
    + apply matches_distance_prefix. now exists x.
    + apply matches_distance_constraint. exists y. now split.
    + repeat rewrite <- app_assoc. reflexivity.
Qed.

(** The no-lookahead control used by the benchmark has exactly the same
    projected language. *)
Theorem distance_ordinary_projected_exact n w :
  rewpla_language distance_symbol_eqb (distance_ordinary_expression n) w <->
  exists x y, length y = n /\
    w = x ++ DistanceA :: y ++ [DistanceB].
Proof.
  unfold distance_ordinary_expression. rewrite embed_regex_projected. split.
  - intro H. inversion H; subst.
    match goal with
    | Hprefix : matches distance_prefix ?u,
      Hconstraint : matches (distance_constraint n) ?v |- _ =>
        apply matches_distance_prefix in Hprefix as [x ->];
        apply matches_distance_constraint in Hconstraint as [y [Hlen ->]];
        exists x, y; split; [exact Hlen|];
        repeat rewrite <- app_assoc; reflexivity
    end.
  - intros [x [y [Hlen ->]]].
    replace (x ++ DistanceA :: y ++ [DistanceB]) with
      ((x ++ [DistanceA]) ++ (y ++ [DistanceB])).
    2: { repeat rewrite <- app_assoc. reflexivity. }
    apply M_Concat.
    + apply matches_distance_prefix. now exists x.
    + apply matches_distance_constraint. exists y. now split.
Qed.

Theorem distance_ordinary_projected_equivalent n w :
  rewpla_language distance_symbol_eqb (distance_ordinary_expression n) w <->
  rewpla_language distance_symbol_eqb (distance_expression n) w.
Proof.
  rewrite distance_ordinary_projected_exact,
    distance_expression_projected_exact. reflexivity.
Qed.

Theorem distance_expression_shortest_length n :
  (exists w,
    rewpla_language distance_symbol_eqb (distance_expression n) w /\
    length w = n + 2) /\
  (forall w, rewpla_language distance_symbol_eqb (distance_expression n) w ->
    n + 2 <= length w).
Proof.
  split.
  - exists (DistanceA :: repeat DistanceA n ++ [DistanceB]). split.
    + apply distance_expression_projected_exact.
      exists [], (repeat DistanceA n). split.
      * apply repeat_length.
      * reflexivity.
    + simpl. rewrite length_app, repeat_length. simpl. lia.
  - intros w H.
    apply distance_expression_projected_exact in H
      as [x [y [Hlen ->]]].
    rewrite length_app. simpl. rewrite length_app. simpl. lia.
Qed.

Fixpoint distance_alternating_word (k : nat) : list distance_symbol :=
  match k with
  | 0 => []
  | S k' => DistanceA :: DistanceB :: distance_alternating_word k'
  end.

Lemma distance_alternating_word_length k :
  length (distance_alternating_word k) = 2 * k.
Proof. induction k; simpl; lia. Qed.

Lemma matches_distance_alternating_pair w :
  matches (Concat (Atom DistanceA) (Atom DistanceB)) w <->
  w = [DistanceA; DistanceB].
Proof.
  split.
  - intro H. inversion H; subst. inversion H2; inversion H4; reflexivity.
  - intros ->. change
      (matches (Concat (Atom DistanceA) (Atom DistanceB))
        ([DistanceA] ++ [DistanceB])).
    constructor; constructor.
Qed.

Lemma matches_distance_alternating_word k :
  matches distance_alternating_regex (distance_alternating_word k).
Proof.
  induction k as [|k IH]; simpl.
  - constructor.
  - change (matches distance_alternating_regex
      ([DistanceA; DistanceB] ++ distance_alternating_word k)).
    apply M_StarApp.
    + discriminate.
    + apply matches_distance_alternating_pair. reflexivity.
    + exact IH.
Qed.

Lemma concat_distance_alternating_factors ws :
  Forall (matches (Concat (Atom DistanceA) (Atom DistanceB))) ws ->
  concat_words ws = distance_alternating_word (length ws).
Proof.
  intro H. induction H; simpl; [reflexivity|].
  apply matches_distance_alternating_pair in H. subst x.
  simpl. now rewrite IHForall.
Qed.

Lemma matches_distance_alternating_exact w :
  matches distance_alternating_regex w <->
  exists k, w = distance_alternating_word k.
Proof.
  split.
  - intro H.
    destruct (matches_star_factors distance_symbol_eqb
      distance_symbol_eqb_spec H) as [ws [Hws Hconcat]].
    exists (length ws). rewrite <- Hconcat.
    now apply concat_distance_alternating_factors.
  - intros [k ->]. apply matches_distance_alternating_word.
Qed.

Fixpoint distance_alternating_middle (k : nat) : list distance_symbol :=
  match k with
  | 0 => []
  | S k' => DistanceB :: DistanceA :: distance_alternating_middle k'
  end.

Lemma distance_alternating_middle_length k :
  length (distance_alternating_middle k) = 2 * k.
Proof. induction k; simpl; lia. Qed.

Lemma distance_alternating_word_succ k :
  distance_alternating_word (S k) =
  DistanceA :: distance_alternating_middle k ++ [DistanceB].
Proof.
  induction k as [|k IH].
  - reflexivity.
  - change
      (DistanceA :: DistanceB :: distance_alternating_word (S k) =
       DistanceA :: DistanceB :: DistanceA ::
         distance_alternating_middle k ++ [DistanceB]).
    now rewrite IH.
Qed.

Lemma distance_A_prefix_even k x z :
  distance_alternating_word k = x ++ DistanceA :: z ->
  exists i, length x = 2 * i.
Proof.
  revert x z. induction k as [|k IH]; intros x z Heq.
  - destruct x; discriminate.
  - destruct x as [|c x].
    + exists 0. reflexivity.
    + simpl in Heq. injection Heq as Hc Htail. subst c.
      destruct x as [|d x].
      * discriminate.
      * simpl in Htail. injection Htail as Hd Hrest. subst d.
        destruct (IH x z Hrest) as [i Hi].
        exists (S i). simpl. lia.
Qed.

Definition distance_instance_nonempty n : Prop :=
  exists w,
    rewpla_language distance_symbol_eqb (distance_expression n) w /\
    matches distance_alternating_regex w.

(** The SAT/UNSAT parity invariant checked by the C++ benchmark. *)
Theorem distance_instance_nonempty_iff_even n :
  distance_instance_nonempty n <-> exists k, n = 2 * k.
Proof.
  split.
  - intros [w [Hdistance Halternating]].
    apply distance_expression_projected_exact in Hdistance
      as [x [y [Hy Hword]]].
    apply matches_distance_alternating_exact in Halternating as [j Hj].
    rewrite Hj in Hword.
    destruct (distance_A_prefix_even j x (y ++ [DistanceB]) Hword)
      as [i Hi].
    assert (Hlength : 2 * j = 2 * i + n + 2).
    { rewrite <- distance_alternating_word_length.
      rewrite Hword. rewrite !length_app, Hi.
      simpl. rewrite length_app. simpl. lia. }
    assert (i + 1 <= j) by lia.
    exists (j - i - 1). lia.
  - intros [k ->].
    exists (distance_alternating_word (S k)). split.
    + apply distance_expression_projected_exact.
      exists [], (distance_alternating_middle k). split.
      * apply distance_alternating_middle_length.
      * simpl. apply distance_alternating_word_succ.
    + apply matches_distance_alternating_word.
Qed.

Definition distance_ordinary_instance_nonempty n : Prop :=
  exists w,
    rewpla_language distance_symbol_eqb (distance_ordinary_expression n) w /\
    matches distance_alternating_regex w.

Theorem distance_ordinary_instance_nonempty_iff_even n :
  distance_ordinary_instance_nonempty n <-> exists k, n = 2 * k.
Proof.
  rewrite <- distance_instance_nonempty_iff_even.
  unfold distance_ordinary_instance_nonempty, distance_instance_nonempty.
  split.
  - intros [w [Hdistance Halternating]]. exists w. split.
    + now apply distance_ordinary_projected_equivalent in Hdistance.
    + exact Halternating.
  - intros [w [Hdistance Halternating]]. exists w. split.
    + now apply distance_ordinary_projected_equivalent.
    + exact Halternating.
Qed.

(** A controlled nesting-depth family used by the topology experiment.
    [distance_nested_chain n] contains [n] positive assertions, each requiring
    one more [DistanceA] in the continuation. *)
Fixpoint distance_nested_chain (n : nat) : rewpla distance_symbol :=
  match n with
  | 0 => WEps
  | S n' =>
      WLookahead (WConcat (WAtom DistanceA) (distance_nested_chain n'))
  end.

Lemma distance_nested_chain_denote_exact n p :
  rewpla_denote distance_symbol_eqb (distance_nested_chain n) p <->
  p = ([], repeat DistanceA n).
Proof.
  revert p. induction n as [|n IH]; intro p; simpl.
  - reflexivity.
  - unfold positive_lookahead, lang_concat. split.
    + intros [q [[p1 [p2 [Hatom [Hrest Hconcat]]]] Hp]].
      subst p1. apply IH in Hrest. subst p2.
      rewrite constraint_concat_plain_constraint in Hconcat.
      inversion Hconcat; subst q.
      unfold constraint_projection in Hp. simpl in Hp.
      exact Hp.
    + intros ->. exists ([DistanceA], repeat DistanceA n). split.
      * exists ([DistanceA], []), ([], repeat DistanceA n).
        split.
        -- exact eq_refl.
        -- split.
           ++ apply IH. reflexivity.
           ++ apply constraint_concat_plain_constraint.
      * unfold constraint_projection. simpl. reflexivity.
Qed.

Theorem distance_nested_chain_projected_exact n w :
  rewpla_language distance_symbol_eqb (distance_nested_chain n) w <->
  w = repeat DistanceA n.
Proof.
  unfold rewpla_language, project_language. split.
  - intros [p [Hp Hprojection]].
    apply distance_nested_chain_denote_exact in Hp. subst p.
    unfold constraint_projection in Hprojection. simpl in Hprojection.
    symmetry. exact Hprojection.
  - intros ->. exists ([], repeat DistanceA n). split.
    + apply distance_nested_chain_denote_exact. reflexivity.
    + unfold constraint_projection. simpl. reflexivity.
Qed.

Theorem distance_nested_chain_shortest_length n :
  (exists w,
    rewpla_language distance_symbol_eqb (distance_nested_chain n) w /\
    length w = n) /\
  (forall w,
    rewpla_language distance_symbol_eqb (distance_nested_chain n) w ->
    n <= length w).
Proof.
  split.
  - exists (repeat DistanceA n). split.
    + apply distance_nested_chain_projected_exact. reflexivity.
    + apply repeat_length.
  - intros w Hw. apply distance_nested_chain_projected_exact in Hw.
    subst w. rewrite repeat_length. lia.
Qed.

Print Assumptions ordinary_lookahead_projected.
Print Assumptions distance_expression_projected_exact.
Print Assumptions distance_ordinary_projected_equivalent.
Print Assumptions distance_expression_shortest_length.
Print Assumptions distance_instance_nonempty_iff_even.
Print Assumptions distance_ordinary_instance_nonempty_iff_even.
Print Assumptions distance_nested_chain_projected_exact.
Print Assumptions distance_nested_chain_shortest_length.
