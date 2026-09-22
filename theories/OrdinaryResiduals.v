From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import StringConstraints Syntax LookaheadSemantics
  LookaheadDerivatives LookaheadDecision SemanticDFA.
Import ListNotations.
Set Implicit Arguments.

(** Paper p.16, lines 740--741: ordinary expressions have no context
    residuals; nonempty derivatives are unions of continuation generators.
    The resulting bound is 1 + 2^|A(r)| <= 1 + 2^width(r). *)
Fixpoint ordinaryb {A} (r : rewpla A) : bool :=
  match r with
  | WZero | WEps | WAtom _ => true
  | WPlus r s | WConcat r s => ordinaryb r && ordinaryb s
  | WStar r => ordinaryb r
  | WLookahead _ => false
  end.

Lemma ordinary_embedding {A} (r : rewpla A) :
  ordinaryb r = true -> exists s : regex A, r = embed_regex s.
Proof.
  induction r; simpl; intro H.
  - exists Zero. reflexivity.
  - exists Eps. reflexivity.
  - exists (Atom a). reflexivity.
  - apply Bool.andb_true_iff in H as [Hr Hs].
    destruct (IHr1 Hr) as [r' ->], (IHr2 Hs) as [s' ->].
    exists (Plus r' s'). reflexivity.
  - apply Bool.andb_true_iff in H as [Hr Hs].
    destruct (IHr1 Hr) as [r' ->], (IHr2 Hs) as [s' ->].
    exists (Concat r' s'). reflexivity.
  - destruct (IHr H) as [r' ->]. exists (Star r'). reflexivity.
  - discriminate.
Qed.

Arguments ordinary_embedding {A r} _.

Lemma embed_ordinary {A} (r : regex A) : ordinaryb (embed_regex r) = true.
Proof. induction r; simpl; now rewrite ?IHr, ?IHr1, ?IHr2. Qed.

Definition empty_context_language {A} (R : constraint_language A) :=
  forall u v, R (u,v) -> v = [].

Section Ordinary.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma ordinary_empty_context r : ordinaryb r = true ->
  empty_context_language (rewpla_denote eqb r).
Proof.
  intros H u v Hp. destruct (ordinary_embedding H) as [s ->].
  apply (proj1 (embed_regex_semantics eqb eqb_spec s (u,v))) in Hp.
  destruct Hp as [w [Hpair _]]. now inversion Hpair.
Qed.

Arguments ordinary_empty_context {r} _ u v _.

Lemma ordinary_constraint_generators r : ordinaryb r = true ->
  constraint_generators eqb r = [].
Proof.
  unfold constraint_generators. assert (Hraw : ordinaryb r = true ->
    constraint_generators_raw r = []).
  { induction r; simpl; intro H; try reflexivity; try discriminate.
    - apply Bool.andb_true_iff in H as [Hr Hs]. now rewrite IHr1, IHr2.
    - apply Bool.andb_true_iff in H as [Hr Hs]. now rewrite IHr1, IHr2.
    - now apply IHr. }
  intro H. rewrite Hraw by exact H. reflexivity.
Qed.

Lemma ordinary_continuation_generators r : ordinaryb r = true ->
  forall t, In t (continuation_generators eqb r) -> ordinaryb t = true.
Proof.
  intro Hr. intros t Ht. unfold continuation_generators in Ht.
  apply (proj1 (nodupb_in_iff (rewpla_eqb eqb)
    (rewpla_eqb_spec eqb eqb_spec) _ t)) in Ht.
  revert t Ht. induction r; simpl in *; intros t Ht;
    try contradiction; try discriminate.
  - destruct Ht as [<-|H]; [reflexivity|contradiction].
  - apply Bool.andb_true_iff in Hr as [Hr Hs].
    apply in_app_iff in Ht as [Ht|Ht]; [now apply IHr1|now apply IHr2].
  - apply Bool.andb_true_iff in Hr as [Hr Hs].
    apply in_app_iff in Ht as [Ht|Ht].
    + apply in_map_iff in Ht as [x [<- Hx]]. simpl.
      rewrite (IHr1 Hr x Hx), Hs. reflexivity.
    + now apply IHr2.
  - apply in_map_iff in Ht as [x [<- Hx]]. simpl.
    rewrite (IHr Hr x Hx), Hr. reflexivity.
Qed.

Arguments ordinary_continuation_generators {r} _ {t} _.

Lemma main_terms_no_constraints (as_ : list (rewpla A)) :
  main_terms as_ [] = as_.
Proof.
  unfold main_terms. simpl. rewrite app_nil_r.
  induction as_ as [|r rs IH]; simpl; [reflexivity|].
  rewrite IH. destruct r; reflexivity.
Qed.

Lemma ordinary_main_normal_forms r e : ordinaryb r = true ->
  In e (main_normal_forms (continuation_generators eqb r) []) ->
  empty_context_language (rewpla_denote eqb e).
Proof.
  intros Hr He. unfold main_normal_forms in He.
  rewrite main_terms_no_constraints in He.
  apply in_map_iff in He as [ss [<- Hss]].
  assert (Hall : forall t, In t ss -> ordinaryb t = true).
  { intros t Ht. apply (ordinary_continuation_generators Hr).
    exact ((subset_members_from_source _ ss Hss t) Ht). }
  assert (Hunion : forall xs, (forall t, In t xs -> ordinaryb t = true) ->
    empty_context_language (rewpla_denote eqb (union_expression xs))).
  { intro xs. induction xs as [|t xs IH]; intros Hxs u v Huv.
    - contradiction.
    - apply (proj1 (smart_plus_correct_M eqb t (union_expression xs) (u,v)))
        in Huv. destruct Huv as [Huv|Huv].
      + apply (ordinary_empty_context (Hxs t ltac:(now left)) u v Huv).
      + apply (IH ltac:(intros q Hq; apply Hxs; now right) u v Huv). }
  now apply Hunion.
Qed.

Arguments ordinary_main_normal_forms {r e} _ _.

Lemma empty_context_symbol_quotient a R : empty_context_language R ->
  lang_equiv (pair_language_symbol_quotient eqb a R)
    (main_symbol_quotient a R).
Proof.
  intros HR p. rewrite (pair_symbol_quotient_split eqb eqb_spec a R p).
  unfold lang_union, context_symbol_quotient.
  destruct p as [u v]. simpl. split.
  - intros [H|[_ H]]; [exact H|]. specialize (HR [] (a::v) H). discriminate.
  - intro H. now left.
Qed.

Theorem ordinary_main_normal_forms_closed r e a : ordinaryb r = true ->
  In e (main_normal_forms (continuation_generators eqb r) []) ->
  exists e', In e' (main_normal_forms (continuation_generators eqb r) []) /\
    lang_equiv (rewpla_denote eqb
      (derivative_merge (symbol_derivative_core eqb a e)))
      (rewpla_denote eqb e').
Proof.
  intros Hr He.
  pose proof (ordinary_main_normal_forms Hr He) as Hempty.
  unfold main_normal_forms in He.
  apply in_map_iff in He as [ss [<- Hss]].
  assert (Hmembers : forall t, In t ss -> In t (term_universe
    (continuation_generators eqb r) (constraint_generators eqb r))).
  { intros t Ht. rewrite ordinary_constraint_generators by exact Hr.
    unfold term_universe. apply in_app_iff. right.
    exact ((subset_members_from_source _ ss Hss t) Ht). }
  destruct (finite_union_quotients_represented eqb eqb_spec a r ss Hmembers)
    as [[m [Hm Hmsem]] _].
  rewrite ordinary_constraint_generators in Hm by exact Hr.
  exists m. split; [exact Hm|]. eapply lang_equiv_trans.
  - apply symbol_derivative_core_merge_correct. exact eqb_spec.
  - eapply lang_equiv_trans; [apply empty_context_symbol_quotient; exact Hempty|].
    exact Hmsem.
Qed.

Arguments ordinary_main_normal_forms_closed {r e a} _ _.

Theorem ordinary_one_letter_normal_form r a : ordinaryb r = true ->
  exists e, In e (main_normal_forms (continuation_generators eqb r) []) /\
    lang_equiv (rewpla_denote eqb
      (derivative_merge (symbol_derivative_core eqb a r)))
      (rewpla_denote eqb e).
Proof.
  intro Hr. destruct (symbol_derivative_represented_all eqb eqb_spec a r)
    as [[m [Hm Hmsem]] _].
  rewrite ordinary_constraint_generators in Hm by exact Hr.
  exists m. split; [exact Hm|]. eapply lang_equiv_trans.
  - apply symbol_derivative_core_merge_correct. exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply empty_context_symbol_quotient, ordinary_empty_context. exact Hr.
    + eapply lang_equiv_trans; [|exact Hmsem].
      destruct (symbol_derivative_core_correct eqb eqb_spec a r) as [Hmain _].
      apply lang_equiv_sym. exact Hmain.
Qed.

Arguments ordinary_one_letter_normal_form {r a} _.

Theorem ordinary_word_normal_forms_closed r w e : ordinaryb r = true ->
  In e (main_normal_forms (continuation_generators eqb r) []) ->
  exists e', In e' (main_normal_forms (continuation_generators eqb r) []) /\
    lang_equiv (rewpla_denote eqb (word_derivative eqb w e))
      (rewpla_denote eqb e').
Proof.
  intros Hr. revert e. induction w as [|a w IH]; intros e He; simpl.
  - exists e. split; [exact He|apply lang_equiv_refl].
  - destruct (ordinary_main_normal_forms_closed (a := a) Hr He)
      as [m [Hm Hmsem]].
    destruct (IH m Hm) as [n [Hn Hnsem]]. exists n. split; [exact Hn|].
    eapply lang_equiv_trans; [apply word_derivative_congruent_M; eassumption|].
    exact Hnsem.
Qed.

Arguments ordinary_word_normal_forms_closed {r} w {e} _ _.

Theorem ordinary_nonempty_word_normal_form r w : ordinaryb r = true -> w <> [] ->
  exists e, In e (main_normal_forms (continuation_generators eqb r) []) /\
    lang_equiv (rewpla_denote eqb (word_derivative eqb w r))
      (rewpla_denote eqb e).
Proof.
  intros Hr Hnon. destruct w as [|a w]; [contradiction|]. simpl.
  destruct (ordinary_one_letter_normal_form (a := a) Hr) as [m [Hm Hmsem]].
  destruct (ordinary_word_normal_forms_closed w Hr Hm) as [n [Hn Hnsem]].
  exists n. split; [exact Hn|]. eapply lang_equiv_trans.
  - apply word_derivative_congruent_M; eassumption.
  - exact Hnsem.
Qed.

Arguments ordinary_nonempty_word_normal_form {r w} _ _.

Theorem ordinary_semantic_derivatives_cover_bound r : ordinaryb r = true ->
  exists states : list (rewpla A),
    length states <= 1 + 2 ^ length (continuation_generators eqb r) /\
    length states <= 1 + 2 ^ rewpla_width r /\
    forall w, exists e, In e states /\
      lang_equiv (rewpla_denote eqb (word_derivative eqb w r))
        (rewpla_denote eqb e).
Proof.
  intro Hr. exists (r :: main_normal_forms (continuation_generators eqb r) []).
  assert (Hlength : length (main_normal_forms (continuation_generators eqb r) [])
    = 2 ^ length (continuation_generators eqb r)).
  { unfold main_normal_forms. rewrite length_map, subsets_length,
      main_terms_no_constraints. reflexivity. }
  split; [simpl; rewrite Hlength; lia|]. split.
  - simpl. rewrite Hlength. apply le_n_S, pow_two_monotone.
    pose proof (generator_length_bound eqb r). lia.
  - intro w. destruct w as [|a w].
    + exists r. split; [now left|apply lang_equiv_refl].
    + destruct (ordinary_nonempty_word_normal_form (w := a::w) Hr
        ltac:(discriminate)) as [e [He Hsem]].
      exists e. split; [now right|exact Hsem].
Qed.
End Ordinary.

Print Assumptions ordinary_nonempty_word_normal_form.
Print Assumptions ordinary_semantic_derivatives_cover_bound.
