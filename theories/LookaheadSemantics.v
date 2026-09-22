From Stdlib Require Import List Bool Arith Lia Program.Equality.
From CCont Require Import StringConstraints Syntax.
Import ListNotations.

Set Implicit Arguments.

(** * Syntax and pair-language semantics for REwPLA

    This file formalizes the missing parts of Section 3 of
    [ICFP_2027_Version.pdf].  Locations refer to the red line numbers in the
    September 2026 draft currently shipped with the project.

    - p.4, lines 162--173, Section 3 and Section 3.1: [rewpla].
    - p.6, lines 281--287, Eq. (9): [rewpla_denote].
    - p.6, lines 281--287: [rewpla_derives] is the proof-relevant inference
      presentation of the same inductive semantics.
 *)

(** Paper Section 3.1, p.4, lines 167--173: the ordinary grammar extended by
    a zero-width positive-lookahead constructor.  Constructor names are
    deliberately distinct from [Syntax.regex], so both APIs can be imported
    without ambiguity. *)
Inductive rewpla (A : Type) : Type :=
| WZero
| WEps
| WAtom (a : A)
| WPlus (r s : rewpla A)
| WConcat (r s : rewpla A)
| WStar (r : rewpla A)
| WLookahead (r : rewpla A).

Arguments WZero {A}.
Arguments WEps {A}.
Arguments WAtom {A} _.
Arguments WPlus {A} _ _.
Arguments WConcat {A} _ _.
Arguments WStar {A} _.
Arguments WLookahead {A} _.

(** Paper Eq. (9), p.6, lines 281--287. *)
Fixpoint rewpla_denote {A} (eqb : A -> A -> bool) (r : rewpla A)
  : constraint_language A :=
  match r with
  | WZero => lang_zero
  | WEps => lang_one
  | WAtom a => fun p => p = ([a], [])
  | WPlus r s => lang_union (rewpla_denote eqb r) (rewpla_denote eqb s)
  | WConcat r s =>
      lang_concat eqb (rewpla_denote eqb r) (rewpla_denote eqb s)
  | WStar r => lang_star eqb (rewpla_denote eqb r)
  | WLookahead r => positive_lookahead (rewpla_denote eqb r)
  end.

(** A proof-relevant rule presentation of Eq. (9).  In particular, the two
    star rules retain the finite iteration witness which the powerset
    semantics hides. *)
Inductive rewpla_derives {A} (eqb : A -> A -> bool)
  : rewpla A -> string_constraint A -> Prop :=
| WD_Eps : rewpla_derives eqb WEps ([], [])
| WD_Atom a : rewpla_derives eqb (WAtom a) ([a], [])
| WD_PlusL r s p :
    rewpla_derives eqb r p -> rewpla_derives eqb (WPlus r s) p
| WD_PlusR r s p :
    rewpla_derives eqb s p -> rewpla_derives eqb (WPlus r s) p
| WD_Concat r s p q out :
    rewpla_derives eqb r p ->
    rewpla_derives eqb s q ->
    constraint_concat eqb p q = Some out ->
    rewpla_derives eqb (WConcat r s) out
| WD_Star0 r : rewpla_derives eqb (WStar r) ([], [])
| WD_StarApp r p q out :
    rewpla_derives eqb (WStar r) p ->
    rewpla_derives eqb r q ->
    constraint_concat eqb p q = Some out ->
    rewpla_derives eqb (WStar r) out
| WD_Lookahead r p :
    rewpla_derives eqb r p ->
    rewpla_derives eqb (WLookahead r) ([], constraint_projection p).

Section SemanticsCorrectness.
Context {A : Type} (eqb : A -> A -> bool).

Theorem rewpla_derives_sound r p :
  rewpla_derives eqb r p -> rewpla_denote eqb r p.
Proof.
  intro H. induction H; simpl.
  - reflexivity.
  - reflexivity.
  - now left.
  - now right.
  - exists p, q. repeat split; assumption.
  - exists 0. reflexivity.
  - destruct IHrewpla_derives1 as [n Hn].
    exists (S n). simpl. exists p, q. repeat split; assumption.
  - exists p. now split.
Qed.

Theorem rewpla_derives_complete r p :
  rewpla_denote eqb r p -> rewpla_derives eqb r p.
Proof.
  revert p. induction r; intros p H; simpl in H.
  - contradiction.
  - unfold lang_one in H. rewrite H. constructor.
  - rewrite H. constructor.
  - destruct H as [H|H]; [apply WD_PlusL|apply WD_PlusR]; auto.
  - destruct H as [x [y [Hx [Hy Hxy]]]].
    eapply WD_Concat; eauto.
  - destruct H as [n Hn]. revert p Hn.
    induction n; intros p Hn; simpl in Hn.
    + unfold lang_one in Hn. rewrite Hn. constructor.
    + destruct Hn as [x [y [Hx [Hy Hxy]]]].
      eapply WD_StarApp; eauto.
  - destruct H as [q [Hq ->]]. now constructor; auto.
Qed.

(** Eq. (9) as an equivalence between denotation and inference rules. *)
Theorem rewpla_derives_iff r p :
  rewpla_derives eqb r p <-> rewpla_denote eqb r p.
Proof. split; [apply rewpla_derives_sound|apply rewpla_derives_complete]. Qed.

End SemanticsCorrectness.

(** Constructive form of the paper's [E(R)] from p.7, lines 324--327. *)
Definition epsilon_part {A} (R : constraint_language A)
  : constraint_language A :=
  fun p => R ([], []) /\ p = ([], []).

Lemma positive_lookahead_identity_iff {A} (R : constraint_language A) :
  positive_lookahead R ([], []) <-> R ([], []).
Proof.
  split.
  - intros [[u v] [HR Hout]]. simpl in Hout.
    inversion Hout as [[Huv]]. unfold constraint_projection in Huv; simpl in Huv.
    symmetry in Huv. apply app_eq_nil in Huv as [Hu Hv].
    subst u v. exact HR.
  - intro HR. exists ([], []). split; [exact HR|reflexivity].
Qed.

Section Nullable.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma constraint_concat_identity_iff p q :
  constraint_concat eqb p q = Some ([], []) <->
  p = ([], []) /\ q = ([], []).
Proof.
  split.
  - destruct p as [u v], q as [u' v']. intro H.
    destruct (@constraint_concat_result_shape A eqb u v u' v' ([], []) H)
      as [t Hshape].
    pose proof (f_equal fst Hshape) as Hmain.
    simpl in Hmain. symmetry in Hmain.
    apply app_eq_nil in Hmain as [Hu Hu']. subst u u'.
    pose proof (@constraint_concat_preservation A eqb eqb_spec
      [] v [] v' [] H)
      as [Hv Hv'].
    assert (v = []) as ->.
    { apply word_prefix_antisym; [exact Hv|apply word_prefix_nil]. }
    assert (v' = []) as ->.
    { apply word_prefix_antisym; [exact Hv'|apply word_prefix_nil]. }
    now split.
  - intros [-> ->]. apply (@constraint_concat_left_identity A eqb eqb_spec).
Qed.

Fixpoint rewpla_nullable (r : rewpla A) : bool :=
  match r with
  | WZero | WAtom _ => false
  | WEps | WStar _ => true
  | WPlus r s => rewpla_nullable r || rewpla_nullable s
  | WConcat r s => rewpla_nullable r && rewpla_nullable s
  | WLookahead r => rewpla_nullable r
  end.

(** Paper Eq. (19), p.9, lines 399--405: [lambda] recognizes the identity
    pair.  Unlike [lambda_1], this test is structurally executable. *)
Definition rewpla_lambda (r : rewpla A) : rewpla A :=
  if rewpla_nullable r then WEps else WZero.

Theorem rewpla_nullable_correct r :
  rewpla_nullable r = true <-> rewpla_denote eqb r ([], []).
Proof.
  induction r; simpl.
  - split; [discriminate|contradiction].
  - split.
    + intros _. reflexivity.
    + intros _. reflexivity.
  - split; [discriminate|intro H; discriminate].
  - rewrite orb_true_iff, IHr1, IHr2. reflexivity.
  - rewrite andb_true_iff, IHr1, IHr2. split.
    + intros [Hr Hs]. exists ([], []), ([], []). repeat split; assumption || reflexivity.
    + intros [p [q [Hp [Hq Hout]]]].
      apply constraint_concat_identity_iff in Hout as [-> ->]. now split.
  - split.
    + intros _. exists 0. reflexivity.
    + intros _. reflexivity.
  - rewrite positive_lookahead_identity_iff. exact IHr.
Qed.

Theorem rewpla_lambda_correct r :
  lang_equiv (rewpla_denote eqb (rewpla_lambda r))
    (epsilon_part (rewpla_denote eqb r)).
Proof.
  intro p. unfold rewpla_lambda, epsilon_part.
  destruct (rewpla_nullable r) eqn:Hnull; simpl.
  - apply rewpla_nullable_correct in Hnull. split.
    + intro Hp. unfold lang_one in Hp. subst p. now split.
    + intros [_ Hp]. unfold lang_one. exact Hp.
  - split; [contradiction|]. intros [Hr _].
    apply rewpla_nullable_correct in Hr. congruence.
Qed.

End Nullable.

(** The projected ordinary string language [L_pi], used from p.9 onward. *)
Definition project_language {A} (R : constraint_language A) : word A -> Prop :=
  fun w => exists p, R p /\ constraint_projection p = w.

Definition rewpla_language {A} (eqb : A -> A -> bool) (r : rewpla A)
  : word A -> Prop := project_language (rewpla_denote eqb r).

Definition rewpla_equiv {A} (eqb : A -> A -> bool) (r s : rewpla A) : Prop :=
  lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s).

(** Paper p.6, lines 281--283: the concrete regular fragment is precisely
    the image of finite REwPLA syntax under [M]. *)
Definition rewpla_regular_language {A} (eqb : A -> A -> bool)
  (R : constraint_language A) : Prop :=
  exists r, lang_equiv R (rewpla_denote eqb r).

Section RegularFragment.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma rewpla_regular_zero : @rewpla_regular_language A eqb lang_zero.
Proof. exists WZero. apply lang_equiv_refl. Qed.

Lemma rewpla_regular_one : @rewpla_regular_language A eqb lang_one.
Proof. exists WEps. apply lang_equiv_refl. Qed.

Lemma rewpla_regular_atom a :
  rewpla_regular_language eqb (fun p => p = ([a], [])).
Proof. exists (WAtom a). apply lang_equiv_refl. Qed.

Lemma rewpla_regular_union R S :
  rewpla_regular_language eqb R -> rewpla_regular_language eqb S ->
  rewpla_regular_language eqb (lang_union R S).
Proof.
  intros [r Hr] [s Hs]. exists (WPlus r s).
  now apply lang_union_compat.
Qed.

Lemma rewpla_regular_concat R S :
  rewpla_regular_language eqb R -> rewpla_regular_language eqb S ->
  rewpla_regular_language eqb (lang_concat eqb R S).
Proof.
  intros [r Hr] [s Hs]. exists (WConcat r s).
  now apply lang_concat_compat.
Qed.

Lemma rewpla_regular_star R :
  rewpla_regular_language eqb R ->
  rewpla_regular_language eqb (lang_star eqb R).
Proof.
  intros [r Hr]. exists (WStar r). now apply lang_star_compat.
Qed.

Lemma rewpla_regular_lookahead R :
  rewpla_regular_language eqb R ->
  rewpla_regular_language eqb (positive_lookahead R).
Proof.
  intros [r Hr]. exists (WLookahead r). intros p.
  unfold positive_lookahead. split.
  - intros [q [Hq ->]]. exists q. split; [apply (proj1 (Hr q)); exact Hq|reflexivity].
  - intros [q [Hq ->]]. exists q. split; [apply (proj2 (Hr q)); exact Hq|reflexivity].
Qed.

End RegularFragment.

(** Embedding of the ordinary grammar recalled in Section 2.1. *)
Fixpoint embed_regex {A} (r : regex A) : rewpla A :=
  match r with
  | Zero => WZero
  | Eps => WEps
  | Atom a => WAtom a
  | Plus r s => WPlus (embed_regex r) (embed_regex s)
  | Concat r s => WConcat (embed_regex r) (embed_regex s)
  | Star r => WStar (embed_regex r)
  end.

Section OrdinaryEmbedding.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma constraint_concat_empty_context u v :
  constraint_concat eqb (u, []) (v, []) = Some (u ++ v, []).
Proof.
  unfold constraint_concat. simpl.
  destruct v; reflexivity.
Qed.

Lemma matches_star_append_right (r : regex A) u v :
  matches (Star r) u -> matches r v -> matches (Star r) (u ++ v).
Proof.
  intros Hu Hv. dependent induction Hu.
  - destruct v as [|a v].
    + constructor.
    + change (matches (Star r) (a :: v)). rewrite <- app_nil_r at 1.
      apply M_StarApp.
      * discriminate.
      * exact Hv.
      * constructor.
  - rewrite <- app_assoc. eapply M_StarApp; eauto.
Qed.

Fixpoint concat_words (ws : list (word A)) : word A :=
  match ws with [] => [] | w :: ws' => w ++ concat_words ws' end.

Fixpoint fold_words (acc : word A) (ws : list (word A)) : word A :=
  match ws with [] => acc | w :: ws' => fold_words (acc ++ w) ws' end.

Lemma fold_words_spec acc ws : fold_words acc ws = acc ++ concat_words ws.
Proof.
  revert acc. induction ws as [|w ws IH]; intro acc; simpl.
  - now rewrite app_nil_r.
  - rewrite IH. now rewrite app_assoc.
Qed.

Lemma matches_star_factors (r : regex A) w :
  matches (Star r) w ->
  exists ws, Forall (matches r) ws /\ concat_words ws = w.
Proof.
  intro H. dependent induction H.
  - exists []. now split; constructor.
  - destruct (IHmatches2 eqb eqb_spec r eq_refl) as [ws [Hws Hcat]].
    exists (u :: ws). split; [now constructor|]. simpl. now rewrite Hcat.
Qed.

Lemma rewpla_star_fold (r : rewpla A) ws acc :
  Forall (fun w => rewpla_derives eqb r (w, [])) ws ->
  rewpla_derives eqb (WStar r) (acc, []) ->
  rewpla_derives eqb (WStar r) (fold_words acc ws, []).
Proof.
  intro Hws. revert acc. induction Hws as [|w ws Hw Hws IH]; intro acc; simpl.
  - tauto.
  - intro Hacc. apply IH.
    eapply WD_StarApp; [exact Hacc|exact Hw|].
    apply constraint_concat_empty_context.
Qed.

(** Section 3, p.6, lines 281--287: the ordinary fragment embeds as exactly
    the pairs [(u,epsilon)] for [u] in the ordinary language. *)
Theorem embed_regex_semantics (r : regex A) p :
  rewpla_denote eqb (embed_regex r) p <->
  exists w, p = (w, []) /\ matches r w.
Proof.
  revert p. induction r; intros p; simpl.
  - split; [contradiction|intros [w [_ H]]; inversion H].
  - split.
    + intro Hp. exists []. split; [exact Hp|constructor].
    + intros [w [-> H]]. inversion H. reflexivity.
  - split.
    + intro Hp. exists [a]. now split; [exact Hp|constructor].
    + intros [w [-> H]]. inversion H. reflexivity.
  - split.
    + intros [Hr|Hs].
      * apply IHr1 in Hr as [w [-> Hw]]. exists w. split; [reflexivity|now constructor].
      * apply IHr2 in Hs as [w [-> Hw]]. exists w. split; [reflexivity|now constructor].
    + intros [w [-> Hw]]. inversion Hw; subst; [left; apply IHr1|right; apply IHr2];
        eexists; now split; [reflexivity|eassumption].
  - split.
    + intros [x [y [Hx [Hy Hout]]]].
      apply IHr1 in Hx as [u [-> Hu]].
      apply IHr2 in Hy as [v [-> Hv]].
      rewrite constraint_concat_empty_context in Hout. inversion Hout; subst.
      exists (u ++ v). split; [reflexivity|now constructor].
    + intros [w [-> Hw]]. inversion Hw; subst.
      exists (u, []), (v, []). repeat split.
      * apply IHr1. exists u. now split.
      * apply IHr2. exists v. now split.
      * apply constraint_concat_empty_context.
  - split.
    + intros [n Hn]. revert p Hn.
      induction n as [|n IHn]; intros p Hn; simpl in Hn.
      * exists []. split; [exact Hn|constructor].
      * destruct Hn as [x [y [Hx [Hy Hout]]]].
        apply IHn in Hx as [u [-> Hu]].
        apply IHr in Hy as [v [-> Hv]].
        rewrite constraint_concat_empty_context in Hout. inversion Hout; subst.
        exists (u ++ v). split; [reflexivity|].
        now apply matches_star_append_right.
    + intros [w [-> Hw]].
      destruct (matches_star_factors Hw) as [ws [Hws Hcat]].
      assert (Hderive : Forall
        (fun x => rewpla_derives eqb (embed_regex r) (x, [])) ws).
      { clear Hcat. induction Hws as [|x xs Hx Hxs IHxs].
        - constructor.
        - constructor.
          + apply rewpla_derives_complete. apply IHr. exists x.
            now split.
          + exact IHxs. }
      pose proof (rewpla_star_fold Hderive (@WD_Star0 A eqb (embed_regex r)))
        as Hstar.
      rewrite fold_words_spec, app_nil_l, Hcat in Hstar.
      now apply rewpla_derives_sound in Hstar.
Qed.

End OrdinaryEmbedding.

Print Assumptions rewpla_derives_iff.
Print Assumptions rewpla_nullable_correct.
Print Assumptions rewpla_lambda_correct.
Print Assumptions embed_regex_semantics.
