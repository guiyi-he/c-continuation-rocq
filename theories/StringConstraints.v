From Stdlib Require Import List Bool Arith Lia Relation_Definitions.
Import ListNotations.

Set Implicit Arguments.

(** * Languages with string constraints

    This file formalizes Section 3.2 of [ICFP_2027_Version.pdf].  References
    below use the red source-line numbers printed in that draft.

    Paper-to-code map:

    - p.4, lines 175--179: [word], [string_constraint],
      [constraint_language], and [constraint_projection].
    - p.4, lines 180--182: [word_prefix], [prefix_compatible],
      [left_quotient], its uniqueness theorem, and the executable examples.
    - p.4, lines 183--190, Eq. (4): [join] and [residual].
    - p.4, lines 191--195, Eq. (5): [constraint_concat].
    - pp.4--5, lines 195--202, Proposition 1: [constraint_concat_preservation].
    - p.5, lines 204--212, Lemma 1:
      [constraint_concat_defined_iff_residual] and
      [constraint_concat_defined_iff_compatible].
    - p.5, lines 214--225, Proposition 2:
      [constraint_concat_least_residual].
    - p.5, lines 226--229, Remark 1:
      [constraint_concat_characterization].
    - pp.5--6, lines 231--260, Proposition 3, Eq. (6):
      [constraint_concat_assoc_graph] and [constraint_concat_assoc].
    - p.6, lines 261--268, Eq. (7): [lang_union], [lang_concat],
      [lang_zero], [lang_one], [positive_lookahead], [lang_power], and
      [lang_star].
    - p.6, lines 269--272, Eq. (8): [main_language], [constr_language].
    - p.6, lines 273--280, Proposition 4:
      [constraint_languages_idempotent_semiring].
    - p.6, lines 281--287: [rational_constraint_language].
 *)

(** Paper Section 3.2, p.4, lines 175--179: strings, constrained pairs,
    their full language domain, and "pi(u,v) = uv". *)
Definition word (A : Type) := list A.
Definition string_constraint (A : Type) := (word A * word A)%type.
Definition constraint_language (A : Type) := string_constraint A -> Prop.

Definition constraint_projection {A} (p : string_constraint A) : word A :=
  fst p ++ snd p.

(** Paper Section 3.2, p.4, lines 175--179: the two component projections
    [pi_1] and [pi_2].  Keeping them named makes later quotient statements
    read like the paper rather than exposing pair implementation details. *)
Definition constraint_main {A} (p : string_constraint A) : word A := fst p.
Definition constraint_context {A} (p : string_constraint A) : word A := snd p.

(** Paper Section 3.2, p.4, lines 180--182: "u is a prefix of v" and
    prefix compatibility. *)
Definition word_prefix {A} (u v : word A) : Prop :=
  exists z, v = u ++ z.

Definition prefix_compatible {A} (u v : word A) : Prop :=
  word_prefix u v \/ word_prefix v u.

Lemma word_prefix_refl {A} (u : word A) : word_prefix u u.
Proof. exists []; now rewrite app_nil_r. Qed.

Lemma word_prefix_nil {A} (u : word A) : word_prefix [] u.
Proof. now exists u. Qed.

Lemma word_prefix_trans {A} (u v w : word A) :
  word_prefix u v -> word_prefix v w -> word_prefix u w.
Proof.
  intros [x ->] [y ->]. exists (x ++ y). now rewrite app_assoc.
Qed.

Lemma word_prefix_antisym {A} (u v : word A) :
  word_prefix u v -> word_prefix v u -> u = v.
Proof.
  intros [x Hx] [y Hy]. subst v.
  assert (Hlen : length x = 0).
  { apply (f_equal (@length A)) in Hy. rewrite !length_app in Hy. simpl in Hy. lia. }
  destruct x; [now rewrite app_nil_r|discriminate].
Qed.

Lemma word_prefix_app_left {A} (x u v : word A) :
  word_prefix u v -> word_prefix (x ++ u) (x ++ v).
Proof.
  intros [z ->]. exists z. now rewrite app_assoc.
Qed.

Lemma word_prefix_app_left_iff {A} (x u v : word A) :
  word_prefix (x ++ u) (x ++ v) <-> word_prefix u v.
Proof.
  split; [|apply word_prefix_app_left].
  intros [z Hz]. exists z. apply (app_inv_head x).
  now rewrite app_assoc.
Qed.

Lemma word_prefix_common_upper {A} (u v s : word A) :
  word_prefix u s -> word_prefix v s -> prefix_compatible u v.
Proof.
  revert v s.
  induction u as [|a u IH]; intros v s Hu Hv.
  - left. apply word_prefix_nil.
  - destruct v as [|b v].
    + right. apply word_prefix_nil.
    + destruct Hu as [xu Hu], Hv as [xv Hv].
      destruct s as [|c s]; simpl in Hu, Hv; try discriminate.
      inversion Hu; inversion Hv; subst c b.
      specialize (IH v s).
      assert (Huv : prefix_compatible u v).
      { apply IH; [exists xu | exists xv]; assumption. }
      destruct Huv as [Huv|Hvu].
      * left. destruct Huv as [z ->]. exists z. reflexivity.
      * right. destruct Hvu as [z ->]. exists z. reflexivity.
Qed.

Section ExecutableWords.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

(** Paper Section 3.2, p.4, lines 180--182: executable [u^-1 v]. *)
Fixpoint left_quotient (u v : word A) : option (word A) :=
  match u, v with
  | [], _ => Some v
  | _, [] => None
  | a :: u, b :: v =>
      if eqb a b then left_quotient u v else None
  end.

Lemma left_quotient_spec u v z :
  left_quotient u v = Some z <-> v = u ++ z.
Proof.
  revert v z.
  induction u as [|a u IH]; intros [|b v] z; simpl.
  - split; intro H; [now inversion H|now subst].
  - split; intro H; [now inversion H|now inversion H].
  - split; [discriminate|intro H; discriminate].
  - destruct (eqb a b) eqn:E.
    + apply eqb_spec in E. subst b. rewrite IH.
      split; intro H; [now inversion H|now inversion H].
    + split; [discriminate|].
      intro H. inversion H; subst b.
      pose proof (proj2 (eqb_spec a a) eq_refl). congruence.
Qed.

Lemma left_quotient_defined_iff u v :
  (exists z, left_quotient u v = Some z) <-> word_prefix u v.
Proof.
  split.
  - intros [z Hz]. exists z. now apply left_quotient_spec in Hz.
  - intros [z Hz]. exists z. now apply left_quotient_spec.
Qed.

(** The free-monoid quotient is unique (p.4, line 181). *)
Lemma left_quotient_unique u v x y :
  left_quotient u v = Some x -> left_quotient u v = Some y -> x = y.
Proof. congruence. Qed.

(** Paper Eq. (4), p.4, lines 183--190: [join] returns the longer of two
    compatible words.  It is [None] exactly for incompatible words. *)
Definition join (u v : word A) : option (word A) :=
  match left_quotient u v with
  | Some _ => Some v
  | None =>
      match left_quotient v u with
      | Some _ => Some u
      | None => None
      end
  end.

(** Paper Eq. (4): [v/u] is [u^-1 v] when [u] is a prefix of [v], and the
    empty word otherwise. *)
Definition residual (v u : word A) : word A :=
  match left_quotient u v with
  | Some z => z
  | None => []
  end.

Lemma join_result u v t :
  join u v = Some t ->
  (word_prefix u v /\ t = v) \/ (word_prefix v u /\ t = u).
Proof.
  unfold join. destruct (left_quotient u v) as [z|] eqn:Huv.
  - intro H. inversion H; subst. left. split; [|reflexivity].
    apply left_quotient_spec in Huv. now exists z.
  - destruct (left_quotient v u) as [z|] eqn:Hvu; [|discriminate].
    intro H. inversion H; subst. right. split; [|reflexivity].
    apply left_quotient_spec in Hvu. now exists z.
Qed.

Lemma join_defined_iff u v :
  (exists t, join u v = Some t) <-> prefix_compatible u v.
Proof.
  split.
  - intros [t Ht]. apply join_result in Ht. unfold prefix_compatible. tauto.
  - intros [Huv|Hvu].
    + destruct Huv as [z Hz].
      assert (left_quotient u v = Some z) as Hq.
      { apply left_quotient_spec. exact Hz. }
      exists v. unfold join. now rewrite Hq.
    + destruct Hvu as [z Hz].
      assert (left_quotient v u = Some z) as Hq.
      { apply left_quotient_spec. exact Hz. }
      unfold join. destruct (left_quotient u v) as [x|] eqn:Hfirst.
      * exists v. reflexivity.
      * rewrite Hq. exists u. reflexivity.
Qed.

Lemma join_upper_left u v t :
  join u v = Some t -> word_prefix u t.
Proof.
  intro H. apply join_result in H. destruct H as [[H ->]|[_ ->]];
    [exact H|apply word_prefix_refl].
Qed.

Lemma join_upper_right u v t :
  join u v = Some t -> word_prefix v t.
Proof.
  intro H. apply join_result in H. destruct H as [[_ ->]|[H ->]];
    [apply word_prefix_refl|exact H].
Qed.

Lemma join_least u v t s :
  join u v = Some t ->
  word_prefix u s -> word_prefix v s -> word_prefix t s.
Proof.
  intros H Hu Hv. apply join_result in H.
  destruct H as [[_ ->]|[_ ->]]; assumption.
Qed.

Lemma residual_consumed v u :
  word_prefix v u -> residual v u = [].
Proof.
  intro Hvu. unfold residual.
  destruct (left_quotient u v) as [z|] eqn:Huv; [|reflexivity].
  apply left_quotient_spec in Huv.
  assert (u = v) as ->.
  { apply word_prefix_antisym; [now exists z|exact Hvu]. }
  assert (z = []) as ->.
  { apply (app_inv_head v). now rewrite app_nil_r. }
  reflexivity.
Qed.

Lemma residual_extended v u :
  word_prefix u v -> v = u ++ residual v u.
Proof.
  intros [z Hz]. unfold residual.
  assert (left_quotient u v = Some z) as Hq.
  { apply left_quotient_spec. exact Hz. }
  now rewrite Hq.
Qed.

Lemma residual_least v u s :
  word_prefix v (u ++ s) -> word_prefix (residual v u) s.
Proof.
  intro Hv.
  assert (Hcompat : prefix_compatible v u).
  { eapply word_prefix_common_upper; [exact Hv|].
    exists s. reflexivity. }
  destruct Hcompat as [Hvu|Huv].
  - rewrite (residual_consumed Hvu). apply word_prefix_nil.
  - pose proof (residual_extended Huv) as Heq.
    apply (proj1 (word_prefix_app_left_iff u (residual v u) s)).
    now rewrite <- Heq.
Qed.

Lemma residual_join_compatible v u v' :
  prefix_compatible v (u ++ v') ->
  prefix_compatible (residual v u) v'.
Proof.
  intros [Hv|Hv].
  - assert (Hcompat : prefix_compatible v u).
    { eapply word_prefix_common_upper; [exact Hv|].
      exists v'. reflexivity. }
    destruct Hcompat as [Hvu|Huv].
    + rewrite (residual_consumed Hvu). left. apply word_prefix_nil.
    + left. pose proof (residual_extended Huv) as Heq.
      apply (proj1 (word_prefix_app_left_iff u (residual v u) v')).
      now rewrite <- Heq.
  - assert (Huv : word_prefix u v).
    { eapply word_prefix_trans; [exists v'; reflexivity|exact Hv]. }
    right. pose proof (residual_extended Huv) as Heq.
    apply (proj1 (word_prefix_app_left_iff u v' (residual v u))).
    now rewrite <- Heq.
Qed.

Lemma residual_preserves_constraint v u v' t :
  prefix_compatible v (u ++ v') ->
  word_prefix (residual v u) t ->
  word_prefix v (u ++ t).
Proof.
  intros Hcompat Hres.
  assert (Hvu : prefix_compatible v u).
  { destruct Hcompat as [H|H].
    - eapply word_prefix_common_upper; [exact H|exists v'; reflexivity].
    - right. eapply word_prefix_trans; [exists v'; reflexivity|exact H]. }
  destruct Hvu as [Hvu|Huv].
  - eapply word_prefix_trans; [exact Hvu|]. exists t. reflexivity.
  - pose proof (residual_extended Huv) as Heq. rewrite Heq.
    now apply word_prefix_app_left.
Qed.

(** Paper Eq. (5), p.4, lines 191--195: partial concatenation of constrained
    pairs.  The first [join] is the definedness test [v compatible u'v']; the
    second computes [(v/u') join v']. *)
Definition constraint_concat
  (p q : string_constraint A) : option (string_constraint A) :=
  let '(u, v) := p in
  let '(u', v') := q in
  match join v (u' ++ v') with
  | None => None
  | Some _ =>
      match join (residual v u') v' with
      | None => None
      | Some t => Some (u ++ u', t)
      end
  end.

Lemma constraint_concat_result_shape u v u' v' out :
  constraint_concat (u, v) (u', v') = Some out ->
  exists t, out = (u ++ u', t).
Proof.
  unfold constraint_concat. simpl.
  destruct (join v (u' ++ v')); [|discriminate].
  destruct (join (residual v u') v'); [|discriminate].
  intro H. inversion H; subst. eauto.
Qed.

Lemma constraint_concat_defined_from_compatible u v u' v' :
  prefix_compatible v (u' ++ v') ->
  exists t, constraint_concat (u, v) (u', v') = Some (u ++ u', t).
Proof.
  intro Hcompat.
  apply (proj2 (join_defined_iff v (u' ++ v'))) in Hcompat.
  destruct Hcompat as [outer Houter].
  pose proof (join_result v (u' ++ v') Houter) as Houter_result.
  assert (prefix_compatible v (u' ++ v')) as Hcompatible.
  { destruct Houter_result as [[H _]|[H _]]; [left|right]; exact H. }
  pose proof (@residual_join_compatible v u' v' Hcompatible) as Hres.
  apply (proj2 (join_defined_iff (residual v u') v')) in Hres.
  destruct Hres as [t Ht]. exists t.
  unfold constraint_concat. simpl. now rewrite Houter, Ht.
Qed.

(** Proposition 1 (Constraint preservation), pp.4--5, lines 195--202. *)
Theorem constraint_concat_preservation u v u' v' t :
  constraint_concat (u, v) (u', v') = Some (u ++ u', t) ->
  word_prefix v (u' ++ t) /\ word_prefix v' t.
Proof.
  unfold constraint_concat. simpl.
  destruct (join v (u' ++ v')) as [outer|] eqn:Houter; [|discriminate].
  destruct (join (residual v u') v') as [result|] eqn:Hresult;
    [|discriminate].
  intro H. inversion H; subst result.
  assert (Hcompat : prefix_compatible v (u' ++ v')).
  { apply join_result in Houter.
    destruct Houter as [[Hp _]|[Hp _]]; [left|right]; exact Hp. }
  split.
  - (* Paper pp.4--5, lines 197--202: the two cases [v <= u'] and [u' <= v]
       are encapsulated by [residual_preserves_constraint]. *)
    eapply residual_preserves_constraint; [exact Hcompat|].
    exact (join_upper_left (residual v u') v' Hresult).
  - (* Paper pp.4--5, lines 199--202: the join preserves the right operand. *)
    exact (join_upper_right (residual v u') v' Hresult).
Qed.

(** Lemma 1, p.5, lines 204--212: definedness is exactly prefix
    compatibility. *)
Theorem constraint_concat_defined_iff_compatible u v u' v' :
  (exists t, constraint_concat (u, v) (u', v') = Some (u ++ u', t)) <->
  prefix_compatible v (u' ++ v').
Proof.
  split.
  - intros [t Ht]. apply constraint_concat_preservation in Ht.
    destruct Ht as [Hv Hv'].
    eapply word_prefix_common_upper; [exact Hv|].
    now apply word_prefix_app_left.
  - apply constraint_concat_defined_from_compatible.
Qed.

(** Lemma 1, p.5, lines 204--212: the existential residual
    formulation of definedness. *)
Theorem constraint_concat_defined_iff_residual u v u' v' :
  (exists out, constraint_concat (u, v) (u', v') = Some (u ++ u', out)) <->
  (exists t, word_prefix v (u' ++ t) /\ word_prefix v' t).
Proof.
  split.
  - intros [t Ht]. exists t.
    exact (constraint_concat_preservation u v u' v' Ht).
  - (* Paper p.5, lines 208--212: both constraints are prefixes of [u't],
       hence are compatible and Eq. (5) is defined. *)
    intros [t [Hv Hv']]. apply constraint_concat_defined_from_compatible.
    eapply word_prefix_common_upper; [exact Hv|].
    now apply word_prefix_app_left.
Qed.

Definition residual_requirements
  (v u' v' t : word A) : Prop :=
  word_prefix v (u' ++ t) /\ word_prefix v' t.

Definition least_residual
  (v u' v' t : word A) : Prop :=
  residual_requirements v u' v' t /\
  forall s, residual_requirements v u' v' s -> word_prefix t s.

(** Proposition 2 (Least residual constraint), p.5, lines 214--225. *)
Theorem constraint_concat_least_residual u v u' v' t :
  constraint_concat (u, v) (u', v') = Some (u ++ u', t) ->
  least_residual v u' v' t.
Proof.
  intro Hconcat. split.
  - (* Paper p.5, lines 217--218: Proposition 1 supplies the requirements. *)
    now apply constraint_concat_preservation in Hconcat.
  - intros s [Hvs Hv's].
    unfold constraint_concat in Hconcat. simpl in Hconcat.
    destruct (join v (u' ++ v')) as [outer|] eqn:Houter; [|discriminate].
    destruct (join (residual v u') v') as [result|] eqn:Hresult;
      [|discriminate].
    inversion Hconcat; subst result.
    (* Paper p.5, lines 219--223: [residual_least] covers the two quotient
       cases; the join is the least common prefix upper bound. *)
    eapply join_least; [exact Hresult|now apply residual_least|exact Hv's].
Qed.

(** Remark 1, p.5, lines 226--229: preservation plus leastness completely
    characterizes the residual returned by pair concatenation. *)
Theorem constraint_concat_characterization u v u' v' t :
  constraint_concat (u, v) (u', v') = Some (u ++ u', t) <->
  least_residual v u' v' t.
Proof.
  split; [apply constraint_concat_least_residual|].
  intros Hleast.
  destruct Hleast as [Hreq Hleast].
  assert (Hex : exists s, word_prefix v (u' ++ s) /\ word_prefix v' s).
  { exists t. exact Hreq. }
  pose proof (proj2 (constraint_concat_defined_iff_residual u v u' v') Hex)
    as Hdefined.
  destruct Hdefined as [actual Hactual].
  pose proof (constraint_concat_least_residual u v u' v' Hactual)
    as Hactual_least.
  destruct Hactual_least as [Hactual_req Hactual_least].
  assert (word_prefix t actual) as Hta by now apply Hleast.
  assert (word_prefix actual t) as Hat by now apply Hactual_least.
  assert (t = actual) as -> by now apply word_prefix_antisym.
  exact Hactual.
Qed.

Definition option_bind {X Y} (o : option X) (f : X -> option Y) : option Y :=
  match o with Some x => f x | None => None end.

(** Paper Proposition 3, p.5, lines 235--239: the set [T] of common triple
    residuals. *)
Definition triple_requirements
  (v u' v' u'' v'' t : word A) : Prop :=
  word_prefix v (u' ++ u'' ++ t) /\
  word_prefix v' (u'' ++ t) /\
  word_prefix v'' t.

Definition least_triple_residual
  (v u' v' u'' v'' t : word A) : Prop :=
  triple_requirements v u' v' u'' v'' t /\
  forall s, triple_requirements v u' v' u'' v'' s -> word_prefix t s.

Lemma left_assoc_characterization u v u' v' u'' v'' t :
  option_bind (constraint_concat (u, v) (u', v'))
    (fun pq => constraint_concat pq (u'', v'')) =
  Some (u ++ u' ++ u'', t) <->
  least_triple_residual v u' v' u'' v'' t.
Proof.
  split.
  - (* Paper pp.5--6, lines 240--250: the left-associated result is defined
       exactly when [T] is inhabited and is its least element. *)
    unfold option_bind.
    destruct (constraint_concat (u, v) (u', v')) as [pq|] eqn:Hpq;
      [|discriminate].
    destruct (constraint_concat_result_shape u v u' v' Hpq) as [t1 ->].
    intro Hfinal.
    rewrite app_assoc in Hfinal.
    pose proof (constraint_concat_least_residual u v u' v' Hpq) as Hleast1.
    pose proof (constraint_concat_least_residual
      (u ++ u') t1 u'' v'' Hfinal) as Hleast2.
    destruct Hleast1 as [[Hv Hv'] Hleast1].
    destruct Hleast2 as [[Ht1 Hv''] Hleast2].
    split.
    + repeat split.
      * eapply word_prefix_trans; [exact Hv|].
        now apply word_prefix_app_left.
      * eapply word_prefix_trans; eauto.
      * exact Hv''.
    + intros s [Hvs [Hv's Hv''s]].
      assert (word_prefix t1 (u'' ++ s)) as Ht1s.
      { apply Hleast1. split; [|exact Hv's].
        exact Hvs. }
      apply Hleast2. now split.
  - (* Paper pp.5--6, lines 243--250: an element of [T] first defines the inner
       concatenation, then the outer one; mutual leastness fixes the result. *)
    intros [Hreq Hleast]. destruct Hreq as [Hvt [Hv't Hv''t]].
    assert (Hex1 : exists t1,
      constraint_concat (u, v) (u', v') = Some (u ++ u', t1)).
    { apply constraint_concat_defined_from_compatible.
      eapply word_prefix_common_upper; [exact Hvt|].
      now apply word_prefix_app_left. }
    destruct Hex1 as [t1 Ht1].
    pose proof (constraint_concat_least_residual u v u' v' Ht1) as Hleast1.
    destruct Hleast1 as [[Hv1 Hv1'] Hleast1].
    assert (Ht1t : word_prefix t1 (u'' ++ t)).
    { apply Hleast1. split; [exact Hvt|exact Hv't]. }
    assert (Hex2 : exists t2,
      constraint_concat (u ++ u', t1) (u'', v'') =
        Some ((u ++ u') ++ u'', t2)).
    { apply (proj2 (constraint_concat_defined_iff_residual
        (u ++ u') t1 u'' v'')).
      exists t. now split. }
    destruct Hex2 as [t2 Ht2].
    pose proof (constraint_concat_least_residual
      (u ++ u') t1 u'' v'' Ht2) as Hleast2.
    destruct Hleast2 as [[Ht12 Hv''2] Hleast2].
    assert (Htriple2 : triple_requirements v u' v' u'' v'' t2).
    { repeat split.
      - eapply word_prefix_trans; [exact Hv1|].
        now apply word_prefix_app_left.
      - eapply word_prefix_trans; eauto.
      - exact Hv''2. }
    assert (word_prefix t t2) as Htt2 by now apply Hleast.
    assert (word_prefix t2 t) as Ht2t.
    { apply Hleast2. now split. }
    assert (t = t2) as -> by now apply word_prefix_antisym.
    unfold option_bind. rewrite Ht1. rewrite app_assoc. exact Ht2.
Qed.

Lemma right_assoc_characterization u v u' v' u'' v'' t :
  option_bind (constraint_concat (u', v') (u'', v''))
    (fun qr => constraint_concat (u, v) qr) =
  Some (u ++ u' ++ u'', t) <->
  least_triple_residual v u' v' u'' v'' t.
Proof.
  split.
  - (* Paper p.6, lines 251--260: the right-associated result is governed
       by the same set [T]. *)
    unfold option_bind.
    destruct (constraint_concat (u', v') (u'', v'')) as [qr|] eqn:Hqr;
      [|discriminate].
    destruct (constraint_concat_result_shape u' v' u'' v'' Hqr) as [t2 ->].
    intro Hfinal.
    pose proof (constraint_concat_least_residual u' v' u'' v'' Hqr)
      as Hleast2.
    pose proof (constraint_concat_least_residual
      u v (u' ++ u'') t2 Hfinal) as Hleast3.
    destruct Hleast2 as [[Hv' Hv''] Hleast2].
    destruct Hleast3 as [[Hv Ht2] Hleast3].
    split.
    + repeat split.
      * rewrite <- app_assoc in Hv. exact Hv.
      * eapply word_prefix_trans; [exact Hv'|].
        now apply word_prefix_app_left.
      * eapply word_prefix_trans; eauto.
    + intros s [Hvs [Hv's Hv''s]].
      assert (word_prefix t2 s) as Ht2s.
      { apply Hleast2. now split. }
      apply Hleast3. split; [rewrite app_assoc in Hvs; exact Hvs|exact Ht2s].
  - (* Paper p.6, lines 253--260: leastness on the inner right pair and
       then on the outer pair yields the same least member of [T]. *)
    intros [Hreq Hleast]. destruct Hreq as [Hvt [Hv't Hv''t]].
    assert (Hex1 : exists t2,
      constraint_concat (u', v') (u'', v'') = Some (u' ++ u'', t2)).
    { apply (proj2 (constraint_concat_defined_iff_residual
        u' v' u'' v'')).
      exists t. now split. }
    destruct Hex1 as [t2 Ht2].
    pose proof (constraint_concat_least_residual u' v' u'' v'' Ht2)
      as Hleast2.
    destruct Hleast2 as [[Hv'2 Hv''2] Hleast2].
    assert (Ht2t : word_prefix t2 t).
    { apply Hleast2. now split. }
    assert (Hex2 : exists t3,
      constraint_concat (u, v) (u' ++ u'', t2) =
        Some (u ++ (u' ++ u''), t3)).
    { apply (proj2 (constraint_concat_defined_iff_residual
        u v (u' ++ u'') t2)).
      exists t. split; [now rewrite <- app_assoc|exact Ht2t]. }
    destruct Hex2 as [t3 Ht3].
    pose proof (constraint_concat_least_residual
      u v (u' ++ u'') t2 Ht3) as Hleast3.
    destruct Hleast3 as [[Hv3 Ht23] Hleast3].
    assert (Htriple3 : triple_requirements v u' v' u'' v'' t3).
    { repeat split.
      - rewrite <- app_assoc in Hv3. exact Hv3.
      - eapply word_prefix_trans; [exact Hv'2|].
        now apply word_prefix_app_left.
      - eapply word_prefix_trans; eauto. }
    assert (word_prefix t t3) as Htt3 by now apply Hleast.
    assert (word_prefix t3 t) as Ht3t.
    { apply Hleast3. split; [now rewrite <- app_assoc|exact Ht2t]. }
    assert (t = t3) as -> by now apply word_prefix_antisym.
    unfold option_bind. now rewrite Ht2.
Qed.

(** Proposition 3 (Associativity), pp.5--6, lines 231--260, Eq. (6), in
    graph form. *)
Theorem constraint_concat_assoc_graph p q r out :
  (exists pq,
    constraint_concat p q = Some pq /\
    constraint_concat pq r = Some out) <->
  (exists qr,
    constraint_concat q r = Some qr /\
    constraint_concat p qr = Some out).
Proof.
  destruct p as [u v], q as [u' v'], r as [u'' v''], out as [main t].
  split.
  - intros [pq [Hpq Hout]].
    destruct (constraint_concat_result_shape u v u' v' Hpq) as [t1 ->].
    destruct (constraint_concat_result_shape
      (u ++ u') t1 u'' v'' Hout) as [t2 Hshape].
    inversion Hshape; subst main t2.
    assert (Hleft : option_bind (constraint_concat (u, v) (u', v'))
      (fun x => constraint_concat x (u'', v'')) =
      Some (u ++ u' ++ u'', t)).
    { unfold option_bind. rewrite Hpq. rewrite app_assoc. exact Hout. }
    apply (proj1 (left_assoc_characterization u v u' v' u'' v'' t)) in Hleft.
    pose proof (proj2 (right_assoc_characterization
      u v u' v' u'' v'' t) Hleft) as Hright.
    unfold option_bind in Hright.
    destruct (constraint_concat (u', v') (u'', v'')) as [qr|] eqn:Hqr;
      [|discriminate].
    exists qr. split; [reflexivity|].
    rewrite app_assoc in Hright. exact Hright.
  - intros [qr [Hqr Hout]].
    destruct (constraint_concat_result_shape u' v' u'' v'' Hqr) as [t2 ->].
    destruct (constraint_concat_result_shape
      u v (u' ++ u'') t2 Hout) as [t3 Hshape].
    inversion Hshape; subst main t3.
    assert (Hright : option_bind (constraint_concat (u', v') (u'', v''))
      (fun x => constraint_concat (u, v) x) =
      Some (u ++ u' ++ u'', t)).
    { unfold option_bind. rewrite Hqr. exact Hout. }
    apply (proj1 (right_assoc_characterization u v u' v' u'' v'' t))
      in Hright.
    pose proof (proj2 (left_assoc_characterization
      u v u' v' u'' v'' t) Hright) as Hleft.
    unfold option_bind in Hleft.
    destruct (constraint_concat (u, v) (u', v')) as [pq|] eqn:Hpq;
      [|discriminate].
    exists pq. split; [reflexivity|].
    exact Hleft.
Qed.

(** Proposition 3, Eq. (6), as equality of partial computations.  Equality
    of options simultaneously states equal definedness and equal results. *)
Theorem constraint_concat_assoc p q r :
  option_bind (constraint_concat p q) (fun pq => constraint_concat pq r) =
  option_bind (constraint_concat q r) (fun qr => constraint_concat p qr).
Proof.
  destruct (option_bind (constraint_concat p q)
    (fun pq => constraint_concat pq r)) as [out|] eqn:Hleft.
  - unfold option_bind in Hleft.
    destruct (constraint_concat p q) as [pq|] eqn:Hpq; [|discriminate].
    assert (exists qr, constraint_concat q r = Some qr /\
      constraint_concat p qr = Some out) as Hright.
    { apply (proj1 (constraint_concat_assoc_graph p q r out)). eauto. }
    destruct Hright as [qr [Hqr Hout]].
    unfold option_bind. now rewrite Hqr, Hout.
  - destruct (option_bind (constraint_concat q r)
      (fun qr => constraint_concat p qr)) as [out|] eqn:Hright;
      [|reflexivity].
    unfold option_bind in Hright.
    destruct (constraint_concat q r) as [qr|] eqn:Hqr; [|discriminate].
    assert (exists pq, constraint_concat p q = Some pq /\
      constraint_concat pq r = Some out) as Hleft_exists.
    { apply (proj2 (constraint_concat_assoc_graph p q r out)). eauto. }
    destruct Hleft_exists as [pq [Hpq Hout]].
    unfold option_bind in Hleft. now rewrite Hpq, Hout in Hleft.
Qed.

Lemma constraint_concat_right_identity (p : string_constraint A) :
  constraint_concat p ([], []) = Some p.
Proof.
  destruct p as [u v].
  assert (Hid : constraint_concat (u, v) ([], []) = Some (u ++ [], v)).
  { apply (proj2 (constraint_concat_characterization u v [] [] v)).
    split.
    - split; [simpl; apply word_prefix_refl|apply word_prefix_nil].
    - intros s [Hvs _]. exact Hvs. }
  now rewrite app_nil_r in Hid.
Qed.

Lemma constraint_concat_left_identity (p : string_constraint A) :
  constraint_concat ([], []) p = Some p.
Proof.
  destruct p as [u v].
  apply (proj2 (constraint_concat_characterization
    [] [] u v v)).
  split.
  - split; [apply word_prefix_nil|apply word_prefix_refl].
  - intros s [_ Hvs]. exact Hvs.
Qed.

End ExecutableWords.

(** Paper p.6, lines 261--265: languages are predicates over constrained
    pairs.  Extensional equivalence avoids any function-extensionality axiom. *)
Definition lang_equiv {A} (R S : constraint_language A) : Prop :=
  forall p, R p <-> S p.

(** Paper Eq. (7), p.6, lines 261--265: language addition is set union. *)
Definition lang_union {A} (R S : constraint_language A)
  : constraint_language A :=
  fun p => R p \/ S p.

Definition lang_intersection {A} (R S : constraint_language A)
  : constraint_language A :=
  fun p => R p /\ S p.

(** Paper p.6, line 266: [0] is empty and [1] contains only the empty pair. *)
Definition lang_zero {A} : constraint_language A := fun _ => False.

Definition lang_one {A} : constraint_language A :=
  fun p => p = ([], []).

(** Paper p.6, lines 266--268: "its positive lookahead" moves the projection
    of each pair into the constraint component. *)
Definition positive_lookahead {A} (R : constraint_language A)
  : constraint_language A :=
  fun p => exists q, R q /\ p = ([], constraint_projection q).

(** Paper Section 3.2, p.6, lines 269--272, Eq. (8). *)
Definition main_language {A} (R : constraint_language A)
  : constraint_language A :=
  fun p => constraint_main p <> [] /\ R p.

Definition constr_language {A} (R : constraint_language A)
  : constraint_language A :=
  fun p => constraint_main p = [] /\ R p.

(** Paper p.6, line 272: [R = Main(R) union Constr(R)]. *)
Lemma main_constr_partition {A} (R : constraint_language A) :
  lang_equiv R (lang_union (main_language R) (constr_language R)).
Proof.
  intros [u v]. destruct u as [|a u];
    unfold lang_union, main_language, constr_language, constraint_main; simpl.
  - split.
    + intro HR. right. now split.
    + intros [[H _]|[_ HR]]; [exfalso; now apply H|exact HR].
  - split.
    + intro HR. left. split; [discriminate|exact HR].
    + intros [[_ HR]|[H _]]; [exact HR|discriminate].
Qed.

(** Paper p.6, line 272: [Main(R) intersection Constr(R) = empty]. *)
Lemma main_constr_disjoint {A} (R : constraint_language A) :
  lang_equiv (lang_intersection (main_language R) (constr_language R))
    lang_zero.
Proof.
  intros p. unfold lang_intersection, main_language, constr_language,
    lang_zero. tauto.
Qed.

Section ConstraintLanguages.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

(** Paper Eq. (7), p.6, lines 261--265: pointwise lifting of the partial
    pair concatenation. *)
Definition lang_concat (R S : constraint_language A)
  : constraint_language A :=
  fun out => exists p q,
    R p /\ S q /\ constraint_concat eqb p q = Some out.

(** Paper p.6, lines 266--268: powers and Kleene star induced by [lang_concat]. *)
Fixpoint lang_power (R : constraint_language A) (n : nat)
  : constraint_language A :=
  match n with
  | 0 => lang_one
  | S n => lang_concat (lang_power R n) R
  end.

Definition lang_star (R : constraint_language A) : constraint_language A :=
  fun p => exists n, lang_power R n p.

Lemma lang_equiv_refl (R : constraint_language A) : lang_equiv R R.
Proof. intros p; tauto. Qed.

Lemma lang_equiv_sym (R S : constraint_language A) :
  lang_equiv R S -> lang_equiv S R.
Proof. intros H p; specialize (H p); tauto. Qed.

Lemma lang_equiv_trans (R S T : constraint_language A) :
  lang_equiv R S -> lang_equiv S T -> lang_equiv R T.
Proof. intros H1 H2 p; specialize (H1 p); specialize (H2 p); tauto. Qed.

Lemma lang_union_compat (R R' S S' : constraint_language A) :
  lang_equiv R R' -> lang_equiv S S' ->
  lang_equiv (lang_union R S) (lang_union R' S').
Proof.
  intros HR HS p. unfold lang_union.
  specialize (HR p); specialize (HS p). tauto.
Qed.

Lemma lang_concat_compat (R R' S S' : constraint_language A) :
  lang_equiv R R' -> lang_equiv S S' ->
  lang_equiv (lang_concat R S) (lang_concat R' S').
Proof.
  intros HR HS out. unfold lang_concat. split.
  - intros [p [q [Hp [Hq Hout]]]]. exists p, q. repeat split; try assumption.
    + apply (proj1 (HR p)). exact Hp.
    + apply (proj1 (HS q)). exact Hq.
  - intros [p [q [Hp [Hq Hout]]]]. exists p, q. repeat split; try assumption.
    + apply (proj2 (HR p)). exact Hp.
    + apply (proj2 (HS q)). exact Hq.
Qed.

Lemma lang_power_compat (R S : constraint_language A) n :
  lang_equiv R S -> lang_equiv (lang_power R n) (lang_power S n).
Proof.
  intro H. induction n; simpl.
  - apply lang_equiv_refl.
  - apply lang_concat_compat; assumption.
Qed.

Lemma lang_star_compat (R S : constraint_language A) :
  lang_equiv R S -> lang_equiv (lang_star R) (lang_star S).
Proof.
  intros H p. unfold lang_star. split; intros [n Hn]; exists n.
  - apply (proj1 (lang_power_compat (R:=R) (S:=S) n H p)). exact Hn.
  - apply (proj2 (lang_power_compat (R:=R) (S:=S) n H p)). exact Hn.
Qed.

Lemma lang_union_assoc (R S T : constraint_language A) :
  lang_equiv (lang_union (lang_union R S) T)
    (lang_union R (lang_union S T)).
Proof. intros p; unfold lang_union; tauto. Qed.

Lemma lang_union_comm (R S : constraint_language A) :
  lang_equiv (lang_union R S) (lang_union S R).
Proof. intros p; unfold lang_union; tauto. Qed.

Lemma lang_union_idempotent (R : constraint_language A) :
  lang_equiv (lang_union R R) R.
Proof. intros p; unfold lang_union; tauto. Qed.

Lemma lang_union_zero_left (R : constraint_language A) :
  lang_equiv (lang_union lang_zero R) R.
Proof. intros p; unfold lang_union, lang_zero; tauto. Qed.

Lemma lang_union_zero_right (R : constraint_language A) :
  lang_equiv (lang_union R lang_zero) R.
Proof. intros p; unfold lang_union, lang_zero; tauto. Qed.

(** Proposition 3 lifted pointwise, as used in the proof of Proposition 4
    (p.6, lines 273--277). *)
Lemma lang_concat_assoc (R S T : constraint_language A) :
  lang_equiv (lang_concat (lang_concat R S) T)
    (lang_concat R (lang_concat S T)).
Proof.
  intros out. unfold lang_concat. split.
  - intros [pq [r [[p [q [Hp [Hq Hpq]]]] [Hr Hout]]]].
    pose proof (proj1 (constraint_concat_assoc_graph eqb eqb_spec p q r out)
      (ex_intro _ pq (conj Hpq Hout))) as Hassoc.
    destruct Hassoc as [qr [Hqr Hfinal]].
    exists p, qr. repeat split; try assumption.
    exists q, r. repeat split; assumption.
  - intros [p [qr [Hp [[q [r [Hq [Hr Hqr]]]] Hout]]]].
    pose proof (proj2 (constraint_concat_assoc_graph eqb eqb_spec p q r out)
      (ex_intro _ qr (conj Hqr Hout))) as Hassoc.
    destruct Hassoc as [pq [Hpq Hfinal]].
    exists pq, r. repeat split; try assumption.
    exists p, q. repeat split; assumption.
Qed.

(** Proposition 4 proof, p.6, lines 276--277: singleton [(epsilon,epsilon)]
    is a two-sided identity. *)
Lemma lang_concat_one_left (R : constraint_language A) :
  lang_equiv (lang_concat lang_one R) R.
Proof.
  intros out. unfold lang_concat, lang_one. split.
  - intros [p [q [-> [Hq Hout]]]].
    rewrite (constraint_concat_left_identity eqb eqb_spec q) in Hout.
    now inversion Hout; subst.
  - intro Hout. exists ([], []), out. repeat split; try assumption.
    exact (constraint_concat_left_identity eqb eqb_spec out).
Qed.

Lemma lang_concat_one_right (R : constraint_language A) :
  lang_equiv (lang_concat R lang_one) R.
Proof.
  intros out. unfold lang_concat, lang_one. split.
  - intros [p [q [Hp [-> Hout]]]].
    rewrite (constraint_concat_right_identity eqb eqb_spec p) in Hout.
    now inversion Hout; subst.
  - intro Hout. exists out, ([], []). repeat split; try assumption.
    exact (constraint_concat_right_identity eqb eqb_spec out).
Qed.

(** Proposition 4 proof, p.6, lines 278--279: zero absorption. *)
Lemma lang_concat_zero_left (R : constraint_language A) :
  lang_equiv (lang_concat lang_zero R) lang_zero.
Proof.
  intros out. unfold lang_concat, lang_zero. split; [|contradiction].
  intros [p [q [Hp _]]]. contradiction.
Qed.

Lemma lang_concat_zero_right (R : constraint_language A) :
  lang_equiv (lang_concat R lang_zero) lang_zero.
Proof.
  intros out. unfold lang_concat, lang_zero. split; [|contradiction].
  intros [p [q [_ [Hq _]]]]. contradiction.
Qed.

(** Proposition 4 proof, p.6, lines 278--279: pointwise distributivity. *)
Lemma lang_concat_union_left (R S T : constraint_language A) :
  lang_equiv (lang_concat (lang_union R S) T)
    (lang_union (lang_concat R T) (lang_concat S T)).
Proof.
  intros out. unfold lang_concat, lang_union. split.
  - intros [p [q [[Hp|Hp] [Hq Hout]]]]; [left|right];
      exists p, q; repeat split; assumption.
  - intros [[p [q [Hp [Hq Hout]]]]|[p [q [Hp [Hq Hout]]]]];
      exists p, q; repeat split; try assumption; [left|right]; assumption.
Qed.

Lemma lang_concat_union_right (R S T : constraint_language A) :
  lang_equiv (lang_concat R (lang_union S T))
    (lang_union (lang_concat R S) (lang_concat R T)).
Proof.
  intros out. unfold lang_concat, lang_union. split.
  - intros [p [q [Hp [[Hq|Hq] Hout]]]]; [left|right];
      exists p, q; repeat split; assumption.
  - intros [[p [q [Hp [Hq Hout]]]]|[p [q [Hp [Hq Hout]]]]];
      exists p, q; repeat split; try assumption; [left|right]; assumption.
Qed.

(** A constructive, setoid-based statement of the algebraic laws.  The
    record is generic so Proposition 4 is expressed as one checked value,
    rather than as an informal collection of unrelated lemmas. *)
Record idempotent_semiring_laws
  (S : Type) (equiv : S -> S -> Prop)
  (plus times : S -> S -> S) (zero one : S) : Prop := {
  isl_equiv_refl : forall x, equiv x x;
  isl_equiv_sym : forall x y, equiv x y -> equiv y x;
  isl_equiv_trans : forall x y z, equiv x y -> equiv y z -> equiv x z;
  isl_plus_compat : forall x x' y y',
    equiv x x' -> equiv y y' -> equiv (plus x y) (plus x' y');
  isl_times_compat : forall x x' y y',
    equiv x x' -> equiv y y' -> equiv (times x y) (times x' y');
  isl_plus_assoc : forall x y z, equiv (plus (plus x y) z) (plus x (plus y z));
  isl_plus_comm : forall x y, equiv (plus x y) (plus y x);
  isl_plus_idempotent : forall x, equiv (plus x x) x;
  isl_plus_zero_left : forall x, equiv (plus zero x) x;
  isl_plus_zero_right : forall x, equiv (plus x zero) x;
  isl_times_assoc : forall x y z,
    equiv (times (times x y) z) (times x (times y z));
  isl_times_one_left : forall x, equiv (times one x) x;
  isl_times_one_right : forall x, equiv (times x one) x;
  isl_times_zero_left : forall x, equiv (times zero x) zero;
  isl_times_zero_right : forall x, equiv (times x zero) zero;
  isl_distrib_left : forall x y z,
    equiv (times (plus x y) z) (plus (times x z) (times y z));
  isl_distrib_right : forall x y z,
    equiv (times x (plus y z)) (plus (times x y) (times x z))
}.

(** Proposition 4 (Idempotent semiring), p.6, lines 273--280. *)
Theorem constraint_languages_idempotent_semiring :
  @idempotent_semiring_laws
    (constraint_language A) lang_equiv lang_union lang_concat lang_zero lang_one.
Proof.
  constructor.
  - apply lang_equiv_refl.
  - apply lang_equiv_sym.
  - apply lang_equiv_trans.
  - apply lang_union_compat.
  - apply lang_concat_compat.
  - apply lang_union_assoc.
  - apply lang_union_comm.
  - apply lang_union_idempotent.
  - apply lang_union_zero_left.
  - apply lang_union_zero_right.
  - apply lang_concat_assoc.
  - apply lang_concat_one_left.
  - apply lang_concat_one_right.
  - apply lang_concat_zero_left.
  - apply lang_concat_zero_right.
  - apply lang_concat_union_left.
  - apply lang_concat_union_right.
Qed.

(** Paper p.6, lines 281--287: the regular fragment is the closure of a
    chosen family of basic constrained languages.  Section 3.1 does not fix
    that family, so it is an explicit parameter here. *)
Inductive rational_constraint_language
  (Basic : constraint_language A -> Prop) : constraint_language A -> Prop :=
| RationalBasic R : Basic R -> rational_constraint_language Basic R
| RationalUnion R S :
    rational_constraint_language Basic R ->
    rational_constraint_language Basic S ->
    rational_constraint_language Basic (lang_union R S)
| RationalConcat R S :
    rational_constraint_language Basic R ->
    rational_constraint_language Basic S ->
    rational_constraint_language Basic (lang_concat R S)
| RationalStar R :
    rational_constraint_language Basic R ->
    rational_constraint_language Basic (lang_star R).

End ConstraintLanguages.

(** Executable counterparts of the two quotient examples on p.4, lines
    169--170.  We encode [h,e,l,o] by [0,1,2,3]. *)
Module PaperExamples.

Definition hello : word nat := [0; 1; 2; 2; 3].

Example left_quotient_h_hello :
  left_quotient Nat.eqb [0] hello = Some [1; 2; 2; 3].
Proof. reflexivity. Qed.

Example left_quotient_he_hello :
  left_quotient Nat.eqb [0; 1] hello = Some [2; 2; 3].
Proof. reflexivity. Qed.

Example residual_consumed_example :
  residual Nat.eqb [1] [1; 2] = [].
Proof. reflexivity. Qed.

Example residual_extended_example :
  residual Nat.eqb [1; 2; 3] [1] = [2; 3].
Proof. reflexivity. Qed.

Example join_example :
  join Nat.eqb [2; 3] [2; 3; 4] = Some [2; 3; 4].
Proof. reflexivity. Qed.

Example concat_consumed_example :
  constraint_concat Nat.eqb ([9], [1]) ([1; 2], [3]) =
    Some ([9; 1; 2], [3]).
Proof. reflexivity. Qed.

Example concat_extended_example :
  constraint_concat Nat.eqb ([9], [1; 2; 3]) ([1], [2; 3; 4]) =
    Some ([9; 1], [2; 3; 4]).
Proof. reflexivity. Qed.

Example concat_undefined_example :
  constraint_concat Nat.eqb ([9], [1]) ([2], [3]) = None.
Proof. reflexivity. Qed.

Example concat_left_identity_example :
  constraint_concat Nat.eqb ([], []) ([1; 2], [3]) = Some ([1; 2], [3]).
Proof. reflexivity. Qed.

Example concat_right_identity_example :
  constraint_concat Nat.eqb ([1; 2], [3]) ([], []) = Some ([1; 2], [3]).
Proof. reflexivity. Qed.

End PaperExamples.

Print Assumptions constraint_concat_preservation.
Print Assumptions constraint_concat_defined_iff_residual.
Print Assumptions constraint_concat_defined_iff_compatible.
Print Assumptions constraint_concat_least_residual.
Print Assumptions constraint_concat_characterization.
Print Assumptions constraint_concat_assoc.
Print Assumptions constraint_languages_idempotent_semiring.
