From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import Syntax Automaton Construction.
Import ListNotations.

Set Implicit Arguments.

Section Canonical.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma ccontinuation_absent p r :
  ~ In p (positions r) -> ccontinuation eqb p r = Zero.
Proof.
  induction r as [| |q|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r IH]; simpl; intro H; try reflexivity.
  - destruct (pos_eqb eqb p q) eqn:E; [|reflexivity].
    apply (pos_eqb_spec eqb eqb_spec) in E. subst. exfalso. apply H. now left.
  - rewrite in_app_iff in H. simpl in H.
    rewrite IH1, IH2; tauto.
  - rewrite in_app_iff in H. simpl in H.
    rewrite IH1, IH2; tauto.
  - rewrite IH; auto.
Qed.

Lemma pderive_has_position p r d :
  In d (pderive eqb p r) -> In p (positions r).
Proof.
  revert d; induction r as [| |q|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r IH]; intros d H; simpl in *; try contradiction.
  - destruct (pos_eqb eqb p q) eqn:E; simpl in H; [|contradiction].
    apply (pos_eqb_spec eqb eqb_spec) in E. subst. now left.
  - apply in_app_iff in H. apply in_app_iff. destruct H; [left; now apply IH1 with d|right; now apply IH2 with d].
  - apply in_app_iff in H. apply in_app_iff. destruct H as [H|H].
    + apply in_map_iff in H. destruct H as [x [_ Hx]]. left. now apply IH1 with x.
    + destruct (nullable r1); simpl in H; [right; now apply IH2 with d|contradiction].
  - apply in_map_iff in H. destruct H as [x [_ Hx]]. now apply IH with x.
Qed.

Definition canonical_pd (base source : regex (position A)) : Prop :=
  forall p d, In d (pderive eqb p source) ->
    d = Zero \/ d = ccontinuation eqb p base.

Lemma nodup_app_inv {X} (l1 l2 : list X) : NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> ~ In x l2).
Proof.
  intro H. split; [now apply NoDup_app_remove_r in H|].
  split; [now apply NoDup_app_remove_l in H|].
  revert l2 H; induction l1 as [|a l1 IH]; intros l2 H x Hx; simpl in *; [contradiction|].
  inversion H as [|? ? Hnot Htail]; subst.
  destruct Hx as [->|Hx].
  - intro Hin. apply Hnot. apply in_app_iff. auto.
  - eapply IH; eauto.
Qed.

Lemma canonical_zero base : canonical_pd base Zero.
Proof. intros p d H; contradiction. Qed.

Lemma canonical_eps base : canonical_pd base Eps.
Proof. intros p d H; contradiction. Qed.

Lemma base_derivatives_canonical r :
  NoDup (positions r) -> canonical_pd r r.
Proof.
  induction r as [| |q|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r IH];
    intro Hnd; intros p d Hd; simpl in Hd.
  - contradiction.
  - contradiction.
  - destruct (pos_eqb eqb p q) eqn:E; simpl in Hd; [|contradiction].
    destruct Hd as [Hd|[]]. subst d. right. simpl. now rewrite E.
  - apply nodup_app_inv in Hnd as [Hn1 [Hn2 Hdis]].
    apply in_app_iff in Hd. destruct Hd as [Hd|Hd].
    + specialize (IH1 Hn1 p d Hd). destruct IH1 as [Hz|He].
      * left. exact Hz.
      * rewrite He. simpl. destruct (ccontinuation eqb p r1);
          [left|right|right|right|right|right]; reflexivity.
    + specialize (IH2 Hn2 p d Hd). destruct IH2 as [->|Hd2]; [now left|].
      assert (~ In p (positions r1)).
      { intro Hp. apply (Hdis p Hp). eapply pderive_has_position; eauto. }
      pose proof (ccontinuation_absent p r1 H) as Ha. simpl. rewrite Ha. right. exact Hd2.
  - apply nodup_app_inv in Hnd as [Hn1 [Hn2 Hdis]].
    apply in_app_iff in Hd. destruct Hd as [Hd|Hd].
    + apply in_map_iff in Hd. destruct Hd as [x [Ex Hx]]. subst d.
      specialize (IH1 Hn1 p x Hx). destruct IH1 as [->|Hxv].
      * left. reflexivity.
      * simpl. rewrite Hxv. destruct (ccontinuation eqb p r1); auto.
    + destruct (nullable r1) eqn:En; simpl in Hd; [|contradiction].
      specialize (IH2 Hn2 p d Hd). destruct IH2 as [->|Hd2]; [now left|].
      assert (~ In p (positions r1)).
      { intro Hp. apply (Hdis p Hp). eapply pderive_has_position; eauto. }
      pose proof (ccontinuation_absent p r1 H) as Ha. simpl. rewrite Ha. right. exact Hd2.
  - apply in_map_iff in Hd. destruct Hd as [x [Ex Hx]]. subst d.
    specialize (IH Hnd p x Hx). destruct IH as [->|Hxv].
    + left. reflexivity.
    + simpl. rewrite Hxv. destruct (ccontinuation eqb p r); auto.
Qed.

Lemma positions_smart_concat (p : position A) a b :
  In p (positions (smart_concat a b)) ->
  In p (positions a) \/ In p (positions b).
Proof.
  destruct a, b; simpl; try tauto;
    intro H; apply in_app_iff in H; exact H.
Qed.

Lemma positions_ccontinuation p x r :
  In p (positions (ccontinuation eqb x r)) -> In p (positions r).
Proof.
  induction r as [| |q|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r IH]; simpl; intro H;
    try contradiction.
  - destruct (pos_eqb eqb x q); simpl in H; contradiction.
  - destruct (ccontinuation eqb x r1) as [| |q|u v|u v|u] eqn:E; simpl in H.
    + apply in_app_iff. right. now apply IH2.
    + apply in_app_iff. left. now apply IH1.
    + apply in_app_iff. left. now apply IH1.
    + apply in_app_iff. left. now apply IH1.
    + apply in_app_iff. left. now apply IH1.
    + apply in_app_iff. left. now apply IH1.
  - destruct (ccontinuation eqb x r1) as [| |q'|u' v'|u' v'|u'] eqn:E; simpl in H.
    + apply in_app_iff. right. now apply IH2.
    + apply in_app_iff; apply (@positions_smart_concat p Eps r2) in H; destruct H;
        [left; now apply IH1|right; assumption].
    + apply in_app_iff; apply (@positions_smart_concat p (Atom q') r2) in H; destruct H;
        [left; now apply IH1|right; assumption].
    + apply in_app_iff; apply (@positions_smart_concat p (Plus u' v') r2) in H; destruct H;
        [left; now apply IH1|right; assumption].
    + apply in_app_iff; apply (@positions_smart_concat p (Concat u' v') r2) in H; destruct H;
        [left; now apply IH1|right; assumption].
    + apply in_app_iff; apply (@positions_smart_concat p (Star u') r2) in H; destruct H;
        [left; now apply IH1|right; assumption].
  - apply positions_smart_concat in H. destruct H; [now apply IH|assumption].
Qed.

Lemma canonical_translate_right l r source :
  NoDup (positions l ++ positions r) ->
  canonical_pd r source ->
  (forall p, In p (positions source) -> In p (positions r)) ->
  canonical_pd (Plus l r) source /\ canonical_pd (Concat l r) source.
Proof.
  intros Hnd Hcan Hsub. apply nodup_app_inv in Hnd as [_ [_ Hdis]]. split;
    intros p d Hd; pose proof (Hcan p d Hd) as Hclass; destruct Hclass as [Hz|He].
  - left. exact Hz.
  - assert (~ In p (positions l)).
    { intro Hp. apply (Hdis p Hp). apply Hsub. eapply pderive_has_position; eauto. }
    pose proof (ccontinuation_absent p l H) as Ha. right. simpl. rewrite Ha. exact He.
  - left. exact Hz.
  - assert (~ In p (positions l)).
    { intro Hp. apply (Hdis p Hp). apply Hsub. eapply pderive_has_position; eauto. }
    pose proof (ccontinuation_absent p l H) as Ha. right. simpl. rewrite Ha. exact He.
Qed.

Lemma canonical_concat_raw l r source :
  NoDup (positions l ++ positions r) ->
  canonical_pd l source ->
  (forall p, In p (positions source) -> In p (positions l)) ->
  canonical_pd r r ->
  canonical_pd (Concat l r) (Concat source r).
Proof.
  intros Hnd Hsrc Hsub Hr p d Hd. apply nodup_app_inv in Hnd as [_ [_ Hdis]].
  simpl in Hd. apply in_app_iff in Hd. destruct Hd as [Hd|Hd].
  - apply in_map_iff in Hd. destruct Hd as [x [Ex Hx]]. subst d.
    pose proof (Hsrc p x Hx) as Hclass. destruct Hclass as [Hz|He].
    + subst x. left. reflexivity.
    + rewrite He. simpl. destruct (ccontinuation eqb p l);
        [left|right|right|right|right|right]; reflexivity.
  - destruct (nullable source) eqn:En; simpl in Hd; [|contradiction].
    pose proof (Hr p d Hd) as Hclass. destruct Hclass as [Hz|He]; [now left|].
    assert (~ In p (positions l)).
    { intro Hp. apply (Hdis p Hp). eapply pderive_has_position; eauto. }
    pose proof (ccontinuation_absent p l H) as Ha. right. simpl. rewrite Ha. exact He.
Qed.

Lemma canonical_translate_left_plus l r source :
  canonical_pd l source -> canonical_pd (Plus l r) source.
Proof.
  intros Hcan p d Hd. pose proof (Hcan p d Hd) as Hclass.
  destruct Hclass as [Hz|He]; [now left|]. rewrite He. simpl.
  destruct (ccontinuation eqb p l); [left|right|right|right|right|right]; reflexivity.
Qed.

Lemma canonical_translate_left_concat_eps l source :
  canonical_pd l source -> canonical_pd (Concat l Eps) source.
Proof.
  intros Hcan p d Hd. pose proof (Hcan p d Hd) as Hclass.
  destruct Hclass as [Hz|He]; [now left|]. rewrite He. simpl.
  destruct (ccontinuation eqb p l); [left|right|right|right|right|right]; reflexivity.
Qed.

Lemma canonical_smart_concat l r source :
  NoDup (positions l ++ positions r) ->
  canonical_pd l source ->
  (forall p, In p (positions source) -> In p (positions l)) ->
  canonical_pd r r ->
  canonical_pd (Concat l r) (smart_concat source r).
Proof.
  intros Hnd Hsrc Hsub Hr.
  destruct source as [| |a|s1 s2|s1 s2|s].
  - apply canonical_zero.
  - destruct r as [| |b|r1 r2|r1 r2|r]; simpl.
    + apply canonical_zero.
    + pose proof (canonical_translate_right l Hnd Hr (fun p H => False_rect _ H)) as HC. exact (proj2 HC).
    + pose proof (canonical_translate_right l Hnd Hr (fun p H => H)) as HC. exact (proj2 HC).
    + pose proof (canonical_translate_right l Hnd Hr (fun p H => H)) as HC. exact (proj2 HC).
    + pose proof (canonical_translate_right l Hnd Hr (fun p H => H)) as HC. exact (proj2 HC).
    + pose proof (canonical_translate_right l Hnd Hr (fun p H => H)) as HC. exact (proj2 HC).
  - destruct r; simpl; first [apply canonical_zero |
      (apply canonical_translate_left_concat_eps; exact Hsrc) |
      (apply canonical_concat_raw; assumption)].
  - destruct r; simpl; first [apply canonical_zero |
      (apply canonical_translate_left_concat_eps; exact Hsrc) |
      (apply canonical_concat_raw; assumption)].
  - destruct r; simpl; first [apply canonical_zero |
      (apply canonical_translate_left_concat_eps; exact Hsrc) |
      (apply canonical_concat_raw; assumption)].
  - destruct r; simpl; first [apply canonical_zero |
      (apply canonical_translate_left_concat_eps; exact Hsrc) |
      (apply canonical_concat_raw; assumption)].
Qed.

Lemma canonical_star_raw r source :
  canonical_pd r source -> canonical_pd (Star r) (Star r) ->
  canonical_pd (Star r) (Concat source (Star r)).
Proof.
  intros Hsrc Hr p d Hd. simpl in Hd. apply in_app_iff in Hd.
  destruct Hd as [Hd|Hd].
  - apply in_map_iff in Hd. destruct Hd as [x [Ex Hx]]. subst d.
    pose proof (Hsrc p x Hx) as Hclass. destruct Hclass as [Hz|He].
    + subst x. left. reflexivity.
    + rewrite He. simpl. destruct (ccontinuation eqb p r);
        [left|right|right|right|right|right]; reflexivity.
  - destruct (nullable source); simpl in Hd; [|contradiction].
    exact (Hr p d Hd).
Qed.

Lemma canonical_smart_star r source :
  canonical_pd r source -> canonical_pd (Star r) (Star r) ->
  canonical_pd (Star r) (smart_concat source (Star r)).
Proof.
  intros Hsrc Hr. destruct source; simpl.
  - apply canonical_zero.
  - exact Hr.
  - apply canonical_star_raw; assumption.
  - apply canonical_star_raw; assumption.
  - apply canonical_star_raw; assumption.
  - apply canonical_star_raw; assumption.
Qed.

Theorem continuation_derivatives_canonical r :
  NoDup (positions r) -> forall x, canonical_pd r (ccontinuation eqb x r).
Proof.
  induction r as [| |q|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r IH]; intros Hnd x; simpl.
  - apply canonical_zero.
  - apply canonical_zero.
  - destruct (pos_eqb eqb x q); [apply canonical_eps|apply canonical_zero].
  - apply nodup_app_inv in Hnd as [Hn1 [Hn2 Hdis]].
    destruct (ccontinuation eqb x r1) eqn:Ec.
    + assert (NoDup (positions r1 ++ positions r2)) as Hfull by now apply NoDup_app.
      pose proof (canonical_translate_right r1 Hfull (IH2 Hn2 x)
        (fun p Hp => positions_ccontinuation p x r2 Hp)) as HC.
      exact (proj1 HC).
    + apply canonical_translate_left_plus. pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
    + apply canonical_translate_left_plus. pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
    + apply canonical_translate_left_plus. pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
    + apply canonical_translate_left_plus. pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
    + apply canonical_translate_left_plus. pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
  - apply nodup_app_inv in Hnd as [Hn1 [Hn2 Hdis]].
    destruct (ccontinuation eqb x r1) eqn:Ec.
    + assert (NoDup (positions r1 ++ positions r2)) as Hfull by now apply NoDup_app.
      pose proof (canonical_translate_right r1 Hfull (IH2 Hn2 x)
        (fun p Hp => positions_ccontinuation p x r2 Hp)) as HC.
      exact (proj2 HC).
    + apply canonical_smart_concat.
      * now apply NoDup_app.
      * pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
      * intros p Hp. eapply positions_ccontinuation. rewrite Ec. exact Hp.
      * apply base_derivatives_canonical. exact Hn2.
    + apply canonical_smart_concat; try (now apply NoDup_app).
      * pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
      * intros p Hp. eapply positions_ccontinuation. rewrite Ec. exact Hp.
      * apply base_derivatives_canonical. exact Hn2.
    + apply canonical_smart_concat; try (now apply NoDup_app).
      * pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
      * intros p Hp. eapply positions_ccontinuation. rewrite Ec. exact Hp.
      * apply base_derivatives_canonical. exact Hn2.
    + apply canonical_smart_concat; try (now apply NoDup_app).
      * pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
      * intros p Hp. eapply positions_ccontinuation. rewrite Ec. exact Hp.
      * apply base_derivatives_canonical. exact Hn2.
    + apply canonical_smart_concat; try (now apply NoDup_app).
      * pose proof (IH1 Hn1 x) as HC. now rewrite Ec in HC.
      * intros p Hp. eapply positions_ccontinuation. rewrite Ec. exact Hp.
      * apply base_derivatives_canonical. exact Hn2.
  - apply canonical_smart_star.
    + apply IH. exact Hnd.
    + apply base_derivatives_canonical. exact Hnd.
Qed.

Lemma smart_concat_nonzero_left {X} (r s : regex X) :
  smart_concat r s <> Zero -> r <> Zero.
Proof. destruct r, s; simpl; congruence. Qed.

Lemma smart_concat_nonzero_right {X} (r s : regex X) :
  smart_concat r s <> Zero -> s <> Zero.
Proof. destruct r, s; simpl; congruence. Qed.

Lemma pderive_nonzero_cderive p r d :
  In d (pderive eqb p r) -> d <> Zero -> cderive eqb p r <> Zero.
Proof.
  revert d; induction r as [| |q|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r IH];
    intros d Hd Hnz; simpl in *; try contradiction.
  - destruct (pos_eqb eqb p q); simpl in Hd; [congruence|contradiction].
  - apply in_app_iff in Hd. destruct Hd as [Hd|Hd].
    + pose proof (IH1 d Hd Hnz). destruct (cderive eqb p r1); simpl; congruence.
    + pose proof (IH2 d Hd Hnz). destruct (cderive eqb p r1); simpl; congruence.
  - apply in_app_iff in Hd. destruct Hd as [Hd|Hd].
    + apply in_map_iff in Hd. destruct Hd as [x [Ex Hx]]. subst d.
      pose proof (@smart_concat_nonzero_left (position A) x r2 Hnz) as Hxn.
      pose proof (@smart_concat_nonzero_right (position A) x r2 Hnz) as Hrn.
      pose proof (IH1 x Hx Hxn). destruct (cderive eqb p r1), r2; simpl; congruence.
    + destruct (nullable r1) eqn:En; simpl in Hd; [|contradiction].
      pose proof (IH2 d Hd Hnz) as H2.
      assert (r2 <> Zero) as Hr2 by (intro E; subst; simpl in H2; contradiction).
      destruct (cderive eqb p r1), (cderive eqb p r2), r2; simpl in *; congruence.
  - apply in_map_iff in Hd. destruct Hd as [x [Ex Hx]]. subst d.
    pose proof (@smart_concat_nonzero_left (position A) x (Star r) Hnz) as Hxn.
    pose proof (IH x Hx Hxn). destruct (cderive eqb p r); simpl; congruence.
Qed.

Lemma cderive_member_if_nonzero p r :
  cderive eqb p r <> Zero -> In (cderive eqb p r) (pderive eqb p r).
Proof.
  induction r as [| |q|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r IH];
    intro H; simpl in *; try contradiction.
  - destruct (pos_eqb eqb p q); simpl in *; auto; contradiction.
  - destruct (cderive eqb p r1) as [| |q|x y|x y|x] eqn:E1; simpl in *.
    + apply in_app_iff. right. now apply IH2.
    + apply in_app_iff. left. apply IH1. congruence.
    + apply in_app_iff. left. apply IH1. congruence.
    + apply in_app_iff. left. apply IH1. congruence.
    + apply in_app_iff. left. apply IH1. congruence.
    + apply in_app_iff. left. apply IH1. congruence.
  - destruct (cderive eqb p r1) as [| |q'|x' y'|x' y'|x'] eqn:E1; simpl in *.
    + destruct (nullable r1) eqn:En; [|contradiction].
      apply in_app_iff. right. now apply IH2.
    + apply in_app_iff. left. apply in_map_iff.
      exists Eps. split; [reflexivity|]. apply IH1. congruence.
    + apply in_app_iff. left. apply in_map_iff.
      exists (Atom q'). split; [reflexivity|]. apply IH1. congruence.
    + apply in_app_iff. left. apply in_map_iff.
      exists (Plus x' y'). split; [reflexivity|]. apply IH1. congruence.
    + apply in_app_iff. left. apply in_map_iff.
      exists (Concat x' y'). split; [reflexivity|]. apply IH1. congruence.
    + apply in_app_iff. left. apply in_map_iff.
      exists (Star x'). split; [reflexivity|]. apply IH1. congruence.
  - apply in_map_iff. exists (cderive eqb p r). split; [reflexivity|].
    apply IH. destruct (cderive eqb p r); simpl in H; congruence.
Qed.

Lemma canonical_one_step base source p w :
  canonical_pd base source ->
  (matches source (p :: w) <->
   cderive eqb p source = ccontinuation eqb p base /\
   matches (ccontinuation eqb p base) w).
Proof.
  intro Hcan. rewrite pderive_correct by exact eqb_spec. split.
  - intros [d [Hd Hm]]. pose proof (Hcan p d Hd) as Hclass.
    destruct Hclass as [Hz|He].
    + subst d. exfalso. now apply no_match_zero in Hm.
    + rewrite He in Hm. split; [|exact Hm].
      assert (d <> Zero) as Hdn.
      { intro Ed. rewrite Ed in He. rewrite <- He in Hm. now apply no_match_zero in Hm. }
      pose proof (@pderive_nonzero_cderive p source d Hd Hdn) as Hcn.
      pose proof (@cderive_member_if_nonzero p source Hcn) as Hmem.
      pose proof (Hcan p (cderive eqb p source) Hmem) as Hclass.
      destruct Hclass as [Hz|Hsame]; [contradiction|exact Hsame].
  - intros [Ec Hm]. exists (ccontinuation eqb p base). split; [|exact Hm].
    rewrite <- Ec. apply cderive_member_if_nonzero.
    intro Ez. rewrite Ez in Ec. rewrite <- Ec in Hm.
    now apply no_match_zero in Hm.
Qed.

End Canonical.
