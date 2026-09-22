From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import StringConstraints LookaheadSemantics
  LookaheadDerivatives LookaheadDecision.
Import ListNotations.
Set Implicit Arguments.

(** * Cardinality of the full-pair semantic derivative DFA (Eq. 44--46)

    Rocq uses a setoid of reachable word derivatives instead of postulating
    quotient types or a decision procedure for semantic equivalence. A finite
    cover bounds every list of distinct reachable equivalence classes. *)
Fixpoint semantic_distinct {A} eqb (states : list (rewpla A)) : Prop :=
  match states with
  | [] => True
  | r :: rs =>
      (forall s, In s rs ->
        ~ lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s)) /\
      semantic_distinct eqb rs
  end.

Lemma Forall2_member_right {X Y} (R : X -> Y -> Prop) xs ys y :
  Forall2 R xs ys -> In y ys -> exists x, In x xs /\ R x y.
Proof.
  intros H. induction H as [|x z xs ys Hxz Hrest IH]; simpl.
  - contradiction.
  - intros [<-|Hy].
    + exists x. split; [now left|exact Hxz].
    + destruct (IH Hy) as [x' [Hx' Hr]]. exists x'. split; [now right|exact Hr].
Qed.

Lemma semantic_distinct_cover_selection {A} eqb (xs cover : list (rewpla A)) :
  semantic_distinct eqb xs ->
  (forall r, In r xs -> exists s, In s cover /\
    lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s)) ->
  exists selected,
    NoDup selected /\ incl selected cover /\
    Forall2 (fun r s => lang_equiv (rewpla_denote eqb r)
      (rewpla_denote eqb s)) xs selected.
Proof.
  induction xs as [|r rs IH]; intros Hdistinct Hcover.
  - exists []. split; [constructor|]. split; [intros x H; contradiction|constructor].
  - destruct Hdistinct as [Hhead Htail].
    destruct (Hcover r ltac:(now left)) as [s [Hs Hsem]].
    destruct (IH Htail) as [selected [Hdup [Hincl Hmatch]]].
    { intros q Hq. apply Hcover. now right. }
    assert (Hfresh : ~ In s selected).
    { intro Hin.
      destruct (Forall2_member_right s Hmatch Hin) as [q [Hq Hqs]].
      apply (Hhead q Hq). eapply lang_equiv_trans; [exact Hsem|].
      apply lang_equiv_sym. exact Hqs. }
    exists (s :: selected). split; [constructor; assumption|]. split.
    + intros q [<-|Hq]; [exact Hs|now apply Hincl].
    + constructor; assumption.
Qed.

Theorem semantic_distinct_cover_length {A} eqb (xs cover : list (rewpla A)) :
  semantic_distinct eqb xs ->
  (forall r, In r xs -> exists s, In s cover /\
    lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s)) ->
  length xs <= length cover.
Proof.
  intros Hdistinct Hcover.
  destruct (semantic_distinct_cover_selection eqb xs cover Hdistinct Hcover)
    as [selected [Hdup [Hincl Hmatch]]].
  assert (Hlength : length xs = length selected).
  { clear Hdup Hincl Hdistinct Hcover.
    induction Hmatch; simpl; congruence. }
  rewrite Hlength. now apply NoDup_incl_length.
Qed.

Definition semantic_reachable {A} eqb (initial : rewpla A)
    (states : list (rewpla A)) : Prop :=
  forall r, In r states -> exists w,
    lang_equiv (rewpla_denote eqb r)
      (rewpla_denote eqb (word_derivative eqb w initial)).

Lemma pair_equivalence_projected {A} eqb (r s : rewpla A) :
  lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s) ->
  forall w, rewpla_language eqb r w <-> rewpla_language eqb s w.
Proof.
  intros H w. unfold rewpla_language, project_language. split;
    intros [p [Hp Hout]]; exists p; split; try exact Hout.
  - now apply (proj1 (H p)).
  - now apply (proj2 (H p)).
Qed.

Fixpoint projected_distinct {A} eqb (states : list (rewpla A)) : Prop :=
  match states with
  | [] => True
  | r :: rs =>
      (forall s, In s rs ->
        ~ (forall w, rewpla_language eqb r w <-> rewpla_language eqb s w)) /\
      projected_distinct eqb rs
  end.

Lemma projected_distinct_semantic_distinct {A} eqb (states : list (rewpla A)) :
  projected_distinct eqb states -> semantic_distinct eqb states.
Proof.
  induction states as [|r rs IH]; simpl; [tauto|].
  intros [Hhead Htail]. split; [|now apply IH].
  intros s Hs Hsem. apply (Hhead s Hs). now apply pair_equivalence_projected.
Qed.

Theorem semantic_dfa_state_bound {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    (initial : rewpla A) states :
  semantic_distinct eqb states -> semantic_reachable eqb initial states ->
  length states <=
    1 + 2 ^ ((length (continuation_generators eqb initial) + 1) *
      2 ^ length (constraint_generators eqb initial)) /\
  length states <= 1 + 2 ^ (2 ^ rewpla_width initial).
Proof.
  intros Hdistinct Hreachable.
  destruct (semantic_derivatives_finite_cover_and_bound
    eqb atom_code eqb_spec initial) as [cover [Hcount [Hwidth Hcover]]].
  assert (Hlength : length states <= length cover).
  { apply (semantic_distinct_cover_length eqb states cover); [exact Hdistinct|].
    intros r Hr. destruct (Hreachable r Hr) as [w Hw].
    destruct (Hcover w) as [s [Hs Hssem]]. exists s. split; [exact Hs|].
    eapply lang_equiv_trans; eassumption. }
  split; lia.
Qed.

(** The left inequality in Eq. (46) uses the onto map from full-pair
    residual classes to projected residual classes. Representatives of
    distinct projected classes are also distinct full-pair classes. *)
Theorem projected_dfa_state_bound {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    (initial : rewpla A) states :
  projected_distinct eqb states -> semantic_reachable eqb initial states ->
  length states <=
    1 + 2 ^ ((length (continuation_generators eqb initial) + 1) *
      2 ^ length (constraint_generators eqb initial)) /\
  length states <= 1 + 2 ^ (2 ^ rewpla_width initial).
Proof.
  intros Hdistinct Hreachable.
  apply (@semantic_dfa_state_bound A eqb atom_code eqb_spec initial states);
    [now apply projected_distinct_semantic_distinct|exact Hreachable].
Qed.

(** State equivalence, well-defined transition, initial/final states and
    word acceptance are precisely the paper's DFA five-tuple. The state
    carrier is words modulo full pair-language equality of their derivatives. *)
Section SemanticMachine.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.
Variable initial : rewpla A.

Definition semantic_word_equiv (u v : list A) :=
  lang_equiv (rewpla_denote eqb (word_derivative eqb u initial))
    (rewpla_denote eqb (word_derivative eqb v initial)).
Definition semantic_word_step (u : list A) (a : A) := u ++ [a].
Definition semantic_word_final (u : list A) :=
  rewpla_denote eqb (word_derivative eqb u initial) ([], []).
Definition semantic_word_initial : list A := [].
Fixpoint semantic_word_run (u w : list A) :=
  match w with
  | [] => u
  | a :: w' => semantic_word_run (semantic_word_step u a) w'
  end.

Lemma semantic_word_run_app u w : semantic_word_run u w = u ++ w.
Proof.
  revert u. induction w as [|a w IH]; intro u; simpl.
  - now rewrite app_nil_r.
  - unfold semantic_word_step. rewrite IH, <- app_assoc. reflexivity.
Qed.

Theorem semantic_word_equiv_equivalence :
  (forall u, semantic_word_equiv u u) /\
  (forall u v, semantic_word_equiv u v -> semantic_word_equiv v u) /\
  (forall u v w, semantic_word_equiv u v -> semantic_word_equiv v w ->
    semantic_word_equiv u w).
Proof.
  unfold semantic_word_equiv. split.
  - intro u. apply lang_equiv_refl.
  - split.
    + intros u v H. now apply lang_equiv_sym.
    + intros u v w Huv Hvw. eapply lang_equiv_trans; eassumption.
Qed.

Theorem semantic_word_step_well_defined u v a :
  semantic_word_equiv u v ->
  semantic_word_equiv (semantic_word_step u a) (semantic_word_step v a).
Proof.
  unfold semantic_word_equiv, semantic_word_step. intro H.
  rewrite !word_derivative_app. apply word_derivative_congruent_M; assumption.
Qed.

Theorem semantic_word_final_well_defined u v :
  semantic_word_equiv u v -> (semantic_word_final u <-> semantic_word_final v).
Proof. intro H. apply H. Qed.

Definition projected_word_equiv (u v : list A) :=
  forall z, rewpla_language eqb initial (u ++ z) <->
    rewpla_language eqb initial (v ++ z).

Theorem semantic_to_projected_residual_classes u v :
  semantic_word_equiv u v -> projected_word_equiv u v.
Proof.
  intros H z. unfold semantic_word_equiv in H.
  pose proof (@pair_equivalence_projected A eqb
    (word_derivative eqb u initial) (word_derivative eqb v initial) H z) as Hproj.
  rewrite !word_derivative_projected_correct in Hproj by exact eqb_spec.
  exact Hproj.
Qed.

Theorem semantic_word_dfa_accept_correct w :
  semantic_word_final w <-> rewpla_language eqb initial w.
Proof.
  unfold semantic_word_final.
  rewrite <- rewpla_nullable_correct by exact eqb_spec.
  apply rewpla_acceptb_correct. exact eqb_spec.
Qed.

Theorem semantic_to_projected_residual_classes_onto w :
  exists u, projected_word_equiv u w.
Proof. exists w. intro z. tauto. Qed.

Theorem semantic_word_dfa_run_accept_correct w :
  semantic_word_final (semantic_word_run semantic_word_initial w) <->
    rewpla_language eqb initial w.
Proof.
  rewrite semantic_word_run_app. apply semantic_word_dfa_accept_correct.
Qed.
End SemanticMachine.

Print Assumptions semantic_dfa_state_bound.
Print Assumptions semantic_word_step_well_defined.
Print Assumptions semantic_word_dfa_accept_correct.
