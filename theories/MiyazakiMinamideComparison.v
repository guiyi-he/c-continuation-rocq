From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import StringConstraints LookaheadSemantics
  ConstraintExpansion LookaheadDerivatives LookaheadDecision
  PositiveCongruence PositiveCongruenceNormalization SemanticDFA.
Import ListNotations.

Set Implicit Arguments.

(** * Comparison with Miyazaki--Minamide's derivative DFA

    Their automaton distinguishes letters consumed from the matching
    component from letters consumed from the remaining-input component.
    [MMMain a] and [MMContext a] are the two copies of [a].  Positive
    lookahead is written primitively here; its context derivative is the
    positive-fragment expansion of the two nested negative lookaheads used
    in the original presentation. *)

Inductive mm_letter (A : Type) : Type :=
| MMMain (a : A)
| MMContext (a : A).

Arguments MMMain {A} _.
Arguments MMContext {A} _.

Definition erase_mm_letter {A} (c : mm_letter A) : A :=
  match c with MMMain a | MMContext a => a end.

Definition erase_mm_word {A} (z : list (mm_letter A)) : word A :=
  map erase_mm_letter z.

Theorem erase_mm_letter_surjective {A} (a : A) :
  exists c, erase_mm_letter c = a.
Proof. now exists (MMMain a). Qed.

Theorem erase_mm_letter_two_components {A} (a : A) :
  MMMain a <> MMContext a.
Proof. discriminate. Qed.

Fixpoint mm_symbol_derivative {A} (eqb : A -> A -> bool) (a : A)
    (r : rewpla A) : derivative_pair A :=
  match r with
  | WZero => (WZero, WZero)
  | WEps => (WZero, WEps)
  | WAtom b =>
      if eqb a b then (WEps, WZero) else (WZero, WZero)
  | WPlus r s =>
      let '(rm, rc) := mm_symbol_derivative eqb a r in
      let '(sm, sc) := mm_symbol_derivative eqb a s in
      (WPlus rm sm, WPlus rc sc)
  | WConcat r s =>
      let '(rm, rc) := mm_symbol_derivative eqb a r in
      let '(sm, sc) := mm_symbol_derivative eqb a s in
      (WPlus (WConcat rm s) (WConcat rc sm), WConcat rc sc)
  | WStar r =>
      let '(rm, _) := mm_symbol_derivative eqb a r in
      (WConcat rm (WStar r), WEps)
  | WLookahead r =>
      let '(rm, rc) := mm_symbol_derivative eqb a r in
      (WZero, WLookahead (WPlus rm rc))
  end.

Definition mm_derivative {A} (eqb : A -> A -> bool)
    (c : mm_letter A) (r : rewpla A) : rewpla A :=
  match c with
  | MMMain a => fst (mm_symbol_derivative eqb a r)
  | MMContext a => snd (mm_symbol_derivative eqb a r)
  end.

Fixpoint mm_word_derivative {A} (eqb : A -> A -> bool)
    (w : list (mm_letter A)) (r : rewpla A) : rewpla A :=
  match w with
  | [] => r
  | c :: w' => mm_word_derivative eqb w' (mm_derivative eqb c r)
  end.

(** The behavior semantics used by Miyazaki--Minamide is exactly the
    upward closure [Gamma(M)] already proved in [ConstraintExpansion]. *)
Definition mm_behavior {A} (eqb : A -> A -> bool) (r : rewpla A) :=
  constraint_expansion (rewpla_denote eqb r).

Definition behavior_erasure {A} (R : constraint_language A)
    (w : word A) : Prop :=
  exists p, R p /\ constraint_projection p = w.

Definition right_ideal {A} (L : word A -> Prop) (w : word A) : Prop :=
  exists x y, L x /\ w = x ++ y.

(** Forgetting whether a letter is from the main or context copy maps the
    MM behavior language not to [L_pi], but to its right ideal
    [L_pi Sigma*].  This is the semantic obstruction to a direct quotient. *)
Theorem behavior_erasure_constraint_expansion {A}
    (R : constraint_language A) w :
  behavior_erasure (constraint_expansion R) w <->
  right_ideal (project_language R) w.
Proof.
  unfold behavior_erasure, right_ideal, project_language,
    constraint_expansion.
  split.
  - intros [[u z] [[v [HR Hv]] Huz]]. simpl in *.
    destruct Hv as [t Hzt]. subst z w.
    exists (u ++ v), t. split.
    + exists (u, v). now split.
    + symmetry. unfold constraint_projection. simpl.
      rewrite app_assoc. reflexivity.
  - intros [x [t [[p [HR Hpx]] Hwt]]].
    destruct p as [u v]. simpl in Hpx. subst x w.
    exists (u, v ++ t). split.
    + exists v. split; [exact HR|exists t; reflexivity].
    + symmetry. unfold constraint_projection. simpl.
      rewrite app_assoc. reflexivity.
Qed.

Corollary mm_erasure_is_projected_right_ideal {A} eqb
    (r : rewpla A) w :
  behavior_erasure (mm_behavior eqb r) w <->
  right_ideal (rewpla_language eqb r) w.
Proof. apply behavior_erasure_constraint_expansion. Qed.

(** Relabeling both MM copies of [a] by [a] turns the two MM quotients
    into a nondeterministic union.  Iterating this operator is the semantic
    powerset/tag-erasure construction; it is deliberately kept distinct
    from the least-constraint merged quotient. *)
Definition erased_behavior_symbol_quotient {A} (a : A)
    (R : constraint_language A) : constraint_language A :=
  lang_union (main_symbol_quotient a R) (context_symbol_quotient a R).

Definition mm_behavior_symbol_quotient {A} (c : mm_letter A)
    (R : constraint_language A) : constraint_language A :=
  match c with
  | MMMain a => main_symbol_quotient a R
  | MMContext a => context_symbol_quotient a R
  end.

Fixpoint mm_behavior_word_quotient {A} (z : list (mm_letter A))
    (R : constraint_language A) : constraint_language A :=
  match z with
  | [] => R
  | c :: z' => mm_behavior_word_quotient z'
      (mm_behavior_symbol_quotient c R)
  end.

Fixpoint erased_behavior_word_quotient {A} (w : word A)
    (R : constraint_language A) : constraint_language A :=
  match w with
  | [] => R
  | a :: w' => erased_behavior_word_quotient w'
      (erased_behavior_symbol_quotient a R)
  end.

Lemma mm_behavior_symbol_quotient_compat {A} c
    (R S : constraint_language A) :
  lang_equiv R S ->
  lang_equiv (mm_behavior_symbol_quotient c R)
    (mm_behavior_symbol_quotient c S).
Proof.
  intro H. destruct c as [a|a]; intros [u v]; simpl.
  - apply H.
  - split; intros [Hu HR]; split; [exact Hu| |exact Hu|];
      [apply (proj1 (H ([], a :: v)))|apply (proj2 (H ([], a :: v)))];
      exact HR.
Qed.

Lemma mm_behavior_word_quotient_compat {A} z
    (R S : constraint_language A) :
  lang_equiv R S ->
  lang_equiv (mm_behavior_word_quotient z R)
    (mm_behavior_word_quotient z S).
Proof.
  revert R S. induction z as [|c z IH]; intros R S H; simpl.
  - exact H.
  - apply IH, mm_behavior_symbol_quotient_compat. exact H.
Qed.

Lemma mm_behavior_symbol_quotient_union {A} c
    (R S : constraint_language A) :
  lang_equiv (mm_behavior_symbol_quotient c (lang_union R S))
    (lang_union (mm_behavior_symbol_quotient c R)
      (mm_behavior_symbol_quotient c S)).
Proof.
  destruct c as [a|a]; intros [u v]; simpl; unfold lang_union.
  - tauto.
  - split.
    + intros [Hu [HR|HS]]; [left|right]; now split.
    + intros [[Hu HR]|[Hu HS]]; split; [assumption|now left|assumption|now right].
Qed.

Lemma mm_behavior_word_quotient_union {A} z
    (R S : constraint_language A) :
  lang_equiv (mm_behavior_word_quotient z (lang_union R S))
    (lang_union (mm_behavior_word_quotient z R)
      (mm_behavior_word_quotient z S)).
Proof.
  revert R S. induction z as [|c z IH]; intros R S; simpl.
  - apply lang_equiv_refl.
  - eapply lang_equiv_trans.
    + apply mm_behavior_word_quotient_compat.
      apply mm_behavior_symbol_quotient_union.
    + apply IH.
Qed.

(** Exact trace meaning of tag erasure: this is the determinization of the
    NFA obtained by relabeling both [MMMain a] and [MMContext a] by [a]. *)
Theorem erased_behavior_word_quotient_trace {A} w
    (R : constraint_language A) p :
  erased_behavior_word_quotient w R p <->
  exists z, erase_mm_word z = w /\ mm_behavior_word_quotient z R p.
Proof.
  revert R p. induction w as [|a w IH]; intros R p; simpl.
  - split.
    + intro Hp. exists []. now split.
    + intros [[|c z] [Hz Hp]]; [exact Hp|discriminate].
  - rewrite IH. split.
    + intros [z [Hz Hpath]].
      apply (proj1 (mm_behavior_word_quotient_union z
        (main_symbol_quotient a R) (context_symbol_quotient a R) p))
        in Hpath.
      destruct Hpath as [Hm|Hc].
      * exists (MMMain a :: z). split.
        -- simpl. now rewrite Hz.
        -- exact Hm.
      * exists (MMContext a :: z). split.
        -- simpl. now rewrite Hz.
        -- exact Hc.
    + intros [[|[b|b] z] [Hz Hpath]]; try discriminate; simpl in Hz.
      * injection Hz as Hba Hzw. subst b. exists z. split; [exact Hzw|].
        apply (proj2 (mm_behavior_word_quotient_union z
          (main_symbol_quotient a R) (context_symbol_quotient a R) p)).
        now left.
      * injection Hz as Hba Hzw. subst b. exists z. split; [exact Hzw|].
        apply (proj2 (mm_behavior_word_quotient_union z
          (main_symbol_quotient a R) (context_symbol_quotient a R) p)).
        now right.
Qed.

(** The published MM derivative-correctness theorem is isolated as an
    explicit interface.  The comparison below does not postulate it as an
    axiom: all lifting theorems quantify over this property. *)
Definition mm_derivative_correct_B {A} (eqb : A -> A -> bool) : Prop :=
  forall c (r : rewpla A),
    lang_equiv (mm_behavior eqb (mm_derivative eqb c r))
      (mm_behavior_symbol_quotient c (mm_behavior eqb r)).

Theorem mm_word_derivative_correct_B {A} (eqb : A -> A -> bool)
    (Hcorrect : mm_derivative_correct_B eqb) z (r : rewpla A) :
  lang_equiv (mm_behavior eqb (mm_word_derivative eqb z r))
    (mm_behavior_word_quotient z (mm_behavior eqb r)).
Proof.
  revert r. induction z as [|c z IH]; intro r; simpl.
  - apply lang_equiv_refl.
  - eapply lang_equiv_trans.
    + apply IH.
    + apply mm_behavior_word_quotient_compat, Hcorrect.
Qed.

(** Under the published derivative-correctness interface, the semantic
    erased quotient is exactly the union of behaviors of the reachable MM
    derivatives whose tagged traces erase to the given untagged word. *)
Theorem erased_MM_subset_behavior_correct {A}
    (eqb : A -> A -> bool) (Hcorrect : mm_derivative_correct_B eqb)
    w (r : rewpla A) p :
  erased_behavior_word_quotient w (mm_behavior eqb r) p <->
  exists z, erase_mm_word z = w /\
    mm_behavior eqb (mm_word_derivative eqb z r) p.
Proof.
  rewrite erased_behavior_word_quotient_trace. split.
  - intros [z [Hz Hquot]]. exists z. split; [exact Hz|].
    apply (proj2 (mm_word_derivative_correct_B
      (eqb:=eqb) Hcorrect z r p)).
    exact Hquot.
  - intros [z [Hz Hderiv]]. exists z. split; [exact Hz|].
    apply (proj1 (mm_word_derivative_correct_B
      (eqb:=eqb) Hcorrect z r p)).
    exact Hderiv.
Qed.

Lemma erased_behavior_symbol_quotient_mono {A} a
    (R S : constraint_language A) :
  lang_incl R S ->
  lang_incl (erased_behavior_symbol_quotient a R)
    (erased_behavior_symbol_quotient a S).
Proof.
  intros H [u v] [Hm|Hc]; [left|right].
  - now apply H.
  - destruct Hc as [-> Hc]. split; [reflexivity|now apply H].
Qed.

Lemma erased_behavior_word_quotient_mono {A} w
    (R S : constraint_language A) :
  lang_incl R S ->
  lang_incl (erased_behavior_word_quotient w R)
    (erased_behavior_word_quotient w S).
Proof.
  revert R S. induction w as [|a w IH]; intros R S H; simpl.
  - exact H.
  - apply IH, erased_behavior_symbol_quotient_mono. exact H.
Qed.

(** The component-erasure square is only lax: expanding an exact merged
    quotient gives a subset of the union of the two MM behavior quotients. *)
Theorem constraint_expansion_merged_symbol_quotient_lax {A}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    a (R : constraint_language A) :
  lang_incl
    (constraint_expansion (pair_language_symbol_quotient eqb a R))
    (erased_behavior_symbol_quotient a (constraint_expansion R)).
Proof.
  intros [u z] [v [Hquot Hvz]].
  apply (proj1 (pair_symbol_quotient_split
    eqb eqb_spec a R (u, v))) in Hquot.
  destruct Hquot as [Hm|[Hu Hc]].
  - left. exists v. now split.
  - subst u. right. split; [reflexivity|].
    exists (a :: v). split; [exact Hc|].
    change (word_prefix ([a] ++ v) ([a] ++ z)).
    now apply word_prefix_app_left.
Qed.

(** The inclusion is strict already at the identity expression.  MM's
    context quotient of [I = Gamma(1)] loops, whereas the exact quotient of
    the least pair [(epsilon,epsilon)] is empty. *)
Theorem constraint_expansion_merged_symbol_quotient_strict {A}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y, eqb x y = true <-> x = y) a :
  ~ lang_equiv
      (constraint_expansion
        (pair_language_symbol_quotient eqb a (@lang_one A)))
      (erased_behavior_symbol_quotient a
        (constraint_expansion (@lang_one A))).
Proof.
  intro H. specialize (H ([], [])).
  assert (Hr : erased_behavior_symbol_quotient a
      (constraint_expansion (@lang_one A)) ([], [])).
  { right. split; [reflexivity|].
    exists []. split; [reflexivity|apply word_prefix_nil]. }
  apply (proj2 H) in Hr.
  destruct Hr as [v [[p [Hp Hstep]] _]].
  unfold lang_one in Hp. subst p. discriminate.
Qed.

Definition component_refinement {A} (R B : constraint_language A) : Prop :=
  lang_incl (constraint_expansion R) B.

Theorem component_refinement_initial {A} (R : constraint_language A) :
  component_refinement R (constraint_expansion R).
Proof. intros p Hp. exact Hp. Qed.

(** This is the genuine one-step simulation theorem.  Its direction is from
    the exact merged least-constraint state to the tag-erased MM powerset
    state: MM erasure is an over-approximation. *)
Theorem component_refinement_step {A}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    a (R B : constraint_language A) :
  component_refinement R B ->
  component_refinement
    (pair_language_symbol_quotient eqb a R)
    (erased_behavior_symbol_quotient a B).
Proof.
  intros H p Hp.
  apply (erased_behavior_symbol_quotient_mono
    (a:=a) (R:=constraint_expansion R) (S:=B) H).
  apply (constraint_expansion_merged_symbol_quotient_lax
    (eqb:=eqb) eqb_spec (a:=a) (R:=R)). exact Hp.
Qed.

Theorem component_refinement_preserves_final {A}
    (R B : constraint_language A) :
  component_refinement R B -> R ([], []) -> B ([], []).
Proof.
  intros H HR. apply H. exists []. split; [exact HR|apply word_prefix_nil].
Qed.

(** Path-level version of the lax square. *)
Theorem constraint_expansion_merged_word_quotient_lax {A}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    w (R : constraint_language A) :
  lang_incl
    (constraint_expansion (pair_language_word_quotient eqb w R))
    (erased_behavior_word_quotient w (constraint_expansion R)).
Proof.
  revert R. induction w as [|a w IH]; intro R.
  - intros [u z] [v [[p [Hp Hstep]] Hvz]]. simpl in Hstep.
    inversion Hstep; subst p. exists v. now split.
  - intros [u z] [v [Hword Hvz]].
    assert (Hnested : pair_language_word_quotient eqb w
        (pair_language_symbol_quotient eqb a R) (u, v)).
    { apply (proj1 (pair_language_word_quotient_cons
        eqb a w R (u, v))). exact Hword. }
    assert (Hexpanded : constraint_expansion
        (pair_language_word_quotient eqb w
          (pair_language_symbol_quotient eqb a R)) (u, z)).
    { exists v. now split. }
    pose proof (IH (pair_language_symbol_quotient eqb a R)
      (u, z) Hexpanded) as Hpath.
    simpl. eapply erased_behavior_word_quotient_mono; [|exact Hpath].
    apply constraint_expansion_merged_symbol_quotient_lax.
    exact eqb_spec.
Qed.

(** Consequently the actual merged construction is a semantic refinement
    of the tag-erased MM powerset construction, not its quotient. *)
Theorem merged_trace_refines_erased_MM {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    (r : rewpla A) w :
  lang_incl
    (constraint_expansion
      (rewpla_denote eqb
        (rewpla_positive_word_step eqb atom_code w r)))
    (erased_behavior_word_quotient w (mm_behavior eqb r)).
Proof.
  intros [u z] [v [Hmerged Hvz]].
  pose proof (rewpla_positive_word_step_correct_M
    eqb atom_code eqb_spec w r (u, v)) as Hcorrect.
  apply (proj1 Hcorrect) in Hmerged.
  apply (constraint_expansion_merged_word_quotient_lax
    (eqb:=eqb) eqb_spec (w:=w) (R:=rewpla_denote eqb r)).
  exists v. now split.
Qed.

(** Syntactic-state formulation of the preceding result.  Its sole premise
    is MM's published derivative-correctness theorem, represented by the
    explicit interface [mm_derivative_correct_B]. *)
Theorem merged_trace_refines_MM_derivatives {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    (HMM : mm_derivative_correct_B eqb)
    (r : rewpla A) w :
  lang_incl
    (constraint_expansion
      (rewpla_denote eqb
        (rewpla_positive_word_step eqb atom_code w r)))
    (fun p => exists z, erase_mm_word z = w /\
      mm_behavior eqb (mm_word_derivative eqb z r) p).
Proof.
  intros p Hp.
  apply (proj1 (erased_MM_subset_behavior_correct
    (eqb:=eqb) HMM w r p)).
  eapply (merged_trace_refines_erased_MM
    eqb atom_code eqb_spec r w).
  exact Hp.
Qed.

(** No extensional operation on MM behavior languages can reconstruct the
    least-constraint semantics for all positive expressions: [Gamma] has
    already forgotten branchwise nonminimal constraints. *)
Theorem no_behavior_extensional_recovery :
  ~ exists recover : constraint_language bool -> constraint_language bool,
    (forall R S, lang_equiv R S ->
      lang_equiv (recover R) (recover S)) /\
    (forall r : rewpla bool,
      lang_equiv (recover (mm_behavior Bool.eqb r))
        (rewpla_denote Bool.eqb r)).
Proof.
  intros [recover [Hext Hrecover]].
  pose proof (Hrecover (strict_left false)) as Hl.
  pose proof (Hrecover (strict_right false true)) as Hr.
  pose proof (Hext _ _
    (strict_expansions_equal Bool.eqb false true)) as He.
  apply (@strict_pair_languages_differ bool Bool.eqb false true).
  eapply lang_equiv_trans.
  - apply lang_equiv_sym. exact Hl.
  - eapply lang_equiv_trans; [exact He|exact Hr].
Qed.

(** There is, however, a genuine quotient theorem for the *merged*
    positive-congruence construction used by the executable artifact.  This
    construction has the same untyped alphabet and the same merged
    transition as [A_ours]; it is not the published MM automaton. *)
Definition merged_syntactic_reachable_cover {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (initial : rewpla A) (states : list (rewpla A)) : Prop :=
  forall w, In (rewpla_positive_word_step eqb atom_code w initial) states.

Theorem merged_positive_step_respects_M {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    a (r s : rewpla A) :
  lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s) ->
  lang_equiv
    (rewpla_denote eqb
      (rewpla_positive_symbol_step eqb atom_code a r))
    (rewpla_denote eqb
      (rewpla_positive_symbol_step eqb atom_code a s)).
Proof.
  intro Hrs. eapply lang_equiv_trans.
  - apply rewpla_positive_symbol_step_correct_M. exact eqb_spec.
  - eapply lang_equiv_trans.
    + now apply pair_language_symbol_quotient_compat_positive.
    + apply lang_equiv_sym, rewpla_positive_symbol_step_correct_M.
      exact eqb_spec.
Qed.

Theorem merged_positive_final_respects_M {A}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    (r s : rewpla A) :
  lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s) ->
  rewpla_nullable r = rewpla_nullable s.
Proof.
  intro Hrs.
  destruct (rewpla_nullable r) eqn:Hr,
           (rewpla_nullable s) eqn:Hs; try reflexivity.
  - exfalso.
    apply (proj1 (rewpla_nullable_correct eqb eqb_spec r)) in Hr.
    apply (proj1 (Hrs ([], []))) in Hr.
    apply (proj2 (rewpla_nullable_correct eqb eqb_spec s)) in Hr.
    congruence.
  - exfalso.
    apply (proj1 (rewpla_nullable_correct eqb eqb_spec s)) in Hs.
    apply (proj2 (Hrs ([], []))) in Hs.
    apply (proj2 (rewpla_nullable_correct eqb eqb_spec r)) in Hs.
    congruence.
Qed.

(** A quotient certificate without committing to a particular implementation
    of finite quotient types.  The first component gives the canonical
    surjection on reachable states (use the same word on both sides); the
    second and third components say that its kernel respects transitions and
    finality.  At the empty word the two representatives are definitionally
    the common initial expression. *)
Theorem merged_semantic_quotient_certificate {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    (initial : rewpla A) :
  (forall w,
    lang_equiv
      (rewpla_denote eqb
        (rewpla_positive_word_step eqb atom_code w initial))
      (rewpla_denote eqb (word_derivative eqb w initial))) /\
  (forall a r s,
    lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s) ->
    lang_equiv
      (rewpla_denote eqb
        (rewpla_positive_symbol_step eqb atom_code a r))
      (rewpla_denote eqb
        (rewpla_positive_symbol_step eqb atom_code a s))) /\
  (forall r s,
    lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s) ->
    rewpla_nullable r = rewpla_nullable s).
Proof.
  split.
  - intro w. eapply lang_equiv_trans.
    + apply rewpla_positive_word_step_correct_M. exact eqb_spec.
    + apply lang_equiv_sym, word_derivative_correct. exact eqb_spec.
  - split.
    + intros a r s Hrs.
      eapply merged_positive_step_respects_M; eauto.
    + intros r s Hrs.
      eapply merged_positive_final_respects_M; eauto.
Qed.

(** Finite-cardinality form of the quotient theorem: any list containing
    one representative of every reachable merged syntactic state is at
    least as large as any list of pair-semantically distinct reachable
    states of [A_ours]. *)
Theorem ours_vs_merged_syntactic_state_bound {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y, eqb x y = true <-> x = y)
    (initial : rewpla A) ours_states merged_states :
  semantic_distinct eqb ours_states ->
  semantic_reachable eqb initial ours_states ->
  merged_syntactic_reachable_cover eqb atom_code initial merged_states ->
  length ours_states <= length merged_states.
Proof.
  intros Hdistinct Hreachable Hcover.
  apply (semantic_distinct_cover_length eqb ours_states merged_states);
    [exact Hdistinct|].
  intros r Hr. destruct (Hreachable r Hr) as [w Hrw].
  exists (rewpla_positive_word_step eqb atom_code w initial). split.
  - apply Hcover.
  - eapply lang_equiv_trans; [exact Hrw|].
    eapply lang_equiv_trans.
    + apply word_derivative_correct. exact eqb_spec.
    + apply lang_equiv_sym, rewpla_positive_word_step_correct_M.
      exact eqb_spec.
Qed.

(** * Additional positive-lookahead equations *)

(** Projection forgets the boundary moved by lookahead.  This is a
    projected-language equation, not a pair-language equation. *)
Theorem rewpla_language_lookahead {A} eqb (r : rewpla A) w :
  rewpla_language eqb (WLookahead r) w <-> rewpla_language eqb r w.
Proof.
  unfold rewpla_language, project_language. simpl.
  split.
  - intros [p [[q [Hq Hp]] Hproj]]. subst p. simpl in Hproj.
    exists q. now split.
  - intros [q [Hq Hproj]].
    exists ([], constraint_projection q). split.
    + exists q. now split.
    + simpl. exact Hproj.
Qed.

(** Moving an assertion at the right boundary of [r] into an enclosing
    assertion does not change the least required word. *)
Lemma constraint_concat_right_lookahead_projection {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (x v u z t : word A) :
  constraint_concat eqb (x, v) (u, z) = Some (x ++ u, t) <->
  constraint_concat eqb (x, v) ([], u ++ z) = Some (x, u ++ t).
Proof.
  split; intro H.
  - replace (x, u ++ t) with (x ++ [], u ++ t)
      by now rewrite app_nil_r.
    apply (proj2 (constraint_concat_characterization
      eqb eqb_spec x v [] (u ++ z) (u ++ t))).
    pose proof (constraint_concat_least_residual
      eqb eqb_spec x v u z H) as [[Hv Hz] Hleast].
    unfold least_residual, residual_requirements in *.
    split.
    + split; [now simpl|]. apply word_prefix_app_left. exact Hz.
    + intros s [Hvs Huz].
      destruct Huz as [extra Hs]. subst s.
      rewrite <- app_assoc.
      apply word_prefix_app_left.
      apply Hleast. split.
      * now rewrite <- app_assoc in Hvs.
      * exists extra. reflexivity.
  - apply (proj2 (constraint_concat_characterization
      eqb eqb_spec x v u z t)).
    assert (H' : constraint_concat eqb (x, v) ([], u ++ z) =
        Some (x ++ [], u ++ t)).
    { now rewrite app_nil_r. }
    pose proof (constraint_concat_least_residual
      eqb eqb_spec x v [] (u ++ z) H') as [[Hv Huz] Hleast].
    unfold least_residual, residual_requirements in *.
    split.
    + split; [now simpl in Hv|].
      now apply (proj1 (word_prefix_app_left_iff u z t)).
    + intros s [Hvs Hz].
      apply (proj1 (word_prefix_app_left_iff u t s)).
      apply Hleast. split; [exact Hvs|].
      apply word_prefix_app_left. exact Hz.
Qed.

Theorem rewpla_lookahead_right_assertion {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r s : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (WLookahead (WConcat r (WLookahead s))))
    (rewpla_denote eqb (WLookahead (WConcat r s))).
Proof.
  intros [out k]. simpl. unfold positive_lookahead, lang_concat.
  split.
  - intros [[x t] [[p [la [Hp [Hla Hcat]]]] Hproj]].
    destruct p as [u v]. destruct Hla as [[y z] [Hs Hla]].
    inversion Hla; subst.
    pose proof (constraint_concat_result_shape
      eqb u v [] (y ++ z) Hcat) as [actual Hshape].
    inversion Hshape; subst x actual.
    unfold constraint_projection in Hproj. simpl in Hproj.
    inversion Hproj; subst out k.
    assert (Hcompat : prefix_compatible v (y ++ z)).
    { apply (proj1 (constraint_concat_defined_iff_compatible
        eqb eqb_spec u v [] (y ++ z))). exists t. exact Hcat. }
    destruct (@constraint_concat_defined_from_compatible
      A eqb eqb_spec u v y z Hcompat) as [t' Hcat'].
    pose proof ((proj1 (constraint_concat_right_lookahead_projection
      eqb eqb_spec u v y z t')) Hcat') as Hlift.
    pose proof (eq_trans (eq_sym Hcat) Hlift) as Heq.
    inversion Heq; subst t.
    exists (u ++ y, t'). split.
    + exists (u, v), (y, z). repeat split; assumption.
    + unfold constraint_projection. simpl.
      repeat rewrite app_nil_r. rewrite app_assoc. reflexivity.
  - intros [[x t] [[p [q [Hp [Hq Hcat]]]] Hproj]].
    destruct p as [u v], q as [y z].
    pose proof (constraint_concat_result_shape
      eqb u v y z Hcat) as [actual Hshape].
    inversion Hshape; subst x actual.
    unfold constraint_projection in Hproj. simpl in Hproj.
    inversion Hproj; subst out k.
    exists (u, y ++ t). split.
    + exists (u, v), ([], y ++ z). repeat split; try assumption.
      * exists (y, z). split; [exact Hq|reflexivity].
      * now apply (proj1 (constraint_concat_right_lookahead_projection
          eqb eqb_spec u v y z t)).
    + unfold constraint_projection. simpl.
      rewrite app_assoc. reflexivity.
Qed.

(** Any empty-main language is idempotent under constrained
    concatenation, and its star therefore adds only the identity. *)
Lemma empty_main_language_concat_idempotent {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (R : constraint_language A) :
  empty_main_language R -> lang_equiv (lang_concat eqb R R) R.
Proof.
  intros HR out. unfold lang_concat. split.
  - intros [p [q [Hp [Hq Hout]]]].
    destruct p as [u v], q as [u' v'].
    pose proof (HR (u, v) Hp) as Hu.
    pose proof (HR (u', v') Hq) as Hu'.
    simpl in Hu, Hu'. subst u u'.
    destruct out as [uo vo].
    pose proof (constraint_concat_result_shape eqb [] v [] v' Hout)
      as [t Hshape]. inversion Hshape; subst uo vo.
    destruct (empty_pair_concat_is_operand eqb eqb_spec v v' Hout)
      as [Heq|Heq]; subst t; assumption.
  - intro Hout. destruct out as [u v].
    pose proof (HR (u, v) Hout) as Hu. simpl in Hu. subst u.
    exists ([], v), ([], v). repeat split; try exact Hout.
    apply empty_pair_concat_idempotent. exact eqb_spec.
Qed.

Lemma empty_main_power_positive {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (R : constraint_language A) :
  empty_main_language R -> forall n,
  lang_equiv (lang_power eqb R (S n)) R.
Proof.
  intro HR. induction n as [|n IH]; simpl.
  - apply lang_concat_one_left. exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply lang_concat_compat; [exact IH|apply lang_equiv_refl].
    + now apply empty_main_language_concat_idempotent.
Qed.

Theorem empty_main_star_collapse {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (R : constraint_language A) :
  empty_main_language R ->
  lang_equiv (lang_star eqb R) (lang_union lang_one R).
Proof.
  intro HR. intros p. unfold lang_star, lang_union. split.
  - intros [n Hn]. destruct n as [|n].
    + now left.
    + right. apply (proj1 (empty_main_power_positive
        eqb eqb_spec (R:=R) HR n p)).
      exact Hn.
  - intros [Hone|HRp].
    + exists 0. exact Hone.
    + exists 1. apply (proj2
        (empty_main_power_positive
          eqb eqb_spec (R:=R) HR 0 p)). exact HRp.
Qed.

Lemma lang_star_unfold_right {A} eqb (R : constraint_language A) :
  lang_equiv (lang_star eqb R)
    (lang_union lang_one (lang_concat eqb (lang_star eqb R) R)).
Proof.
  intro p. unfold lang_star, lang_union. split.
  - intros [n Hn]. destruct n as [|n].
    + now left.
    + right. simpl in Hn.
      destruct Hn as [q [t [Hq [Ht Hcat]]]].
      exists q, t. repeat split; try assumption.
      now exists n.
  - intros [Hone|Hstep].
    + now exists 0.
    + destruct Hstep as [q [t [[n Hq] [Ht Hcat]]]].
      exists (S n). simpl. exists q, t. repeat split; assumption.
Qed.

(** Exact pair-semantic star law.  Unlike the projected-language equation
    below, this retains every least suffix constraint. *)
Theorem rewpla_lookahead_star_unfold {A} eqb (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (WLookahead (WStar r)))
    (rewpla_denote eqb
      (WPlus WEps (WLookahead (WConcat (WStar r) r)))).
Proof.
  eapply lang_equiv_trans with (S :=
    rewpla_denote eqb
      (WLookahead (WPlus WEps (WConcat (WStar r) r)))).
  - apply positive_lookahead_compat, lang_star_unfold_right.
  - eapply lang_equiv_trans.
    + apply rewpla_lookahead_union.
    + apply lang_union_compat.
      * apply (rewpla_lookahead_eps_M eqb).
      * apply lang_equiv_refl.
Qed.

Theorem rewpla_lookahead_star_collapse {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (WStar (WLookahead r)))
    (rewpla_denote eqb (WPlus WEps (WLookahead r))).
Proof.
  simpl. apply empty_main_star_collapse; [exact eqb_spec|].
  intros p [q [_ ->]]. reflexivity.
Qed.

Theorem rewpla_nested_lookahead_star_collapse {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (WLookahead (WStar (WLookahead r))))
    (rewpla_denote eqb (WPlus WEps (WLookahead r))).
Proof.
  eapply lang_equiv_trans.
  - apply rewpla_lookahead_constraint; [exact eqb_spec|].
    apply empty_main_star; [exact eqb_spec|].
    intros p [q [_ ->]]. reflexivity.
  - apply rewpla_lookahead_star_collapse. exact eqb_spec.
Qed.

(** The tempting unrestricted product and star simplifications are false
    for the complete least-constraint semantics. *)
Theorem lookahead_concat_distribution_fails :
  ~ lang_equiv
      (rewpla_denote Bool.eqb
        (WLookahead (WConcat (WAtom false) (WAtom true))))
      (rewpla_denote Bool.eqb
        (WConcat (WLookahead (WAtom false))
          (WLookahead (WAtom true)))).
Proof.
  intro H. specialize (H ([], [false; true])).
  assert (HL : rewpla_denote Bool.eqb
      (WLookahead (WConcat (WAtom false) (WAtom true)))
      ([], [false; true])).
  { exists ([false; true], []). split.
    - exists ([false], []), ([true], []). repeat split; reflexivity.
    - reflexivity. }
  apply (proj1 H) in HL.
  destruct HL as [p [q [Hp [Hq Hcat]]]].
  destruct Hp as [p' [Hp' Heqp]], Hq as [q' [Hq' Heqq]].
  simpl in Hp', Hq'. inversion Hp'; inversion Hq'; subst.
  discriminate.
Qed.

Theorem lookahead_star_epsilon_fails :
  ~ lang_equiv
      (rewpla_denote Bool.eqb (WLookahead (WStar (WAtom false))))
      (rewpla_denote Bool.eqb WEps).
Proof.
  intro H. specialize (H ([], [false])).
  assert (HL : rewpla_denote Bool.eqb
      (WLookahead (WStar (WAtom false))) ([], [false])).
  { exists ([false], []). split.
    - exists 1. simpl. exists ([], []), ([false], []).
      repeat split; reflexivity.
    - reflexivity. }
  apply (proj1 H) in HL. discriminate.
Qed.

(** * Concrete obstruction to a DFA homomorphism *)

Inductive mm_la_state := MMLAStart | MMLAEps | MMLAZero.
Inductive ours_la_state := OLAStart | OLAEps | OLAZero.

Definition mm_la_main_delta (q : mm_la_state) : mm_la_state :=
  match q with MMLAStart | MMLAEps => MMLAZero | MMLAZero => MMLAZero end.

Definition ours_la_delta (q : ours_la_state) : ours_la_state :=
  match q with OLAStart => OLAEps | OLAEps | OLAZero => OLAZero end.

Definition la_shared_alphabet_homomorphism
    (h : mm_la_state -> ours_la_state) : Prop :=
  h MMLAStart = OLAStart /\
  forall q, h (mm_la_main_delta q) = ours_la_delta (h q).

Theorem no_la_shared_alphabet_homomorphism :
  ~ exists h, la_shared_alphabet_homomorphism h.
Proof.
  intros [h [Hinit Hstep]].
  pose proof (Hstep MMLAStart) as Hstart.
  simpl in Hstart. rewrite Hinit in Hstart. simpl in Hstart.
  pose proof (Hstep MMLAZero) as Hzero. simpl in Hzero.
  rewrite Hstart in Hzero. discriminate.
Qed.

Definition mm_la_repr (q : mm_la_state) : rewpla bool :=
  match q with
  | MMLAStart => WLookahead (WAtom false)
  | MMLAEps => WEps
  | MMLAZero => WZero
  end.

Definition ours_la_repr (q : ours_la_state) : rewpla bool :=
  match q with
  | OLAStart => WLookahead (WAtom false)
  | OLAEps => WEps
  | OLAZero => WZero
  end.

Definition bool_code (b : bool) : nat := if b then 1 else 0.

Definition mm_positive_step (c : mm_letter bool) (r : rewpla bool) :=
  rewpla_positive_normalize Bool.eqb bool_code
    (mm_derivative Bool.eqb c r).

Fixpoint mm_positive_word_step (w : list (mm_letter bool))
    (r : rewpla bool) : rewpla bool :=
  match w with
  | [] => r
  | c :: w' => mm_positive_word_step w' (mm_positive_step c r)
  end.

Definition ours_positive_step (a : bool) (r : rewpla bool) :=
  rewpla_positive_symbol_step Bool.eqb bool_code a r.

Lemma mm_la_main_transition_representation q :
  mm_positive_step (MMMain false) (mm_la_repr q) =
  mm_la_repr (mm_la_main_delta q).
Proof. destruct q; reflexivity. Qed.

Lemma ours_la_transition_representation q :
  ours_positive_step false (ours_la_repr q) =
  ours_la_repr (ours_la_delta q).
Proof. destruct q; reflexivity. Qed.

(** Relabeling the two MM letters is not enough even if a homomorphism is
    weakened to an acceptance-preserving forward simulation relation.  The
    identity expression is the smallest obstruction: MM may consume any
    context letter while staying in its accepting [epsilon] state, whereas
    the merged least-constraint step goes to [zero]. *)
Inductive epsilon_residual_state := EpsResidual | ZeroResidual.

Definition epsilon_residual_repr (q : epsilon_residual_state)
    : rewpla bool :=
  match q with EpsResidual => WEps | ZeroResidual => WZero end.

Definition mm_epsilon_delta (q : epsilon_residual_state)
    (c : mm_letter bool) : epsilon_residual_state :=
  match q, c with
  | EpsResidual, MMMain _ => ZeroResidual
  | EpsResidual, MMContext _ => EpsResidual
  | ZeroResidual, _ => ZeroResidual
  end.

Definition merged_epsilon_delta (q : epsilon_residual_state)
    : epsilon_residual_state :=
  match q with EpsResidual | ZeroResidual => ZeroResidual end.

Definition epsilon_residual_final (q : epsilon_residual_state) : bool :=
  match q with EpsResidual => true | ZeroResidual => false end.

Lemma mm_epsilon_transition_representation q c :
  mm_positive_step c (epsilon_residual_repr q) =
  epsilon_residual_repr (mm_epsilon_delta q c).
Proof. destruct q, c; reflexivity. Qed.

Lemma merged_epsilon_transition_representation q a :
  ours_positive_step a (epsilon_residual_repr q) =
  epsilon_residual_repr (merged_epsilon_delta q).
Proof. destruct q, a; reflexivity. Qed.

Definition erased_MM_merged_forward_simulation
    (R : epsilon_residual_state -> epsilon_residual_state -> Prop) : Prop :=
  R EpsResidual EpsResidual /\
  (forall q p, R q p -> epsilon_residual_final q = true ->
    epsilon_residual_final p = true) /\
  (forall q p c, R q p ->
    R (mm_epsilon_delta q c) (merged_epsilon_delta p)).

Theorem no_erased_MM_to_merged_forward_simulation :
  ~ exists R, erased_MM_merged_forward_simulation R.
Proof.
  intros [R [Hinit [Hfinal Hstep]]].
  pose proof (Hstep EpsResidual EpsResidual
    (MMContext false) Hinit) as Hcontext.
  simpl in Hcontext.
  pose proof (Hfinal EpsResidual ZeroResidual Hcontext eq_refl).
  discriminate.
Qed.

(** * A strict state-count example *)

Definition universal_expression : rewpla bool :=
  WStar (WPlus (WAtom false) (WAtom true)).

Inductive mm_universal_state := MMUStar | MMUEps | MMUZero.

Definition mm_universal_repr (q : mm_universal_state) : rewpla bool :=
  match q with
  | MMUStar => universal_expression
  | MMUEps => WEps
  | MMUZero => WZero
  end.

Definition mm_universal_delta (q : mm_universal_state)
    (c : mm_letter bool) : mm_universal_state :=
  match q, c with
  | MMUStar, MMMain _ => MMUStar
  | MMUStar, MMContext _ => MMUEps
  | MMUEps, MMMain _ => MMUZero
  | MMUEps, MMContext _ => MMUEps
  | MMUZero, _ => MMUZero
  end.

Lemma mm_universal_transition_table q c :
  mm_positive_step c (mm_universal_repr q) =
  mm_universal_repr (mm_universal_delta q c).
Proof. destruct q, c, a; reflexivity. Qed.

Lemma mm_positive_step_represents_derivative c r :
  mm_derivative Bool.eqb c r ==p mm_positive_step c r.
Proof.
  unfold mm_positive_step.
  apply rewpla_positive_normalize_congruent.
  exact Bool.eqb_true_iff.
Qed.

Lemma mm_universal_run_from_state w q :
  exists q', mm_positive_word_step w (mm_universal_repr q) =
    mm_universal_repr q'.
Proof.
  revert q. induction w as [|c w IH]; intro q; simpl.
  - now exists q.
  - rewrite mm_universal_transition_table. apply IH.
Qed.

Lemma mm_universal_all_normalized_derivatives w :
  exists q, mm_positive_word_step w universal_expression =
    mm_universal_repr q.
Proof. apply (mm_universal_run_from_state w MMUStar). Qed.

Lemma mm_universal_every_state_reached q :
  exists w, mm_positive_word_step w universal_expression =
    mm_universal_repr q.
Proof.
  destruct q.
  - exists []. reflexivity.
  - exists [MMContext false]. reflexivity.
  - exists [MMContext false; MMMain false]. reflexivity.
Qed.

Lemma mm_universal_three_states_reachable :
  mm_word_derivative Bool.eqb [] universal_expression =
      mm_universal_repr MMUStar /\
  mm_word_derivative Bool.eqb [MMContext false] universal_expression =
      mm_universal_repr MMUEps /\
  mm_word_derivative Bool.eqb [MMContext false; MMMain false]
      universal_expression = mm_universal_repr MMUZero.
Proof. repeat split; reflexivity. Qed.

Lemma mm_universal_star_not_eps :
  ~ universal_expression ==p (@WEps bool).
Proof.
  intro H. pose proof (positive_congruence_sound_M Bool.eqb
    Bool.eqb_true_iff H ([false], [])) as Hsem.
  simpl in Hsem.
  assert (Hs : rewpla_denote Bool.eqb universal_expression ([false], [])).
  { exists 1. simpl. exists ([], []), ([false], []).
    repeat split; try reflexivity. now left. }
  apply (proj1 Hsem) in Hs. discriminate.
Qed.

Lemma mm_universal_star_not_zero :
  ~ universal_expression ==p (@WZero bool).
Proof.
  intro H. pose proof (positive_congruence_sound_M Bool.eqb
    Bool.eqb_true_iff H ([], [])) as Hsem.
  simpl in Hsem. apply (proj1 Hsem).
  exists 0. reflexivity.
Qed.

Lemma mm_universal_eps_not_zero : ~ (@WEps bool) ==p WZero.
Proof.
  intro H. pose proof (positive_congruence_sound_M Bool.eqb
    Bool.eqb_true_iff H ([], [])) as Hsem.
  simpl in Hsem. apply (proj1 Hsem). reflexivity.
Qed.

Theorem mm_universal_three_distinct_classes :
  ~ mm_universal_repr MMUStar ==p mm_universal_repr MMUEps /\
  ~ mm_universal_repr MMUStar ==p mm_universal_repr MMUZero /\
  ~ mm_universal_repr MMUEps ==p mm_universal_repr MMUZero.
Proof.
  repeat split.
  - exact mm_universal_star_not_eps.
  - exact mm_universal_star_not_zero.
  - exact mm_universal_eps_not_zero.
Qed.

(** These three residuals are also distinct at the MM behavior level, not
    merely under the positive syntactic congruence.  Together with the
    semantic soundness of MM's full congruence, this rules out any collapse
    caused by its additional negative-lookahead equations. *)
Theorem mm_universal_three_distinct_behaviors :
  ~ lang_equiv
      (mm_behavior Bool.eqb universal_expression)
      (mm_behavior Bool.eqb (@WEps bool)) /\
  ~ lang_equiv
      (mm_behavior Bool.eqb universal_expression)
      (mm_behavior Bool.eqb (@WZero bool)) /\
  ~ lang_equiv
      (mm_behavior Bool.eqb (@WEps bool))
      (mm_behavior Bool.eqb (@WZero bool)).
Proof.
  repeat split; intro H.
  - specialize (H ([false], [])).
    assert (Hs : mm_behavior Bool.eqb universal_expression
        ([false], [])).
    { exists []. split.
      - exists 1. simpl. exists ([], []), ([false], []).
        repeat split; try reflexivity. now left.
      - exists []. reflexivity. }
    apply (proj1 H) in Hs. destruct Hs as [v [Hv _]].
    discriminate.
  - specialize (H ([], [])).
    assert (Hs : mm_behavior Bool.eqb universal_expression ([], [])).
    { exists []. split.
      - exists 0. reflexivity.
      - exists []. reflexivity. }
    apply (proj1 H) in Hs. destruct Hs as [v [Hv _]]. exact Hv.
  - specialize (H ([], [])).
    assert (He : mm_behavior Bool.eqb (@WEps bool) ([], [])).
    { exists []. split; [reflexivity|exists []; reflexivity]. }
    apply (proj1 H) in He. destruct He as [v [Hv _]]. exact Hv.
Qed.

Lemma mm_universal_class_representatives_injective q q' :
  mm_universal_repr q ==p mm_universal_repr q' -> q = q'.
Proof.
  destruct q, q'; try reflexivity; intro H.
  - exfalso. exact (mm_universal_star_not_eps H).
  - exfalso. exact (mm_universal_star_not_zero H).
  - exfalso. apply mm_universal_star_not_eps, PC_sym. exact H.
  - exfalso. exact (mm_universal_eps_not_zero H).
  - exfalso. apply mm_universal_star_not_zero, PC_sym. exact H.
  - exfalso. apply mm_universal_eps_not_zero, PC_sym. exact H.
Qed.

Theorem mm_universal_quotient_exactly_three :
  (forall w, exists q,
    mm_positive_word_step w universal_expression = mm_universal_repr q) /\
  (forall q, exists w,
    mm_positive_word_step w universal_expression = mm_universal_repr q) /\
  (forall q q', mm_universal_repr q ==p mm_universal_repr q' -> q = q').
Proof.
  repeat split.
  - exact mm_universal_all_normalized_derivatives.
  - exact mm_universal_every_state_reached.
  - exact mm_universal_class_representatives_injective.
Qed.

Lemma ours_universal_symbol_step a :
  ours_positive_step a universal_expression = universal_expression.
Proof. destruct a; reflexivity. Qed.

Lemma ours_universal_word_step w :
  rewpla_positive_word_step Bool.eqb bool_code w universal_expression =
  universal_expression.
Proof.
  induction w as [|a w IH]; simpl; [reflexivity|].
  rewrite ours_universal_symbol_step. exact IH.
Qed.

Theorem ours_universal_all_residuals_one_class w :
  lang_equiv
    (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb w universal_expression))
    (rewpla_denote Bool.eqb universal_expression).
Proof.
  eapply lang_equiv_trans.
  - apply word_derivative_correct. exact Bool.eqb_true_iff.
  - apply lang_equiv_sym.
    rewrite <- ours_universal_word_step at 1.
    apply rewpla_positive_word_step_correct_M. exact Bool.eqb_true_iff.
Qed.

Theorem ours_universal_semantic_quotient_singleton u v :
  @semantic_word_equiv bool Bool.eqb universal_expression u v.
Proof.
  unfold semantic_word_equiv.
  eapply lang_equiv_trans.
  - apply ours_universal_all_residuals_one_class.
  - apply lang_equiv_sym, ours_universal_all_residuals_one_class.
Qed.

Theorem strict_state_count_witness :
  (forall u v,
    @semantic_word_equiv bool Bool.eqb universal_expression u v) /\
  (forall w, exists q,
    mm_positive_word_step w universal_expression = mm_universal_repr q) /\
  (forall q, exists w,
    mm_positive_word_step w universal_expression = mm_universal_repr q) /\
  (forall q q', mm_universal_repr q ==p mm_universal_repr q' -> q = q').
Proof.
  split.
  - exact ours_universal_semantic_quotient_singleton.
  - split.
    + exact mm_universal_all_normalized_derivatives.
    + split.
      * exact mm_universal_every_state_reached.
      * exact mm_universal_class_representatives_injective.
Qed.

Print Assumptions behavior_erasure_constraint_expansion.
Print Assumptions erased_behavior_word_quotient_trace.
Print Assumptions mm_word_derivative_correct_B.
Print Assumptions erased_MM_subset_behavior_correct.
Print Assumptions constraint_expansion_merged_symbol_quotient_lax.
Print Assumptions constraint_expansion_merged_symbol_quotient_strict.
Print Assumptions component_refinement_step.
Print Assumptions component_refinement_preserves_final.
Print Assumptions constraint_expansion_merged_word_quotient_lax.
Print Assumptions merged_trace_refines_erased_MM.
Print Assumptions merged_trace_refines_MM_derivatives.
Print Assumptions no_behavior_extensional_recovery.
Print Assumptions merged_semantic_quotient_certificate.
Print Assumptions ours_vs_merged_syntactic_state_bound.
Print Assumptions rewpla_lookahead_right_assertion.
Print Assumptions rewpla_lookahead_star_unfold.
Print Assumptions rewpla_nested_lookahead_star_collapse.
Print Assumptions no_la_shared_alphabet_homomorphism.
Print Assumptions no_erased_MM_to_merged_forward_simulation.
Print Assumptions mm_universal_three_distinct_classes.
Print Assumptions mm_universal_three_distinct_behaviors.
Print Assumptions mm_universal_quotient_exactly_three.
Print Assumptions ours_universal_semantic_quotient_singleton.
