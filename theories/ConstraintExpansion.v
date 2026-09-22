From Stdlib Require Import List.
From CCont Require Import StringConstraints Syntax LookaheadSemantics.
Import ListNotations.
Set Implicit Arguments.

(** * Constraint expansion (paper Section 3.2, Eq. (9)--(10)) *)

Definition constraint_expansion {A} (R : constraint_language A)
    : constraint_language A :=
  fun p => exists v, R (fst p, v) /\ word_prefix v (snd p).

Definition suffix_concat {A} (R S : constraint_language A)
    : constraint_language A :=
  fun p => exists u v u' v',
    R (u, v) /\ S (u', v') /\ fst p = u ++ u' /\
    word_prefix v (u' ++ snd p) /\ word_prefix v' (snd p).

Lemma constraint_expansion_union {A} (R S : constraint_language A) :
  lang_equiv (constraint_expansion (lang_union R S))
    (lang_union (constraint_expansion R) (constraint_expansion S)).
Proof.
  intros [u z]. unfold constraint_expansion, lang_union. simpl. split.
  - intros [v [[HR|HS] Hv]]; [left|right]; exists v; now split.
  - intros [[v [HR Hv]]|[v [HS Hv]]].
    + exists v. split; [now left|exact Hv].
    + exists v. split; [now right|exact Hv].
Qed.

Section Expansion.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

(** The algebraic content of Proposition 5: expanding the least residual
    produced by [odot] gives exactly the suffix-style concatenation condition. *)
Theorem constraint_expansion_concat (R S : constraint_language A) :
  lang_equiv (constraint_expansion (lang_concat eqb R S))
    (suffix_concat R S).
Proof.
  intros [out z]. unfold constraint_expansion, suffix_concat. simpl. split.
  - intros [t [[p [q [Hp [Hq Hcat]]]] Htz]].
    destruct p as [u v], q as [u' v'].
    destruct (@constraint_concat_result_shape A eqb u v u' v' (out,t) Hcat)
      as [actual Hshape].
    inversion Hshape; subst out actual.
    pose proof (constraint_concat_preservation eqb eqb_spec
      u v u' v' Hcat)
      as [Hv Hv'].
    exists u, v, u', v'. repeat split; try assumption.
    + eapply word_prefix_trans; [exact Hv|].
      now apply word_prefix_app_left.
    + eapply word_prefix_trans; eassumption.
  - intros [u [v [u' [v' [HR [HS [Hout [Hv Hv']]]]]]]].
    subst out.
    assert (Hex : exists t,
        word_prefix v (u' ++ t) /\ word_prefix v' t).
    { exists z. now split. }
    apply (proj2 (constraint_concat_defined_iff_residual
      eqb eqb_spec u v u' v')) in Hex.
    destruct Hex as [t Hcat]. exists t. split.
    + exists (u,v), (u',v'). repeat split; assumption.
    + pose proof (constraint_concat_least_residual
        eqb eqb_spec u v u' v' Hcat) as [_ Hleast].
      apply Hleast. now split.
Qed.

Lemma constraint_expansion_lookahead (R : constraint_language A) u z :
  constraint_expansion (positive_lookahead R) (u,z) <->
  u = [] /\ exists p, R p /\ word_prefix (constraint_projection p) z.
Proof.
  unfold constraint_expansion, positive_lookahead. simpl. split.
  - intros [v [[p [Hp Heq]] Hv]]. inversion Heq; subst.
    split; [reflexivity|]. exists p. now split.
  - intros [-> [p [Hp Hprefix]]].
    exists (constraint_projection p). split; [|exact Hprefix].
    exists p. now split.
Qed.

(** The paper's strictness witness, Eq. (10): least constraints distinguish
    [LA(a)] from [LA(a + ab)], while their expansions coincide. *)
Definition strict_left (a : A) : rewpla A := WLookahead (WAtom a).
Definition strict_right (a b : A) : rewpla A :=
  WLookahead (WPlus (WAtom a) (WConcat (WAtom a) (WAtom b))).

Theorem strict_pair_languages_differ a b :
  ~ lang_equiv (rewpla_denote eqb (strict_left a))
      (rewpla_denote eqb (strict_right a b)).
Proof.
  intro H. specialize (H ([], [a;b])).
  assert (Hr : rewpla_denote eqb (strict_right a b) ([], [a;b])).
  { exists ([a;b], []). split.
    - right. exists ([a], []), ([b], []). repeat split; reflexivity.
    - reflexivity. }
  apply (proj2 H) in Hr. destruct Hr as [[u v] [Hatom Heq]].
  simpl in Hatom. inversion Hatom; subst u v. discriminate.
Qed.

Theorem strict_expansions_equal a b :
  lang_equiv
    (constraint_expansion (rewpla_denote eqb (strict_left a)))
    (constraint_expansion (rewpla_denote eqb (strict_right a b))).
Proof.
  intros [u z]. split.
  - intros [v [Hleft Hv]].
    exists v. split; [|exact Hv].
    destruct Hleft as [p [Hp Heq]]. exists p. split; [now left|exact Heq].
  - intros [v [Hright Hv]].
    destruct Hright as [p [[Hp|Hp] Heq]].
    + exists v. split; [|exact Hv]. exists p. now split.
    + destruct p as [m c].
      destruct Hp as [p [q [Hp [Hq Hcat]]]].
      inversion Heq; subst u v. simpl in Hp, Hq.
      inversion Hp; inversion Hq; subst.
      simpl in Hcat. inversion Hcat; subst m c.
      exists [a]. split.
      * exists ([a], []). split; reflexivity.
      * eapply word_prefix_trans; [|exact Hv].
        exists [b]. reflexivity.
Qed.

(** A compositional presentation of the expanded semantics.  The judgment
    [suffix_satisfies r u z] says that [r] consumes [u] and that its least
    residual constraint is satisfied by the available suffix [z]. *)
Definition suffix_satisfies (r : rewpla A) (u z : word A) : Prop :=
  constraint_expansion (rewpla_denote eqb r) (u,z).

Lemma suffix_satisfies_zero u z : ~ suffix_satisfies WZero u z.
Proof. intros [v [H _]]. exact H. Qed.

Lemma suffix_satisfies_eps u z :
  suffix_satisfies WEps u z <-> u = [].
Proof.
  unfold suffix_satisfies, constraint_expansion. simpl. split.
  - intros [v [H _]]. unfold lang_one in H. now inversion H.
  - intros ->. exists []. split; [reflexivity|apply word_prefix_nil].
Qed.

Lemma suffix_satisfies_atom a u z :
  suffix_satisfies (WAtom a) u z <-> u = [a].
Proof.
  unfold suffix_satisfies, constraint_expansion. simpl. split.
  - intros [v [H _]]. now inversion H.
  - intros ->. exists []. split; [reflexivity|apply word_prefix_nil].
Qed.

Lemma suffix_satisfies_plus r s u z :
  suffix_satisfies (WPlus r s) u z <->
  suffix_satisfies r u z \/ suffix_satisfies s u z.
Proof.
  unfold suffix_satisfies. simpl.
  exact (constraint_expansion_union (rewpla_denote eqb r)
    (rewpla_denote eqb s) (u,z)).
Qed.

Lemma suffix_satisfies_concat r s out z :
  suffix_satisfies (WConcat r s) out z <->
  exists u u', out = u ++ u' /\
    suffix_satisfies r u (u' ++ z) /\ suffix_satisfies s u' z.
Proof.
  unfold suffix_satisfies. simpl.
  rewrite (constraint_expansion_concat
    (rewpla_denote eqb r) (rewpla_denote eqb s) (out,z)).
  unfold suffix_concat. simpl. split.
  - intros [u [v [u' [v' [Hr [Hs [Hout [Hv Hv']]]]]]]].
    exists u, u'. repeat split; try assumption;
      [exists v|exists v']; now split.
  - intros [u [u' [Hout [[v [Hr Hv]] [v' [Hs Hv']]]]]].
    exists u, v, u', v'. repeat split; assumption.
Qed.

Lemma suffix_satisfies_lookahead r u z :
  suffix_satisfies (WLookahead r) u z <->
  u = [] /\ exists p, rewpla_denote eqb r p /\
    word_prefix (constraint_projection p) z.
Proof.
  unfold suffix_satisfies. apply constraint_expansion_lookahead.
Qed.

Lemma suffix_satisfies_embed (r : regex A) u z :
  suffix_satisfies (embed_regex r) u z <-> matches r u.
Proof.
  unfold suffix_satisfies, constraint_expansion. split.
  - intros [v [Hr _]].
    apply (proj1 (embed_regex_semantics eqb eqb_spec r (u,v))) in Hr.
    destruct Hr as [w [Heq Hm]]. inversion Heq; now subst.
  - intro Hm. exists []. split.
    + apply (proj2 (embed_regex_semantics eqb eqb_spec r (u,[]))).
      exists u. now split.
    + apply word_prefix_nil.
Qed.

End Expansion.

Print Assumptions constraint_expansion_concat.
Print Assumptions strict_pair_languages_differ.
Print Assumptions strict_expansions_equal.
Print Assumptions suffix_satisfies_concat.
Print Assumptions suffix_satisfies_embed.
