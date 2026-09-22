From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import StringConstraints LookaheadSemantics.
Import ListNotations.

Set Implicit Arguments.

(** * Quotients and executable derivatives for REwPLA

    Paper Section 4.1--4.2, p.7--10, red lines 295--502, Eq. (10)--(31).
    Definitions explicitly called an extension below are mechanization
    infrastructure and do not claim to occur in the paper. *)

(** Paper Eq. (10), p.7, lines 296--304. *)
Definition pair_symbol_quotient {A} (eqb : A -> A -> bool) (a : A)
  (p : string_constraint A) : option (string_constraint A) :=
  match p with
  | (b :: u, v) => if eqb a b then Some (u, v) else None
  | ([], b :: v) => if eqb a b then Some ([], v) else None
  | ([], []) => None
  end.

(** Paper p.7, lines 302--310: inductive word quotient. *)
Fixpoint pair_word_quotient {A} (eqb : A -> A -> bool) (w : word A)
  (p : string_constraint A) : option (string_constraint A) :=
  match w with
  | [] => Some p
  | a :: w' =>
      match pair_symbol_quotient eqb a p with
      | Some q => pair_word_quotient eqb w' q
      | None => None
      end
  end.

(** Paper p.7, lines 308--311: pointwise language quotients. *)
Definition pair_language_symbol_quotient {A}
  (eqb : A -> A -> bool) (a : A) (R : constraint_language A)
  : constraint_language A :=
  fun q => exists p, R p /\ pair_symbol_quotient eqb a p = Some q.

Definition pair_language_word_quotient {A}
  (eqb : A -> A -> bool) (w : word A) (R : constraint_language A)
  : constraint_language A :=
  fun q => exists p, R p /\ pair_word_quotient eqb w p = Some q.

(** Paper Eq. (12), p.7, lines 313--323. *)
Definition main_symbol_quotient {A} (a : A) (R : constraint_language A)
  : constraint_language A :=
  fun p => let '(u, v) := p in R (a :: u, v).

Definition context_symbol_quotient {A} (a : A) (R : constraint_language A)
  : constraint_language A :=
  fun p => let '(u, v) := p in u = [] /\ R ([], a :: v).

(** Constructive [E(R)] from the paragraph before Lemma 2. *)
Definition language_epsilon_part {A} (R : constraint_language A)
  : constraint_language A := epsilon_part R.

Section Quotients.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma pair_symbol_quotient_main a u v :
  pair_symbol_quotient eqb a (a :: u, v) = Some (u, v).
Proof. simpl. rewrite (proj2 (eqb_spec a a) eq_refl). reflexivity. Qed.

Lemma pair_symbol_quotient_context a v :
  pair_symbol_quotient eqb a ([], a :: v) = Some ([], v).
Proof. simpl. rewrite (proj2 (eqb_spec a a) eq_refl). reflexivity. Qed.

Lemma pair_symbol_quotient_identity a :
  pair_symbol_quotient eqb a ([], []) = None.
Proof. reflexivity. Qed.

(** Eq. (12), following paragraph: the total quotient is the disjoint
    union of its main and context components. *)
Theorem pair_symbol_quotient_split a R :
  lang_equiv (pair_language_symbol_quotient eqb a R)
    (lang_union (main_symbol_quotient a R) (context_symbol_quotient a R)).
Proof.
  intros [u v]. split.
  - intros [[u0 v0] [HR Hstep]]. destruct u0 as [|b u'].
    + destruct v0 as [|c v']; simpl in Hstep; [discriminate|].
      destruct (eqb a c) eqn:Hac; inversion Hstep; subst.
      apply eqb_spec in Hac. subst c. right. now split.
    + simpl in Hstep. destruct (eqb a b) eqn:Hab; inversion Hstep; subst.
      apply eqb_spec in Hab. subst b. now left.
  - intros [Hm|[Hu Hc]].
    + exists (a :: u, v). split; [exact Hm|apply pair_symbol_quotient_main].
    + subst u. exists ([], a :: v). split; [exact Hc|].
      apply pair_symbol_quotient_context.
Qed.

Lemma pair_symbol_quotient_projection a p q :
  pair_symbol_quotient eqb a p = Some q ->
  constraint_projection p = a :: constraint_projection q.
Proof.
  destruct p as [[|b u] [|c v]], q as [x y]; simpl;
    try discriminate.
  - destruct (eqb a c) eqn:Hac; intro H; inversion H; subst.
    apply eqb_spec in Hac. now subst c.
  - destruct (eqb a b) eqn:Hab; intro H; inversion H; subst.
    apply eqb_spec in Hab. now subst b.
  - destruct (eqb a b) eqn:Hab; intro H; inversion H; subst.
    apply eqb_spec in Hab. now subst b.
Qed.

Lemma pair_symbol_quotient_from_projection a p z :
  constraint_projection p = a :: z ->
  exists q, pair_symbol_quotient eqb a p = Some q /\
            constraint_projection q = z.
Proof.
  destruct p as [[|b u] [|c v]]; simpl; intro H; try discriminate.
  - inversion H; subst c z. exists ([], v). split.
    + apply pair_symbol_quotient_context.
    + reflexivity.
  - inversion H; subst b z. exists (u, []). split.
    + apply pair_symbol_quotient_main.
    + reflexivity.
  - inversion H; subst b z. exists (u, c :: v). split.
    + apply pair_symbol_quotient_main.
    + reflexivity.
Qed.

Lemma symbol_quotient_union a R S :
  lang_equiv (pair_language_symbol_quotient eqb a (lang_union R S))
    (lang_union (pair_language_symbol_quotient eqb a R)
                (pair_language_symbol_quotient eqb a S)).
Proof.
  intro q. unfold pair_language_symbol_quotient, lang_union. split.
  - intros [p [[Hp|Hp] Hq]]; [left|right]; exists p; now split.
  - intros [[p [Hp Hq]]|[p [Hp Hq]]]; exists p; split; try assumption;
      [left|right]; assumption.
Qed.

(** Auxiliary cancellation facts used in the four product/star cases of
    Lemma 2.  They are stated for the executable operations of Eq. (4)--(5),
    so no cancellation property is hidden in the semantic proofs below. *)
Lemma left_quotient_cons_same a u v :
  left_quotient eqb (a :: u) (a :: v) = left_quotient eqb u v.
Proof.
  simpl. rewrite (proj2 (eqb_spec a a) eq_refl). reflexivity.
Qed.

Lemma join_cons_same a u v :
  join eqb (a :: u) (a :: v) =
  option_map (cons a) (join eqb u v).
Proof.
  unfold join. rewrite !left_quotient_cons_same.
  destruct (left_quotient eqb u v), (left_quotient eqb v u);
    reflexivity.
Qed.

Lemma residual_cons_same a u v :
  residual eqb (a :: u) (a :: v) = residual eqb u v.
Proof. unfold residual. now rewrite left_quotient_cons_same. Qed.

Lemma constraint_concat_prepend_left_main a x c q out :
  constraint_concat eqb (x, c) q = Some out ->
  constraint_concat eqb (a :: x, c) q =
    Some (a :: fst out, snd out).
Proof.
  destruct q as [y d], out as [z t]. simpl.
  unfold constraint_concat. simpl.
  destruct (join eqb c (y ++ d)); [|discriminate].
  destruct (join eqb (residual eqb c y) d); [|discriminate].
  intro H. inversion H; subst z t. reflexivity.
Qed.

Lemma constraint_concat_cancel_context_main a c y d :
  constraint_concat eqb ([], a :: c) (a :: y, d) =
  option_map (fun p => (a :: fst p, snd p))
    (constraint_concat eqb ([], c) (y, d)).
Proof.
  unfold constraint_concat. simpl.
  rewrite join_cons_same, residual_cons_same.
  destruct (join eqb c (y ++ d)); simpl; [|reflexivity].
  destruct (join eqb (residual eqb c y) d); reflexivity.
Qed.

Lemma constraint_concat_empty_mains c d :
  constraint_concat eqb ([], c) ([], d) =
  option_map (fun t => ([], t)) (join eqb c d).
Proof.
  unfold constraint_concat. simpl.
  destruct (join eqb c d) eqn:Hjoin; [|reflexivity].
  unfold residual. simpl. rewrite Hjoin. reflexivity.
Qed.

Lemma prefix_compatible_cons_heads (a b : A) (u v : word A) :
  prefix_compatible (a :: u) (b :: v) -> a = b.
Proof.
  intros [[z H]|[z H]]; inversion H; reflexivity.
Qed.

Lemma constraint_concat_context_main_head a c b y d out :
  constraint_concat eqb ([], b :: c) (a :: y, d) = Some out ->
  a = b.
Proof.
  intro H.
  destruct (constraint_concat_result_shape eqb [] (b :: c) (a :: y) d H)
    as [t Hout].
  subst out.
  pose proof (proj1
    (constraint_concat_defined_iff_compatible eqb eqb_spec
      [] (b :: c) (a :: y) d)
    (ex_intro _ t H)) as Hcompat.
  simpl in Hcompat. symmetry.
  now apply prefix_compatible_cons_heads in Hcompat.
Qed.

Lemma constraint_concat_empty_mains_result c d t :
  constraint_concat eqb ([], c) ([], d) = Some ([], t) ->
  t = c \/ t = d.
Proof.
  rewrite constraint_concat_empty_mains.
  destruct (join eqb c d) as [z|] eqn:Hz; [|discriminate].
  intro Heq. inversion Heq; subst z.
  apply (join_result eqb eqb_spec c d) in Hz.
  destruct Hz as [[_ Htd]|[_ Htc]].
  - right. exact Htd.
  - left. exact Htc.
Qed.

Lemma constraint_concat_empty_mains_cons a c d t :
  constraint_concat eqb ([], a :: c) ([], a :: d) = Some ([], a :: t) <->
  constraint_concat eqb ([], c) ([], d) = Some ([], t).
Proof.
  rewrite !constraint_concat_empty_mains, join_cons_same.
  destruct (join eqb c d); simpl; split; intro H; try discriminate;
    now inversion H.
Qed.

Lemma constraint_concat_empty_left q out :
  constraint_concat eqb ([], []) q = Some out <-> out = q.
Proof.
  split.
  - intro H. rewrite (constraint_concat_left_identity eqb eqb_spec q) in H.
    now inversion H.
  - intro H. subst out. apply constraint_concat_left_identity; exact eqb_spec.
Qed.

Lemma constraint_concat_empty_right p out :
  constraint_concat eqb p ([], []) = Some out <-> out = p.
Proof.
  split.
  - intro H. rewrite (constraint_concat_right_identity eqb eqb_spec p) in H.
    now inversion H.
  - intro H. subst out. apply constraint_concat_right_identity; exact eqb_spec.
Qed.

(** Lemma 2, first identity (Eq. (13), p.8): main quotient of a
    constrained-language product. *)
Theorem main_quotient_concat (a : A) (R S : constraint_language A) :
  lang_equiv (main_symbol_quotient a (lang_concat eqb R S))
    (lang_union
      (lang_union
        (lang_concat eqb (main_symbol_quotient a R) S)
        (lang_concat eqb (context_symbol_quotient a R)
                         (main_symbol_quotient a S)))
      (lang_concat eqb (language_epsilon_part R)
                       (main_symbol_quotient a S))).
Proof.
  intros [u v].
  unfold main_symbol_quotient, context_symbol_quotient, lang_concat,
    lang_union, language_epsilon_part, epsilon_part. simpl.
  split.
  - intros [[x c] [[y d] [HR [HS Hout]]]].
    destruct x as [|h x].
    + destruct y as [|k y].
      { destruct (constraint_concat_result_shape eqb [] c [] d Hout)
          as [t Hshape].
        discriminate. }
      destruct (constraint_concat_result_shape eqb [] c (k :: y) d Hout)
        as [t Hshape].
      simpl in Hshape. inversion Hshape; subst k y t.
      destruct c as [|h c].
      * unfold constraint_concat in Hout. simpl in Hout.
        inversion Hout; subst d.
        right. exists ([], []), (u, v). split.
        -- split; [exact HR|reflexivity].
        -- split; [exact HS|].
           apply constraint_concat_left_identity; exact eqb_spec.
      * assert (a = h) as ->.
        { eapply constraint_concat_context_main_head; exact Hout. }
        left; right. exists ([], c), (u, d). split.
        -- split; [reflexivity|exact HR].
        -- split; [exact HS|].
           rewrite constraint_concat_cancel_context_main in Hout.
           change
             (option_map (fun p => (h :: fst p, snd p))
               (constraint_concat eqb ([], c) (u, d)) =
              Some (h :: u, v)) in Hout.
           destruct (constraint_concat eqb ([], c) (u, d)) as [[zu zv]|]
             eqn:Hz;
             simpl in Hout; try discriminate.
           inversion Hout; subst. reflexivity.
    + destruct (constraint_concat_result_shape eqb (h :: x) c y d Hout)
        as [t Hshape].
      simpl in Hshape. inversion Hshape; subst h u t.
      left; left. exists (x, c), (y, d). split; [exact HR|].
      split; [exact HS|].
      unfold constraint_concat in Hout |- *. simpl in Hout |- *.
      destruct (join eqb c (y ++ d)); [|discriminate].
      destruct (join eqb (residual eqb c y) d); [|discriminate].
      inversion Hout. reflexivity.
  - intros [H12|H3].
    + destruct H12 as [H1|H2].
      * destruct H1 as [[x c] [[y d] [HR [HS Hout]]]].
        exists (a :: x, c), (y, d). split; [exact HR|].
        split; [exact HS|].
        apply (constraint_concat_prepend_left_main a) in Hout.
        simpl in Hout. exact Hout.
      * destruct H2 as [[x c] [[y d] [[Hx HR] [HS Hout]]]].
        subst x. exists ([], a :: c), (a :: y, d). split; [exact HR|].
        split; [exact HS|].
        rewrite constraint_concat_cancel_context_main.
        exact (f_equal
          (option_map (fun p => (a :: fst p, snd p))) Hout).
    + destruct H3 as [[x c] [[y d] [[HR Hid] [HS Hout]]]].
      inversion Hid; subst x c.
      change (constraint_concat eqb ([], []) (y, d) = Some (u, v)) in Hout.
      rewrite (constraint_concat_left_identity eqb eqb_spec (y, d)) in Hout.
      injection Hout as Hy Hd. subst u v.
      exists ([], []), (a :: y, d). split; [exact HR|].
      split; [exact HS|].
      apply constraint_concat_left_identity; exact eqb_spec.
Qed.

Lemma constraint_concat_empty_mains_heads a h c k d v :
  constraint_concat eqb ([], h :: c) ([], k :: d) = Some ([], a :: v) ->
  h = a /\ k = a /\
  constraint_concat eqb ([], c) ([], d) = Some ([], v).
Proof.
  intro Hout.
  pose proof (constraint_concat_empty_mains_result
    (h :: c) (k :: d) Hout) as Hresult.
  pose proof (proj1
    (constraint_concat_defined_iff_compatible eqb eqb_spec
      [] (h :: c) [] (k :: d))
    (ex_intro _ (a :: v) Hout)) as Hcompat.
  assert (h = k) as Hhk by now apply prefix_compatible_cons_heads in Hcompat.
  destruct Hresult as [Hac|Had].
  - injection Hac as Hva Hha. subst v h. subst k. repeat split; try reflexivity.
    now apply (proj1 (constraint_concat_empty_mains_cons a c d c)).
  - injection Had as Hva Hka. subst v k. subst h. repeat split; try reflexivity.
    now apply (proj1 (constraint_concat_empty_mains_cons a c d d)).
Qed.

(** Lemma 2, second identity (Eq. (13), p.8): context quotient of a
    constrained-language product. *)
Theorem context_quotient_concat (a : A) (R S : constraint_language A) :
  lang_equiv (context_symbol_quotient a (lang_concat eqb R S))
    (lang_union
      (lang_union
        (lang_concat eqb (context_symbol_quotient a R)
                         (context_symbol_quotient a S))
        (lang_concat eqb (context_symbol_quotient a R)
                         (language_epsilon_part S)))
      (lang_concat eqb (language_epsilon_part R)
                       (context_symbol_quotient a S))).
Proof.
  intros [u v].
  unfold context_symbol_quotient, lang_concat, lang_union,
    language_epsilon_part, epsilon_part. simpl.
  split.
  - intros [Hu [[x c] [[y d] [HR [HS Hout]]]]]. subst u.
    destruct (constraint_concat_result_shape eqb x c y d Hout)
      as [t Hshape].
    inversion Hshape as [[Hmain Hcontext]].
    symmetry in Hmain. apply app_eq_nil in Hmain as [Hx Hy].
    subst x y t.
    destruct c as [|h c], d as [|k d].
    + change (constraint_concat eqb ([], []) ([], []) =
        Some ([], a :: v)) in Hout.
      rewrite (constraint_concat_left_identity eqb eqb_spec ([], [])) in Hout.
      discriminate.
    + change (constraint_concat eqb ([], []) ([], k :: d) =
        Some ([], a :: v)) in Hout.
      rewrite (constraint_concat_left_identity eqb eqb_spec ([], k :: d))
        in Hout.
      injection Hout as Hkd. inversion Hkd; subst k d.
      right. exists ([], []), ([], v). split.
      * split; [exact HR|reflexivity].
      * split; [split; [reflexivity|exact HS]|].
        apply constraint_concat_left_identity; exact eqb_spec.
    + change (constraint_concat eqb ([], h :: c) ([], []) =
        Some ([], a :: v)) in Hout.
      rewrite (constraint_concat_right_identity eqb eqb_spec ([], h :: c))
        in Hout.
      injection Hout as Hhc. inversion Hhc; subst h c.
      left; right. exists ([], v), ([], []). split.
      * split; [reflexivity|exact HR].
      * split.
        -- split; [exact HS|reflexivity].
        -- apply constraint_concat_right_identity; exact eqb_spec.
    + destruct (@constraint_concat_empty_mains_heads a h c k d v Hout)
        as [Hh [Hk Hstrip]]. subst h k.
      left; left. exists ([], c), ([], d). split.
      * split; [reflexivity|exact HR].
      * split; [split; [reflexivity|exact HS]|exact Hstrip].
  - intros [H12|H3].
    + destruct H12 as [H1|H2].
      * destruct H1 as [[x c] [[y d] [[Hx HR] [[Hy HS] Hout]]]].
        subst x y.
        destruct (constraint_concat_result_shape eqb [] c [] d Hout)
          as [t Hshape]. inversion Hshape; subst u t.
        split; [reflexivity|].
        exists ([], a :: c), ([], a :: d). split; [exact HR|].
        split; [exact HS|].
        now apply (proj2 (constraint_concat_empty_mains_cons a c d v)).
      * destruct H2 as [[x c] [[y d] [[Hx HR] [[HS Hid] Hout]]]].
        subst x. inversion Hid; subst y d.
        destruct (constraint_concat_result_shape eqb [] c [] [] Hout)
          as [t Hshape]. inversion Hshape; subst u t.
        change (constraint_concat eqb ([], c) ([], []) = Some ([], v))
          in Hout.
        rewrite (constraint_concat_right_identity eqb eqb_spec ([], c))
          in Hout. injection Hout as Hc. subst c.
        split; [reflexivity|].
        exists ([], a :: v), ([], []). split; [exact HR|].
        split; [exact HS|].
        apply constraint_concat_right_identity; exact eqb_spec.
    + destruct H3 as [[x c] [[y d] [[HR Hid] [[Hy HS] Hout]]]].
      inversion Hid; subst x c. subst y.
      destruct (constraint_concat_result_shape eqb [] [] [] d Hout)
        as [t Hshape]. inversion Hshape; subst u t.
      change (constraint_concat eqb ([], []) ([], d) = Some ([], v))
        in Hout.
      rewrite (constraint_concat_left_identity eqb eqb_spec ([], d))
        in Hout. injection Hout as Hd. subst d.
      split; [reflexivity|].
      exists ([], []), ([], a :: v). split; [exact HR|].
      split; [exact HS|].
      apply constraint_concat_left_identity; exact eqb_spec.
Qed.

Lemma lang_power_nonempty_context_factor (R : constraint_language A) n v :
  lang_power eqb R n ([], v) -> v <> [] -> R ([], v).
Proof.
  revert v. induction n as [|n IH]; intros v Hpow Hne; simpl in Hpow.
  - unfold lang_one in Hpow. inversion Hpow. contradiction.
  - destruct Hpow as [[x c] [[y d] [Hp [Hq Hout]]]].
    destruct (constraint_concat_result_shape eqb x c y d Hout)
      as [t Hshape]. inversion Hshape as [[Hmain Hcontext]].
    symmetry in Hmain. apply app_eq_nil in Hmain as [Hx Hy].
    subst x y t.
    pose proof (constraint_concat_empty_mains_result c d Hout) as Hcd.
    destruct Hcd as [Hvc|Hvd].
    + subst v. now apply IH in Hp.
    + subst v. exact Hq.
Qed.

(** Lemma 2, fourth identity (Eq. (13), p.8): the nonempty context of a
    finite product is the longest compatible factor context, hence already
    occurs in the base language. *)
Theorem context_quotient_star (a : A) (R : constraint_language A) :
  lang_equiv (context_symbol_quotient a (lang_star eqb R))
             (context_symbol_quotient a R).
Proof.
  intros [u v]. unfold context_symbol_quotient, lang_star. simpl.
  split.
  - intros [Hu [n Hpow]]. split; [exact Hu|]. subst u.
    eapply lang_power_nonempty_context_factor; [exact Hpow|discriminate].
  - intros [Hu HR]. split; [exact Hu|]. subst u.
    exists 1. simpl. exists ([], []), ([], a :: v). split.
    + reflexivity.
    + split; [exact HR|].
      apply constraint_concat_left_identity; exact eqb_spec.
Qed.

Definition lang_incl (R S : constraint_language A) : Prop :=
  forall p, R p -> S p.

Lemma lang_concat_mono_left R S T :
  lang_incl R S -> lang_incl (lang_concat eqb R T) (lang_concat eqb S T).
Proof.
  intros H q [p [t [Hp [Ht Hout]]]].
  exists p, t. repeat split; auto.
Qed.

Lemma lang_concat_mono_right R S T :
  lang_incl R S -> lang_incl (lang_concat eqb T R) (lang_concat eqb T S).
Proof.
  intros H q [t [p [Ht [Hp Hout]]]].
  exists t, p. repeat split; auto.
Qed.

Lemma main_quotient_mono a R S :
  lang_incl R S ->
  lang_incl (main_symbol_quotient a R) (main_symbol_quotient a S).
Proof. intros H [u v] HR. now apply H. Qed.

Lemma context_quotient_power_in_base a R n :
  lang_incl (context_symbol_quotient a (lang_power eqb R n))
            (context_symbol_quotient a R).
Proof.
  intros [u v] [Hu Hpow]. split; [exact Hu|]. subst u.
  eapply lang_power_nonempty_context_factor; [exact Hpow|discriminate].
Qed.

Lemma lang_power_succ_left (R : constraint_language A) n :
  lang_equiv (lang_concat eqb R (lang_power eqb R n))
             (lang_power eqb R (S n)).
Proof.
  induction n as [|n IH]; simpl.
  - eapply lang_equiv_trans.
    + apply lang_concat_one_right; exact eqb_spec.
    + apply lang_equiv_sym. apply lang_concat_one_left; exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply lang_equiv_sym. apply lang_concat_assoc; exact eqb_spec.
    + apply lang_concat_compat; [exact IH|apply lang_equiv_refl].
Qed.

Lemma lang_base_star_in_star (R : constraint_language A) :
  lang_incl (lang_concat eqb R (lang_star eqb R)) (lang_star eqb R).
Proof.
  intros q [p [s [Hp [[n Hn] Hout]]]].
  exists (S n). apply (proj1 (lang_power_succ_left R n q)).
  exists p, s. repeat split; assumption.
Qed.

Lemma lang_star_right_closed (R : constraint_language A) :
  lang_incl (lang_concat eqb (lang_star eqb R) R) (lang_star eqb R).
Proof.
  intros q [s [p [[n Hn] [Hp Hout]]]].
  exists (S n). simpl. exists s, p. repeat split; assumption.
Qed.

Lemma lang_append_star_identity X R :
  lang_incl X (lang_concat eqb X (lang_star eqb R)).
Proof.
  intros p Hp. exists p, ([], []). repeat split; try assumption.
  - exists 0. reflexivity.
  - apply constraint_concat_right_identity; exact eqb_spec.
Qed.

Lemma lang_append_base_after_star X R :
  lang_incl
    (lang_concat eqb (lang_concat eqb X (lang_star eqb R)) R)
    (lang_concat eqb X (lang_star eqb R)).
Proof.
  intros q Hq.
  apply (proj1 (lang_concat_assoc eqb eqb_spec X (lang_star eqb R) R q))
    in Hq.
  destruct Hq as [x [sr [Hx [Hsr Hout]]]].
  exists x, sr. repeat split; try assumption.
  now apply lang_star_right_closed in Hsr.
Qed.

Lemma epsilon_concat_elim R S :
  lang_incl (lang_concat eqb (language_epsilon_part R) S) S.
Proof.
  intros q [[x c] [p [[HR Hid] [Hp Hout]]]].
  inversion Hid; subst x c.
  change (constraint_concat eqb ([], []) p = Some q) in Hout.
  rewrite (constraint_concat_left_identity eqb eqb_spec p) in Hout.
  inversion Hout; subst q. exact Hp.
Qed.

Lemma two_base_star_in_star (R : constraint_language A) :
  lang_incl
    (lang_concat eqb (lang_concat eqb R R) (lang_star eqb R))
    (lang_star eqb R).
Proof.
  intros q Hq.
  apply (proj1 (lang_concat_assoc eqb eqb_spec R R (lang_star eqb R) q))
    in Hq.
  apply lang_base_star_in_star.
  eapply lang_concat_mono_right; [apply lang_base_star_in_star|exact Hq].
Qed.

Lemma main_quotient_power_in_star_form a R n :
  lang_incl (main_symbol_quotient a (lang_power eqb R n))
    (lang_union
      (lang_concat eqb (main_symbol_quotient a R) (lang_star eqb R))
      (lang_concat eqb
        (lang_concat eqb (context_symbol_quotient a R)
                         (main_symbol_quotient a R))
        (lang_star eqb R))).
Proof.
  induction n as [|n IH].
  - intros [u v] H. unfold main_symbol_quotient, lang_power, lang_one in H.
    discriminate.
  - intros q Hq. simpl in Hq.
    apply (proj1 (main_quotient_concat a (lang_power eqb R n) R q)) in Hq.
    destruct Hq as [H12|H3].
    + destruct H12 as [H1|H2].
      * destruct H1 as [p [r [Hp [Hr Hout]]]].
        specialize (IH p Hp). destruct IH as [IH|IH].
        -- left. apply lang_append_base_after_star.
           exists p, r. repeat split; assumption.
        -- right. apply lang_append_base_after_star.
           exists p, r. repeat split; assumption.
      * right.
        apply lang_append_star_identity.
        destruct H2 as [c [m [Hc [Hm Hout]]]].
        exists c, m. repeat split; try assumption.
        now apply (context_quotient_power_in_base a R n c) in Hc.
    + left. apply lang_append_star_identity.
      now apply epsilon_concat_elim in H3.
Qed.

(** Lemma 2, third identity (Eq. (13), p.8): main quotient of star. *)
Theorem main_quotient_star (a : A) (R : constraint_language A) :
  lang_equiv (main_symbol_quotient a (lang_star eqb R))
    (lang_union
      (lang_concat eqb (main_symbol_quotient a R) (lang_star eqb R))
      (lang_concat eqb
        (lang_concat eqb (context_symbol_quotient a R)
                         (main_symbol_quotient a R))
        (lang_star eqb R))).
Proof.
  intros [u v]. unfold main_symbol_quotient at 1. simpl.
  unfold lang_star at 1.
  split.
  - intros [n Hn].
    now apply (main_quotient_power_in_star_form a R n (u, v)).
  - intros [Hmain|Hcontext].
    + assert (Hprod : main_symbol_quotient a
          (lang_concat eqb R (lang_star eqb R)) (u, v)).
      { apply (proj2 (main_quotient_concat a R (lang_star eqb R) (u, v))).
        left; left. exact Hmain. }
      apply lang_base_star_in_star. exact Hprod.
    + destruct Hcontext as [p [s [Hcm [Hs Hout]]]].
      assert (Hrr : main_symbol_quotient a (lang_concat eqb R R) p).
      { apply (proj2 (main_quotient_concat a R R p)).
        left; right. exact Hcm. }
      assert (Hrrs : main_symbol_quotient a
          (lang_concat eqb (lang_concat eqb R R) (lang_star eqb R))
          (u, v)).
      { apply (proj2
          (main_quotient_concat a (lang_concat eqb R R)
            (lang_star eqb R) (u, v))).
        left; left. exists p, s. repeat split; assumption. }
      apply two_base_star_in_star. exact Hrrs.
Qed.

(** Lemma 2, last identity: lookahead has no main quotient. *)
Theorem main_quotient_lookahead (a : A) (R : constraint_language A) :
  lang_equiv (main_symbol_quotient a (positive_lookahead R)) lang_zero.
Proof.
  intros [u v]. unfold main_symbol_quotient, positive_lookahead, lang_zero.
  split; [|contradiction]. intros [q [_ Hq]]. discriminate.
Qed.

(** Lemma 2, penultimate identity.  The right-hand side is written using the
    total quotient; [pair_symbol_quotient_split] rewrites it to the paper's
    explicit main/context union. *)
Theorem context_quotient_lookahead (a : A) (R : constraint_language A) :
  lang_equiv (context_symbol_quotient a (positive_lookahead R))
    (positive_lookahead (pair_language_symbol_quotient eqb a R)).
Proof.
  intros [u v]. unfold context_symbol_quotient, positive_lookahead.
  split.
  - intros [Hu [p [Hp Hpair]]]. subst u.
    inversion Hpair as [[Hproj]].
    symmetry in Hproj.
    destruct (pair_symbol_quotient_from_projection (a:=a) (z:=v) p Hproj)
      as [q [Hstep Hqproj]].
    exists q. split.
    + exists p. now split.
    + unfold constraint_projection in Hqproj. simpl in Hqproj. now f_equal.
  - intros [q [[p [Hp Hstep]] Hpair]].
    pose proof (pair_symbol_quotient_projection a p (q:=q) Hstep)
      as Hproj.
    inversion Hpair as [[Hu Hv]]. subst u v.
    split.
    + reflexivity.
    + exists p. split; [exact Hp|].
      unfold constraint_projection in *. simpl in *. f_equal. symmetry.
      exact Hproj.
Qed.

Lemma main_quotient_union (a : A) (R S : constraint_language A) :
  lang_equiv (main_symbol_quotient a (lang_union R S))
    (lang_union (main_symbol_quotient a R) (main_symbol_quotient a S)).
Proof. intros [u v]. unfold main_symbol_quotient, lang_union. simpl. tauto. Qed.

Lemma context_quotient_union (a : A) (R S : constraint_language A) :
  lang_equiv (context_symbol_quotient a (lang_union R S))
    (lang_union (context_symbol_quotient a R) (context_symbol_quotient a S)).
Proof.
  intros [u v]. unfold context_symbol_quotient, lang_union. simpl. tauto.
Qed.

Lemma pair_word_quotient_nil p :
  pair_word_quotient eqb [] p = Some p.
Proof. reflexivity. Qed.

Lemma pair_word_quotient_app x y p q :
  pair_word_quotient eqb (x ++ y) p = Some q <->
  exists m, pair_word_quotient eqb x p = Some m /\
            pair_word_quotient eqb y m = Some q.
Proof.
  revert p. induction x as [|a x IH]; intros p; simpl.
  - split.
    + intro H. exists p. now split.
    + intros [m [Hpm Hmq]]. inversion Hpm. exact Hmq.
  - destruct (pair_symbol_quotient eqb a p) as [m|] eqn:Hm.
    + apply IH.
    + split; [discriminate|]. intros [z [Hz _]]. discriminate.
Qed.

(** Paper Eq. (14): word quotient is pointwise pair quotient. *)
Theorem pair_language_word_quotient_pointwise w R q :
  pair_language_word_quotient eqb w R q <->
  exists p, R p /\ pair_word_quotient eqb w p = Some q.
Proof. reflexivity. Qed.

End Quotients.

(** Eq. (18), p.8, lines 393--398. *)
Definition derivative_pair (A : Type) := (rewpla A * rewpla A)%type.

Definition derivative_main {A} (d : derivative_pair A) := fst d.
Definition derivative_context {A} (d : derivative_pair A) := snd d.
Definition derivative_merge {A} (d : derivative_pair A) : rewpla A :=
  WPlus (fst d) (snd d).

Definition wguard {A} (b : bool) (r : rewpla A) : rewpla A :=
  if b then r else WZero.

(** Paper Eq. (19): the semantic specification of [lambda_1].  It is kept
    proof-relevant here; LookaheadDecision supplies its Boolean decision. *)
Definition lambda1_spec {A} (eqb : A -> A -> bool)
  (lambda1b : rewpla A -> bool) : Prop :=
  forall r, lambda1b r = true <->
    exists v, rewpla_denote eqb r ([], v).

Definition rewpla_has_empty_main {A} (eqb : A -> A -> bool)
  (r : rewpla A) : Prop := exists v, rewpla_denote eqb r ([], v).

(** Paper Eq. (20), p.9, lines 406--414.  Parameterizing the rule by a
    Boolean satisfying [lambda1_spec] separates the mathematical rule from
    the finite decision procedure. *)
Fixpoint paper_symbol_derivative {A} (eqb : A -> A -> bool)
  (lambda1b : rewpla A -> bool) (a : A) (r : rewpla A)
  : derivative_pair A :=
  match r with
  | WZero | WEps => (WZero, WZero)
  | WAtom b => if eqb a b then (WEps, WZero) else (WZero, WZero)
  | WPlus r s =>
      let '(rm, rc) := paper_symbol_derivative eqb lambda1b a r in
      let '(sm, sc) := paper_symbol_derivative eqb lambda1b a s in
      (WPlus rm sm, WPlus rc sc)
  | WConcat r s =>
      let '(rm, rc) := paper_symbol_derivative eqb lambda1b a r in
      let '(sm, sc) := paper_symbol_derivative eqb lambda1b a s in
      (WPlus (WPlus (WConcat rm s)
                    (WConcat (wguard (lambda1b r) rc) sm))
             (WConcat (rewpla_lambda r) sm),
       WPlus (WPlus (WConcat (wguard (lambda1b r) rc) sc)
                    (WConcat (wguard (lambda1b r) rc)
                             (rewpla_lambda s)))
             (WConcat (rewpla_lambda r) sc))
  | WStar r =>
      let '(rm, rc) := paper_symbol_derivative eqb lambda1b a r in
      (WPlus (WConcat rm (WStar r))
             (WConcat (WConcat rc rm) (WStar r)), rc)
  | WLookahead r =>
      let d := paper_symbol_derivative eqb lambda1b a r in
      (WZero, WLookahead (derivative_merge d))
  end.

(** Mechanization extension.  The occurrences of [lambda_1(r)] multiplying
    [r_c] in Eq. (20) are semantically redundant: a nonempty [r_c] already
    witnesses an empty-main pair of [r].  Erasing those gates gives a wholly
    structural, constructive derivative used by routine computation. *)
Fixpoint symbol_derivative_core {A} (eqb : A -> A -> bool)
  (a : A) (r : rewpla A) : derivative_pair A :=
  match r with
  | WZero | WEps => (WZero, WZero)
  | WAtom b => if eqb a b then (WEps, WZero) else (WZero, WZero)
  | WPlus r s =>
      let '(rm, rc) := symbol_derivative_core eqb a r in
      let '(sm, sc) := symbol_derivative_core eqb a s in
      (WPlus rm sm, WPlus rc sc)
  | WConcat r s =>
      let '(rm, rc) := symbol_derivative_core eqb a r in
      let '(sm, sc) := symbol_derivative_core eqb a s in
      (WPlus (WPlus (WConcat rm s) (WConcat rc sm))
             (WConcat (rewpla_lambda r) sm),
       WPlus (WPlus (WConcat rc sc)
                    (WConcat rc (rewpla_lambda s)))
             (WConcat (rewpla_lambda r) sc))
  | WStar r =>
      let '(rm, rc) := symbol_derivative_core eqb a r in
      (WPlus (WConcat rm (WStar r))
             (WConcat (WConcat rc rm) (WStar r)), rc)
  | WLookahead r =>
      let d := symbol_derivative_core eqb a r in
      (WZero, WLookahead (derivative_merge d))
  end.

(** Paper Eq. (21), p.9, lines 415--419. *)
Fixpoint word_derivative {A} (eqb : A -> A -> bool)
  (w : word A) (r : rewpla A) : rewpla A :=
  match w with
  | [] => r
  | a :: w' =>
      word_derivative eqb w'
        (derivative_merge (symbol_derivative_core eqb a r))
  end.

Fixpoint paper_word_derivative {A} (eqb : A -> A -> bool)
  (lambda1b : rewpla A -> bool) (w : word A) (r : rewpla A) : rewpla A :=
  match w with
  | [] => r
  | a :: w' =>
      paper_word_derivative eqb lambda1b w'
        (derivative_merge (paper_symbol_derivative eqb lambda1b a r))
  end.

(** Daily executable acceptance entry point, Eq. (24), p.10. *)
Definition rewpla_acceptb {A} (eqb : A -> A -> bool)
  (r : rewpla A) (w : word A) : bool :=
  rewpla_nullable (word_derivative eqb w r).

(** Paper's finite-alphabet derivative equation, Eq. (25)--(26). *)
Definition derivative_equation_rhs {A} (eqb : A -> A -> bool)
    (alphabet : list A) (r : rewpla A) : rewpla A :=
  WPlus (rewpla_lambda r)
    (fold_right WPlus WZero
      (map (fun a => WConcat (WAtom a)
        (derivative_merge (symbol_derivative_core eqb a r))) alphabet)).

Section DerivativeCorrectness.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma positive_lookahead_compat (R S : constraint_language A) :
  lang_equiv R S ->
  lang_equiv (positive_lookahead R) (positive_lookahead S).
Proof.
  intros H p. unfold positive_lookahead. split.
  - intros [q [Hq ->]]. exists q. split.
    + apply (proj1 (H q)); exact Hq.
    + reflexivity.
  - intros [q [Hq ->]]. exists q. split.
    + apply (proj2 (H q)); exact Hq.
    + reflexivity.
Qed.

Lemma epsilon_part_compat (R S : constraint_language A) :
  lang_equiv R S -> lang_equiv (epsilon_part R) (epsilon_part S).
Proof. intros H p. unfold epsilon_part. specialize (H ([], [])). tauto. Qed.

Lemma main_quotient_compat a (R S : constraint_language A) :
  lang_equiv R S ->
  lang_equiv (main_symbol_quotient a R) (main_symbol_quotient a S).
Proof. intros H [u v]. unfold main_symbol_quotient. simpl. apply H. Qed.

Lemma context_quotient_compat a (R S : constraint_language A) :
  lang_equiv R S ->
  lang_equiv (context_symbol_quotient a R) (context_symbol_quotient a S).
Proof.
  intros H [u v]. unfold context_symbol_quotient. simpl.
  specialize (H ([], a :: v)). tauto.
Qed.

Lemma main_quotient_zero a :
  lang_equiv (main_symbol_quotient a (@lang_zero A)) lang_zero.
Proof. intros [u v]. unfold main_symbol_quotient, lang_zero. tauto. Qed.

Lemma context_quotient_zero a :
  lang_equiv (context_symbol_quotient a (@lang_zero A)) lang_zero.
Proof. intros [u v]. unfold context_symbol_quotient, lang_zero. tauto. Qed.

Lemma main_quotient_one a :
  lang_equiv (main_symbol_quotient a (@lang_one A)) lang_zero.
Proof.
  intros [u v]. unfold main_symbol_quotient, lang_one, lang_zero. simpl.
  split; [discriminate|contradiction].
Qed.

Lemma context_quotient_one a :
  lang_equiv (context_symbol_quotient a (@lang_one A)) lang_zero.
Proof.
  intros [u v]. unfold context_symbol_quotient, lang_one, lang_zero. simpl.
  split; [intros [_ H]; discriminate|contradiction].
Qed.

Lemma main_quotient_atom a b :
  lang_equiv
    (rewpla_denote eqb (if eqb a b then WEps else WZero))
    (main_symbol_quotient a (rewpla_denote eqb (WAtom b))).
Proof.
  intros [u v]. destruct (eqb a b) eqn:Hab; simpl.
  - apply eqb_spec in Hab. subst b. unfold lang_one, main_symbol_quotient.
    simpl. split; intro H; [now inversion H|].
    inversion H. reflexivity.
  - unfold lang_zero, main_symbol_quotient. simpl. split; [contradiction|].
    intro H. inversion H; subst b.
    pose proof (proj2 (eqb_spec a a) eq_refl). congruence.
Qed.

Lemma context_quotient_atom a b :
  lang_equiv (rewpla_denote eqb WZero)
    (context_symbol_quotient a (rewpla_denote eqb (WAtom b))).
Proof.
  intros [u v]. unfold context_symbol_quotient, lang_zero. simpl.
  split; [contradiction|intros [_ H]; discriminate].
Qed.

Lemma main_quotient_atom_component a b :
  lang_equiv
    (rewpla_denote eqb
      (fst (if eqb a b
            then ((WEps, WZero) : derivative_pair A)
            else ((WZero, WZero) : derivative_pair A))))
    (main_symbol_quotient a (rewpla_denote eqb (WAtom b))).
Proof.
  destruct (eqb a b) eqn:Hab; simpl.
  - apply eqb_spec in Hab. subst b. intros [u v].
    unfold main_symbol_quotient. simpl. unfold lang_one.
    split; intro H; inversion H; reflexivity.
  - intros [u v]. unfold main_symbol_quotient, lang_zero. simpl.
    split; [contradiction|]. intro H. inversion H; subst b.
    pose proof (proj2 (eqb_spec a a) eq_refl). congruence.
Qed.

Lemma context_quotient_atom_component a b :
  lang_equiv
    (rewpla_denote eqb
      (snd (if eqb a b
            then ((WEps, WZero) : derivative_pair A)
            else ((WZero, WZero) : derivative_pair A))))
    (context_symbol_quotient a (rewpla_denote eqb (WAtom b))).
Proof. destruct (eqb a b); simpl; apply context_quotient_atom. Qed.

Lemma derivative_merge_denote (d : derivative_pair A) :
  lang_equiv (rewpla_denote eqb (derivative_merge d))
    (lang_union (rewpla_denote eqb (fst d))
                (rewpla_denote eqb (snd d))).
Proof. apply lang_equiv_refl. Qed.

(** Paper Theorem 2, Eq. (22): simultaneous correctness of the main and
    context components of Eq. (20).  The proof follows the six identities of
    Lemma 2 constructor by constructor. *)
Theorem symbol_derivative_core_correct (a : A) (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (fst (symbol_derivative_core eqb a r)))
    (main_symbol_quotient a (rewpla_denote eqb r)) /\
  lang_equiv
    (rewpla_denote eqb (snd (symbol_derivative_core eqb a r)))
    (context_symbol_quotient a (rewpla_denote eqb r)).
Proof.
  induction r as [| |b|r IHr s IHs|r IHr s IHs|r IHr|r IHr].
  - split; simpl; [apply lang_equiv_sym, main_quotient_zero|
                    apply lang_equiv_sym, context_quotient_zero].
  - split; simpl; [apply lang_equiv_sym, main_quotient_one|
                    apply lang_equiv_sym, context_quotient_one].
  - split.
    + apply main_quotient_atom_component.
    + apply context_quotient_atom_component.
  - destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:Dr.
    destruct (symbol_derivative_core eqb a s) as [sm sc] eqn:Ds.
    simpl in IHr, IHs.
    destruct IHr as [IHrm IHrc], IHs as [IHsm IHsc].
    cbn [symbol_derivative_core]. rewrite Dr, Ds. cbn. split.
    + eapply lang_equiv_trans with (S :=
        lang_union (main_symbol_quotient a (rewpla_denote eqb r))
                   (main_symbol_quotient a (rewpla_denote eqb s))).
      * apply lang_union_compat; [exact IHrm|exact IHsm].
      * apply lang_equiv_sym. apply main_quotient_union; exact eqb_spec.
    + eapply lang_equiv_trans with (S :=
        lang_union (context_symbol_quotient a (rewpla_denote eqb r))
                   (context_symbol_quotient a (rewpla_denote eqb s))).
      * apply lang_union_compat; [exact IHrc|exact IHsc].
      * apply lang_equiv_sym. apply context_quotient_union; exact eqb_spec.
  - destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:Dr.
    destruct (symbol_derivative_core eqb a s) as [sm sc] eqn:Ds.
    simpl in IHr, IHs.
    destruct IHr as [IHrm IHrc], IHs as [IHsm IHsc].
    cbn [symbol_derivative_core]. rewrite Dr, Ds. cbn. split.
    + eapply lang_equiv_trans.
      * apply lang_union_compat.
        -- apply lang_union_compat.
           ++ apply lang_concat_compat; [exact IHrm|apply lang_equiv_refl].
           ++ apply lang_concat_compat; [exact IHrc|exact IHsm].
        -- apply lang_concat_compat.
           ++ apply rewpla_lambda_correct; exact eqb_spec.
           ++ exact IHsm.
      * apply lang_equiv_sym. apply main_quotient_concat; exact eqb_spec.
    + eapply lang_equiv_trans.
      * apply lang_union_compat.
        -- apply lang_union_compat.
           ++ apply lang_concat_compat; [exact IHrc|exact IHsc].
           ++ apply lang_concat_compat.
              ** exact IHrc.
              ** apply rewpla_lambda_correct; exact eqb_spec.
        -- apply lang_concat_compat.
           ++ apply rewpla_lambda_correct; exact eqb_spec.
           ++ exact IHsc.
      * apply lang_equiv_sym. apply context_quotient_concat; exact eqb_spec.
  - destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:Dr.
    simpl in IHr. destruct IHr as [IHrm IHrc].
    cbn [symbol_derivative_core]. rewrite Dr. cbn. split.
    + eapply lang_equiv_trans.
      * apply lang_union_compat.
        -- apply lang_concat_compat; [exact IHrm|apply lang_equiv_refl].
        -- apply lang_concat_compat.
           ++ apply lang_concat_compat; [exact IHrc|exact IHrm].
           ++ apply lang_equiv_refl.
      * apply lang_equiv_sym. apply main_quotient_star; exact eqb_spec.
    + eapply lang_equiv_trans; [exact IHrc|].
      apply lang_equiv_sym. apply context_quotient_star; exact eqb_spec.
  - destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:Dr.
    simpl in IHr. destruct IHr as [IHrm IHrc].
    cbn [symbol_derivative_core]. rewrite Dr. cbn. split.
    + apply lang_equiv_sym. apply main_quotient_lookahead.
    + eapply lang_equiv_trans.
      * apply positive_lookahead_compat, lang_union_compat;
          [exact IHrm|exact IHrc].
      * eapply lang_equiv_trans.
        -- apply positive_lookahead_compat.
           apply lang_equiv_sym. apply pair_symbol_quotient_split; exact eqb_spec.
        -- apply lang_equiv_sym. apply context_quotient_lookahead; exact eqb_spec.
Qed.

(** The Boolean guard in paper Eq. (20) is redundant on a context derivative:
    when it is false, that derivative has empty denotation. *)
Lemma paper_context_guard_equiv (lambda1b : rewpla A -> bool)
    (Hlambda1 : lambda1_spec eqb lambda1b) (a : A)
    (r x : rewpla A) :
  lang_equiv (rewpla_denote eqb x)
    (context_symbol_quotient a (rewpla_denote eqb r)) ->
  lang_equiv (rewpla_denote eqb (wguard (lambda1b r) x))
    (rewpla_denote eqb x).
Proof.
  intro Hx.
  destruct (lambda1b r) eqn:Hguard.
  - apply lang_equiv_refl.
  - assert (Hnone : ~ exists v, rewpla_denote eqb r ([], v)).
    { intro H. apply (proj2 (Hlambda1 r)) in H. congruence. }
    intro p. simpl. split; [contradiction|].
    intro Hp. apply (proj1 (Hx p)) in Hp.
    destruct p as [u v]. destruct Hp as [_ Hr].
    exfalso. apply Hnone. now exists (a :: v).
Qed.

(** Eq. (20) is not merely mirrored as syntax: under its semantic
    specification of lambda_1, it denotes the same two quotients as the
    constructive, gate-free derivative used by the executable core. *)
Theorem paper_symbol_derivative_equiv_core
    (lambda1b : rewpla A -> bool)
    (Hlambda1 : lambda1_spec eqb lambda1b) (a : A)
    (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (fst (paper_symbol_derivative eqb lambda1b a r)))
    (rewpla_denote eqb (fst (symbol_derivative_core eqb a r))) /\
  lang_equiv
    (rewpla_denote eqb (snd (paper_symbol_derivative eqb lambda1b a r)))
    (rewpla_denote eqb (snd (symbol_derivative_core eqb a r))).
Proof.
  induction r as [| |b|r IHr s IHs|r IHr s IHs|r IHr|r IHr].
  - split; apply lang_equiv_refl.
  - split; apply lang_equiv_refl.
  - destruct (eqb a b); split; apply lang_equiv_refl.
  - destruct (paper_symbol_derivative eqb lambda1b a r)
      as [prm prc] eqn:Pr.
    destruct (paper_symbol_derivative eqb lambda1b a s)
      as [psm psc] eqn:Ps.
    destruct (symbol_derivative_core eqb a r)
      as [crm crc] eqn:Cr.
    destruct (symbol_derivative_core eqb a s)
      as [csm csc] eqn:Cs.
    simpl in IHr, IHs. destruct IHr as [Hrm Hrc], IHs as [Hsm Hsc].
    cbn [paper_symbol_derivative symbol_derivative_core].
    rewrite Pr, Ps, Cr, Cs. cbn.
    split; apply lang_union_compat; assumption.
  - destruct (paper_symbol_derivative eqb lambda1b a r)
      as [prm prc] eqn:Pr.
    destruct (paper_symbol_derivative eqb lambda1b a s)
      as [psm psc] eqn:Ps.
    destruct (symbol_derivative_core eqb a r)
      as [crm crc] eqn:Cr.
    destruct (symbol_derivative_core eqb a s)
      as [csm csc] eqn:Cs.
    simpl in IHr, IHs. destruct IHr as [Hrm Hrc], IHs as [Hsm Hsc].
    assert (Hguard : lang_equiv
        (rewpla_denote eqb (wguard (lambda1b r) prc))
        (rewpla_denote eqb crc)).
    { eapply lang_equiv_trans.
      - apply paper_context_guard_equiv with (r := r) (a := a);
          [exact Hlambda1|].
        eapply lang_equiv_trans; [exact Hrc|].
        pose proof (symbol_derivative_core_correct a r) as [_ Hcore].
        now rewrite Cr in Hcore.
      - exact Hrc. }
    cbn [paper_symbol_derivative symbol_derivative_core].
    rewrite Pr, Ps, Cr, Cs. cbn. split.
    + apply lang_union_compat.
      * apply lang_union_compat.
        -- apply lang_concat_compat; [exact Hrm|apply lang_equiv_refl].
        -- apply lang_concat_compat; [exact Hguard|exact Hsm].
      * apply lang_concat_compat; [apply lang_equiv_refl|exact Hsm].
    + apply lang_union_compat.
      * apply lang_union_compat.
        -- apply lang_concat_compat; [exact Hguard|exact Hsc].
        -- apply lang_concat_compat;
             [exact Hguard|apply lang_equiv_refl].
      * apply lang_concat_compat; [apply lang_equiv_refl|exact Hsc].
  - destruct (paper_symbol_derivative eqb lambda1b a r)
      as [prm prc] eqn:Pr.
    destruct (symbol_derivative_core eqb a r)
      as [crm crc] eqn:Cr.
    simpl in IHr. destruct IHr as [Hrm Hrc].
    cbn [paper_symbol_derivative symbol_derivative_core].
    rewrite Pr, Cr. cbn. split.
    + apply lang_union_compat.
      * apply lang_concat_compat; [exact Hrm|apply lang_equiv_refl].
      * apply lang_concat_compat.
        -- apply lang_concat_compat; [exact Hrc|exact Hrm].
        -- apply lang_equiv_refl.
    + exact Hrc.
  - destruct (paper_symbol_derivative eqb lambda1b a r)
      as [prm prc] eqn:Pr.
    destruct (symbol_derivative_core eqb a r)
      as [crm crc] eqn:Cr.
    simpl in IHr. destruct IHr as [Hrm Hrc].
    cbn [paper_symbol_derivative symbol_derivative_core].
    rewrite Pr, Cr. cbn. split.
    + apply lang_equiv_refl.
    + apply positive_lookahead_compat.
      apply lang_union_compat; assumption.
Qed.

Theorem paper_symbol_derivative_correct
    (lambda1b : rewpla A -> bool)
    (Hlambda1 : lambda1_spec eqb lambda1b) (a : A)
    (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (fst (paper_symbol_derivative eqb lambda1b a r)))
    (main_symbol_quotient a (rewpla_denote eqb r)) /\
  lang_equiv
    (rewpla_denote eqb (snd (paper_symbol_derivative eqb lambda1b a r)))
    (context_symbol_quotient a (rewpla_denote eqb r)).
Proof.
  destruct (paper_symbol_derivative_equiv_core
    Hlambda1 a r) as [Hm Hc].
  destruct (symbol_derivative_core_correct a r) as [Hcm Hcc].
  split; eapply lang_equiv_trans; eauto.
Qed.

(** Eq. (23), first identity: merging the two components is exactly the total
    symbol quotient. *)
Theorem symbol_derivative_core_merge_correct (a : A) (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (derivative_merge (symbol_derivative_core eqb a r)))
    (pair_language_symbol_quotient eqb a (rewpla_denote eqb r)).
Proof.
  destruct (symbol_derivative_core_correct a r) as [Hm Hc].
  eapply lang_equiv_trans.
  - apply lang_union_compat; [exact Hm|exact Hc].
  - apply lang_equiv_sym. apply pair_symbol_quotient_split; exact eqb_spec.
Qed.

(** The paper's guarded derivative yields the same full pair quotient. *)
Theorem paper_symbol_derivative_merge_correct
    (lambda1b : rewpla A -> bool)
    (Hlambda1 : lambda1_spec eqb lambda1b) (a : A)
    (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb
      (derivative_merge (paper_symbol_derivative eqb lambda1b a r)))
    (pair_language_symbol_quotient eqb a (rewpla_denote eqb r)).
Proof.
  destruct (paper_symbol_derivative_correct Hlambda1 a r)
    as [Hm Hc].
  eapply lang_equiv_trans.
  - apply lang_union_compat; [exact Hm|exact Hc].
  - apply lang_equiv_sym, pair_symbol_quotient_split; exact eqb_spec.
Qed.

Lemma pair_language_word_quotient_compat w
  (R S : constraint_language A) :
  lang_equiv R S ->
  lang_equiv (pair_language_word_quotient eqb w R)
             (pair_language_word_quotient eqb w S).
Proof.
  intros H q. unfold pair_language_word_quotient. split.
  - intros [p [Hp Hstep]]. exists p. split;
      [apply (proj1 (H p)); exact Hp|exact Hstep].
  - intros [p [Hp Hstep]]. exists p. split;
      [apply (proj2 (H p)); exact Hp|exact Hstep].
Qed.

Lemma pair_language_word_quotient_cons a w R :
  lang_equiv (pair_language_word_quotient eqb (a :: w) R)
    (pair_language_word_quotient eqb w
      (pair_language_symbol_quotient eqb a R)).
Proof.
  intro q. unfold pair_language_word_quotient,
    pair_language_symbol_quotient. simpl. split.
  - intros [p [Hp Hstep]].
    destruct (pair_symbol_quotient eqb a p) as [m|] eqn:Hm;
      [|discriminate].
    exists m. split; [exists p; now split|exact Hstep].
  - intros [m [[p [Hp Hm]] Hstep]].
    exists p. split; [exact Hp|]. now rewrite Hm.
Qed.

(** Eq. (23), second identity: iterated expression derivatives denote the
    executable quotient by the whole input word. *)
Theorem word_derivative_correct w (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (word_derivative eqb w r))
    (pair_language_word_quotient eqb w (rewpla_denote eqb r)).
Proof.
  revert r. induction w as [|a w IH]; intro r; simpl.
  - intro q. unfold pair_language_word_quotient. split.
    + intro Hq. exists q. now split.
    + intros [p [Hp Hstep]]. inversion Hstep; subst p. exact Hp.
  - eapply lang_equiv_trans.
    + apply IH.
    + eapply lang_equiv_trans.
      * apply pair_language_word_quotient_compat.
        apply symbol_derivative_core_merge_correct; exact eqb_spec.
      * apply lang_equiv_sym. apply pair_language_word_quotient_cons.
Qed.

(** Paper Eq. (23) for iteration of the actual guarded Eq. (20). *)
Theorem paper_word_derivative_correct
    (lambda1b : rewpla A -> bool)
    (Hlambda1 : lambda1_spec eqb lambda1b)
    w (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (paper_word_derivative eqb lambda1b w r))
    (pair_language_word_quotient eqb w (rewpla_denote eqb r)).
Proof.
  revert r. induction w as [|a w IH]; intro r; simpl.
  - intro q. unfold pair_language_word_quotient. split.
    + intro Hq. exists q. now split.
    + intros [p [Hp Hstep]]. inversion Hstep; subst p. exact Hp.
  - eapply lang_equiv_trans.
    + apply IH.
    + eapply lang_equiv_trans.
      * apply pair_language_word_quotient_compat.
        apply paper_symbol_derivative_merge_correct; exact Hlambda1.
      * apply lang_equiv_sym, pair_language_word_quotient_cons.
Qed.

Definition word_language_quotient (w : word A) (L : word A -> Prop)
  : word A -> Prop := fun z => L (w ++ z).

Lemma project_symbol_quotient a (R : constraint_language A) z :
  project_language (pair_language_symbol_quotient eqb a R) z <->
  project_language R (a :: z).
Proof.
  unfold project_language, pair_language_symbol_quotient. split.
  - intros [q [[p [Hp Hstep]] Hproj]]. exists p. split; [exact Hp|].
    pose proof (pair_symbol_quotient_projection eqb eqb_spec a p Hstep)
      as Hprefix. now rewrite Hproj in Hprefix.
  - intros [p [Hp Hproj]].
    destruct (pair_symbol_quotient_from_projection eqb eqb_spec p Hproj)
      as [q [Hstep Hq]].
    exists q. split; [exists p; now split|exact Hq].
Qed.

Lemma project_word_quotient w (R : constraint_language A) z :
  project_language (pair_language_word_quotient eqb w R) z <->
  word_language_quotient w (project_language R) z.
Proof.
  revert R z. induction w as [|a w IH]; intros R z.
  - unfold project_language, pair_language_word_quotient,
      word_language_quotient. simpl. split.
    + intros [q [[p [Hp Hstep]] Hproj]]. inversion Hstep; subst p.
      exists q. now split.
    + intros [p [Hp Hproj]]. exists p. split; [exists p; now split|exact Hproj].
  - unfold word_language_quotient. simpl.
    pose proof (pair_language_word_quotient_cons a w R)
      as Hcons.
    split; intro H.
    + assert (Hnested : project_language
          (pair_language_word_quotient eqb w
            (pair_language_symbol_quotient eqb a R)) z).
      { destruct H as [q [Hq Hproj]]. exists q. split.
        - apply (proj1 (Hcons q)); exact Hq.
        - exact Hproj. }
      apply (proj1 (project_symbol_quotient a R (w ++ z))).
      apply (proj1 (IH (pair_language_symbol_quotient eqb a R) z)).
      exact Hnested.
    + pose proof
        (proj2 (project_symbol_quotient a R (w ++ z)) H)
        as Hsymbol.
      pose proof
        (proj2 (IH (pair_language_symbol_quotient eqb a R) z) Hsymbol)
        as Hnested.
      destruct Hnested as [q [Hq Hproj]]. exists q. split.
      * apply (proj2 (Hcons q)); exact Hq.
      * exact Hproj.
Qed.

Lemma project_empty_iff_identity (r : rewpla A) :
  rewpla_language eqb r [] <-> rewpla_denote eqb r ([], []).
Proof.
  unfold rewpla_language, project_language. split.
  - intros [[u v] [Hr Hproj]]. unfold constraint_projection in Hproj. simpl in Hproj.
    apply app_eq_nil in Hproj as [Hu Hv]. subst u v. exact Hr.
  - intro Hr. exists ([], []). now split.
Qed.

Theorem word_derivative_projected_correct w (r : rewpla A) z :
  rewpla_language eqb (word_derivative eqb w r) z <->
  word_language_quotient w (rewpla_language eqb r) z.
Proof.
  unfold rewpla_language.
  eapply iff_trans with (B :=
    project_language
      (pair_language_word_quotient eqb w (rewpla_denote eqb r)) z).
  - unfold project_language. split;
      intros [p [Hp Hproj]]; exists p; split; try exact Hproj.
    + apply (proj1 (word_derivative_correct w r p)); exact Hp.
    + apply (proj2 (word_derivative_correct w r p)); exact Hp.
  - apply project_word_quotient.
Qed.

(** Eq. (24): executable acceptance agrees with the projected language. *)
Theorem rewpla_acceptb_correct (r : rewpla A) w :
  rewpla_acceptb eqb r w = true <-> rewpla_language eqb r w.
Proof.
  unfold rewpla_acceptb.
  rewrite rewpla_nullable_correct by exact eqb_spec.
  rewrite <- project_empty_iff_identity.
  rewrite word_derivative_projected_correct.
  unfold word_language_quotient. now rewrite app_nil_r.
Qed.

Lemma rewpla_language_plus (r s : rewpla A) w :
  rewpla_language eqb (WPlus r s) w <->
  rewpla_language eqb r w \/ rewpla_language eqb s w.
Proof.
  unfold rewpla_language, project_language. simpl.
  split.
  - intros [p [[Hr|Hs] Hw]]; [left|right]; exists p; now split.
  - intros [[p [Hr Hw]]|[p [Hs Hw]]].
    + exists p. split; [now left|exact Hw].
    + exists p. split; [now right|exact Hw].
Qed.

Lemma rewpla_language_union_list (xs : list (rewpla A)) w :
  rewpla_language eqb (fold_right WPlus WZero xs) w <->
  exists x, In x xs /\ rewpla_language eqb x w.
Proof.
  induction xs as [|x xs IH]; simpl.
  - unfold rewpla_language, project_language. simpl.
    split; [intros [p [H _]]; contradiction|intros [x [[] _]]].
  - rewrite rewpla_language_plus, IH. split.
    + intros [Hx|[y [Hy Hylang]]].
      * exists x. split; [now left|exact Hx].
      * exists y. split; [now right|exact Hylang].
    + intros [y [[<-|Hy] Hylang]].
      * now left.
      * right. exists y. now split.
Qed.

Lemma constraint_concat_atom_left a u v :
  constraint_concat eqb ([a], []) (u, v) = Some (a :: u, v).
Proof. destruct u; reflexivity. Qed.

Lemma rewpla_denote_atom_concat a (s : rewpla A) u v :
  rewpla_denote eqb (WConcat (WAtom a) s) (u, v) <->
  exists t, u = a :: t /\ rewpla_denote eqb s (t, v).
Proof.
  simpl. unfold lang_concat. split.
  - intros [p [q [Hp [Hq Hout]]]]. subst p.
    destruct q as [t z]. rewrite constraint_concat_atom_left in Hout.
    inversion Hout; subst. exists t. now split.
  - intros [t [-> Ht]].
    exists ([a], []), (t, v). repeat split; try exact Ht;
      try reflexivity. apply constraint_concat_atom_left.
Qed.

Lemma rewpla_language_atom_concat a (s : rewpla A) w :
  rewpla_language eqb (WConcat (WAtom a) s) w <->
  exists z, w = a :: z /\ rewpla_language eqb s z.
Proof.
  unfold rewpla_language, project_language. split.
  - intros [[u v] [Huv Hw]].
    apply rewpla_denote_atom_concat in Huv as [t [-> Ht]].
    exists (t ++ v). split; [symmetry; exact Hw|].
    exists (t, v). now split.
  - intros [z [-> [[u v] [Hs Hz]]]].
    exists (a :: u, v). split.
    + apply rewpla_denote_atom_concat. exists u. now split.
    + unfold constraint_projection in Hz. simpl in Hz.
      unfold constraint_projection. simpl. now rewrite Hz.
Qed.

Lemma rewpla_lambda_projected (r : rewpla A) w :
  rewpla_language eqb (rewpla_lambda r) w <->
  w = [] /\ rewpla_language eqb r [].
Proof.
  unfold rewpla_lambda.
  destruct (rewpla_nullable r) eqn:Hnullable.
  - split.
    + intros [p [Hp Hw]]. simpl in Hp. unfold lang_one in Hp.
      subst p. simpl in Hw. subst w. split; [reflexivity|].
      apply project_empty_iff_identity, rewpla_nullable_correct;
        [exact eqb_spec|exact Hnullable].
    + intros [-> _]. exists ([], []). now split.
  - split.
    + intros [p [Hp _]]. simpl in Hp. contradiction.
    + intros [_ Hr]. apply project_empty_iff_identity in Hr.
      apply rewpla_nullable_correct in Hr; [congruence|exact eqb_spec].
Qed.

Theorem derivative_equation_decomposed (alphabet : list A)
    (alphabet_complete : forall a : A, In a alphabet)
    (r : rewpla A) w :
  rewpla_language eqb r w <->
  rewpla_language eqb (rewpla_lambda r) w \/
  exists a, In a alphabet /\ exists z,
    w = a :: z /\
    rewpla_language eqb
      (derivative_merge (symbol_derivative_core eqb a r)) z.
Proof.
  destruct w as [|a z].
  - split.
    + intro Hr. left. apply rewpla_lambda_projected. now split.
    + intros [Hlambda|[b [_ [z [H _]]]]].
      * apply rewpla_lambda_projected in Hlambda. exact (proj2 Hlambda).
      * discriminate.
  - split.
    + intro Hr. right. exists a. split; [apply alphabet_complete|].
      exists z. split; [reflexivity|].
      apply (proj2 (word_derivative_projected_correct [a] r z)).
      simpl. exact Hr.
    + intros [Hlambda|[b [_ [z' [Hword Hderiv]]]]].
      * apply rewpla_lambda_projected in Hlambda.
        discriminate (proj1 Hlambda).
      * inversion Hword; subst b z'.
        apply (proj1 (word_derivative_projected_correct [a] r z)).
        simpl. exact Hderiv.
Qed.

Theorem derivative_equation_expression (alphabet : list A)
    (alphabet_complete : forall a : A, In a alphabet)
    (r : rewpla A) w :
  rewpla_language eqb r w <->
  rewpla_language eqb (derivative_equation_rhs eqb alphabet r) w.
Proof.
  unfold derivative_equation_rhs.
  rewrite rewpla_language_plus, rewpla_language_union_list.
  rewrite (derivative_equation_decomposed alphabet
    alphabet_complete r w).
  split.
  - intros [Hlambda|[a [Ha [z [Hw Hderiv]]]]].
    + now left.
    + right. exists (WConcat (WAtom a)
        (derivative_merge (symbol_derivative_core eqb a r))).
      split; [apply in_map_iff; exists a; now split|].
      apply rewpla_language_atom_concat. now exists z.
  - intros [Hlambda|[x [Hx Hxlang]]].
    + now left.
    + apply in_map_iff in Hx as [a [Hexpr Ha]]. subst x.
      apply rewpla_language_atom_concat in Hxlang
        as [z [Hw Hderiv]].
      right. exists a. split; [exact Ha|].
      exists z. now split.
Qed.

End DerivativeCorrectness.

(** Directly verified base cases of the component-correctness equation.
    The composite cases are exposed through [symbol_derivative_components]
    below so later proofs and examples can rewrite them one constructor at a
    time without unfolding the fixpoint. *)
Lemma symbol_derivative_core_zero {A : Type} (eqb : A -> A -> bool) (a : A) :
  @symbol_derivative_core A eqb a WZero = (WZero, WZero).
Proof. reflexivity. Qed.

Lemma symbol_derivative_core_eps {A : Type} (eqb : A -> A -> bool) (a : A) :
  @symbol_derivative_core A eqb a WEps = (WZero, WZero).
Proof. reflexivity. Qed.

Lemma symbol_derivative_core_atom_hit {A : Type} (eqb : A -> A -> bool)
  (eqb_spec : forall x y, eqb x y = true <-> x = y) a :
  symbol_derivative_core eqb a (WAtom a) = (WEps, WZero).
Proof. simpl. rewrite (proj2 (eqb_spec a a) eq_refl). reflexivity. Qed.

(** Unfolding theorem corresponding line-for-line to Eq. (20). *)
Theorem symbol_derivative_components {A : Type} (eqb : A -> A -> bool)
  (a : A) (r : rewpla A) :
  symbol_derivative_core eqb a r =
  match r with
  | WZero | WEps => (WZero, WZero)
  | WAtom b => if eqb a b then (WEps, WZero) else (WZero, WZero)
  | WPlus r s =>
      let '(rm, rc) := symbol_derivative_core eqb a r in
      let '(sm, sc) := symbol_derivative_core eqb a s in
      (WPlus rm sm, WPlus rc sc)
  | WConcat r s =>
      let '(rm, rc) := symbol_derivative_core eqb a r in
      let '(sm, sc) := symbol_derivative_core eqb a s in
      (WPlus (WPlus (WConcat rm s) (WConcat rc sm))
             (WConcat (rewpla_lambda r) sm),
       WPlus (WPlus (WConcat rc sc) (WConcat rc (rewpla_lambda s)))
             (WConcat (rewpla_lambda r) sc))
  | WStar r =>
      let '(rm, rc) := symbol_derivative_core eqb a r in
      (WPlus (WConcat rm (WStar r))
             (WConcat (WConcat rc rm) (WStar r)), rc)
  | WLookahead r =>
      let d := symbol_derivative_core eqb a r in
      (WZero, WLookahead (derivative_merge d))
  end.
Proof. destruct r; reflexivity. Qed.

(** Mechanization extension: administrative smart constructors implementing
    the zero/unit equations already proved for constraint languages in
    [StringConstraints].  They keep computed paper examples readable. *)
Definition smart_plus {A} (r s : rewpla A) : rewpla A :=
  match r, s with
  | WZero, x => x
  | x, WZero => x
  | _, _ => WPlus r s
  end.

Definition smart_concat {A} (r s : rewpla A) : rewpla A :=
  match r, s with
  | WZero, _ | _, WZero => WZero
  | WEps, x => x
  | x, WEps => x
  | _, _ => WConcat r s
  end.

Definition smart_star {A} (r : rewpla A) : rewpla A :=
  match r with WZero | WEps => WEps | _ => WStar r end.

Definition smart_lookahead {A} (r : rewpla A) : rewpla A :=
  match r with
  | WZero => WZero
  | WEps => WEps
  | WLookahead s => WLookahead s
  | _ => WLookahead r
  end.

Fixpoint rewpla_simplify {A} (r : rewpla A) : rewpla A :=
  match r with
  | WZero => WZero
  | WEps => WEps
  | WAtom a => WAtom a
  | WPlus r s => smart_plus (rewpla_simplify r) (rewpla_simplify s)
  | WConcat r s => smart_concat (rewpla_simplify r) (rewpla_simplify s)
  | WStar r => smart_star (rewpla_simplify r)
  | WLookahead r => smart_lookahead (rewpla_simplify r)
  end.

Definition simplified_symbol_derivative {A} (eqb : A -> A -> bool)
  (a : A) (r : rewpla A) : derivative_pair A :=
  let '(rm, rc) := symbol_derivative_core eqb a r in
  (rewpla_simplify rm, rewpla_simplify rc).

Fixpoint simplified_word_derivative {A} (eqb : A -> A -> bool)
  (w : word A) (r : rewpla A) : rewpla A :=
  match w with
  | [] => rewpla_simplify r
  | a :: w' =>
      simplified_word_derivative eqb w'
        (rewpla_simplify
          (derivative_merge (simplified_symbol_derivative eqb a r)))
  end.

Print Assumptions pair_symbol_quotient_split.
Print Assumptions pair_word_quotient_app.
Print Assumptions context_quotient_lookahead.
Print Assumptions paper_symbol_derivative_correct.
Print Assumptions paper_word_derivative_correct.
Print Assumptions derivative_equation_expression.
