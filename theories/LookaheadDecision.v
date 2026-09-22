From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import StringConstraints Syntax LookaheadSemantics
  LookaheadDerivatives.
Import ListNotations.

Set Implicit Arguments.

(** * Finite representations and constructive exploration

    The size measures and generator families below follow paper Section 4.3,
    p.11--15, red lines 503--735, Eq. (32)--(48).  Tagged quotients and the
    generic finite worklist are mechanization extensions. *)

(** Paper Eq. (33), p.11, lines 520--529: alphabetic width and nodes. *)
Fixpoint rewpla_width {A} (r : rewpla A) : nat :=
  match r with
  | WZero | WEps => 0
  | WAtom _ => 1
  | WPlus r s | WConcat r s => rewpla_width r + rewpla_width s
  | WStar r | WLookahead r => rewpla_width r
  end.

Fixpoint rewpla_nodes {A} (r : rewpla A) : nat :=
  match r with
  | WZero | WEps | WAtom _ => 1
  | WPlus r s | WConcat r s => 1 + rewpla_nodes r + rewpla_nodes s
  | WStar r | WLookahead r => 1 + rewpla_nodes r
  end.

Theorem rewpla_width_le_nodes {A} (r : rewpla A) :
  rewpla_width r <= rewpla_nodes r.
Proof. induction r; simpl; lia. Qed.

(** Paper Eq. (35), p.12, red lines 549--552: lookahead distributes
    over union at the level of complete pair-language [M] semantics. *)
Theorem rewpla_lookahead_union {A} eqb (r s : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (WLookahead (WPlus r s)))
    (rewpla_denote eqb (WPlus (WLookahead r) (WLookahead s))).
Proof.
  intro p. simpl. unfold positive_lookahead, lang_union.
  split.
  - intros [q [[H|H] Hout]]; [left|right];
      exists q; now split.
  - intros [[q [H Hout]]|[q [H Hout]]].
    + exists q. split; [now left|exact Hout].
    + exists q. split; [now right|exact Hout].
Qed.

(** Paper Eq. (34), p.12, red lines 540--544: the REwPLA-specific
    associativity, identity and zero laws are inherited from the constructive
    constrained-language semiring proved in Section 3. *)
Theorem rewpla_concat_assoc_M {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (p q t : rewpla A) :
  lang_equiv (rewpla_denote eqb (WConcat (WConcat p q) t))
    (rewpla_denote eqb (WConcat p (WConcat q t))).
Proof. simpl. apply lang_concat_assoc. exact eqb_spec. Qed.

Theorem rewpla_concat_one_left_M {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (p : rewpla A) :
  lang_equiv (rewpla_denote eqb (WConcat WEps p))
    (rewpla_denote eqb p).
Proof. simpl. apply lang_concat_one_left. exact eqb_spec. Qed.

Theorem rewpla_concat_one_right_M {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (p : rewpla A) :
  lang_equiv (rewpla_denote eqb (WConcat p WEps))
    (rewpla_denote eqb p).
Proof. simpl. apply lang_concat_one_right. exact eqb_spec. Qed.

Theorem rewpla_concat_zero_left_M {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (p : rewpla A) :
  lang_equiv (rewpla_denote eqb (WConcat WZero p))
    (rewpla_denote eqb WZero).
Proof. simpl. apply lang_concat_zero_left. Qed.

Theorem rewpla_concat_zero_right_M {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (p : rewpla A) :
  lang_equiv (rewpla_denote eqb (WConcat p WZero))
    (rewpla_denote eqb WZero).
Proof. simpl. apply lang_concat_zero_right. Qed.

(** A decidable structural equality, used only to store finite syntactic
    representatives.  Semantic equality is deliberately not conflated with
    this test. *)
Fixpoint rewpla_eqb {A} (eqb : A -> A -> bool) (r s : rewpla A) : bool :=
  match r, s with
  | WZero, WZero | WEps, WEps => true
  | WAtom a, WAtom b => eqb a b
  | WPlus r1 r2, WPlus s1 s2
  | WConcat r1 r2, WConcat s1 s2 =>
      rewpla_eqb eqb r1 s1 && rewpla_eqb eqb r2 s2
  | WStar r, WStar s | WLookahead r, WLookahead s => rewpla_eqb eqb r s
  | _, _ => false
  end.

Theorem rewpla_eqb_spec {A} (eqb : A -> A -> bool)
  (eqb_spec : forall x y, eqb x y = true <-> x = y) r s :
  rewpla_eqb eqb r s = true <-> r = s.
Proof.
  revert s. induction r; intros s; destruct s; simpl; try (split; discriminate).
  - tauto.
  - tauto.
  - rewrite eqb_spec. split; [now intros ->|now intros [= ->]].
  - rewrite andb_true_iff, IHr1, IHr2. split.
    + intros [-> ->]. reflexivity.
    + intros [= -> ->]. now split.
  - rewrite andb_true_iff, IHr1, IHr2. split.
    + intros [-> ->]. reflexivity.
    + intros [= -> ->]. now split.
  - rewrite IHr. split; [now intros ->|now intros [= ->]].
  - rewrite IHr. split; [now intros ->|now intros [= ->]].
Qed.

(** Paper Eq. (36), p.12, lines 560--575: continuation and constraint
    families.  These raw lists retain duplicates; applying [nodup] gives the
    finite set presentation from the paper, while the raw cardinality bound
    below is stronger than the corresponding set bound. *)
Fixpoint continuation_generators_raw {A} (r : rewpla A) : list (rewpla A) :=
  match r with
  | WZero | WEps => []
  | WAtom _ => [WEps]
  | WPlus r s => continuation_generators_raw r ++ continuation_generators_raw s
  | WConcat r s =>
      map (fun x => WConcat x s) (continuation_generators_raw r) ++
      continuation_generators_raw s
  | WStar r => map (fun x => WConcat x (WStar r))
                     (continuation_generators_raw r)
  | WLookahead _ => []
  end.

Fixpoint constraint_generators_raw {A} (r : rewpla A) : list (rewpla A) :=
  match r with
  | WZero | WEps | WAtom _ => []
  | WPlus r s | WConcat r s =>
      constraint_generators_raw r ++ constraint_generators_raw s
  | WStar r => constraint_generators_raw r
  | WLookahead r =>
      constraint_generators_raw r ++
      map WLookahead (continuation_generators_raw r)
  end.

Fixpoint nodupb {X} (eqb : X -> X -> bool) (xs : list X) : list X :=
  match xs with
  | [] => []
  | x :: xs' =>
      if existsb (eqb x) xs' then nodupb eqb xs' else x :: nodupb eqb xs'
  end.

Lemma nodupb_length_le {X} eqb (xs : list X) :
  length (nodupb eqb xs) <= length xs.
Proof.
  induction xs as [|x xs IH]; simpl; [lia|].
  destruct (existsb (eqb x) xs); simpl; lia.
Qed.

Lemma nodupb_in_iff {X} eqb
    (eqb_spec : forall x y : X, eqb x y = true <-> x = y)
    (xs : list X) x :
  In x (nodupb eqb xs) <-> In x xs.
Proof.
  induction xs as [|head tail IH]; simpl; [tauto|].
  destruct (existsb (eqb head) tail) eqn:Hduplicate.
  - rewrite IH. split.
    + intro H. now right.
    + intros [<-|H]; [|exact H].
      apply existsb_exists in Hduplicate as [y [Hy Htest]].
      apply eqb_spec in Htest. now subst y.
  - simpl. rewrite IH. tauto.
Qed.

Theorem nodupb_nodup {X} eqb
    (eqb_spec : forall x y : X, eqb x y = true <-> x = y)
    (xs : list X) :
  NoDup (nodupb eqb xs).
Proof.
  induction xs as [|head tail IH]; simpl; [constructor|].
  destruct (existsb (eqb head) tail) eqn:Hduplicate; [exact IH|].
  constructor; [|exact IH].
  intro H. apply (proj1 (nodupb_in_iff eqb eqb_spec tail head)) in H.
  assert (Htrue : existsb (eqb head) tail = true).
  { apply existsb_exists. exists head. split;
      [exact H|apply eqb_spec; reflexivity]. }
  congruence.
Qed.

Definition continuation_generators {A} (eqb : A -> A -> bool) (r : rewpla A) :=
  nodupb (rewpla_eqb eqb) (continuation_generators_raw r).

Definition constraint_generators {A} (eqb : A -> A -> bool) (r : rewpla A) :=
  nodupb (rewpla_eqb eqb) (constraint_generators_raw r).

Theorem continuation_generators_nodup {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  NoDup (continuation_generators eqb r).
Proof.
  unfold continuation_generators. apply nodupb_nodup.
  exact (rewpla_eqb_spec eqb eqb_spec).
Qed.

Theorem constraint_generators_nodup {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  NoDup (constraint_generators eqb r).
Proof.
  unfold constraint_generators. apply nodupb_nodup.
  exact (rewpla_eqb_spec eqb eqb_spec).
Qed.

Lemma raw_generator_length_bound {A} (r : rewpla A) :
  length (continuation_generators_raw r) +
  length (constraint_generators_raw r) <= rewpla_width r.
Proof.
  induction r; simpl; rewrite ?length_app, ?length_map in *; lia.
Qed.

Theorem generator_length_bound {A} eqb (r : rewpla A) :
  length (continuation_generators eqb r) +
  length (constraint_generators eqb r) <= rewpla_width r.
Proof.
  unfold continuation_generators, constraint_generators.
  eapply Nat.le_trans; [apply Nat.add_le_mono; apply nodupb_length_le|].
  apply raw_generator_length_bound.
Qed.

(** Paper Lemma 3, p.12, red lines 582--611: the raw families already
    satisfy the recursive generator inclusions; nodup/order changes only their
    finite set presentation.  [incl] is ordinary membership inclusion. *)
Theorem raw_generator_inclusion {A} (r : rewpla A) :
  (forall x, In x (continuation_generators_raw r) ->
    incl (continuation_generators_raw x) (continuation_generators_raw r) /\
    incl (constraint_generators_raw x) (constraint_generators_raw r)) /\
  (forall x, In x (constraint_generators_raw r) ->
    continuation_generators_raw x = [] /\
    incl (constraint_generators_raw x) (constraint_generators_raw r)).
Proof.
  induction r as [| |a|r Hr s Hs|r Hr s Hs|r Hr|r Hr]; simpl.
  - split; intros x H; contradiction.
  - split; intros x H; contradiction.
  - split.
    + intros x [<-|[]]. split; intros y Hy; contradiction.
    + intros x H. contradiction.
  - destruct Hr as [Har Hcr], Hs as [Has Hcs]. split.
    + intros x H. apply in_app_iff in H as [H|H].
      * specialize (Har x H) as [Hax Hcx]. split; intros y Hy;
          apply in_app_iff; left; [apply Hax|apply Hcx]; exact Hy.
      * specialize (Has x H) as [Hax Hcx]. split; intros y Hy;
          apply in_app_iff; right; [apply Hax|apply Hcx]; exact Hy.
    + intros x H. apply in_app_iff in H as [H|H].
      * specialize (Hcr x H) as [Hax Hcx]. split; [exact Hax|].
        intros y Hy. apply in_app_iff; left; now apply Hcx.
      * specialize (Hcs x H) as [Hax Hcx]. split; [exact Hax|].
        intros y Hy. apply in_app_iff; right; now apply Hcx.
  - destruct Hr as [Har Hcr], Hs as [Has Hcs]. split.
    + intros x H. apply in_app_iff in H as [H|H].
      * apply in_map_iff in H as [z [<- Hz]].
        specialize (Har z Hz) as [Haz Hcz].
        simpl. split.
        -- intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
           ++ apply in_map_iff in Hy as [z' [<- Hz']].
              apply in_app_iff; left. apply in_map_iff.
              exists z'. split; [reflexivity|now apply Haz].
           ++ apply in_app_iff; right; exact Hy.
        -- intros y Hy. apply in_app_iff in Hy as [Hy|Hy];
             apply in_app_iff; [left; now apply Hcz|right; exact Hy].
      * specialize (Has x H) as [Hax Hcx]. split.
        -- intros y Hy. apply in_app_iff; right; now apply Hax.
        -- intros y Hy. apply in_app_iff; right; now apply Hcx.
    + intros x H. apply in_app_iff in H as [H|H].
      * specialize (Hcr x H) as [Hax Hcx]. split; [exact Hax|].
        intros y Hy. apply in_app_iff; left; now apply Hcx.
      * specialize (Hcs x H) as [Hax Hcx]. split; [exact Hax|].
        intros y Hy. apply in_app_iff; right; now apply Hcx.
  - destruct Hr as [Har Hcr]. split.
    + intros x H. apply in_map_iff in H as [z [<- Hz]].
      specialize (Har z Hz) as [Haz Hcz]. simpl. split.
      * intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
        -- apply in_map_iff in Hy as [z' [<- Hz']].
           apply in_map_iff. exists z'. split; [reflexivity|now apply Haz].
        -- exact Hy.
      * intros y Hy. apply in_app_iff in Hy as [Hy|Hy];
          [now apply Hcz|exact Hy].
    + intros x H. specialize (Hcr x H) as [Hax Hcx].
      split; [exact Hax|exact Hcx].
  - destruct Hr as [Har Hcr]. split.
    + intros x H. contradiction.
    + intros x H. apply in_app_iff in H as [H|H].
      * specialize (Hcr x H) as [Hax Hcx]. split; [exact Hax|].
        intros y Hy. apply in_app_iff; left; now apply Hcx.
      * apply in_map_iff in H as [z [<- Hz]].
        specialize (Har z Hz) as [Haz Hcz]. simpl. split; [reflexivity|].
        intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
        -- apply in_app_iff; left; now apply Hcz.
        -- apply in_map_iff in Hy as [z' [<- Hz']].
           apply in_app_iff; right. apply in_map. now apply Haz.
Qed.

(** Paper Lemma 3 in the deduplicated family presentation used by the
    executable algorithm.  Membership equivalence for [nodupb] transports
    the simultaneous raw inclusions without changing generator identity. *)
Theorem normalized_generator_inclusion {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  (forall x, In x (continuation_generators eqb r) ->
    incl (continuation_generators eqb x) (continuation_generators eqb r) /\
    incl (constraint_generators eqb x) (constraint_generators eqb r)) /\
  (forall x, In x (constraint_generators eqb r) ->
    continuation_generators_raw x = [] /\
    incl (constraint_generators eqb x) (constraint_generators eqb r)).
Proof.
  assert (Hexpr : forall x y : rewpla A,
      rewpla_eqb eqb x y = true <-> x = y).
  { exact (rewpla_eqb_spec eqb eqb_spec). }
  destruct (raw_generator_inclusion r) as [Har Hcr].
  split.
  - intros x Hx.
    apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr
      (continuation_generators_raw r) x)) in Hx.
    destruct (Har x Hx) as [Hax Hcx]. split.
    + intros y Hy.
      apply (proj2 (nodupb_in_iff (rewpla_eqb eqb) Hexpr
        (continuation_generators_raw r) y)).
      apply Hax.
      apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr
        (continuation_generators_raw x) y)). exact Hy.
    + intros y Hy.
      apply (proj2 (nodupb_in_iff (rewpla_eqb eqb) Hexpr
        (constraint_generators_raw r) y)).
      apply Hcx.
      apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr
        (constraint_generators_raw x) y)). exact Hy.
  - intros x Hx.
    apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr
      (constraint_generators_raw r) x)) in Hx.
    destruct (Hcr x Hx) as [Hax Hcx]. split; [exact Hax|].
    intros y Hy.
    apply (proj2 (nodupb_in_iff (rewpla_eqb eqb) Hexpr
      (constraint_generators_raw r) y)).
    apply Hcx.
    apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr
      (constraint_generators_raw x) y)). exact Hy.
Qed.

(** Mechanization extension for paper Section 4.3, p.12, lines 540--559:
    executable ACI normal forms for union.  The preorder term key gives a
    deterministic order; it does not enter the semantic soundness proof. *)
Fixpoint rewpla_term_key {A} (atom_code : A -> nat)
    (r : rewpla A) : list nat :=
  match r with
  | WZero => [0]
  | WEps => [1]
  | WAtom a => [2; atom_code a]
  | WPlus p q =>
      let kp := rewpla_term_key atom_code p in
      let kq := rewpla_term_key atom_code q in
      [3; length kp] ++ kp ++ [length kq] ++ kq
  | WConcat p q =>
      let kp := rewpla_term_key atom_code p in
      let kq := rewpla_term_key atom_code q in
      [4; length kp] ++ kp ++ [length kq] ++ kq
  | WStar p =>
      let kp := rewpla_term_key atom_code p in
      [5; length kp] ++ kp
  | WLookahead p =>
      let kp := rewpla_term_key atom_code p in
      [6; length kp] ++ kp
  end.

Fixpoint nat_list_ltb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs', y :: ys' =>
      if Nat.ltb x y then true
      else if Nat.ltb y x then false
      else nat_list_ltb xs' ys'
  end.

Definition rewpla_term_ltb {A} (atom_code : A -> nat)
    (r s : rewpla A) : bool :=
  nat_list_ltb (rewpla_term_key atom_code r) (rewpla_term_key atom_code s).

Fixpoint aci_union_terms {A} (r : rewpla A) : list (rewpla A) :=
  match r with
  | WZero => []
  | WPlus p q => aci_union_terms p ++ aci_union_terms q
  | _ => [r]
  end.

Fixpoint aci_insert_term {A} (atom_code : A -> nat)
    (x : rewpla A) (xs : list (rewpla A)) : list (rewpla A) :=
  match xs with
  | [] => [x]
  | y :: ys =>
      if rewpla_term_ltb atom_code x y then x :: y :: ys
      else y :: aci_insert_term atom_code x ys
  end.

Fixpoint aci_sort_terms {A} (atom_code : A -> nat)
    (xs : list (rewpla A)) : list (rewpla A) :=
  match xs with
  | [] => []
  | x :: xs' => aci_insert_term atom_code x (aci_sort_terms atom_code xs')
  end.

Fixpoint aci_union_build {A} (xs : list (rewpla A)) : rewpla A :=
  match xs with
  | [] => WZero
  | x :: xs' =>
      match xs' with [] => x | _ => WPlus x (aci_union_build xs') end
  end.

Definition aci_union_normalize {A} eqb atom_code (r : rewpla A) : rewpla A :=
  aci_union_build
    (nodupb (rewpla_eqb eqb)
      (aci_sort_terms atom_code (aci_union_terms r))).

Fixpoint rewpla_aci_normalize {A} eqb atom_code (r : rewpla A) : rewpla A :=
  match r with
  | WZero => WZero
  | WEps => WEps
  | WAtom a => WAtom a
  | WPlus p q =>
      aci_union_normalize eqb atom_code
        (WPlus (rewpla_aci_normalize eqb atom_code p)
          (rewpla_aci_normalize eqb atom_code q))
  | WConcat p q =>
      WConcat (rewpla_aci_normalize eqb atom_code p)
        (rewpla_aci_normalize eqb atom_code q)
  | WStar p => WStar (rewpla_aci_normalize eqb atom_code p)
  | WLookahead p => WLookahead (rewpla_aci_normalize eqb atom_code p)
  end.

Lemma aci_insert_in_iff {A} atom_code
    (x y : rewpla A) xs :
  In y (aci_insert_term atom_code x xs) <-> y = x \/ In y xs.
Proof.
  assert (Hxy : y = x <-> x = y).
  { split; intros ->; reflexivity. }
  rewrite Hxy.
  induction xs as [|head tail IH]; simpl.
  - tauto.
  - destruct (rewpla_term_ltb atom_code x head); simpl; [tauto|].
    rewrite IH. tauto.
Qed.

Lemma aci_sort_in_iff {A} atom_code
    (xs : list (rewpla A)) y :
  In y (aci_sort_terms atom_code xs) <-> In y xs.
Proof.
  induction xs as [|head tail IH]; simpl; [tauto|].
  rewrite aci_insert_in_iff, IH.
  assert (Hhy : y = head <-> head = y).
  { split; intros ->; reflexivity. }
  rewrite Hhy. tauto.
Qed.

Lemma aci_union_terms_semantics {A} eqb (r : rewpla A) p :
  rewpla_denote eqb r p <->
  exists t, In t (aci_union_terms r) /\ rewpla_denote eqb t p.
Proof.
  induction r; simpl.
  - split; [contradiction|intros [t [H _]]; contradiction].
  - split; [intro H; exists WEps; split; [now left|exact H]|
      intros [t [[<-|[]] H]]; exact H].
  - split; [intro H; exists (WAtom a); split; [now left|exact H]|
      intros [t [[<-|[]] H]]; exact H].
  - split.
    + intros [H|H].
      * apply IHr1 in H as [t [Ht Hp]]. exists t. split;
          [apply in_app_iff; now left|exact Hp].
      * apply IHr2 in H as [t [Ht Hp]]. exists t. split;
          [apply in_app_iff; now right|exact Hp].
    + intros [t [Ht Hp]]. apply in_app_iff in Ht as [Ht|Ht].
      * left. apply (proj2 IHr1). exists t. now split.
      * right. apply (proj2 IHr2). exists t. now split.
  - split; [intro H; exists (WConcat r1 r2); split; [now left|exact H]|
      intros [t [[<-|[]] H]]; exact H].
  - split; [intro H; exists (WStar r); split; [now left|exact H]|
      intros [t [[<-|[]] H]]; exact H].
  - split; [intro H; exists (WLookahead r); split; [now left|exact H]|
      intros [t [[<-|[]] H]]; exact H].
Qed.

Lemma aci_union_build_semantics {A} eqb
    (xs : list (rewpla A)) p :
  rewpla_denote eqb (aci_union_build xs) p <->
  exists t, In t xs /\ rewpla_denote eqb t p.
Proof.
  induction xs as [|head tail IH]; simpl.
  - split; [contradiction|intros [t [H _]]; contradiction].
  - destruct tail as [|second rest].
    + split; [intro H; exists head; split; [now left|exact H]|
        intros [t [[<-|[]] H]]; exact H].
    + change ((rewpla_denote eqb head p \/
        rewpla_denote eqb (aci_union_build (second :: rest)) p) <->
        (exists t, (head = t \/ In t (second :: rest)) /\
          rewpla_denote eqb t p)).
      rewrite IH. split.
      * intros [H|[t [Ht Hp]]].
        -- exists head. split; [now left|exact H].
        -- exists t. split; [now right|exact Hp].
      * intros [t [[<-|Ht] Hp]].
        -- now left.
        -- right. exists t. split; assumption.
Qed.

Theorem aci_union_normalize_correct {A} eqb atom_code
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (aci_union_normalize eqb atom_code r))
    (rewpla_denote eqb r).
Proof.
  intro p. unfold aci_union_normalize.
  rewrite aci_union_build_semantics.
  split.
  - intros [t [Ht Hp]].
    apply (proj1 (nodupb_in_iff (rewpla_eqb eqb)
      (rewpla_eqb_spec eqb eqb_spec) _ t)) in Ht.
    apply (proj1 (aci_sort_in_iff atom_code _ t)) in Ht.
    apply (proj2 (aci_union_terms_semantics eqb r p)).
    exists t. now split.
  - intro Hr. apply (proj1 (aci_union_terms_semantics eqb r p))
      in Hr as [t [Ht Hp]].
    exists t. split; [|exact Hp].
    apply (proj2 (nodupb_in_iff (rewpla_eqb eqb)
      (rewpla_eqb_spec eqb eqb_spec) _ t)).
    apply (proj2 (aci_sort_in_iff atom_code _ t)). exact Ht.
Qed.

(** Constructive semantic soundness, independent of whether [atom_code]
    is injective.  An injective code makes the output canonical for ACI
    examples such as [a+b=b+a]; equality is still complete [M]-semantics. *)
Theorem rewpla_aci_normalize_correct {A} eqb atom_code
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (rewpla_aci_normalize eqb atom_code r))
    (rewpla_denote eqb r).
Proof.
  induction r; simpl; try apply lang_equiv_refl.
  - eapply lang_equiv_trans.
    + apply aci_union_normalize_correct. exact eqb_spec.
    + apply lang_union_compat; assumption.
  - apply lang_concat_compat; assumption.
  - apply lang_star_compat. exact IHr.
  - apply positive_lookahead_compat. exact IHr.
Qed.

(** Executable ACI class used by the debug-state merger: two expressions
    belong to one class exactly when their sorted, idempotent union ASTs
    coincide.  The relation is finer than full [M]-equivalence. *)
Definition rewpla_aci_equiv {A : Type} eqb atom_code
    (r s : rewpla A) : Prop :=
  rewpla_aci_normalize eqb atom_code r =
  rewpla_aci_normalize eqb atom_code s.

Theorem rewpla_aci_equiv_refl {A : Type} eqb atom_code
    (r : rewpla A) : rewpla_aci_equiv eqb atom_code r r.
Proof. reflexivity. Qed.

Theorem rewpla_aci_equiv_sym {A : Type} eqb atom_code
    (r s : rewpla A) :
  rewpla_aci_equiv eqb atom_code r s ->
  rewpla_aci_equiv eqb atom_code s r.
Proof. unfold rewpla_aci_equiv. congruence. Qed.

Theorem rewpla_aci_equiv_trans {A : Type} eqb atom_code
    (r s t : rewpla A) :
  rewpla_aci_equiv eqb atom_code r s ->
  rewpla_aci_equiv eqb atom_code s t ->
  rewpla_aci_equiv eqb atom_code r t.
Proof. unfold rewpla_aci_equiv. congruence. Qed.

Theorem rewpla_aci_equiv_sound_M {A : Type} eqb atom_code
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r s : rewpla A) :
  rewpla_aci_equiv eqb atom_code r s ->
  lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s).
Proof.
  unfold rewpla_aci_equiv. intro H. eapply lang_equiv_trans.
  - apply lang_equiv_sym, rewpla_aci_normalize_correct.
    exact eqb_spec.
  - rewrite H. apply rewpla_aci_normalize_correct.
    exact eqb_spec.
Qed.

(** Mechanization extension: the executable smart constructors used before
    ACI normalization also preserve the full pair-language [M].  In
    particular, [WEps] is the two-sided concatenation unit, rather than a
    literal character "1" in a continuation. *)
Lemma rewpla_star_zero_M {A : Type} (eqb : A -> A -> bool) :
  lang_equiv (rewpla_denote eqb (@WStar A WZero))
    (rewpla_denote eqb WEps).
Proof.
  intro p. simpl. unfold lang_star. split.
  - intros [n Hn]. destruct n; [exact Hn|].
    simpl in Hn. destruct Hn as [x [y [_ [Hy _]]]]. contradiction.
  - intro Hp. exists 0. exact Hp.
Qed.

Lemma rewpla_star_eps_M {A : Type} (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y) :
  lang_equiv (rewpla_denote eqb (WStar WEps))
    (rewpla_denote eqb WEps).
Proof.
  intro p. simpl. unfold lang_star. split.
  - intros [n Hn]. induction n; [exact Hn|].
    simpl in Hn. apply (proj1 (lang_concat_one_right eqb eqb_spec
      (lang_power eqb lang_one n) p)) in Hn.
    exact (IHn Hn).
  - intro Hp. exists 0. exact Hp.
Qed.

Lemma rewpla_lookahead_zero_M {A : Type} (eqb : A -> A -> bool) :
  lang_equiv (rewpla_denote eqb (@WLookahead A WZero))
    (rewpla_denote eqb WZero).
Proof.
  intro p. simpl. unfold positive_lookahead, lang_zero.
  split; [intros [q [H _]]; contradiction|contradiction].
Qed.

Lemma rewpla_lookahead_eps_M {A : Type} (eqb : A -> A -> bool) :
  lang_equiv (rewpla_denote eqb (WLookahead WEps))
    (rewpla_denote eqb WEps).
Proof.
  intro p. simpl. unfold positive_lookahead, lang_one.
  split.
  - intros [q [-> Hp]]. exact Hp.
  - intro Hp. exists ([], []). split; [reflexivity|exact Hp].
Qed.

Lemma rewpla_lookahead_nested_M {A : Type} (eqb : A -> A -> bool)
    (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (WLookahead (WLookahead r)))
    (rewpla_denote eqb (WLookahead r)).
Proof.
  intro p. simpl. unfold positive_lookahead. split.
  - intros [q [[t [Ht Hq]] Hp]]. subst q.
    exists t. split; [exact Ht|exact Hp].
  - intros [q [Hq Hp]].
    exists ([], constraint_projection q). split.
    + exists q. split; [exact Hq|reflexivity].
    + exact Hp.
Qed.

Lemma smart_plus_correct_M {A : Type} (eqb : A -> A -> bool)
    (r s : rewpla A) :
  lang_equiv (rewpla_denote eqb (smart_plus r s))
    (rewpla_denote eqb (WPlus r s)).
Proof.
  destruct r, s; simpl; try apply lang_equiv_refl;
    try (apply lang_equiv_sym; apply lang_union_zero_left);
    try (apply lang_equiv_sym; apply lang_union_zero_right).
Qed.

Lemma smart_concat_correct_M {A : Type} (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r s : rewpla A) :
  lang_equiv (rewpla_denote eqb (smart_concat r s))
    (rewpla_denote eqb (WConcat r s)).
Proof.
  destruct r, s; simpl; try apply lang_equiv_refl;
    try (apply lang_equiv_sym; apply lang_concat_zero_left);
    try (apply lang_equiv_sym; apply lang_concat_zero_right);
    try (apply lang_equiv_sym; apply lang_concat_one_left; exact eqb_spec);
    try (apply lang_equiv_sym; apply lang_concat_one_right; exact eqb_spec).
Qed.

Lemma smart_star_correct_M {A : Type} (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (smart_star r))
    (rewpla_denote eqb (WStar r)).
Proof.
  destruct r; simpl; try apply lang_equiv_refl.
  - apply lang_equiv_sym, rewpla_star_zero_M.
  - apply lang_equiv_sym, rewpla_star_eps_M. exact eqb_spec.
Qed.

Lemma smart_lookahead_correct_M {A : Type} (eqb : A -> A -> bool)
    (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (smart_lookahead r))
    (rewpla_denote eqb (WLookahead r)).
Proof.
  destruct r; simpl; try apply lang_equiv_refl.
  - apply lang_equiv_sym. apply (rewpla_lookahead_zero_M eqb).
  - apply lang_equiv_sym. apply (rewpla_lookahead_eps_M eqb).
  - apply lang_equiv_sym. apply (rewpla_lookahead_nested_M eqb).
Qed.

Theorem rewpla_simplify_correct_M {A : Type} (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (rewpla_simplify r))
    (rewpla_denote eqb r).
Proof.
  induction r; simpl; try apply lang_equiv_refl.
  - eapply lang_equiv_trans.
    + apply smart_plus_correct_M.
    + apply lang_union_compat; assumption.
  - eapply lang_equiv_trans.
    + apply smart_concat_correct_M. exact eqb_spec.
    + apply lang_concat_compat; assumption.
  - eapply lang_equiv_trans.
    + apply smart_star_correct_M. exact eqb_spec.
    + apply lang_star_compat. exact IHr.
  - eapply lang_equiv_trans.
    + apply smart_lookahead_correct_M.
    + apply positive_lookahead_compat. exact IHr.
Qed.

Theorem rewpla_simplify_aci_correct_M {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb
      (rewpla_aci_normalize eqb atom_code (rewpla_simplify r)))
    (rewpla_denote eqb r).
Proof.
  eapply lang_equiv_trans.
  - apply rewpla_aci_normalize_correct. exact eqb_spec.
  - apply rewpla_simplify_correct_M. exact eqb_spec.
Qed.

(** Mechanization extension: exactly the normalized one-letter transition
    exported to the generic REwPLA debug DFA.  This is a pair-language
    quotient, not merely a projected-language derivative. *)
Definition rewpla_normalized_symbol_step {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (a : A) (r : rewpla A) : rewpla A :=
  rewpla_aci_normalize eqb atom_code
    (rewpla_simplify
      (derivative_merge (simplified_symbol_derivative eqb a r))).

Theorem rewpla_normalized_symbol_step_correct_M {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (a : A) (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (rewpla_normalized_symbol_step eqb atom_code a r))
    (pair_language_symbol_quotient eqb a (rewpla_denote eqb r)).
Proof.
  unfold rewpla_normalized_symbol_step.
  eapply lang_equiv_trans.
  - apply rewpla_simplify_aci_correct_M. exact eqb_spec.
  - unfold simplified_symbol_derivative.
    destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:D.
    cbn [derivative_merge].
    eapply lang_equiv_trans.
    + apply lang_union_compat; apply rewpla_simplify_correct_M;
        exact eqb_spec.
    + pose proof (symbol_derivative_core_merge_correct eqb eqb_spec a r)
        as H. rewrite D in H. exact H.
Qed.

(** Executable iteration of the same normalized symbol derivative used by
    the general command-line state explorer.  Its states have the complete
    pair residual semantics of Eq. (23), independently of exploration order. *)
Fixpoint rewpla_normalized_word_step {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (w : word A) (r : rewpla A) : rewpla A :=
  match w with
  | [] => r
  | a :: w' => rewpla_normalized_word_step eqb atom_code w'
      (rewpla_normalized_symbol_step eqb atom_code a r)
  end.

Theorem rewpla_normalized_word_step_correct_M {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    w (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (rewpla_normalized_word_step eqb atom_code w r))
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
        apply rewpla_normalized_symbol_step_correct_M; exact eqb_spec.
      * apply lang_equiv_sym, pair_language_word_quotient_cons.
Qed.

(** Eq. (45): every state reached by the generic derivative interpreter
    recognizes exactly the projected language of its consumed prefix. *)
Theorem rewpla_normalized_word_step_accept_correct {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) w :
  rewpla_nullable (rewpla_normalized_word_step eqb atom_code w r) = true
    <-> rewpla_language eqb r w.
Proof.
  rewrite rewpla_nullable_correct by exact eqb_spec.
  rewrite <- project_empty_iff_identity.
  unfold rewpla_language, project_language.
  eapply iff_trans with (B :=
    project_language
      (pair_language_word_quotient eqb w (rewpla_denote eqb r)) []).
  - split; intros [p [Hp Hproj]]; exists p; split; try exact Hproj.
    + apply (proj1 (rewpla_normalized_word_step_correct_M
        eqb atom_code eqb_spec w r p)); exact Hp.
    + apply (proj2 (rewpla_normalized_word_step_correct_M
        eqb atom_code eqb_spec w r p)); exact Hp.
  - rewrite project_word_quotient by exact eqb_spec.
    unfold word_language_quotient.
    now rewrite app_nil_r.
Qed.

(** Paper Eq. (44)--(45) as an abstract semantic quotient machine.  Its
    transition acts on full pair languages; [lang_equiv] supplies the
    equivalence classes without assuming a decision procedure for them.
    This verifies transition independence and acceptance for all words. *)
Definition rewpla_semantic_step {A : Type} (eqb : A -> A -> bool)
    (a : A) (R : constraint_language A) : constraint_language A :=
  pair_language_symbol_quotient eqb a R.

Fixpoint rewpla_semantic_run {A : Type} (eqb : A -> A -> bool)
    (w : word A) (R : constraint_language A) : constraint_language A :=
  match w with
  | [] => R
  | a :: w' => rewpla_semantic_run eqb w'
      (rewpla_semantic_step eqb a R)
  end.

Lemma rewpla_semantic_step_congruent {A : Type}
    (eqb : A -> A -> bool) a (R S : constraint_language A) :
  lang_equiv R S ->
  lang_equiv (rewpla_semantic_step eqb a R)
    (rewpla_semantic_step eqb a S).
Proof.
  intros H p. unfold rewpla_semantic_step,
    pair_language_symbol_quotient. split;
    intros [q [Hq Hstep]]; exists q; split; try exact Hstep.
  - apply (proj1 (H q)); exact Hq.
  - apply (proj2 (H q)); exact Hq.
Qed.

Lemma rewpla_semantic_final_congruent {A : Type}
    (R S : constraint_language A) :
  lang_equiv R S -> (R ([], []) <-> S ([], [])).
Proof. intro H. apply H. Qed.

Theorem rewpla_semantic_run_correct {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    w (R : constraint_language A) :
  lang_equiv (rewpla_semantic_run eqb w R)
    (pair_language_word_quotient eqb w R).
Proof.
  revert R. induction w as [|a w IH]; intro R; simpl.
  - intro q. unfold pair_language_word_quotient. split.
    + intro Hq. exists q. now split.
    + intros [p [Hp Hstep]]. inversion Hstep; subst p. exact Hp.
  - eapply lang_equiv_trans.
    + apply IH.
    + apply lang_equiv_sym, pair_language_word_quotient_cons.
Qed.

Theorem rewpla_semantic_run_accept_correct {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) w :
  rewpla_semantic_run eqb w (rewpla_denote eqb r) ([], [])
    <-> rewpla_language eqb r w.
Proof.
  eapply iff_trans with (B :=
    rewpla_denote eqb (word_derivative eqb w r) ([], [])).
  - pose proof (rewpla_semantic_run_correct eqb eqb_spec w
      (rewpla_denote eqb r) ([], [])) as Hrun.
    pose proof (word_derivative_correct eqb eqb_spec w r ([], []))
      as Hword.
    tauto.
  - rewrite <- rewpla_nullable_correct by exact eqb_spec.
    apply rewpla_acceptb_correct; exact eqb_spec.
Qed.

(** Paper p.12: syntactic sufficient condition for a constraint expression.
    Its semantic soundness follows immediately for the generators, which are
    either lookaheads or inherited lookahead generators. *)
Fixpoint constraint_expressionb {A} (r : rewpla A) : bool :=
  match r with
  | WZero | WEps | WLookahead _ => true
  | WPlus r s | WConcat r s =>
      constraint_expressionb r && constraint_expressionb s
  | WStar r => constraint_expressionb r
  | WAtom _ => false
  end.

Definition empty_main_language {A} (R : constraint_language A) : Prop :=
  forall p, R p -> constraint_main p = [].

Lemma empty_main_concat {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (R S : constraint_language A) :
  empty_main_language R -> empty_main_language S ->
  empty_main_language (lang_concat eqb R S).
Proof.
  intros HR HS [u v] [p [q [Hp [Hq Hout]]]].
  destruct p as [x y], q as [x' y'].
  specialize (HR (x, y) Hp). specialize (HS (x', y') Hq).
  simpl in HR, HS. subst x x'.
  apply constraint_concat_result_shape in Hout as [t Hout].
  inversion Hout. reflexivity.
Qed.

Lemma empty_main_power {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (R : constraint_language A) n :
  empty_main_language R -> empty_main_language (lang_power eqb R n).
Proof.
  intro HR. induction n; simpl.
  - intros [u v] H. inversion H. reflexivity.
  - apply empty_main_concat; assumption.
Qed.

Lemma empty_main_star {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (R : constraint_language A) :
  empty_main_language R -> empty_main_language (lang_star eqb R).
Proof.
  intros HR p [n Hn]. eapply empty_main_power; eauto.
Qed.

(** Paper Eq. (35), p.12, red lines 553--556: the core pair calculation.
    Compare an ordinary pair concat with a concat whose right operand has
    already been projected to an empty-main constraint. *)
Lemma constraint_concat_lookahead_lift {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (v u z t : word A) :
  constraint_concat eqb ([], v) (u, z) = Some (u, t) <->
  constraint_concat eqb ([], v) ([], u ++ z) = Some ([], u ++ t).
Proof.
  split; intro H.
  - apply (proj2 (constraint_concat_characterization
      eqb eqb_spec [] v [] (u ++ z) (u ++ t))).
    pose proof (constraint_concat_least_residual
      eqb eqb_spec [] v u z H) as [[Hv Hz] Hleast].
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
      eqb eqb_spec [] v u z t)).
    pose proof (constraint_concat_least_residual
      eqb eqb_spec [] v [] (u ++ z) H)
      as [[Hv Huz] Hleast].
    unfold least_residual, residual_requirements in *.
    split.
    + split; [now simpl in Hv|].
      now apply (proj1 (word_prefix_app_left_iff u z t)).
    + intros s [Hvs Hz].
      apply (proj1 (word_prefix_app_left_iff u t s)).
      apply Hleast. split; [exact Hvs|].
      apply word_prefix_app_left. exact Hz.
Qed.

(** Paper p.12, lines 545--548: a constraint expression contributes no
    nonempty-main pair.  The syntactic check is sufficient, not complete. *)
Theorem constraint_expression_sound {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  constraint_expressionb r = true ->
  empty_main_language (rewpla_denote eqb r).
Proof.
  induction r; simpl; intro H; try discriminate.
  - intros p Hp. contradiction.
  - intros [u v] Hp. inversion Hp. reflexivity.
  - apply andb_true_iff in H as [Hr Hs].
    intros p [Hp|Hp]; [apply IHr1|apply IHr2]; assumption.
  - apply andb_true_iff in H as [Hr Hs].
    eapply empty_main_concat; [exact eqb_spec|apply IHr1|apply IHr2];
      assumption.
  - eapply empty_main_star; [exact eqb_spec|apply IHr]; exact H.
  - intros p [q [_ ->]]. reflexivity.
Qed.

(** First equation of paper Eq. (35): [LA(c)] and [c] have the same
    complete pair semantics when [c] is a constraint expression. *)
Theorem rewpla_lookahead_constraint {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (c : rewpla A) :
  empty_main_language (rewpla_denote eqb c) ->
  lang_equiv (rewpla_denote eqb (WLookahead c))
    (rewpla_denote eqb c).
Proof.
  intros Hc [u v]. simpl. unfold positive_lookahead.
  split.
  - intros [[x y] [Hq Hout]].
    pose proof (Hc (x, y) Hq) as Hx.
    simpl in Hx. subst x.
    unfold constraint_projection in Hout. simpl in Hout.
    inversion Hout; subst u v. exact Hq.
  - intro Hpair.
    pose proof (Hc (u, v) Hpair) as Hu.
    simpl in Hu. subst u.
    exists ([], v). split; [exact Hpair|reflexivity].
Qed.

(** Second equation of paper Eq. (35), p.12, red lines 549--556.
    The nested pair-concat calculation is discharged by the constructive
    least-residual correspondence [constraint_concat_lookahead_lift]. *)
Theorem rewpla_lookahead_constraint_concat {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (c p : rewpla A) :
  empty_main_language (rewpla_denote eqb c) ->
  lang_equiv
    (rewpla_denote eqb (WLookahead (WConcat c p)))
    (rewpla_denote eqb (WConcat c (WLookahead p))).
Proof.
  intros Hc [u v]. simpl. unfold positive_lookahead, lang_concat.
  split.
  - intros [[x t] [[cp [qp [Hcp [Hqp Hout]]]] Hproj]].
    destruct cp as [xc vc], qp as [xq z].
    pose proof (Hc (xc, vc) Hcp) as Hxc.
    simpl in Hxc. subst xc.
    pose proof (constraint_concat_result_shape
      eqb [] vc xq z Hout) as [t' Hshape].
    inversion Hshape; subst x t'.
    unfold constraint_projection in Hproj. simpl in Hproj.
    inversion Hproj; subst u v.
    exists ([], vc), ([], xq ++ z).
    split; [exact Hcp|]. split.
    + exists (xq, z). split; [exact Hqp|reflexivity].
    + apply (proj1 (constraint_concat_lookahead_lift
        eqb eqb_spec vc xq z t)). exact Hout.
  - intros [cp [lp [Hcp [Hlp Hout]]]].
    destruct cp as [xc vc], lp as [xl vl].
    pose proof (Hc (xc, vc) Hcp) as Hxc.
    simpl in Hxc. subst xc.
    destruct Hlp as [[x z] [Hqp Hlp]].
    unfold constraint_projection in Hlp. simpl in Hlp.
    inversion Hlp; subst xl vl.
    pose proof (constraint_concat_result_shape
      eqb [] vc [] (x ++ z) Hout) as [actual Hshape].
    inversion Hshape; subst u actual.
    assert (Hcompat : prefix_compatible vc (x ++ z)).
    { apply (proj1 (constraint_concat_defined_iff_compatible
        eqb eqb_spec [] vc [] (x ++ z))).
      exists v. exact Hout. }
    destruct (@constraint_concat_defined_from_compatible
      A eqb eqb_spec [] vc x z Hcompat) as [t Hpair].
    pose proof ((proj1 (constraint_concat_lookahead_lift
      eqb eqb_spec vc x z t)) Hpair) as Hlift.
    pose proof (eq_trans (eq_sym Hout) Hlift) as Hsame.
    inversion Hsame; subst v.
    exists (x, t). split.
    + exists ([], vc), (x, z). split; [exact Hcp|].
      split; [exact Hqp|exact Hpair].
    + reflexivity.
Qed.

(** A constructive use of all three equations in paper Eq. (35).  The
    derivative core can introduce assertions over unions and assertions
    whose first factor is already a constraint.  Pulling these into sums and
    leading constraint factors prevents repeated derivatives from nesting
    the same assertion at increasing depth. *)
Fixpoint rewpla_lookahead_lift {A : Type}
    (eqb : A -> A -> bool) (r : rewpla A) : rewpla A :=
  match r with
  | WPlus p q => smart_plus
      (rewpla_lookahead_lift eqb p) (rewpla_lookahead_lift eqb q)
  | WConcat c p =>
      if constraint_expressionb c then
        smart_concat c (rewpla_lookahead_lift eqb p)
      else smart_lookahead r
  | _ => smart_lookahead r
  end.

Theorem rewpla_lookahead_lift_correct_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (rewpla_lookahead_lift eqb r))
    (rewpla_denote eqb (WLookahead r)).
Proof.
  induction r as [| |a|p IHp q IHq|c IHc p IHp|p IHp|p IHp];
    simpl.
  - apply (smart_lookahead_correct_M eqb (@WZero A)).
  - apply (smart_lookahead_correct_M eqb (@WEps A)).
  - apply (smart_lookahead_correct_M eqb (WAtom a)).
  - eapply lang_equiv_trans.
    + apply smart_plus_correct_M.
    + eapply lang_equiv_trans.
      * apply lang_union_compat; [exact IHp|exact IHq].
      * apply lang_equiv_sym, rewpla_lookahead_union.
  - destruct (constraint_expressionb c) eqn:Hc.
    + eapply lang_equiv_trans.
      * apply smart_concat_correct_M; exact eqb_spec.
      * eapply lang_equiv_trans.
        -- apply lang_concat_compat; [apply lang_equiv_refl|exact IHp].
        -- apply lang_equiv_sym, rewpla_lookahead_constraint_concat;
             [exact eqb_spec|].
           apply constraint_expression_sound; [exact eqb_spec|exact Hc].
    + apply (smart_lookahead_correct_M eqb (WConcat c p)).
  - apply (smart_lookahead_correct_M eqb (WStar p)).
  - apply (smart_lookahead_correct_M eqb (WLookahead p)).
Qed.

Fixpoint rewpla_paper_normalize {A : Type}
    (eqb : A -> A -> bool) (r : rewpla A) : rewpla A :=
  match r with
  | WZero => WZero
  | WEps => WEps
  | WAtom a => WAtom a
  | WPlus p q => smart_plus
      (rewpla_paper_normalize eqb p) (rewpla_paper_normalize eqb q)
  | WConcat p q => smart_concat
      (rewpla_paper_normalize eqb p) (rewpla_paper_normalize eqb q)
  | WStar p => smart_star (rewpla_paper_normalize eqb p)
  | WLookahead p => rewpla_lookahead_lift eqb
      (rewpla_paper_normalize eqb p)
  end.

Theorem rewpla_paper_normalize_correct_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (rewpla_paper_normalize eqb r))
    (rewpla_denote eqb r).
Proof.
  induction r; simpl; try apply lang_equiv_refl.
  - eapply lang_equiv_trans.
    + apply smart_plus_correct_M.
    + apply lang_union_compat; assumption.
  - eapply lang_equiv_trans.
    + apply smart_concat_correct_M; exact eqb_spec.
    + apply lang_concat_compat; assumption.
  - eapply lang_equiv_trans.
    + apply smart_star_correct_M; exact eqb_spec.
    + apply lang_star_compat; assumption.
  - eapply lang_equiv_trans.
    + apply rewpla_lookahead_lift_correct_M; exact eqb_spec.
    + apply positive_lookahead_compat; assumption.
Qed.

Definition rewpla_paper_symbol_step {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (a : A) (r : rewpla A) : rewpla A :=
  rewpla_aci_normalize eqb atom_code
    (rewpla_paper_normalize eqb
      (derivative_merge (symbol_derivative_core eqb a r))).

Theorem rewpla_paper_symbol_step_correct_M {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r : rewpla A) :
  lang_equiv (rewpla_denote eqb
      (rewpla_paper_symbol_step eqb atom_code a r))
    (pair_language_symbol_quotient eqb a (rewpla_denote eqb r)).
Proof.
  unfold rewpla_paper_symbol_step. eapply lang_equiv_trans.
  - apply rewpla_aci_normalize_correct; exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply rewpla_paper_normalize_correct_M; exact eqb_spec.
    + apply symbol_derivative_core_merge_correct; exact eqb_spec.
Qed.

Fixpoint rewpla_paper_word_step {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (w : word A) (r : rewpla A) : rewpla A :=
  match w with
  | [] => r
  | a :: w' => rewpla_paper_word_step eqb atom_code w'
      (rewpla_paper_symbol_step eqb atom_code a r)
  end.

Theorem rewpla_paper_word_step_correct_M {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    w (r : rewpla A) :
  lang_equiv (rewpla_denote eqb
      (rewpla_paper_word_step eqb atom_code w r))
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
        apply rewpla_paper_symbol_step_correct_M; exact eqb_spec.
      * apply lang_equiv_sym, pair_language_word_quotient_cons.
Qed.

Theorem rewpla_paper_word_step_accept_correct {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) w :
  rewpla_nullable (rewpla_paper_word_step eqb atom_code w r) = true
    <-> rewpla_language eqb r w.
Proof.
  rewrite rewpla_nullable_correct by exact eqb_spec.
  pose proof (rewpla_paper_word_step_correct_M eqb atom_code eqb_spec
    w r ([], [])) as Hword.
  pose proof (rewpla_semantic_run_correct eqb eqb_spec w
    (rewpla_denote eqb r) ([], [])) as Hrun.
  pose proof (rewpla_semantic_run_accept_correct eqb eqb_spec r w)
    as Haccept.
  tauto.
Qed.

(** Paper Eq. (34), p.12, red lines 545--548: empty-main constraints
    concatenate by taking the *longer compatible* required context.  This
    product is commutative; its result is always one of its two inputs. *)
Lemma empty_pair_concat_comm {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (v v' t : word A) :
  constraint_concat eqb ([], v) ([], v') = Some ([], t) <->
  constraint_concat eqb ([], v') ([], v) = Some ([], t).
Proof.
  split; intro H.
  - apply (proj2 (constraint_concat_characterization
      eqb eqb_spec [] v' [] v t)).
    pose proof (constraint_concat_least_residual
      eqb eqb_spec [] v [] v' H) as [[Hv Hv'] Hleast].
    unfold least_residual, residual_requirements in *.
    split.
    + simpl. now split.
    + intros s [H1 H2]. apply Hleast. simpl. now split.
  - apply (proj2 (constraint_concat_characterization
      eqb eqb_spec [] v [] v' t)).
    pose proof (constraint_concat_least_residual
      eqb eqb_spec [] v' [] v H) as [[Hv' Hv] Hleast].
    unfold least_residual, residual_requirements in *.
    split.
    + simpl. now split.
    + intros s [H1 H2]. apply Hleast. simpl. now split.
Qed.

Lemma empty_pair_concat_is_operand {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (v v' t : word A) :
  constraint_concat eqb ([], v) ([], v') = Some ([], t) ->
  t = v \/ t = v'.
Proof.
  intro H.
  pose proof (constraint_concat_least_residual
    eqb eqb_spec [] v [] v' H) as [[Hv Hv'] Hleast].
  simpl in Hv.
  destruct (@word_prefix_common_upper A v v' t Hv Hv')
    as [Hvv'|Hv'v].
  - right. apply word_prefix_antisym.
    + apply Hleast. split; [exact Hvv'|apply word_prefix_refl].
    + exact Hv'.
  - left. apply word_prefix_antisym.
    + apply Hleast. split; [apply word_prefix_refl|exact Hv'v].
    + exact Hv.
Qed.

Lemma empty_pair_concat_idempotent {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (v : word A) :
  constraint_concat eqb ([], v) ([], v) = Some ([], v).
Proof.
  apply (proj2 (constraint_concat_characterization
    eqb eqb_spec [] v [] v v)).
  unfold least_residual, residual_requirements. simpl.
  split; [split; apply word_prefix_refl|].
  intros s [H _]. exact H.
Qed.

Theorem rewpla_constraint_concat_comm {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (c d : rewpla A) :
  empty_main_language (rewpla_denote eqb c) ->
  empty_main_language (rewpla_denote eqb d) ->
  lang_equiv (rewpla_denote eqb (WConcat c d))
    (rewpla_denote eqb (WConcat d c)).
Proof.
  intros Hc Hd out. simpl. unfold lang_concat.
  split; intros [p [q [Hp [Hq Hout]]]].
  - destruct p as [u v], q as [u' v'].
    pose proof (Hc (u, v) Hp) as Hu.
    pose proof (Hd (u', v') Hq) as Hu'.
    simpl in Hu, Hu'. subst u u'.
    exists ([], v'), ([], v). repeat split; try assumption.
    destruct out as [uo vo].
    pose proof (constraint_concat_result_shape eqb [] v [] v' Hout)
      as [t Hshape]. inversion Hshape; subst uo vo.
    now apply (proj1 (empty_pair_concat_comm eqb eqb_spec v v' t)).
  - destruct p as [u v], q as [u' v'].
    pose proof (Hd (u, v) Hp) as Hu.
    pose proof (Hc (u', v') Hq) as Hu'.
    simpl in Hu, Hu'. subst u u'.
    exists ([], v'), ([], v). repeat split; try assumption.
    destruct out as [uo vo].
    pose proof (constraint_concat_result_shape eqb [] v [] v' Hout)
      as [t Hshape]. inversion Hshape; subst uo vo.
    now apply (proj1 (empty_pair_concat_comm eqb eqb_spec v v' t)).
Qed.

Theorem rewpla_constraint_concat_idempotent {A} eqb
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (c : rewpla A) :
  empty_main_language (rewpla_denote eqb c) ->
  lang_equiv (rewpla_denote eqb (WConcat c c))
    (rewpla_denote eqb c).
Proof.
  intros Hc out. simpl. unfold lang_concat. split.
  - intros [p [q [Hp [Hq Hout]]]].
    destruct p as [u v], q as [u' v'].
    pose proof (Hc (u, v) Hp) as Hu.
    pose proof (Hc (u', v') Hq) as Hu'.
    simpl in Hu, Hu'. subst u u'.
    destruct out as [uo vo].
    pose proof (constraint_concat_result_shape eqb [] v [] v' Hout)
      as [t Hshape]. inversion Hshape; subst uo vo.
    destruct (empty_pair_concat_is_operand eqb eqb_spec v v' Hout)
      as [Heq|Heq]; subst t; assumption.
  - intro Hout.
    destruct out as [u v].
    pose proof (Hc (u, v) Hout) as Hu.
    simpl in Hu. subst u.
    exists ([], v), ([], v). repeat split; try exact Hout.
    apply empty_pair_concat_idempotent. exact eqb_spec.
Qed.

Lemma constraint_generator_is_constraint {A} (r c : rewpla A) :
  In c (constraint_generators_raw r) -> constraint_expressionb c = true.
Proof.
  revert c. induction r; intros c H; simpl in H; try contradiction.
  - apply in_app_iff in H as [H|H]; auto.
  - apply in_app_iff in H as [H|H]; auto.
  - auto.
  - apply in_app_iff in H as [H|H]; auto.
    apply in_map_iff in H as [x [Hx _]]. subst c. reflexivity.
Qed.

Theorem constraint_generators_empty_main {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) c :
  In c (constraint_generators eqb r) ->
  empty_main_language (rewpla_denote eqb c).
Proof.
  unfold constraint_generators. intro Hc.
  apply (proj1 (nodupb_in_iff (rewpla_eqb eqb)
    (rewpla_eqb_spec eqb eqb_spec) _ _)) in Hc.
  apply constraint_expression_sound; [exact eqb_spec|].
  now apply (constraint_generator_is_constraint r c).
Qed.

Theorem union_generator_inclusions {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r s : rewpla A) :
  (forall t, In t (continuation_generators eqb r) ->
    In t (continuation_generators eqb (WPlus r s))) /\
  (forall t, In t (continuation_generators eqb s) ->
    In t (continuation_generators eqb (WPlus r s))) /\
  (forall c, In c (constraint_generators eqb r) ->
    In c (constraint_generators eqb (WPlus r s))) /\
  (forall c, In c (constraint_generators eqb s) ->
    In c (constraint_generators eqb (WPlus r s))).
Proof.
  repeat split; intros t Ht;
    unfold continuation_generators, constraint_generators in *;
    apply (proj2 (nodupb_in_iff (rewpla_eqb eqb)
      (rewpla_eqb_spec eqb eqb_spec) _ _)); simpl;
    apply in_app_iff;
    (left; apply (proj1 (nodupb_in_iff (rewpla_eqb eqb)
        (rewpla_eqb_spec eqb eqb_spec) _ _)); exact Ht) ||
    (right; apply (proj1 (nodupb_in_iff (rewpla_eqb eqb)
        (rewpla_eqb_spec eqb eqb_spec) _ _)); exact Ht).
Qed.

Theorem concat_generator_inclusions {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r s : rewpla A) :
  (forall t, In t (continuation_generators eqb r) ->
    In (WConcat t s) (continuation_generators eqb (WConcat r s))) /\
  (forall t, In t (continuation_generators eqb s) ->
    In t (continuation_generators eqb (WConcat r s))) /\
  (forall c, In c (constraint_generators eqb r) ->
    In c (constraint_generators eqb (WConcat r s))) /\
  (forall c, In c (constraint_generators eqb s) ->
    In c (constraint_generators eqb (WConcat r s))).
Proof.
  assert (Hexpr : forall x y : rewpla A,
      rewpla_eqb eqb x y = true <-> x = y).
  { apply rewpla_eqb_spec. exact eqb_spec. }
  repeat split; intros t Ht;
    unfold continuation_generators, constraint_generators in *;
    apply (proj2 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
    simpl; apply in_app_iff.
  - left. apply in_map_iff. exists t. split; [reflexivity|].
    apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
      exact Ht.
  - right. apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
      exact Ht.
  - left. apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
      exact Ht.
  - right. apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
      exact Ht.
Qed.

Theorem star_generator_inclusions {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  (forall t, In t (continuation_generators eqb r) ->
    In (WConcat t (WStar r))
      (continuation_generators eqb (WStar r))) /\
  (forall c, In c (constraint_generators eqb r) ->
    In c (constraint_generators eqb (WStar r))).
Proof.
  assert (Hexpr : forall x y : rewpla A,
      rewpla_eqb eqb x y = true <-> x = y).
  { apply rewpla_eqb_spec. exact eqb_spec. }
  split; intros t Ht;
    unfold continuation_generators, constraint_generators in *;
    apply (proj2 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
    simpl.
  - apply in_map_iff. exists t. split; [reflexivity|].
    apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
      exact Ht.
  - apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
      exact Ht.
Qed.

Theorem lookahead_generator_inclusions {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  (forall c, In c (constraint_generators eqb r) ->
    In c (constraint_generators eqb (WLookahead r))) /\
  (forall t, In t (continuation_generators eqb r) ->
    In (WLookahead t) (constraint_generators eqb (WLookahead r))).
Proof.
  assert (Hexpr : forall x y : rewpla A,
      rewpla_eqb eqb x y = true <-> x = y).
  { apply rewpla_eqb_spec. exact eqb_spec. }
  split; intros t Ht;
    unfold continuation_generators, constraint_generators in *;
    apply (proj2 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
    simpl; apply in_app_iff.
  - left. apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
      exact Ht.
  - right. apply in_map_iff. exists t. split; [reflexivity|].
    apply (proj1 (nodupb_in_iff (rewpla_eqb eqb) Hexpr _ _));
      exact Ht.
Qed.

(** Paper Eq. (39)--(40), p.13: finite term and normal-form universes.
    The list order supplies the paper's fixed ordering and parenthesization. *)
Fixpoint subsets {X} (xs : list X) : list (list X) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
      let ps := subsets xs' in ps ++ map (cons x) ps
  end.

Fixpoint constraint_product {A} (xs : list (rewpla A)) : rewpla A :=
  match xs with
  | [] => WEps
  | x :: xs' => smart_concat x (constraint_product xs')
  end.

Fixpoint union_expression {A} (xs : list (rewpla A)) : rewpla A :=
  match xs with
  | [] => WZero
  | x :: xs' => smart_plus x (union_expression xs')
  end.

Definition constraint_terms {A} (cs : list (rewpla A)) : list (rewpla A) :=
  map constraint_product (subsets cs).

Definition main_terms {A} (as_ cs : list (rewpla A)) : list (rewpla A) :=
  flat_map
    (fun ss => map (fun t => smart_concat (constraint_product ss) t) as_)
    (subsets cs).

Definition term_universe {A} (as_ cs : list (rewpla A)) : list (rewpla A) :=
  constraint_terms cs ++ main_terms as_ cs.

Definition normal_forms {A} (as_ cs : list (rewpla A)) : list (rewpla A) :=
  map union_expression (subsets (term_universe as_ cs)).

(** The two component families of paper Lemma 4.  Their union-level
    representatives are deliberately separate from complete residuals. *)
Definition constraint_normal_forms {A} (cs : list (rewpla A))
    : list (rewpla A) :=
  map union_expression (subsets (constraint_terms cs)).

Definition main_normal_forms {A} (as_ cs : list (rewpla A))
    : list (rewpla A) :=
  map union_expression (subsets (main_terms as_ cs)).

Lemma subsets_length {X} (xs : list X) : length (subsets xs) = 2 ^ length xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl. rewrite length_app, length_map, IH. simpl. lia.
Qed.

Lemma flat_map_fixed_length {X Y} (f : X -> list Y) xs n :
  (forall x, In x xs -> length (f x) = n) ->
  length (flat_map f xs) = length xs * n.
Proof.
  intro Hf. induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite length_app, Hf by now left. rewrite IH.
  - lia.
  - intros y Hy. apply Hf. now right.
Qed.

Lemma constraint_terms_length {A} (cs : list (rewpla A)) :
  length (constraint_terms cs) = 2 ^ length cs.
Proof. unfold constraint_terms. now rewrite length_map, subsets_length. Qed.

Lemma main_terms_length {A} (as_ cs : list (rewpla A)) :
  length (main_terms as_ cs) = (2 ^ length cs) * length as_.
Proof.
  unfold main_terms. rewrite flat_map_fixed_length with (n:=length as_).
  - now rewrite subsets_length.
  - intros ss _. now rewrite length_map.
Qed.

Theorem term_universe_length {A} (as_ cs : list (rewpla A)) :
  length (term_universe as_ cs) = (length as_ + 1) * 2 ^ length cs.
Proof.
  unfold term_universe. rewrite length_app, constraint_terms_length,
    main_terms_length. nia.
Qed.

Theorem normal_forms_length {A} (as_ cs : list (rewpla A)) :
  length (normal_forms as_ cs) =
    2 ^ ((length as_ + 1) * 2 ^ length cs).
Proof.
  unfold normal_forms. rewrite length_map, subsets_length,
  term_universe_length. reflexivity.
Qed.

Lemma empty_subset_member {X : Type} (xs : list X) :
  In [] (subsets xs).
Proof.
  induction xs as [|x xs IH]; simpl; [now left|].
  apply in_app_iff. now left.
Qed.

Lemma singleton_subset_member {X : Type} (xs : list X) x :
  In x xs -> In [x] (subsets xs).
Proof.
  induction xs as [|y ys IH]; intros Hx; [contradiction|].
  simpl. destruct Hx as [<-|Hx].
  - apply in_app_iff. right. apply in_map_iff.
    exists []. split; [reflexivity|apply empty_subset_member].
  - apply in_app_iff. left. now apply IH.
Qed.

Lemma zero_in_main_normal_forms {A : Type}
    (as_ cs : list (rewpla A)) :
  In WZero (main_normal_forms as_ cs).
Proof.
  unfold main_normal_forms. apply in_map_iff.
  exists []. split; [reflexivity|apply empty_subset_member].
Qed.

Lemma zero_in_constraint_normal_forms {A : Type}
    (cs : list (rewpla A)) :
  In WZero (constraint_normal_forms cs).
Proof.
  unfold constraint_normal_forms. apply in_map_iff.
  exists []. split; [reflexivity|apply empty_subset_member].
Qed.

Lemma epsilon_in_main_normal_forms_if_generator {A : Type}
    (as_ cs : list (rewpla A)) :
  In WEps as_ -> In WEps (main_normal_forms as_ cs).
Proof.
  intro Heps.
  assert (Hterm : In WEps (main_terms as_ cs)).
  { unfold main_terms. apply in_flat_map. exists []. split.
    - apply empty_subset_member.
    - apply in_map_iff. exists WEps. split;
        [reflexivity|exact Heps]. }
  unfold main_normal_forms. apply in_map_iff.
  exists [WEps]. split; [reflexivity|].
  now apply singleton_subset_member.
Qed.

Definition symbol_derivative_represented {A : Type}
    (eqb : A -> A -> bool) (a : A) (r : rewpla A) : Prop :=
  (exists m, In m (main_normal_forms
        (continuation_generators eqb r) (constraint_generators eqb r)) /\
      lang_equiv (rewpla_denote eqb
        (fst (symbol_derivative_core eqb a r)))
        (rewpla_denote eqb m)) /\
  (exists c, In c (constraint_normal_forms
        (constraint_generators eqb r)) /\
      lang_equiv (rewpla_denote eqb
        (snd (symbol_derivative_core eqb a r)))
        (rewpla_denote eqb c)).

Theorem symbol_derivative_represented_zero {A : Type}
    (eqb : A -> A -> bool) a :
  symbol_derivative_represented eqb a WZero.
Proof.
  unfold symbol_derivative_represented. simpl.
  split.
  - exists WZero. split; [now left|apply lang_equiv_refl].
  - exists WZero. split; [now left|apply lang_equiv_refl].
Qed.

Theorem symbol_derivative_represented_epsilon {A : Type}
    (eqb : A -> A -> bool) a :
  symbol_derivative_represented eqb a WEps.
Proof.
  unfold symbol_derivative_represented. simpl.
  split.
  - exists WZero. split; [now left|apply lang_equiv_refl].
  - exists WZero. split; [now left|apply lang_equiv_refl].
Qed.

Theorem symbol_derivative_represented_atom {A : Type}
    (eqb : A -> A -> bool) a b :
  symbol_derivative_represented eqb a (WAtom b).
Proof.
  unfold symbol_derivative_represented. simpl.
  destruct (eqb a b) eqn:Hab; split.
  - exists WEps. split.
    + right. now left.
    + apply lang_equiv_refl.
  - exists WZero. split;
      [now left|apply lang_equiv_refl].
  - exists WZero. split;
      [now left|apply lang_equiv_refl].
  - exists WZero. split;
      [now left|apply lang_equiv_refl].
Qed.

(** Any selected subset of a finite term universe has the paper's chosen
    union representative.  This is the outer, second powerset layer used in
    Lemmas 4--5, independently of the inner constraint-product layer. *)
Lemma filter_is_subset {X : Type} (p : X -> bool) xs :
  In (filter p xs) (subsets xs).
Proof.
  induction xs as [|x xs IH]; simpl; [now left|].
  destruct (p x) eqn:Hx; simpl.
  - apply in_app_iff. right. apply in_map_iff.
    exists (filter p xs). split; [reflexivity|exact IH].
  - apply in_app_iff. now left.
Qed.

Lemma union_expression_membership {A : Type} (eqb : A -> A -> bool)
    (xs : list (rewpla A)) p :
  rewpla_denote eqb (union_expression xs) p <->
    exists t, In t xs /\ rewpla_denote eqb t p.
Proof.
  induction xs as [|x xs IH]; simpl.
  - split; [intro H; contradiction|intros [t [[] _]]].
  - rewrite (smart_plus_correct_M eqb x (union_expression xs) p).
    simpl. unfold lang_union. rewrite IH. split.
    + intros [Hx|[t [Ht Hp]]].
      * exists x. now split; [left|].
      * exists t. split; [now right|exact Hp].
    + intros [t [[<-|Ht] Hp]]; [now left|].
      right. exists t. now split.
Qed.

Theorem normal_forms_cover_finite_union {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as_ cs ys : list (rewpla A)) :
  (forall t, In t ys -> In t (term_universe as_ cs)) ->
  exists n, In n (normal_forms as_ cs) /\
    lang_equiv (rewpla_denote eqb n)
      (rewpla_denote eqb (union_expression ys)).
Proof.
  intro Hys.
  let selected := constr:(filter
    (fun t => existsb (rewpla_eqb eqb t) ys)
    (term_universe as_ cs)) in
  exists (union_expression selected). split.
  - unfold normal_forms. apply in_map. apply filter_is_subset.
  - intro p. repeat rewrite union_expression_membership.
    split; intros [t [Ht Hp]].
    + apply filter_In in Ht as [_ Htest].
      apply existsb_exists in Htest as [y [Hy Hty]].
      apply (proj1 (rewpla_eqb_spec eqb eqb_spec _ _)) in Hty.
      subst y. exists t. now split.
    + exists t. split; [|exact Hp].
      apply filter_In. split; [apply Hys; exact Ht|].
      apply existsb_exists. exists t. split;
        [exact Ht|apply (proj2 (rewpla_eqb_spec eqb eqb_spec _ _));
          reflexivity].
Qed.

Theorem chosen_union_forms_cover_finite_union {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (terms ys : list (rewpla A)) :
  (forall t, In t ys -> In t terms) ->
  exists n, In n (map union_expression (subsets terms)) /\
    lang_equiv (rewpla_denote eqb n)
      (rewpla_denote eqb (union_expression ys)).
Proof.
  intro Hys.
  let selected := constr:(filter
    (fun t => existsb (rewpla_eqb eqb t) ys) terms) in
  exists (union_expression selected). split.
  - apply in_map. apply filter_is_subset.
  - intro p. repeat rewrite union_expression_membership.
    split; intros [t [Ht Hp]].
    + apply filter_In in Ht as [_ Htest].
      apply existsb_exists in Htest as [y [Hy Hty]].
      apply (proj1 (rewpla_eqb_spec eqb eqb_spec _ _)) in Hty.
      subst y. exists t. now split.
    + exists t. split; [|exact Hp].
      apply filter_In. split; [apply Hys; exact Ht|].
      apply existsb_exists. exists t. split;
        [exact Ht|apply (proj2 (rewpla_eqb_spec eqb eqb_spec _ _));
          reflexivity].
Qed.

(** The inner powerset layer contains only genuine zero-width constraints.
    This invariant justifies the commutative and idempotent products used in
    the representation and closure arguments of paper Lemmas 4--5. *)
Lemma subset_members_from_source {X : Type} (xs ys : list X) :
  In ys (subsets xs) -> forall x, In x ys -> In x xs.
Proof.
  revert ys. induction xs as [|t xs IH]; intros ys Hys x Hx; simpl in Hys.
  - destruct Hys as [Hnil|[]]. subst ys. simpl in Hx. contradiction.
  - apply in_app_iff in Hys as [Hys|Hys].
    + right. eapply IH; eauto.
    + apply in_map_iff in Hys as [zs [<- Hzs]].
      destruct Hx as [<-|Hx]; [now left|].
      right. eapply IH; eauto.
Qed.

Lemma constraint_product_empty_main {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (xs : list (rewpla A)) :
  (forall x, In x xs -> empty_main_language (rewpla_denote eqb x)) ->
  empty_main_language (rewpla_denote eqb (constraint_product xs)).
Proof.
  intro Hxs. induction xs as [|x xs IH]; simpl.
  - intros [u v] Hp. inversion Hp. reflexivity.
  - assert (Hx : empty_main_language (rewpla_denote eqb x)).
    { apply Hxs. now left. }
    assert (Htail : empty_main_language
        (rewpla_denote eqb (constraint_product xs))).
    { apply IH. intros y Hy. apply Hxs. now right. }
    intros p Hp. apply (proj1 (smart_concat_correct_M eqb eqb_spec
      x (constraint_product xs) p)) in Hp.
    exact (empty_main_concat eqb_spec Hx Htail Hp).
Qed.

Theorem constraint_terms_empty_main {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r t : rewpla A) :
  In t (constraint_terms (constraint_generators eqb r)) ->
  empty_main_language (rewpla_denote eqb t).
Proof.
  unfold constraint_terms. intro Ht.
  apply in_map_iff in Ht as [ss [<- Hss]].
  apply constraint_product_empty_main; [exact eqb_spec|].
  intros c Hc.
  apply (subset_members_from_source _ _ Hss c) in Hc.
  unfold constraint_generators in Hc.
  apply (proj1 (nodupb_in_iff (rewpla_eqb eqb)
    (rewpla_eqb_spec eqb eqb_spec) _ _)) in Hc.
  apply constraint_expression_sound; [exact eqb_spec|].
  now apply (constraint_generator_is_constraint r c).
Qed.

(** The paper's fixed-order constraint product denotes the commutative,
    idempotent product of its selected generators.  The following algebra
    lets Lemma 5 replace an arbitrary derivative product by the subset of
    the original finite generator list with the same members. *)
Lemma constraint_product_head_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    x (xs : list (rewpla A)) :
  lang_equiv (rewpla_denote eqb (constraint_product (x :: xs)))
    (rewpla_denote eqb (WConcat x (constraint_product xs))).
Proof. simpl. apply smart_concat_correct_M; exact eqb_spec. Qed.

Lemma constraint_product_append_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (xs ys : list (rewpla A)) :
  lang_equiv (rewpla_denote eqb (constraint_product (xs ++ ys)))
    (rewpla_denote eqb (WConcat
      (constraint_product xs) (constraint_product ys))).
Proof.
  induction xs as [|x xs IH]; simpl.
  - apply lang_equiv_sym, rewpla_concat_one_left_M; exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply smart_concat_correct_M; exact eqb_spec.
    + eapply lang_equiv_trans.
      * apply lang_concat_compat; [apply lang_equiv_refl|exact IH].
      * eapply lang_equiv_trans.
        -- apply lang_equiv_sym, rewpla_concat_assoc_M; exact eqb_spec.
        -- apply lang_concat_compat.
           ++ apply lang_equiv_sym, constraint_product_head_M;
                exact eqb_spec.
           ++ apply lang_equiv_refl.
Qed.

Lemma constraint_product_adjacent_swap_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    x y (xs : list (rewpla A)) :
  empty_main_language (rewpla_denote eqb x) ->
  empty_main_language (rewpla_denote eqb y) ->
  lang_equiv
    (rewpla_denote eqb (constraint_product (x :: y :: xs)))
    (rewpla_denote eqb (constraint_product (y :: x :: xs))).
Proof.
  intros Hx Hy. eapply lang_equiv_trans.
  - apply constraint_product_head_M; exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply lang_concat_compat; [apply lang_equiv_refl|].
      apply constraint_product_head_M; exact eqb_spec.
    + eapply lang_equiv_trans.
      * apply lang_equiv_sym, rewpla_concat_assoc_M; exact eqb_spec.
      * eapply lang_equiv_trans.
        -- apply lang_concat_compat.
           ++ apply rewpla_constraint_concat_comm;
                [exact eqb_spec|exact Hx|exact Hy].
           ++ apply lang_equiv_refl.
        -- eapply lang_equiv_trans.
           ++ apply rewpla_concat_assoc_M; exact eqb_spec.
           ++ eapply lang_equiv_trans.
              ** apply lang_concat_compat; [apply lang_equiv_refl|].
                 apply lang_equiv_sym, constraint_product_head_M;
                   exact eqb_spec.
              ** apply lang_equiv_sym, constraint_product_head_M;
                   exact eqb_spec.
Qed.

Lemma constraint_product_duplicate_member_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    x (xs : list (rewpla A)) :
  empty_main_language (rewpla_denote eqb x) ->
  (forall y, In y xs -> empty_main_language (rewpla_denote eqb y)) ->
  In x xs ->
  lang_equiv (rewpla_denote eqb (constraint_product (x :: xs)))
    (rewpla_denote eqb (constraint_product xs)).
Proof.
  intros Hx. induction xs as [|y ys IH]; intros Hxs Hin;
    [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst y. eapply lang_equiv_trans.
    + apply constraint_product_head_M; exact eqb_spec.
    + eapply lang_equiv_trans.
      * apply lang_concat_compat; [apply lang_equiv_refl|].
        apply constraint_product_head_M; exact eqb_spec.
      * eapply lang_equiv_trans.
        -- apply lang_equiv_sym, rewpla_concat_assoc_M;
             exact eqb_spec.
        -- eapply lang_equiv_trans.
           ++ apply lang_concat_compat.
              ** apply rewpla_constraint_concat_idempotent;
                   [exact eqb_spec|exact Hx].
              ** apply lang_equiv_refl.
           ++ apply lang_equiv_sym, constraint_product_head_M;
                exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply constraint_product_adjacent_swap_M;
        [exact eqb_spec|exact Hx|apply Hxs; now left].
    + eapply lang_equiv_trans.
      * apply constraint_product_head_M; exact eqb_spec.
      * eapply lang_equiv_trans.
        -- apply lang_concat_compat; [apply lang_equiv_refl|].
           apply IH.
           ++ intros z Hz. apply Hxs. now right.
           ++ exact Hin.
        -- apply lang_equiv_sym, constraint_product_head_M;
             exact eqb_spec.
Qed.

Lemma constraint_product_subset_absorb_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (xs ys : list (rewpla A)) :
  (forall c, In c (xs ++ ys) ->
    empty_main_language (rewpla_denote eqb c)) ->
  (forall c, In c xs -> In c ys) ->
  lang_equiv (rewpla_denote eqb (constraint_product (xs ++ ys)))
    (rewpla_denote eqb (constraint_product ys)).
Proof.
  revert ys. induction xs as [|x xs IH]; intros ys Hall Hsubset;
    simpl; [apply lang_equiv_refl|].
  eapply lang_equiv_trans.
  - apply constraint_product_duplicate_member_M;
      [exact eqb_spec|apply Hall; now left| |].
    + intros c Hc. apply Hall. right. exact Hc.
    + apply in_app_iff. right. apply Hsubset. now left.
  - apply IH.
    + intros c Hc. apply Hall. right. exact Hc.
    + intros c Hc. apply Hsubset. now right.
Qed.

Theorem constraint_product_same_members_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (xs ys : list (rewpla A)) :
  (forall c, In c (xs ++ ys) ->
    empty_main_language (rewpla_denote eqb c)) ->
  (forall c, In c xs <-> In c ys) ->
  lang_equiv (rewpla_denote eqb (constraint_product xs))
    (rewpla_denote eqb (constraint_product ys)).
Proof.
  intros Hall Hmembers. eapply lang_equiv_trans.
  - apply lang_equiv_sym, constraint_product_subset_absorb_M.
    + exact eqb_spec.
    + intros c Hc. apply Hall.
      apply in_app_iff in Hc as [Hy|Hx].
      * apply in_app_iff. right. exact Hy.
      * apply in_app_iff. left. exact Hx.
    + intros c Hc. apply (proj2 (Hmembers c)); exact Hc.
  - eapply lang_equiv_trans.
    + eapply lang_equiv_trans.
      * apply constraint_product_append_M; exact eqb_spec.
      * eapply lang_equiv_trans.
        -- apply rewpla_constraint_concat_comm;
             [exact eqb_spec| |].
           ++ apply constraint_product_empty_main;
                [exact eqb_spec|].
              intros c Hc. apply Hall, in_app_iff. now right.
           ++ apply constraint_product_empty_main;
                [exact eqb_spec|].
              intros c Hc. apply Hall, in_app_iff. now left.
        -- apply lang_equiv_sym, constraint_product_append_M;
             exact eqb_spec.
    + apply constraint_product_subset_absorb_M.
      * exact eqb_spec.
      * exact Hall.
      * intros c Hc. apply (proj1 (Hmembers c)); exact Hc.
Qed.

Theorem constraint_product_canonical_subset_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs ys : list (rewpla A)) :
  (forall c, In c cs -> empty_main_language (rewpla_denote eqb c)) ->
  (forall c, In c ys -> In c cs) ->
  exists ss, In ss (subsets cs) /\
    lang_equiv (rewpla_denote eqb (constraint_product ys))
      (rewpla_denote eqb (constraint_product ss)).
Proof.
  intros Hall Hys.
  set (ss := filter (fun c => existsb (rewpla_eqb eqb c) ys) cs).
  assert (Hselection : forall c, In c ss <-> In c ys).
  { intro c. unfold ss. rewrite filter_In. split.
    - intros [_ Htest]. apply existsb_exists in Htest
        as [y [Hy Hcy]].
      apply (proj1 (rewpla_eqb_spec eqb eqb_spec _ _)) in Hcy.
      now subst y.
    - intro Hy. split; [apply Hys; exact Hy|].
      apply existsb_exists. exists c. split;
        [exact Hy|apply (proj2 (rewpla_eqb_spec eqb eqb_spec _ _));
          reflexivity]. }
  exists ss. split.
  - unfold ss. apply filter_is_subset.
  - apply constraint_product_same_members_M; [exact eqb_spec| |].
    + intros c Hc. apply in_app_iff in Hc as [Hy|Hss];
        apply Hall.
      * apply Hys. exact Hy.
      * apply filter_In in Hss as [Hc _]. exact Hc.
    + intro c. specialize (Hselection c). tauto.
Qed.

Theorem constraint_terms_monotone_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs1 cs2 : list (rewpla A)) (t : rewpla A) :
  (forall c, In c cs2 -> empty_main_language (rewpla_denote eqb c)) ->
  (forall c, In c cs1 -> In c cs2) ->
  In t (constraint_terms cs1) ->
  exists u, In u (constraint_terms cs2) /\
    lang_equiv (rewpla_denote eqb t) (rewpla_denote eqb u).
Proof.
  intros Hall Hsub Ht. unfold constraint_terms in Ht.
  apply in_map_iff in Ht as [ss [<- Hss]].
  assert (Hsource : forall c, In c ss -> In c cs2).
  { intros c Hc. apply Hsub.
    exact ((subset_members_from_source cs1 ss Hss c) Hc). }
  destruct (constraint_product_canonical_subset_M eqb eqb_spec
    cs2 ss Hall Hsource) as [us [Hus Hsem]].
  exists (constraint_product us). split.
  - unfold constraint_terms. apply in_map. exact Hus.
  - exact Hsem.
Qed.

Lemma constraint_generator_singleton_term_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs : list (rewpla A)) (c : rewpla A) :
  In c cs ->
  exists t, In t (constraint_terms cs) /\
    lang_equiv (rewpla_denote eqb c) (rewpla_denote eqb t).
Proof.
  intro Hc. exists (constraint_product [c]). split.
  - unfold constraint_terms. apply in_map.
    now apply singleton_subset_member.
  - simpl. eapply lang_equiv_trans.
    + apply lang_equiv_sym, rewpla_concat_one_right_M;
        exact eqb_spec.
    + apply lang_equiv_sym, smart_concat_correct_M;
        exact eqb_spec.
Qed.

Theorem constraint_terms_product_closed_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs : list (rewpla A)) (x y : rewpla A) :
  (forall c, In c cs -> empty_main_language (rewpla_denote eqb c)) ->
  In x (constraint_terms cs) -> In y (constraint_terms cs) ->
  exists z, In z (constraint_terms cs) /\
    lang_equiv (rewpla_denote eqb (WConcat x y))
      (rewpla_denote eqb z).
Proof.
  intros Hall Hx Hy. unfold constraint_terms in Hx, Hy.
  apply in_map_iff in Hx as [sx [<- Hsx]].
  apply in_map_iff in Hy as [sy [<- Hsy]].
  assert (Hsource : forall c, In c (sx ++ sy) -> In c cs).
  { intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
    - exact ((subset_members_from_source cs sx Hsx c) Hc).
    - exact ((subset_members_from_source cs sy Hsy c) Hc). }
  destruct (constraint_product_canonical_subset_M eqb eqb_spec cs
    (sx ++ sy) Hall Hsource) as [ss [Hss Hsem]].
  exists (constraint_product ss). split.
  - unfold constraint_terms. apply in_map. exact Hss.
  - eapply lang_equiv_trans.
    + apply lang_equiv_sym, constraint_product_append_M;
        exact eqb_spec.
    + exact Hsem.
Qed.

Theorem constraint_main_terms_product_closed_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as_ cs : list (rewpla A)) (x y : rewpla A) :
  (forall c, In c cs -> empty_main_language (rewpla_denote eqb c)) ->
  In x (constraint_terms cs) -> In y (main_terms as_ cs) ->
  exists z, In z (main_terms as_ cs) /\
    lang_equiv (rewpla_denote eqb (WConcat x y))
      (rewpla_denote eqb z).
Proof.
  intros Hall Hx Hy. unfold constraint_terms in Hx.
  apply in_map_iff in Hx as [sx [<- Hsx]].
  unfold main_terms in Hy.
  apply in_flat_map in Hy as [sy [Hsy Hmap]].
  apply in_map_iff in Hmap as [t [<- Ht]].
  assert (Hsource : forall c, In c (sx ++ sy) -> In c cs).
  { intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
    - exact ((subset_members_from_source cs sx Hsx c) Hc).
    - exact ((subset_members_from_source cs sy Hsy c) Hc). }
  destruct (constraint_product_canonical_subset_M eqb eqb_spec cs
    (sx ++ sy) Hall Hsource) as [ss [Hss Hsem]].
  exists (smart_concat (constraint_product ss) t). split.
  - unfold main_terms. apply in_flat_map. exists ss.
    split; [exact Hss|]. apply in_map. exact Ht.
  - eapply lang_equiv_trans.
    + apply lang_concat_compat; [apply lang_equiv_refl|].
      apply smart_concat_correct_M; exact eqb_spec.
    + eapply lang_equiv_trans.
      * apply lang_equiv_sym, rewpla_concat_assoc_M;
          exact eqb_spec.
      * eapply lang_equiv_trans.
        -- apply lang_concat_compat.
           ++ apply lang_equiv_sym, constraint_product_append_M;
                exact eqb_spec.
           ++ apply lang_equiv_refl.
        -- eapply lang_equiv_trans.
           ++ apply lang_concat_compat; [exact Hsem|apply lang_equiv_refl].
           ++ apply lang_equiv_sym, smart_concat_correct_M;
                exact eqb_spec.
Qed.

Theorem main_terms_monotone_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as1 as2 cs1 cs2 : list (rewpla A)) (y : rewpla A) :
  (forall c, In c cs2 -> empty_main_language (rewpla_denote eqb c)) ->
  (forall t, In t as1 -> In t as2) ->
  (forall c, In c cs1 -> In c cs2) ->
  In y (main_terms as1 cs1) ->
  exists z, In z (main_terms as2 cs2) /\
    lang_equiv (rewpla_denote eqb y) (rewpla_denote eqb z).
Proof.
  intros Hall Has Hcs Hy. unfold main_terms in Hy.
  apply in_flat_map in Hy as [ss [Hss Hmap]].
  apply in_map_iff in Hmap as [t [<- Ht]].
  assert (Hsource : forall c, In c ss -> In c cs2).
  { intros c Hc. apply Hcs.
    exact ((subset_members_from_source cs1 ss Hss c) Hc). }
  destruct (constraint_product_canonical_subset_M eqb eqb_spec
    cs2 ss Hall Hsource) as [us [Hus Hsem]].
  exists (smart_concat (constraint_product us) t). split.
  - unfold main_terms. apply in_flat_map. exists us.
    split; [exact Hus|]. apply in_map. now apply Has.
  - eapply lang_equiv_trans.
    + apply smart_concat_correct_M; exact eqb_spec.
    + eapply lang_equiv_trans.
      * apply lang_concat_compat; [exact Hsem|apply lang_equiv_refl].
      * apply lang_equiv_sym, smart_concat_correct_M;
          exact eqb_spec.
Qed.

Theorem main_terms_append_suffix_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as1 as2 cs1 cs2 : list (rewpla A))
    (suffix y : rewpla A) :
  (forall c, In c cs2 -> empty_main_language (rewpla_denote eqb c)) ->
  (forall t, In t as1 -> In (WConcat t suffix) as2) ->
  (forall c, In c cs1 -> In c cs2) ->
  In y (main_terms as1 cs1) ->
  exists z, In z (main_terms as2 cs2) /\
    lang_equiv (rewpla_denote eqb (WConcat y suffix))
      (rewpla_denote eqb z).
Proof.
  intros Hall Hgen Hcs Hy. unfold main_terms in Hy.
  apply in_flat_map in Hy as [ss [Hss Hmap]].
  apply in_map_iff in Hmap as [t [<- Ht]].
  assert (Hsource : forall c, In c ss -> In c cs2).
  { intros c Hc. apply Hcs.
    exact ((subset_members_from_source cs1 ss Hss c) Hc). }
  destruct (constraint_product_canonical_subset_M eqb eqb_spec
    cs2 ss Hall Hsource) as [us [Hus Hsem]].
  exists (smart_concat (constraint_product us) (WConcat t suffix)).
  split.
  - unfold main_terms. apply in_flat_map. exists us.
    split; [exact Hus|]. apply in_map. now apply Hgen.
  - eapply lang_equiv_trans.
    + apply lang_concat_compat;
        [apply smart_concat_correct_M; exact eqb_spec|
         apply lang_equiv_refl].
    + eapply lang_equiv_trans.
      * apply rewpla_concat_assoc_M; exact eqb_spec.
      * eapply lang_equiv_trans.
        -- apply lang_concat_compat; [exact Hsem|apply lang_equiv_refl].
        -- apply lang_equiv_sym.
           apply (smart_concat_correct_M eqb eqb_spec
             (constraint_product us) (WConcat t suffix)).
Qed.

Lemma finite_semantic_representative_list {A : Type}
    (eqb : A -> A -> bool)
    (universe inputs : list (rewpla A)) :
  (forall x, In x inputs -> exists y, In y universe /\
    lang_equiv (rewpla_denote eqb x) (rewpla_denote eqb y)) ->
  exists reps, (forall y, In y reps -> In y universe) /\
    lang_equiv (rewpla_denote eqb (union_expression inputs))
      (rewpla_denote eqb (union_expression reps)).
Proof.
  intro Hinputs. induction inputs as [|x xs IH].
  - exists []. split; [intros y H; contradiction|apply lang_equiv_refl].
  - destruct (Hinputs x (or_introl eq_refl)) as [y [Hy Hxy]].
    destruct IH as [reps [Hreps Hrest]].
    { intros z Hz. apply Hinputs. now right. }
    exists (y :: reps). split.
    + intros z [<-|Hz]; [exact Hy|now apply Hreps].
    + eapply lang_equiv_trans.
      * apply smart_plus_correct_M.
      * eapply lang_equiv_trans.
        -- apply lang_union_compat; [exact Hxy|exact Hrest].
        -- apply lang_equiv_sym, smart_plus_correct_M.
Qed.

Theorem constraint_normal_forms_monotone_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs1 cs2 : list (rewpla A)) (n : rewpla A) :
  (forall c, In c cs2 -> empty_main_language (rewpla_denote eqb c)) ->
  (forall c, In c cs1 -> In c cs2) ->
  In n (constraint_normal_forms cs1) ->
  exists m, In m (constraint_normal_forms cs2) /\
    lang_equiv (rewpla_denote eqb n) (rewpla_denote eqb m).
Proof.
  intros Hall Hsub Hn. unfold constraint_normal_forms in Hn.
  apply in_map_iff in Hn as [ss [<- Hss]].
  assert (Hssrep : forall t, In t ss ->
      exists u, In u (constraint_terms cs2) /\
        lang_equiv (rewpla_denote eqb t) (rewpla_denote eqb u)).
  { intros t Ht. eapply constraint_terms_monotone_M;
      [exact eqb_spec|exact Hall|exact Hsub|].
    exact ((subset_members_from_source
      (constraint_terms cs1) ss Hss t) Ht). }
  destruct (finite_semantic_representative_list eqb
    (constraint_terms cs2) ss Hssrep) as [reps [Hreps Hsem]].
  destruct (chosen_union_forms_cover_finite_union eqb eqb_spec
    (constraint_terms cs2) reps Hreps) as [m [Hm Hmsem]].
  exists m. split; [exact Hm|].
  eapply lang_equiv_trans; [exact Hsem|].
  apply lang_equiv_sym. exact Hmsem.
Qed.

Lemma union_expression_pair_products_M {A : Type}
    (eqb : A -> A -> bool) (xs ys : list (rewpla A)) :
  lang_equiv (rewpla_denote eqb
      (WConcat (union_expression xs) (union_expression ys)))
    (rewpla_denote eqb
      (union_expression (flat_map (fun x => map (WConcat x) ys) xs))).
Proof.
  intro p. rewrite union_expression_membership. simpl.
  unfold lang_union.
  unfold lang_concat. split.
  - intros [p1 [p2 [Hp1 [Hp2 Hout]]]].
    apply union_expression_membership in Hp1 as [x [Hx Hxp]].
    apply union_expression_membership in Hp2 as [y [Hy Hyp]].
    exists (WConcat x y). split.
    + apply in_flat_map. exists x. split; [exact Hx|].
      apply in_map. exact Hy.
    + exists p1, p2. repeat split; assumption.
  - intros [t [Ht Htp]].
    apply in_flat_map in Ht as [x [Hx Hmap]].
    apply in_map_iff in Hmap as [y [<- Hy]].
    destruct Htp as [p1 [p2 [Hxp [Hyp Hout]]]].
    exists p1, p2. repeat split; try exact Hout.
    + apply union_expression_membership. exists x. now split.
    + apply union_expression_membership. exists y. now split.
Qed.

Lemma union_expression_append_suffix_M {A : Type}
    (eqb : A -> A -> bool) (xs : list (rewpla A)) suffix :
  lang_equiv (rewpla_denote eqb
      (WConcat (union_expression xs) suffix))
    (rewpla_denote eqb
      (union_expression (map (fun x => WConcat x suffix) xs))).
Proof.
  intro p. rewrite union_expression_membership. simpl.
  unfold lang_concat. split.
  - intros [p1 [p2 [Hp1 [Hp2 Hout]]]].
    apply union_expression_membership in Hp1 as [x [Hx Hxp]].
    exists (WConcat x suffix). split.
    + apply in_map_iff. exists x. split; [reflexivity|exact Hx].
    + exists p1, p2. repeat split; assumption.
  - intros [t [Ht Htp]].
    apply in_map_iff in Ht as [x [<- Hx]].
    destruct Htp as [p1 [p2 [Hxp [Hp2 Hout]]]].
    exists p1, p2. repeat split; try exact Hp2; try exact Hout.
    apply union_expression_membership. exists x. now split.
Qed.

Theorem main_normal_forms_append_suffix_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as1 as2 cs1 cs2 : list (rewpla A))
    (suffix n : rewpla A) :
  (forall c, In c cs2 -> empty_main_language (rewpla_denote eqb c)) ->
  (forall t, In t as1 -> In (WConcat t suffix) as2) ->
  (forall c, In c cs1 -> In c cs2) ->
  In n (main_normal_forms as1 cs1) ->
  exists m, In m (main_normal_forms as2 cs2) /\
    lang_equiv (rewpla_denote eqb (WConcat n suffix))
      (rewpla_denote eqb m).
Proof.
  intros Hall Hgen Hcs Hn. unfold main_normal_forms in Hn.
  apply in_map_iff in Hn as [ss [<- Hss]].
  set (appended := map (fun t => WConcat t suffix) ss).
  assert (Happended : forall t, In t appended ->
    exists u, In u (main_terms as2 cs2) /\
      lang_equiv (rewpla_denote eqb t) (rewpla_denote eqb u)).
  { intros t Ht. unfold appended in Ht.
    apply in_map_iff in Ht as [x [<- Hx]].
    eapply main_terms_append_suffix_M;
      [exact eqb_spec|exact Hall|exact Hgen|exact Hcs|].
    exact ((subset_members_from_source
      (main_terms as1 cs1) ss Hss x) Hx). }
  destruct (finite_semantic_representative_list eqb
    (main_terms as2 cs2) appended Happended)
    as [reps [Hreps Hsem]].
  destruct (chosen_union_forms_cover_finite_union eqb eqb_spec
    (main_terms as2 cs2) reps Hreps) as [m [Hm Hmsem]].
  exists m. split; [exact Hm|].
  eapply lang_equiv_trans.
  - apply union_expression_append_suffix_M.
  - eapply lang_equiv_trans; [exact Hsem|].
    apply lang_equiv_sym. exact Hmsem.
Qed.

Lemma main_terms_nil {A : Type} (cs : list (rewpla A)) :
  main_terms [] cs = [].
Proof.
  unfold main_terms. induction (subsets cs) as [|ss ssrest IH];
    simpl; [reflexivity|exact IH].
Qed.

Lemma normal_forms_nil_constraint {A : Type}
    (cs : list (rewpla A)) :
  normal_forms [] cs = map union_expression (subsets (constraint_terms cs)).
Proof.
  unfold normal_forms, term_universe.
  rewrite main_terms_nil, app_nil_r. reflexivity.
Qed.

Lemma union_expression_append_M {A : Type}
    (eqb : A -> A -> bool) (xs ys : list (rewpla A)) :
  lang_equiv (rewpla_denote eqb (union_expression (xs ++ ys)))
    (rewpla_denote eqb
      (WPlus (union_expression xs) (union_expression ys))).
Proof.
  intro p. rewrite union_expression_membership. simpl.
  unfold lang_union.
  repeat rewrite union_expression_membership.
  split.
  - intros [t [Ht Hp]]. apply in_app_iff in Ht as [Hx|Hy].
    + left. exists t. now split.
    + right. exists t. now split.
  - intros [[t [Ht Hp]]|[t [Ht Hp]]]; exists t; split;
      [apply in_app_iff; now left|exact Hp|apply in_app_iff; now right|exact Hp].
Qed.

Theorem constraint_normal_forms_union_closed_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs : list (rewpla A)) (x y : rewpla A) :
  In x (constraint_normal_forms cs) ->
  In y (constraint_normal_forms cs) ->
  exists n, In n (constraint_normal_forms cs) /\
    lang_equiv (rewpla_denote eqb (WPlus x y))
      (rewpla_denote eqb n).
Proof.
  intros Hx Hy. unfold constraint_normal_forms in Hx, Hy.
  apply in_map_iff in Hx as [sx [<- Hsx]].
  apply in_map_iff in Hy as [sy [<- Hsy]].
  destruct (normal_forms_cover_finite_union eqb eqb_spec [] cs
    (sx ++ sy)) as [n [Hn Hsem]].
  { intros t Ht. apply in_app_iff in Ht as [Ht|Ht];
      unfold term_universe; apply in_app_iff; left.
    - exact ((subset_members_from_source
        (constraint_terms cs) sx Hsx t) Ht).
    - exact ((subset_members_from_source
        (constraint_terms cs) sy Hsy t) Ht). }
  rewrite normal_forms_nil_constraint in Hn.
  exists n. split; [exact Hn|].
  eapply lang_equiv_trans.
  - apply lang_equiv_sym, union_expression_append_M.
  - apply lang_equiv_sym. exact Hsem.
Qed.

(** Paper Lemma 5, first algebraic closure: the whole constraint-normal-form
    family [N_c] is closed under partial concatenation up to complete
    pair-language equivalence.  No syntactic or semantic equality oracle is
    assumed; finite representatives are chosen from the candidate universe. *)
Theorem constraint_normal_forms_concat_closed_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs : list (rewpla A)) (x y : rewpla A) :
  (forall c, In c cs -> empty_main_language (rewpla_denote eqb c)) ->
  In x (constraint_normal_forms cs) ->
  In y (constraint_normal_forms cs) ->
  exists n, In n (constraint_normal_forms cs) /\
    lang_equiv (rewpla_denote eqb (WConcat x y))
      (rewpla_denote eqb n).
Proof.
  intros Hall Hx Hy. unfold constraint_normal_forms in Hx, Hy.
  apply in_map_iff in Hx as [sx [<- Hsx]].
  apply in_map_iff in Hy as [sy [<- Hsy]].
  set (pairs := flat_map (fun a => map (WConcat a) sy) sx).
  assert (Hpairs : forall t, In t pairs ->
    exists z, In z (constraint_terms cs) /\
      lang_equiv (rewpla_denote eqb t) (rewpla_denote eqb z)).
  { intros t Ht. unfold pairs in Ht.
    apply in_flat_map in Ht as [a [Ha Hmap]].
    apply in_map_iff in Hmap as [b [<- Hb]].
    apply constraint_terms_product_closed_M; [exact eqb_spec|exact Hall| |].
    - exact ((subset_members_from_source
        (constraint_terms cs) sx Hsx a) Ha).
    - exact ((subset_members_from_source
        (constraint_terms cs) sy Hsy b) Hb). }
  destruct (finite_semantic_representative_list eqb
    (constraint_terms cs) pairs Hpairs) as [reps [Hreps Hsem]].
  destruct (normal_forms_cover_finite_union eqb eqb_spec [] cs reps)
    as [n [Hn Hnsem]].
  { intros t Ht. unfold term_universe.
    apply in_app_iff. left. now apply Hreps. }
  rewrite normal_forms_nil_constraint in Hn.
  exists n. split; [exact Hn|].
  eapply lang_equiv_trans.
  - apply union_expression_pair_products_M.
  - eapply lang_equiv_trans; [exact Hsem|].
    apply lang_equiv_sym. exact Hnsem.
Qed.

(** Paper Lemma 5, second algebraic closure: multiplying an [N_c] assertion
    with an [N_m] continuation stays in [N_m] up to full pair semantics. *)
Theorem constraint_main_normal_forms_concat_closed_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as_ cs : list (rewpla A)) (x y : rewpla A) :
  (forall c, In c cs -> empty_main_language (rewpla_denote eqb c)) ->
  In x (constraint_normal_forms cs) ->
  In y (main_normal_forms as_ cs) ->
  exists n, In n (main_normal_forms as_ cs) /\
    lang_equiv (rewpla_denote eqb (WConcat x y))
      (rewpla_denote eqb n).
Proof.
  intros Hall Hx Hy.
  unfold constraint_normal_forms in Hx.
  unfold main_normal_forms in Hy.
  apply in_map_iff in Hx as [sx [<- Hsx]].
  apply in_map_iff in Hy as [sy [<- Hsy]].
  set (pairs := flat_map (fun a => map (WConcat a) sy) sx).
  assert (Hpairs : forall t, In t pairs ->
    exists z, In z (main_terms as_ cs) /\
      lang_equiv (rewpla_denote eqb t) (rewpla_denote eqb z)).
  { intros t Ht. unfold pairs in Ht.
    apply in_flat_map in Ht as [a [Ha Hmap]].
    apply in_map_iff in Hmap as [b [<- Hb]].
    apply constraint_main_terms_product_closed_M;
      [exact eqb_spec|exact Hall| |].
    - exact ((subset_members_from_source
        (constraint_terms cs) sx Hsx a) Ha).
    - exact ((subset_members_from_source
        (main_terms as_ cs) sy Hsy b) Hb). }
  destruct (finite_semantic_representative_list eqb
    (main_terms as_ cs) pairs Hpairs) as [reps [Hreps Hsem]].
  destruct (chosen_union_forms_cover_finite_union eqb eqb_spec
    (main_terms as_ cs) reps Hreps) as [n [Hn Hnsem]].
  exists n. split; [exact Hn|].
  eapply lang_equiv_trans.
  - apply union_expression_pair_products_M.
  - eapply lang_equiv_trans; [exact Hsem|].
    apply lang_equiv_sym. exact Hnsem.
Qed.

Theorem main_normal_forms_union_closed_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as_ cs : list (rewpla A)) (x y : rewpla A) :
  In x (main_normal_forms as_ cs) ->
  In y (main_normal_forms as_ cs) ->
  exists n, In n (main_normal_forms as_ cs) /\
    lang_equiv (rewpla_denote eqb (WPlus x y))
      (rewpla_denote eqb n).
Proof.
  intros Hx Hy. unfold main_normal_forms in Hx, Hy.
  apply in_map_iff in Hx as [sx [<- Hsx]].
  apply in_map_iff in Hy as [sy [<- Hsy]].
  destruct (chosen_union_forms_cover_finite_union eqb eqb_spec
    (main_terms as_ cs) (sx ++ sy)) as [n [Hn Hsem]].
  { intros t Ht. apply in_app_iff in Ht as [Ht|Ht].
    - exact ((subset_members_from_source
        (main_terms as_ cs) sx Hsx t) Ht).
    - exact ((subset_members_from_source
        (main_terms as_ cs) sy Hsy t) Ht). }
  exists n. split; [exact Hn|].
  eapply lang_equiv_trans.
  - apply lang_equiv_sym, union_expression_append_M.
  - apply lang_equiv_sym. exact Hsem.
Qed.

Theorem main_normal_forms_monotone_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as1 as2 cs1 cs2 : list (rewpla A)) (n : rewpla A) :
  (forall c, In c cs2 -> empty_main_language (rewpla_denote eqb c)) ->
  (forall t, In t as1 -> In t as2) ->
  (forall c, In c cs1 -> In c cs2) ->
  In n (main_normal_forms as1 cs1) ->
  exists m, In m (main_normal_forms as2 cs2) /\
    lang_equiv (rewpla_denote eqb n) (rewpla_denote eqb m).
Proof.
  intros Hall Has Hcs Hn. unfold main_normal_forms in Hn.
  apply in_map_iff in Hn as [ss [<- Hss]].
  assert (Hssrep : forall t, In t ss ->
      exists u, In u (main_terms as2 cs2) /\
        lang_equiv (rewpla_denote eqb t) (rewpla_denote eqb u)).
  { intros t Ht. eapply main_terms_monotone_M;
      [exact eqb_spec|exact Hall|exact Has|exact Hcs|].
    exact ((subset_members_from_source
      (main_terms as1 cs1) ss Hss t) Ht). }
  destruct (finite_semantic_representative_list eqb
    (main_terms as2 cs2) ss Hssrep) as [reps [Hreps Hsem]].
  destruct (chosen_union_forms_cover_finite_union eqb eqb_spec
    (main_terms as2 cs2) reps Hreps) as [m [Hm Hmsem]].
  exists m. split; [exact Hm|].
  eapply lang_equiv_trans; [exact Hsem|].
  apply lang_equiv_sym. exact Hmsem.
Qed.

(** Paper Lemma 4, union case, reusable in the full structural induction.
    Both derivative components are represented in their separate families;
    semantic equivalence is preserved while operand generators are embedded
    into the generators of the whole union expression. *)
Theorem symbol_derivative_represented_union {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r s : rewpla A) :
  symbol_derivative_represented eqb a r ->
  symbol_derivative_represented eqb a s ->
  symbol_derivative_represented eqb a (WPlus r s).
Proof.
  unfold symbol_derivative_represented.
  intros [[mr [Hmr Hmrsem]] [cr [Hcr Hcrsem]]]
    [[ms [Hms Hmssem]] [cs [Hcs Hcssem]]].
  destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:Dr.
  destruct (symbol_derivative_core eqb a s) as [sm sc] eqn:Ds.
  simpl in Hmrsem, Hcrsem, Hmssem, Hcssem.
  destruct (union_generator_inclusions eqb eqb_spec r s)
    as [HAr [HAs [HCr HCs]]].
  pose proof (constraint_generators_empty_main eqb eqb_spec
    (WPlus r s)) as Hall.
  destruct (main_normal_forms_monotone_M eqb eqb_spec
    (continuation_generators eqb r)
    (continuation_generators eqb (WPlus r s))
    (constraint_generators eqb r)
    (constraint_generators eqb (WPlus r s))
    mr Hall HAr HCr Hmr) as [mr' [Hmr' Hmr'sem]].
  destruct (main_normal_forms_monotone_M eqb eqb_spec
    (continuation_generators eqb s)
    (continuation_generators eqb (WPlus r s))
    (constraint_generators eqb s)
    (constraint_generators eqb (WPlus r s))
    ms Hall HAs HCs Hms) as [ms' [Hms' Hms'sem]].
  destruct (constraint_normal_forms_monotone_M eqb eqb_spec
    (constraint_generators eqb r)
    (constraint_generators eqb (WPlus r s))
    cr Hall HCr Hcr) as [cr' [Hcr' Hcr'sem]].
  destruct (constraint_normal_forms_monotone_M eqb eqb_spec
    (constraint_generators eqb s)
    (constraint_generators eqb (WPlus r s))
    cs Hall HCs Hcs) as [cs' [Hcs' Hcs'sem]].
  destruct (main_normal_forms_union_closed_M eqb eqb_spec
    (continuation_generators eqb (WPlus r s))
    (constraint_generators eqb (WPlus r s))
    mr' ms' Hmr' Hms') as [m [Hm Hmsem]].
  destruct (constraint_normal_forms_union_closed_M eqb eqb_spec
    (constraint_generators eqb (WPlus r s))
    cr' cs' Hcr' Hcs') as [c [Hc Hcsem]].
  simpl. rewrite Dr, Ds. simpl. split.
  - exists m. split; [exact Hm|].
    eapply lang_equiv_trans.
    + apply lang_union_compat; [exact Hmrsem|exact Hmssem].
    + eapply lang_equiv_trans.
      * apply lang_union_compat; [exact Hmr'sem|exact Hms'sem].
      * exact Hmsem.
  - exists c. split; [exact Hc|].
    eapply lang_equiv_trans.
    + apply lang_union_compat; [exact Hcrsem|exact Hcssem].
    + eapply lang_equiv_trans.
      * apply lang_union_compat; [exact Hcr'sem|exact Hcs'sem].
      * exact Hcsem.
Qed.

(** Multiplication by the Boolean epsilon part in Eq. (20) selects either
    the existing normal form or the zero normal form. *)
Lemma main_normal_forms_lambda_left_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as_ cs : list (rewpla A)) (r x : rewpla A) :
  In x (main_normal_forms as_ cs) ->
  exists n, In n (main_normal_forms as_ cs) /\
    lang_equiv (rewpla_denote eqb (WConcat (rewpla_lambda r) x))
      (rewpla_denote eqb n).
Proof.
  intro Hx. unfold rewpla_lambda.
  destruct (rewpla_nullable r) eqn:Hnull.
  - exists x. split; [exact Hx|].
    apply rewpla_concat_one_left_M. exact eqb_spec.
  - exists WZero. split; [apply zero_in_main_normal_forms|].
    apply rewpla_concat_zero_left_M. exact eqb_spec.
Qed.

Lemma constraint_normal_forms_lambda_left_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs : list (rewpla A)) (r x : rewpla A) :
  In x (constraint_normal_forms cs) ->
  exists n, In n (constraint_normal_forms cs) /\
    lang_equiv (rewpla_denote eqb (WConcat (rewpla_lambda r) x))
      (rewpla_denote eqb n).
Proof.
  intro Hx. unfold rewpla_lambda.
  destruct (rewpla_nullable r) eqn:Hnull.
  - exists x. split; [exact Hx|].
    apply rewpla_concat_one_left_M. exact eqb_spec.
  - exists WZero. split; [apply zero_in_constraint_normal_forms|].
    apply rewpla_concat_zero_left_M. exact eqb_spec.
Qed.

Lemma constraint_normal_forms_lambda_right_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs : list (rewpla A)) (r x : rewpla A) :
  In x (constraint_normal_forms cs) ->
  exists n, In n (constraint_normal_forms cs) /\
    lang_equiv (rewpla_denote eqb (WConcat x (rewpla_lambda r)))
      (rewpla_denote eqb n).
Proof.
  intro Hx. unfold rewpla_lambda.
  destruct (rewpla_nullable r) eqn:Hnull.
  - exists x. split; [exact Hx|].
    apply rewpla_concat_one_right_M. exact eqb_spec.
  - exists WZero. split; [apply zero_in_constraint_normal_forms|].
    apply rewpla_concat_zero_right_M. exact eqb_spec.
Qed.

(** Paper Lemma 4, concatenation case of Eq. (20).  The three main
    summands and the three context summands are represented separately,
    then folded back into their respective finite union families. *)
Theorem symbol_derivative_represented_concat {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r s : rewpla A) :
  symbol_derivative_represented eqb a r ->
  symbol_derivative_represented eqb a s ->
  symbol_derivative_represented eqb a (WConcat r s).
Proof.
  unfold symbol_derivative_represented.
  intros [[mr [Hmr Hmrsem]] [cr [Hcr Hcrsem]]]
    [[ms [Hms Hmssem]] [cs [Hcs Hcssem]]].
  destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:Dr.
  destruct (symbol_derivative_core eqb a s) as [sm sc] eqn:Ds.
  simpl in Hmrsem, Hcrsem, Hmssem, Hcssem.
  set (ats := continuation_generators eqb (WConcat r s)).
  set (cts := constraint_generators eqb (WConcat r s)).
  destruct (concat_generator_inclusions eqb eqb_spec r s)
    as [HAr [HAs [HCr HCs]]].
  pose proof (constraint_generators_empty_main eqb eqb_spec
    (WConcat r s)) as Hall.
  destruct (main_normal_forms_append_suffix_M eqb eqb_spec
    (continuation_generators eqb r) ats
    (constraint_generators eqb r) cts s mr
    Hall HAr HCr Hmr) as [p1 [Hp1 Hp1sem]].
  destruct (main_normal_forms_monotone_M eqb eqb_spec
    (continuation_generators eqb s) ats
    (constraint_generators eqb s) cts ms
    Hall HAs HCs Hms) as [ms' [Hms' Hms'sem]].
  destruct (constraint_normal_forms_monotone_M eqb eqb_spec
    (constraint_generators eqb r) cts cr
    Hall HCr Hcr) as [cr' [Hcr' Hcr'sem]].
  destruct (constraint_normal_forms_monotone_M eqb eqb_spec
    (constraint_generators eqb s) cts cs
    Hall HCs Hcs) as [cs' [Hcs' Hcs'sem]].
  destruct (constraint_main_normal_forms_concat_closed_M eqb eqb_spec
    ats cts cr' ms' Hall Hcr' Hms') as [p2 [Hp2 Hp2sem]].
  destruct (main_normal_forms_lambda_left_M eqb eqb_spec
    ats cts r ms' Hms') as [p3 [Hp3 Hp3sem]].
  destruct (main_normal_forms_union_closed_M eqb eqb_spec
    ats cts p1 p2 Hp1 Hp2) as [p12 [Hp12 Hp12sem]].
  destruct (main_normal_forms_union_closed_M eqb eqb_spec
    ats cts p12 p3 Hp12 Hp3) as [pm [Hpm Hpmsem]].
  destruct (constraint_normal_forms_concat_closed_M eqb eqb_spec
    cts cr' cs' Hall Hcr' Hcs') as [q1 [Hq1 Hq1sem]].
  destruct (constraint_normal_forms_lambda_right_M eqb eqb_spec
    cts s cr' Hcr') as [q2 [Hq2 Hq2sem]].
  destruct (constraint_normal_forms_lambda_left_M eqb eqb_spec
    cts r cs' Hcs') as [q3 [Hq3 Hq3sem]].
  destruct (constraint_normal_forms_union_closed_M eqb eqb_spec
    cts q1 q2 Hq1 Hq2) as [q12 [Hq12 Hq12sem]].
  destruct (constraint_normal_forms_union_closed_M eqb eqb_spec
    cts q12 q3 Hq12 Hq3) as [qc [Hqc Hqcsem]].
  assert (Hp1raw : lang_equiv
      (rewpla_denote eqb (WConcat rm s)) (rewpla_denote eqb p1)).
  { eapply lang_equiv_trans; [|exact Hp1sem].
    simpl. apply lang_concat_compat;
      [exact Hmrsem|apply lang_equiv_refl]. }
  assert (Hp2raw : lang_equiv
      (rewpla_denote eqb (WConcat rc sm)) (rewpla_denote eqb p2)).
  { eapply lang_equiv_trans; [|exact Hp2sem].
    simpl. apply lang_concat_compat.
    - eapply lang_equiv_trans; [exact Hcrsem|exact Hcr'sem].
    - eapply lang_equiv_trans; [exact Hmssem|exact Hms'sem]. }
  assert (Hp3raw : lang_equiv
      (rewpla_denote eqb (WConcat (rewpla_lambda r) sm))
      (rewpla_denote eqb p3)).
  { eapply lang_equiv_trans; [|exact Hp3sem].
    simpl. apply lang_concat_compat;
      [apply lang_equiv_refl|].
    eapply lang_equiv_trans; [exact Hmssem|exact Hms'sem]. }
  assert (Hq1raw : lang_equiv
      (rewpla_denote eqb (WConcat rc sc)) (rewpla_denote eqb q1)).
  { eapply lang_equiv_trans; [|exact Hq1sem].
    simpl. apply lang_concat_compat.
    - eapply lang_equiv_trans; [exact Hcrsem|exact Hcr'sem].
    - eapply lang_equiv_trans; [exact Hcssem|exact Hcs'sem]. }
  assert (Hq2raw : lang_equiv
      (rewpla_denote eqb (WConcat rc (rewpla_lambda s)))
      (rewpla_denote eqb q2)).
  { eapply lang_equiv_trans; [|exact Hq2sem].
    simpl. apply lang_concat_compat.
    - eapply lang_equiv_trans; [exact Hcrsem|exact Hcr'sem].
    - apply lang_equiv_refl. }
  assert (Hq3raw : lang_equiv
      (rewpla_denote eqb (WConcat (rewpla_lambda r) sc))
      (rewpla_denote eqb q3)).
  { eapply lang_equiv_trans; [|exact Hq3sem].
    simpl. apply lang_concat_compat;
      [apply lang_equiv_refl|].
    eapply lang_equiv_trans; [exact Hcssem|exact Hcs'sem]. }
  simpl. rewrite Dr, Ds. simpl. split.
  - exists pm. split; [exact Hpm|].
    eapply lang_equiv_trans.
    + apply lang_union_compat.
      * apply lang_union_compat; [exact Hp1raw|exact Hp2raw].
      * exact Hp3raw.
    + eapply lang_equiv_trans.
      * apply lang_union_compat;
          [exact Hp12sem|apply lang_equiv_refl].
      * exact Hpmsem.
  - exists qc. split; [exact Hqc|].
    eapply lang_equiv_trans.
    + apply lang_union_compat.
      * apply lang_union_compat; [exact Hq1raw|exact Hq2raw].
      * exact Hq3raw.
    + eapply lang_equiv_trans.
      * apply lang_union_compat;
          [exact Hq12sem|apply lang_equiv_refl].
      * exact Hqcsem.
Qed.

(** Paper Lemma 4, Kleene-star case: the continuation generator is a
    derivative continuation followed by the original star. *)
Theorem symbol_derivative_represented_star {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r : rewpla A) :
  symbol_derivative_represented eqb a r ->
  symbol_derivative_represented eqb a (WStar r).
Proof.
  unfold symbol_derivative_represented.
  intros [[mr [Hmr Hmrsem]] [cr [Hcr Hcrsem]]].
  destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:Dr.
  simpl in Hmrsem, Hcrsem.
  set (ars := continuation_generators eqb r).
  set (crs := constraint_generators eqb r).
  set (asts := continuation_generators eqb (WStar r)).
  set (csts := constraint_generators eqb (WStar r)).
  destruct (star_generator_inclusions eqb eqb_spec r) as [HA HC].
  pose proof (constraint_generators_empty_main eqb eqb_spec r) as Hallr.
  pose proof (constraint_generators_empty_main eqb eqb_spec (WStar r))
    as Hallstar.
  destruct (main_normal_forms_append_suffix_M eqb eqb_spec
    ars asts crs csts (WStar r) mr
    Hallstar HA HC Hmr) as [p1 [Hp1 Hp1sem]].
  destruct (constraint_main_normal_forms_concat_closed_M eqb eqb_spec
    ars crs cr mr Hallr Hcr Hmr) as [mid [Hmid Hmidsem]].
  destruct (main_normal_forms_append_suffix_M eqb eqb_spec
    ars asts crs csts (WStar r) mid
    Hallstar HA HC Hmid) as [p2 [Hp2 Hp2sem]].
  destruct (main_normal_forms_union_closed_M eqb eqb_spec
    asts csts p1 p2 Hp1 Hp2) as [pm [Hpm Hpmsem]].
  destruct (constraint_normal_forms_monotone_M eqb eqb_spec
    crs csts cr Hallstar HC Hcr) as [qc [Hqc Hqcsem]].
  assert (Hp1raw : lang_equiv
      (rewpla_denote eqb (WConcat rm (WStar r)))
      (rewpla_denote eqb p1)).
  { eapply lang_equiv_trans; [|exact Hp1sem].
    simpl. apply lang_concat_compat;
      [exact Hmrsem|apply lang_equiv_refl]. }
  assert (Hp2raw : lang_equiv
      (rewpla_denote eqb (WConcat (WConcat rc rm) (WStar r)))
      (rewpla_denote eqb p2)).
  { eapply lang_equiv_trans; [|exact Hp2sem].
    simpl. apply lang_concat_compat;
      [|apply lang_equiv_refl].
    eapply lang_equiv_trans; [|exact Hmidsem].
    simpl. apply lang_concat_compat;
      [exact Hcrsem|exact Hmrsem]. }
  simpl. rewrite Dr. simpl. split.
  - exists pm. split; [exact Hpm|].
    eapply lang_equiv_trans.
    + apply lang_union_compat; [exact Hp1raw|exact Hp2raw].
    + exact Hpmsem.
  - exists qc. split; [exact Hqc|].
    eapply lang_equiv_trans; [exact Hcrsem|exact Hqcsem].
Qed.

Lemma lookahead_constraint_term_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r t : rewpla A) :
  In t (constraint_terms (constraint_generators eqb r)) ->
  exists u, In u (constraint_terms
      (constraint_generators eqb (WLookahead r))) /\
    lang_equiv (rewpla_denote eqb (WLookahead t))
      (rewpla_denote eqb u).
Proof.
  intro Ht.
  destruct (lookahead_generator_inclusions eqb eqb_spec r)
    as [HCr _].
  pose proof (constraint_generators_empty_main eqb eqb_spec
    (WLookahead r)) as Hall.
  destruct (constraint_terms_monotone_M eqb eqb_spec
    (constraint_generators eqb r)
    (constraint_generators eqb (WLookahead r))
    t Hall HCr Ht) as [u [Hu Husem]].
  exists u. split; [exact Hu|].
  eapply lang_equiv_trans; [|exact Husem].
  apply rewpla_lookahead_constraint; [exact eqb_spec|].
  exact (constraint_terms_empty_main eqb eqb_spec r t Ht).
Qed.

Lemma lookahead_main_term_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r t : rewpla A) :
  In t (main_terms (continuation_generators eqb r)
      (constraint_generators eqb r)) ->
  exists u, In u (constraint_terms
      (constraint_generators eqb (WLookahead r))) /\
    lang_equiv (rewpla_denote eqb (WLookahead t))
      (rewpla_denote eqb u).
Proof.
  intro Ht. unfold main_terms in Ht.
  apply in_flat_map in Ht as [ss [Hss Hmap]].
  apply in_map_iff in Hmap as [a [<- Ha]].
  destruct (lookahead_generator_inclusions eqb eqb_spec r)
    as [HCr HAr].
  pose proof (constraint_generators_empty_main eqb eqb_spec
    (WLookahead r)) as Hall.
  assert (Hcp : In (constraint_product ss)
      (constraint_terms (constraint_generators eqb r))).
  { unfold constraint_terms. now apply in_map. }
  destruct (constraint_terms_monotone_M eqb eqb_spec
    (constraint_generators eqb r)
    (constraint_generators eqb (WLookahead r))
    (constraint_product ss) Hall HCr Hcp)
    as [cp' [Hcp' Hcp'sem]].
  destruct (constraint_generator_singleton_term_M eqb eqb_spec
    (constraint_generators eqb (WLookahead r))
    (WLookahead a) (HAr a Ha)) as [la' [Hla' Hla'sem]].
  destruct (constraint_terms_product_closed_M eqb eqb_spec
    (constraint_generators eqb (WLookahead r))
    cp' la' Hall Hcp' Hla') as [u [Hu Husem]].
  exists u. split; [exact Hu|].
  eapply lang_equiv_trans.
  - apply positive_lookahead_compat.
    apply smart_concat_correct_M. exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply rewpla_lookahead_constraint_concat;
        [exact eqb_spec|].
      apply constraint_product_empty_main; [exact eqb_spec|].
      intros c Hc.
      exact (constraint_generators_empty_main eqb eqb_spec r c
        ((subset_members_from_source
          (constraint_generators eqb r) ss Hss c) Hc)).
    + eapply lang_equiv_trans; [|exact Husem].
      simpl. apply lang_concat_compat;
        [exact Hcp'sem|exact Hla'sem].
Qed.

Lemma lookahead_union_expression_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (xs : list (rewpla A)) :
  lang_equiv (rewpla_denote eqb (WLookahead (union_expression xs)))
    (rewpla_denote eqb
      (union_expression (map WLookahead xs))).
Proof.
  induction xs as [|x xs IH]; cbn [union_expression map].
  - apply rewpla_lookahead_zero_M.
  - eapply lang_equiv_trans.
    + apply positive_lookahead_compat.
      apply smart_plus_correct_M.
    + eapply lang_equiv_trans.
      * apply rewpla_lookahead_union.
      * eapply lang_equiv_trans.
        -- apply lang_union_compat;
             [apply lang_equiv_refl|exact IH].
        -- change (lang_equiv
             (rewpla_denote eqb
               (WPlus (WLookahead x)
                 (union_expression (map WLookahead xs))))
             (rewpla_denote eqb
               (smart_plus (WLookahead x)
                 (union_expression (map WLookahead xs))))).
           apply lang_equiv_sym, smart_plus_correct_M.
Qed.

Theorem lookahead_main_normal_form_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r n : rewpla A) :
  In n (main_normal_forms (continuation_generators eqb r)
      (constraint_generators eqb r)) ->
  exists u, In u (constraint_normal_forms
      (constraint_generators eqb (WLookahead r))) /\
    lang_equiv (rewpla_denote eqb (WLookahead n))
      (rewpla_denote eqb u).
Proof.
  intro Hn. unfold main_normal_forms in Hn.
  apply in_map_iff in Hn as [ss [<- Hss]].
  set (terms := constraint_terms
    (constraint_generators eqb (WLookahead r))).
  set (lifted := map WLookahead ss).
  assert (Hlifted : forall t, In t lifted ->
      exists u, In u terms /\
        lang_equiv (rewpla_denote eqb t) (rewpla_denote eqb u)).
  { intros t Ht. unfold lifted in Ht.
    apply in_map_iff in Ht as [v [<- Hv]].
    apply lookahead_main_term_represented; [exact eqb_spec|].
    exact ((subset_members_from_source
      (main_terms (continuation_generators eqb r)
        (constraint_generators eqb r)) ss Hss v) Hv). }
  destruct (finite_semantic_representative_list eqb
    terms lifted Hlifted) as [reps [Hreps Hsem]].
  destruct (chosen_union_forms_cover_finite_union eqb eqb_spec
    terms reps Hreps) as [u [Hu Husem]].
  exists u. split; [exact Hu|].
  eapply lang_equiv_trans.
  - apply lookahead_union_expression_M. exact eqb_spec.
  - eapply lang_equiv_trans; [exact Hsem|].
    apply lang_equiv_sym. exact Husem.
Qed.

Lemma constraint_terms_empty_main_general {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs : list (rewpla A)) (t : rewpla A) :
  (forall c, In c cs -> empty_main_language (rewpla_denote eqb c)) ->
  In t (constraint_terms cs) ->
  empty_main_language (rewpla_denote eqb t).
Proof.
  intros Hall Ht. unfold constraint_terms in Ht.
  apply in_map_iff in Ht as [ss [<- Hss]].
  apply constraint_product_empty_main; [exact eqb_spec|].
  intros c Hc. apply Hall.
  exact ((subset_members_from_source cs ss Hss c) Hc).
Qed.

Lemma union_expression_empty_main {A : Type}
    (eqb : A -> A -> bool) (xs : list (rewpla A)) :
  (forall x, In x xs -> empty_main_language (rewpla_denote eqb x)) ->
  empty_main_language (rewpla_denote eqb (union_expression xs)).
Proof.
  intros Hxs. induction xs as [|x xs IH]; simpl.
  - intros p Hp. contradiction.
  - assert (Hx : empty_main_language (rewpla_denote eqb x)).
    { apply Hxs. now left. }
    assert (Htail : empty_main_language
        (rewpla_denote eqb (union_expression xs))).
    { apply IH. intros y Hy. apply Hxs. now right. }
    intros p Hp. apply (proj1 (smart_plus_correct_M eqb
      x (union_expression xs) p)) in Hp.
    simpl in Hp. unfold lang_union in Hp.
    destruct Hp as [Hp|Hp]; [apply Hx|apply Htail]; exact Hp.
Qed.

Theorem constraint_normal_forms_empty_main {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (cs : list (rewpla A)) (n : rewpla A) :
  (forall c, In c cs -> empty_main_language (rewpla_denote eqb c)) ->
  In n (constraint_normal_forms cs) ->
  empty_main_language (rewpla_denote eqb n).
Proof.
  intros Hall Hn. unfold constraint_normal_forms in Hn.
  apply in_map_iff in Hn as [ss [<- Hss]].
  apply union_expression_empty_main. intros t Ht.
  eapply constraint_terms_empty_main_general;
    [exact eqb_spec|exact Hall|].
  exact ((subset_members_from_source
    (constraint_terms cs) ss Hss t) Ht).
Qed.

(** Paper Lemma 4, positive-lookahead case of Eq. (20).  Eq. (35)
    distributes the assertion over the two residual components.  A main
    continuation contributes [LA(A(r))]; an existing assertion stays in
    [C(r)], exactly the generators of [C(LA(r))]. *)
Theorem symbol_derivative_represented_lookahead {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r : rewpla A) :
  symbol_derivative_represented eqb a r ->
  symbol_derivative_represented eqb a (WLookahead r).
Proof.
  unfold symbol_derivative_represented.
  intros [[mr [Hmr Hmrsem]] [cr [Hcr Hcrsem]]].
  destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:Dr.
  simpl in Hmrsem, Hcrsem.
  destruct (lookahead_generator_inclusions eqb eqb_spec r)
    as [HC _].
  pose proof (constraint_generators_empty_main eqb eqb_spec
    (WLookahead r)) as Halltop.
  pose proof (constraint_generators_empty_main eqb eqb_spec r) as Hallr.
  destruct (lookahead_main_normal_form_represented eqb eqb_spec
    r mr Hmr) as [lm [Hlm Hlmsem]].
  destruct (constraint_normal_forms_monotone_M eqb eqb_spec
    (constraint_generators eqb r)
    (constraint_generators eqb (WLookahead r))
    cr Halltop HC Hcr) as [lc [Hlc Hlcsem]].
  destruct (constraint_normal_forms_union_closed_M eqb eqb_spec
    (constraint_generators eqb (WLookahead r))
    lm lc Hlm Hlc) as [qc [Hqc Hqcsem]].
  assert (Hmain : lang_equiv
      (rewpla_denote eqb (WLookahead rm)) (rewpla_denote eqb lm)).
  { eapply lang_equiv_trans; [|exact Hlmsem].
    apply positive_lookahead_compat. exact Hmrsem. }
  assert (Hctx : lang_equiv
      (rewpla_denote eqb (WLookahead rc)) (rewpla_denote eqb lc)).
  { eapply lang_equiv_trans.
    - apply positive_lookahead_compat. exact Hcrsem.
    - eapply lang_equiv_trans; [|exact Hlcsem].
      apply rewpla_lookahead_constraint; [exact eqb_spec|].
      exact (constraint_normal_forms_empty_main eqb eqb_spec
        (constraint_generators eqb r) cr Hallr Hcr). }
  simpl. rewrite Dr. simpl. split.
  - exists WZero. split;
      [apply zero_in_main_normal_forms|apply lang_equiv_refl].
  - exists qc. split; [exact Hqc|].
    eapply lang_equiv_trans.
    + apply rewpla_lookahead_union.
    + eapply lang_equiv_trans.
      * apply lang_union_compat; [exact Hmain|exact Hctx].
      * exact Hqcsem.
Qed.

(** Paper Lemma 4, p.14: both components of every symbolic derivative
    have finite representations in the expression's fixed [N_m] and [N_c]
    families, with complete pair-language equivalence. *)
Theorem symbol_derivative_represented_all {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r : rewpla A) :
  symbol_derivative_represented eqb a r.
Proof.
  induction r as [| |b|r IHr s IHs|r IHr s IHs|r IHr|r IHr].
  - apply symbol_derivative_represented_zero.
  - apply symbol_derivative_represented_epsilon.
  - apply symbol_derivative_represented_atom.
  - apply symbol_derivative_represented_union;
      [exact eqb_spec|exact IHr|exact IHs].
  - apply symbol_derivative_represented_concat;
      [exact eqb_spec|exact IHr|exact IHs].
  - apply symbol_derivative_represented_star;
      [exact eqb_spec|exact IHr].
  - apply symbol_derivative_represented_lookahead;
      [exact eqb_spec|exact IHr].
Qed.

Lemma main_context_normal_forms_combine_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as_ cs : list (rewpla A)) (m c : rewpla A) :
  In m (main_normal_forms as_ cs) ->
  In c (constraint_normal_forms cs) ->
  exists n, In n (normal_forms as_ cs) /\
    lang_equiv (rewpla_denote eqb (WPlus m c))
      (rewpla_denote eqb n).
Proof.
  intros Hm Hc.
  unfold main_normal_forms in Hm.
  unfold constraint_normal_forms in Hc.
  apply in_map_iff in Hm as [sm [<- Hsm]].
  apply in_map_iff in Hc as [sc [<- Hsc]].
  destruct (normal_forms_cover_finite_union eqb eqb_spec
    as_ cs (sm ++ sc)) as [n [Hn Hnsem]].
  { intros t Ht. apply in_app_iff in Ht as [Ht|Ht].
    - unfold term_universe. apply in_app_iff. right.
      exact ((subset_members_from_source
        (main_terms as_ cs) sm Hsm t) Ht).
    - unfold term_universe. apply in_app_iff. left.
      exact ((subset_members_from_source
        (constraint_terms cs) sc Hsc t) Ht). }
  exists n. split; [exact Hn|].
  eapply lang_equiv_trans.
  - apply lang_equiv_sym, union_expression_append_M.
  - apply lang_equiv_sym. exact Hnsem.
Qed.

(** Proposition 6's one-letter base follows directly from Lemma 4. *)
Theorem one_letter_residual_normal_form {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r : rewpla A) :
  exists n, In n (normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) /\
    lang_equiv (rewpla_denote eqb
      (derivative_merge (symbol_derivative_core eqb a r)))
      (rewpla_denote eqb n).
Proof.
  destruct (symbol_derivative_represented_all eqb eqb_spec a r)
    as [[m [Hm Hmsem]] [c [Hc Hcsem]]].
  destruct (symbol_derivative_core eqb a r) as [rm rc] eqn:Dr.
  simpl in Hmsem, Hcsem.
  destruct (main_context_normal_forms_combine_M eqb eqb_spec
    (continuation_generators eqb r)
    (constraint_generators eqb r) m c Hm Hc)
    as [n [Hn Hnsem]].
  exists n. split; [exact Hn|].
  simpl.
  eapply lang_equiv_trans.
  - apply lang_union_compat; [exact Hmsem|exact Hcsem].
  - exact Hnsem.
Qed.

(** Lemma 5's generator steps use Lemma 3 to embed the derivative
    representatives of a continuation or a basic assertion into the fixed
    families of the original expression. *)
Theorem continuation_generator_derivative_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r t : rewpla A) :
  In t (continuation_generators eqb r) ->
  (exists m, In m (main_normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) /\
    lang_equiv (rewpla_denote eqb
      (fst (symbol_derivative_core eqb a t)))
      (rewpla_denote eqb m)) /\
  (exists c, In c (constraint_normal_forms
      (constraint_generators eqb r)) /\
    lang_equiv (rewpla_denote eqb
      (snd (symbol_derivative_core eqb a t)))
      (rewpla_denote eqb c)).
Proof.
  intro Ht.
  destruct (normalized_generator_inclusion eqb eqb_spec r)
    as [Hgen _].
  destruct (Hgen t Ht) as [HA HC].
  destruct (symbol_derivative_represented_all eqb eqb_spec a t)
    as [[m [Hm Hmsem]] [c [Hc Hcsem]]].
  pose proof (constraint_generators_empty_main eqb eqb_spec r)
    as Hall.
  destruct (main_normal_forms_monotone_M eqb eqb_spec
    (continuation_generators eqb t)
    (continuation_generators eqb r)
    (constraint_generators eqb t)
    (constraint_generators eqb r)
    m Hall HA HC Hm) as [m' [Hm' Hm'sem]].
  destruct (constraint_normal_forms_monotone_M eqb eqb_spec
    (constraint_generators eqb t)
    (constraint_generators eqb r)
    c Hall HC Hc) as [c' [Hc' Hc'sem]].
  split.
  - exists m'. split; [exact Hm'|].
    eapply lang_equiv_trans; [exact Hmsem|exact Hm'sem].
  - exists c'. split; [exact Hc'|].
    eapply lang_equiv_trans; [exact Hcsem|exact Hc'sem].
Qed.

Theorem constraint_generator_context_derivative_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r c : rewpla A) :
  In c (constraint_generators eqb r) ->
  exists n, In n (constraint_normal_forms
      (constraint_generators eqb r)) /\
    lang_equiv (rewpla_denote eqb
      (snd (symbol_derivative_core eqb a c)))
      (rewpla_denote eqb n).
Proof.
  intro Hc.
  destruct (normalized_generator_inclusion eqb eqb_spec r)
    as [_ Hgen].
  destruct (Hgen c Hc) as [_ HC].
  destruct (symbol_derivative_represented_all eqb eqb_spec a c)
    as [_ [n [Hn Hnsem]]].
  pose proof (constraint_generators_empty_main eqb eqb_spec r)
    as Hall.
  destruct (constraint_normal_forms_monotone_M eqb eqb_spec
    (constraint_generators eqb c)
    (constraint_generators eqb r)
    n Hall HC Hn) as [n' [Hn' Hn'sem]].
  exists n'. split; [exact Hn'|].
  eapply lang_equiv_trans; [exact Hnsem|exact Hn'sem].
Qed.

(** Lemma 5, constraint-product induction.  Its main derivative is empty;
    the context quotient is represented in the fixed constraint family.
    The quotient statement makes semantic replacement of [smart_concat]
    explicit and avoids depending on the chosen syntax of products. *)
Theorem constraint_product_context_quotient_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r : rewpla A) (ss : list (rewpla A)) :
  (forall c, In c ss -> In c (constraint_generators eqb r)) ->
  exists n, In n (constraint_normal_forms
      (constraint_generators eqb r)) /\
    lang_equiv (context_symbol_quotient a
      (rewpla_denote eqb (constraint_product ss)))
      (rewpla_denote eqb n).
Proof.
  revert ss. induction ss as [|c ss IH]; intro Hmembers.
  - exists WZero. split; [apply zero_in_constraint_normal_forms|].
    simpl. apply context_quotient_one.
  - assert (Hc : In c (constraint_generators eqb r)).
    { apply Hmembers. now left. }
    assert (Hrest : forall d, In d ss ->
        In d (constraint_generators eqb r)).
    { intros d Hd. apply Hmembers. now right. }
    destruct (constraint_generator_context_derivative_represented
      eqb eqb_spec a r c Hc) as [qc [Hqc Hqcsem]].
    destruct (IH Hrest) as [qs [Hqs Hqssem]].
    pose proof (constraint_generators_empty_main eqb eqb_spec r)
      as Hall.
    destruct (constraint_normal_forms_concat_closed_M eqb eqb_spec
      (constraint_generators eqb r) qc qs Hall Hqc Hqs)
      as [q1 [Hq1 Hq1sem]].
    destruct (constraint_normal_forms_lambda_right_M eqb eqb_spec
      (constraint_generators eqb r) (constraint_product ss) qc Hqc)
      as [q2 [Hq2 Hq2sem]].
    destruct (constraint_normal_forms_lambda_left_M eqb eqb_spec
      (constraint_generators eqb r) c qs Hqs)
      as [q3 [Hq3 Hq3sem]].
    destruct (constraint_normal_forms_union_closed_M eqb eqb_spec
      (constraint_generators eqb r) q1 q2 Hq1 Hq2)
      as [q12 [Hq12 Hq12sem]].
    destruct (constraint_normal_forms_union_closed_M eqb eqb_spec
      (constraint_generators eqb r) q12 q3 Hq12 Hq3)
      as [q [Hq Hqsem]].
    destruct (symbol_derivative_core_correct eqb eqb_spec a c)
      as [_ Hcorectx].
    assert (Hhead : lang_equiv
        (context_symbol_quotient a (rewpla_denote eqb c))
        (rewpla_denote eqb qc)).
    { eapply lang_equiv_trans;
        [apply lang_equiv_sym; exact Hcorectx|exact Hqcsem]. }
    assert (Hlambda_c : lang_equiv
        (language_epsilon_part (rewpla_denote eqb c))
        (rewpla_denote eqb (rewpla_lambda c))).
    { apply lang_equiv_sym, rewpla_lambda_correct. exact eqb_spec. }
    assert (Hlambda_ss : lang_equiv
        (language_epsilon_part
          (rewpla_denote eqb (constraint_product ss)))
        (rewpla_denote eqb (rewpla_lambda
          (constraint_product ss)))).
    { apply lang_equiv_sym, rewpla_lambda_correct. exact eqb_spec. }
    assert (H1 : lang_equiv
        (lang_concat eqb
          (context_symbol_quotient a (rewpla_denote eqb c))
          (context_symbol_quotient a
            (rewpla_denote eqb (constraint_product ss))))
        (rewpla_denote eqb q1)).
    { eapply lang_equiv_trans; [|exact Hq1sem].
      simpl. apply lang_concat_compat; [exact Hhead|exact Hqssem]. }
    assert (H2 : lang_equiv
        (lang_concat eqb
          (context_symbol_quotient a (rewpla_denote eqb c))
          (language_epsilon_part
            (rewpla_denote eqb (constraint_product ss))))
        (rewpla_denote eqb q2)).
    { eapply lang_equiv_trans; [|exact Hq2sem].
      simpl. apply lang_concat_compat; [exact Hhead|exact Hlambda_ss]. }
    assert (H3 : lang_equiv
        (lang_concat eqb
          (language_epsilon_part (rewpla_denote eqb c))
          (context_symbol_quotient a
            (rewpla_denote eqb (constraint_product ss))))
        (rewpla_denote eqb q3)).
    { eapply lang_equiv_trans; [|exact Hq3sem].
      simpl. apply lang_concat_compat; [exact Hlambda_c|exact Hqssem]. }
    exists q. split; [exact Hq|].
    eapply lang_equiv_trans.
    + apply context_quotient_compat.
      apply smart_concat_correct_M. exact eqb_spec.
    + eapply lang_equiv_trans.
      * apply context_quotient_concat. exact eqb_spec.
      * eapply lang_equiv_trans.
        -- apply lang_union_compat.
           ++ apply lang_union_compat; [exact H1|exact H2].
           ++ exact H3.
        -- eapply lang_equiv_trans.
           ++ apply lang_union_compat;
                [exact Hq12sem|apply lang_equiv_refl].
           ++ exact Hqsem.
Qed.

(** A zero-width constraint cannot consume the next symbol in its main
    component.  The context component remains zero-width.  These are the
    semantic facts used for every generator and product in paper Lemma 5. *)
Lemma empty_main_main_symbol_quotient {A : Type} a
    (R : constraint_language A) :
  empty_main_language R ->
  lang_equiv (main_symbol_quotient a R) lang_zero.
Proof.
  intros HR [u v]. unfold main_symbol_quotient, lang_zero.
  split; [|contradiction]. intro H.
  specialize (HR (a :: u, v) H). simpl in HR. discriminate.
Qed.

Lemma empty_main_context_symbol_quotient {A : Type} a
    (R : constraint_language A) :
  empty_main_language (context_symbol_quotient a R).
Proof.
  intros [u v] [Hu _]. simpl. exact Hu.
Qed.

Theorem empty_main_symbol_derivative_components {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (c : rewpla A) :
  empty_main_language (rewpla_denote eqb c) ->
  lang_equiv (rewpla_denote eqb
      (fst (symbol_derivative_core eqb a c))) lang_zero /\
  empty_main_language (rewpla_denote eqb
      (snd (symbol_derivative_core eqb a c))).
Proof.
  intro Hc.
  destruct (symbol_derivative_core_correct eqb eqb_spec a c)
    as [Hm Hcontext]. split.
  - eapply lang_equiv_trans; [exact Hm|].
    now apply empty_main_main_symbol_quotient.
  - intros p Hp. apply (proj1 (Hcontext p)) in Hp.
    now apply empty_main_context_symbol_quotient in Hp.
Qed.

Lemma constraint_product_main_quotient_zero {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r : rewpla A) (ss : list (rewpla A)) :
  (forall c, In c ss -> In c (constraint_generators eqb r)) ->
  lang_equiv (main_symbol_quotient a
      (rewpla_denote eqb (constraint_product ss)))
    (rewpla_denote eqb WZero).
Proof.
  intro Hmembers. apply empty_main_main_symbol_quotient.
  apply constraint_product_empty_main; [exact eqb_spec|].
  intros c Hc.
  exact (constraint_generators_empty_main eqb eqb_spec r c
    (Hmembers c Hc)).
Qed.

(** Algebraic heart of the main-term step of Lemma 5.  A zero-width left
    factor contributes no main quotient; every remaining Eq. (13) summand
    is absorbed by the already-proved normal-form operations. *)
Theorem zero_width_product_quotients_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (as_ cs : list (rewpla A)) (left right : rewpla A)
    (c0 cm cc : rewpla A) :
  (forall c, In c cs -> empty_main_language (rewpla_denote eqb c)) ->
  lang_equiv (main_symbol_quotient a (rewpla_denote eqb left))
    (rewpla_denote eqb WZero) ->
  In cc (constraint_normal_forms cs) ->
  lang_equiv (context_symbol_quotient a (rewpla_denote eqb left))
    (rewpla_denote eqb cc) ->
  In cm (main_normal_forms as_ cs) ->
  lang_equiv (main_symbol_quotient a (rewpla_denote eqb right))
    (rewpla_denote eqb cm) ->
  In c0 (constraint_normal_forms cs) ->
  lang_equiv (context_symbol_quotient a (rewpla_denote eqb right))
    (rewpla_denote eqb c0) ->
  (exists m, In m (main_normal_forms as_ cs) /\
    lang_equiv (main_symbol_quotient a
      (rewpla_denote eqb (WConcat left right)))
      (rewpla_denote eqb m)) /\
  (exists q, In q (constraint_normal_forms cs) /\
    lang_equiv (context_symbol_quotient a
      (rewpla_denote eqb (WConcat left right)))
      (rewpla_denote eqb q)).
Proof.
  intros Hall Hmainleft Hcc Hctxleft Hcm Hmainright
    Hc0 Hctxright.
  destruct (constraint_main_normal_forms_concat_closed_M eqb eqb_spec
    as_ cs cc cm Hall Hcc Hcm) as [m2 [Hm2 Hm2sem]].
  destruct (main_normal_forms_lambda_left_M eqb eqb_spec
    as_ cs left cm Hcm) as [m3 [Hm3 Hm3sem]].
  destruct (main_normal_forms_union_closed_M eqb eqb_spec
    as_ cs WZero m2 (zero_in_main_normal_forms as_ cs) Hm2)
    as [m12 [Hm12 Hm12sem]].
  destruct (main_normal_forms_union_closed_M eqb eqb_spec
    as_ cs m12 m3 Hm12 Hm3) as [m [Hm Hmsem]].
  destruct (constraint_normal_forms_concat_closed_M eqb eqb_spec
    cs cc c0 Hall Hcc Hc0) as [q1 [Hq1 Hq1sem]].
  destruct (constraint_normal_forms_lambda_right_M eqb eqb_spec
    cs right cc Hcc) as [q2 [Hq2 Hq2sem]].
  destruct (constraint_normal_forms_lambda_left_M eqb eqb_spec
    cs left c0 Hc0) as [q3 [Hq3 Hq3sem]].
  destruct (constraint_normal_forms_union_closed_M eqb eqb_spec
    cs q1 q2 Hq1 Hq2) as [q12 [Hq12 Hq12sem]].
  destruct (constraint_normal_forms_union_closed_M eqb eqb_spec
    cs q12 q3 Hq12 Hq3) as [q [Hq Hqsem]].
  assert (Hlambda_left : lang_equiv
      (language_epsilon_part (rewpla_denote eqb left))
      (rewpla_denote eqb (rewpla_lambda left))).
  { apply lang_equiv_sym, rewpla_lambda_correct. exact eqb_spec. }
  assert (Hlambda_right : lang_equiv
      (language_epsilon_part (rewpla_denote eqb right))
      (rewpla_denote eqb (rewpla_lambda right))).
  { apply lang_equiv_sym, rewpla_lambda_correct. exact eqb_spec. }
  assert (HM1 : lang_equiv
      (lang_concat eqb
        (main_symbol_quotient a (rewpla_denote eqb left))
        (rewpla_denote eqb right))
      (rewpla_denote eqb WZero)).
  { eapply lang_equiv_trans.
    - apply lang_concat_compat;
        [exact Hmainleft|apply lang_equiv_refl].
    - apply rewpla_concat_zero_left_M. exact eqb_spec. }
  assert (HM2 : lang_equiv
      (lang_concat eqb
        (context_symbol_quotient a (rewpla_denote eqb left))
        (main_symbol_quotient a (rewpla_denote eqb right)))
      (rewpla_denote eqb m2)).
  { eapply lang_equiv_trans; [|exact Hm2sem].
    simpl. apply lang_concat_compat;
      [exact Hctxleft|exact Hmainright]. }
  assert (HM3 : lang_equiv
      (lang_concat eqb
        (language_epsilon_part (rewpla_denote eqb left))
        (main_symbol_quotient a (rewpla_denote eqb right)))
      (rewpla_denote eqb m3)).
  { eapply lang_equiv_trans; [|exact Hm3sem].
    simpl. apply lang_concat_compat;
      [exact Hlambda_left|exact Hmainright]. }
  assert (HC1 : lang_equiv
      (lang_concat eqb
        (context_symbol_quotient a (rewpla_denote eqb left))
        (context_symbol_quotient a (rewpla_denote eqb right)))
      (rewpla_denote eqb q1)).
  { eapply lang_equiv_trans; [|exact Hq1sem].
    simpl. apply lang_concat_compat;
      [exact Hctxleft|exact Hctxright]. }
  assert (HC2 : lang_equiv
      (lang_concat eqb
        (context_symbol_quotient a (rewpla_denote eqb left))
        (language_epsilon_part (rewpla_denote eqb right)))
      (rewpla_denote eqb q2)).
  { eapply lang_equiv_trans; [|exact Hq2sem].
    simpl. apply lang_concat_compat;
      [exact Hctxleft|exact Hlambda_right]. }
  assert (HC3 : lang_equiv
      (lang_concat eqb
        (language_epsilon_part (rewpla_denote eqb left))
        (context_symbol_quotient a (rewpla_denote eqb right)))
      (rewpla_denote eqb q3)).
  { eapply lang_equiv_trans; [|exact Hq3sem].
    simpl. apply lang_concat_compat;
      [exact Hlambda_left|exact Hctxright]. }
  split.
  - exists m. split; [exact Hm|].
    eapply lang_equiv_trans.
    + apply main_quotient_concat. exact eqb_spec.
    + eapply lang_equiv_trans.
      * apply lang_union_compat.
        -- apply lang_union_compat; [exact HM1|exact HM2].
        -- exact HM3.
      * eapply lang_equiv_trans.
        -- apply lang_union_compat;
             [exact Hm12sem|apply lang_equiv_refl].
        -- exact Hmsem.
  - exists q. split; [exact Hq|].
    eapply lang_equiv_trans.
    + apply context_quotient_concat. exact eqb_spec.
    + eapply lang_equiv_trans.
      * apply lang_union_compat.
        -- apply lang_union_compat; [exact HC1|exact HC2].
        -- exact HC3.
      * eapply lang_equiv_trans.
        -- apply lang_union_compat;
             [exact Hq12sem|apply lang_equiv_refl].
        -- exact Hqsem.
Qed.

Theorem main_term_quotients_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r : rewpla A) (ss : list (rewpla A)) (t : rewpla A) :
  In ss (subsets (constraint_generators eqb r)) ->
  In t (continuation_generators eqb r) ->
  (exists m, In m (main_normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) /\
    lang_equiv (main_symbol_quotient a
      (rewpla_denote eqb
        (smart_concat (constraint_product ss) t)))
      (rewpla_denote eqb m)) /\
  (exists c, In c (constraint_normal_forms
      (constraint_generators eqb r)) /\
    lang_equiv (context_symbol_quotient a
      (rewpla_denote eqb
        (smart_concat (constraint_product ss) t)))
      (rewpla_denote eqb c)).
Proof.
  intros Hss Ht.
  assert (Hmembers : forall c, In c ss ->
      In c (constraint_generators eqb r)).
  { intros c Hc. exact ((subset_members_from_source
      (constraint_generators eqb r) ss Hss c) Hc). }
  destruct (constraint_product_context_quotient_represented
    eqb eqb_spec a r ss Hmembers) as [cp [Hcp Hcpsem]].
  pose proof (constraint_product_main_quotient_zero
    eqb eqb_spec a r ss Hmembers) as Hcpzero.
  destruct (continuation_generator_derivative_represented
    eqb eqb_spec a r t Ht)
    as [[mt [Hmt Hmtsem]] [ct [Hct Hctsem]]].
  destruct (symbol_derivative_core_correct eqb eqb_spec a t)
    as [Hmtcore Hctcore].
  assert (Hmain_t : lang_equiv
      (main_symbol_quotient a (rewpla_denote eqb t))
      (rewpla_denote eqb mt)).
  { eapply lang_equiv_trans;
      [apply lang_equiv_sym; exact Hmtcore|exact Hmtsem]. }
  assert (Hcontext_t : lang_equiv
      (context_symbol_quotient a (rewpla_denote eqb t))
      (rewpla_denote eqb ct)).
  { eapply lang_equiv_trans;
      [apply lang_equiv_sym; exact Hctcore|exact Hctsem]. }
  pose proof (constraint_generators_empty_main eqb eqb_spec r)
    as Hall.
  destruct (@zero_width_product_quotients_represented A
    eqb eqb_spec a
    (continuation_generators eqb r) (constraint_generators eqb r)
    (constraint_product ss) t ct mt cp
    Hall Hcpzero Hcp Hcpsem Hmt Hmain_t Hct Hcontext_t)
    as [[m [Hm Hmsem]] [c [Hc Hcsem]]].
  split.
  - exists m. split; [exact Hm|].
    eapply lang_equiv_trans; [|exact Hmsem].
    apply main_quotient_compat.
    apply smart_concat_correct_M. exact eqb_spec.
  - exists c. split; [exact Hc|].
    eapply lang_equiv_trans; [|exact Hcsem].
    apply context_quotient_compat.
    apply smart_concat_correct_M. exact eqb_spec.
Qed.

Theorem term_universe_quotients_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r term : rewpla A) :
  In term (term_universe
      (continuation_generators eqb r) (constraint_generators eqb r)) ->
  (exists m, In m (main_normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) /\
    lang_equiv (main_symbol_quotient a (rewpla_denote eqb term))
      (rewpla_denote eqb m)) /\
  (exists c, In c (constraint_normal_forms
      (constraint_generators eqb r)) /\
    lang_equiv (context_symbol_quotient a (rewpla_denote eqb term))
      (rewpla_denote eqb c)).
Proof.
  unfold term_universe. intro Hterm.
  apply in_app_iff in Hterm as [Hterm|Hterm].
  - unfold constraint_terms in Hterm.
    apply in_map_iff in Hterm as [ss [<- Hss]].
    assert (Hmembers : forall c, In c ss ->
        In c (constraint_generators eqb r)).
    { intros c Hc. exact ((subset_members_from_source
        (constraint_generators eqb r) ss Hss c) Hc). }
    destruct (constraint_product_context_quotient_represented
      eqb eqb_spec a r ss Hmembers) as [c [Hc Hcsem]].
    split.
    + exists WZero. split;
        [apply zero_in_main_normal_forms|].
      exact (constraint_product_main_quotient_zero
        eqb eqb_spec a r ss Hmembers).
    + exists c. now split.
  - unfold main_terms in Hterm.
    apply in_flat_map in Hterm as [ss [Hss Hmap]].
    apply in_map_iff in Hmap as [t [<- Ht]].
    apply main_term_quotients_represented;
      [exact eqb_spec|exact Hss|exact Ht].
Qed.

Theorem finite_union_quotients_represented {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r : rewpla A) (ss : list (rewpla A)) :
  (forall t, In t ss -> In t (term_universe
      (continuation_generators eqb r) (constraint_generators eqb r))) ->
  (exists m, In m (main_normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) /\
    lang_equiv (main_symbol_quotient a
      (rewpla_denote eqb (union_expression ss)))
      (rewpla_denote eqb m)) /\
  (exists c, In c (constraint_normal_forms
      (constraint_generators eqb r)) /\
    lang_equiv (context_symbol_quotient a
      (rewpla_denote eqb (union_expression ss)))
      (rewpla_denote eqb c)).
Proof.
  revert ss. induction ss as [|x ss IH]; intro Hmembers.
  - split; exists WZero;
      split; [apply zero_in_main_normal_forms|apply main_quotient_zero|
              apply zero_in_constraint_normal_forms|apply context_quotient_zero].
  - assert (Hx : In x (term_universe
        (continuation_generators eqb r) (constraint_generators eqb r))).
    { apply Hmembers. now left. }
    assert (Htail : forall t, In t ss ->
        In t (term_universe
          (continuation_generators eqb r) (constraint_generators eqb r))).
    { intros t Ht. apply Hmembers. now right. }
    destruct (term_universe_quotients_represented
      eqb eqb_spec a r x Hx)
      as [[mx [Hmx Hmxsem]] [cx [Hcx Hcxsem]]].
    destruct (IH Htail)
      as [[ms [Hms Hmssem]] [cs [Hcs Hcssem]]].
    destruct (main_normal_forms_union_closed_M eqb eqb_spec
      (continuation_generators eqb r) (constraint_generators eqb r)
      mx ms Hmx Hms) as [m [Hm Hmsem]].
    destruct (constraint_normal_forms_union_closed_M eqb eqb_spec
      (constraint_generators eqb r) cx cs Hcx Hcs)
      as [c [Hc Hcsem]].
    split.
    + exists m. split; [exact Hm|].
      eapply lang_equiv_trans.
      * apply main_quotient_compat.
        apply smart_plus_correct_M.
      * eapply lang_equiv_trans.
        -- apply main_quotient_union.
        -- eapply lang_equiv_trans.
           ++ apply lang_union_compat;
                [exact Hmxsem|exact Hmssem].
           ++ exact Hmsem.
    + exists c. split; [exact Hc|].
      eapply lang_equiv_trans.
      * apply context_quotient_compat.
        apply smart_plus_correct_M.
      * eapply lang_equiv_trans.
        -- apply context_quotient_union.
        -- eapply lang_equiv_trans.
           ++ apply lang_union_compat;
                [exact Hcxsem|exact Hcssem].
           ++ exact Hcsem.
Qed.

(** Paper Lemma 5, p.14: the entire finite [N(r)] family is closed under
    one symbolic derivative, modulo complete pair-language semantics. *)
Theorem normal_forms_symbol_derivative_closed_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (r e : rewpla A) :
  In e (normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) ->
  exists e', In e' (normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) /\
    lang_equiv (rewpla_denote eqb
      (derivative_merge (symbol_derivative_core eqb a e)))
      (rewpla_denote eqb e').
Proof.
  intro He. unfold normal_forms in He.
  apply in_map_iff in He as [ss [<- Hss]].
  assert (Hmembers : forall t, In t ss ->
      In t (term_universe
        (continuation_generators eqb r)
        (constraint_generators eqb r))).
  { intros t Ht. exact ((subset_members_from_source
      (term_universe (continuation_generators eqb r)
        (constraint_generators eqb r)) ss Hss t) Ht). }
  destruct (finite_union_quotients_represented eqb eqb_spec
    a r ss Hmembers)
    as [[m [Hm Hmsem]] [c [Hc Hcsem]]].
  destruct (symbol_derivative_core_correct eqb eqb_spec
    a (union_expression ss)) as [Hcorem Hcorec].
  destruct (main_context_normal_forms_combine_M eqb eqb_spec
    (continuation_generators eqb r)
    (constraint_generators eqb r) m c Hm Hc)
    as [e' [He' He'sem]].
  exists e'. split; [exact He'|].
  destruct (symbol_derivative_core eqb a (union_expression ss))
    as [dm dc] eqn:D.
  simpl in Hcorem, Hcorec.
  simpl.
  eapply lang_equiv_trans.
  - apply lang_union_compat.
    + eapply lang_equiv_trans; [exact Hcorem|exact Hmsem].
    + eapply lang_equiv_trans; [exact Hcorec|exact Hcsem].
  - exact He'sem.
Qed.

Lemma merged_symbol_derivative_congruent_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    a (u v : rewpla A) :
  lang_equiv (rewpla_denote eqb u) (rewpla_denote eqb v) ->
  lang_equiv (rewpla_denote eqb
      (derivative_merge (symbol_derivative_core eqb a u)))
    (rewpla_denote eqb
      (derivative_merge (symbol_derivative_core eqb a v))).
Proof.
  intro Huv. eapply lang_equiv_trans.
  - apply symbol_derivative_core_merge_correct. exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply rewpla_semantic_step_congruent. exact Huv.
    + apply lang_equiv_sym, symbol_derivative_core_merge_correct.
      exact eqb_spec.
Qed.

Lemma word_derivative_app {A : Type}
    (eqb : A -> A -> bool) (u v : list A) (r : rewpla A) :
  word_derivative eqb (u ++ v) r =
  word_derivative eqb v (word_derivative eqb u r).
Proof.
  revert r. induction u as [|a u IH]; intro r; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma word_derivative_congruent_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (w : list A) (u v : rewpla A) :
  lang_equiv (rewpla_denote eqb u) (rewpla_denote eqb v) ->
  lang_equiv (rewpla_denote eqb (word_derivative eqb w u))
    (rewpla_denote eqb (word_derivative eqb w v)).
Proof.
  intro Huv. eapply lang_equiv_trans.
  - apply word_derivative_correct. exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply pair_language_word_quotient_compat. exact Huv.
    + apply lang_equiv_sym, word_derivative_correct. exact eqb_spec.
Qed.

Theorem normal_forms_word_derivative_closed_M {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r e : rewpla A) (w : list A) :
  In e (normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) ->
  exists e', In e' (normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) /\
    lang_equiv (rewpla_denote eqb (word_derivative eqb w e))
      (rewpla_denote eqb e').
Proof.
  revert e. induction w as [|a w IH]; intros e He.
  - exists e. split; [exact He|apply lang_equiv_refl].
  - destruct (normal_forms_symbol_derivative_closed_M eqb eqb_spec
      a r e He) as [m [Hm Hmsem]].
    destruct (IH m Hm) as [e' [He' He'sem]].
    exists e'. split; [exact He'|]. simpl.
    eapply lang_equiv_trans.
    + apply word_derivative_congruent_M;
        [exact eqb_spec|exact Hmsem].
    + exact He'sem.
Qed.

(** Paper Proposition 6, p.14: every nonempty-word residual has a
    representative in the same finite [N(r)] family. *)
Theorem nonempty_word_residual_normal_form {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) (w : list A) :
  w <> [] ->
  exists e, In e (normal_forms
      (continuation_generators eqb r) (constraint_generators eqb r)) /\
    lang_equiv (rewpla_denote eqb (word_derivative eqb w r))
      (rewpla_denote eqb e).
Proof.
  destruct w as [|a w]; intro Hnonempty; [contradiction|].
  destruct (one_letter_residual_normal_form eqb eqb_spec a r)
    as [e [He Hesem]].
  destruct (normal_forms_word_derivative_closed_M eqb eqb_spec
    r e w He) as [e' [He' He'equiv]].
  exists e'. split; [exact He'|]. simpl.
  eapply lang_equiv_trans.
  - apply word_derivative_congruent_M;
      [exact eqb_spec|exact Hesem].
  - exact He'equiv.
Qed.

(** Mechanization extension to paper Eq. (39)--(40): quotient the finite
    normal-form list by executable union ACI representatives.  The resulting
    list is duplicate-free, retains an [M]-equivalent image of every raw
    normal form, and cannot exceed the paper's raw cardinality bound. *)
Definition canonical_normal_forms {A : Type} eqb atom_code
    (as_ cs : list (rewpla A)) : list (rewpla A) :=
  nodupb (rewpla_eqb eqb)
    (map (rewpla_aci_normalize eqb atom_code) (normal_forms as_ cs)).

Theorem canonical_normal_forms_nodup {A : Type} eqb atom_code
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as_ cs : list (rewpla A)) :
  NoDup (canonical_normal_forms eqb atom_code as_ cs).
Proof.
  unfold canonical_normal_forms. apply nodupb_nodup.
  apply rewpla_eqb_spec. exact eqb_spec.
Qed.

Theorem canonical_normal_forms_length_bound {A : Type} eqb atom_code
    (as_ cs : list (rewpla A)) :
  length (canonical_normal_forms eqb atom_code as_ cs) <=
    2 ^ ((length as_ + 1) * 2 ^ length cs).
Proof.
  unfold canonical_normal_forms.
  eapply Nat.le_trans; [apply nodupb_length_le|].
  rewrite length_map, normal_forms_length. reflexivity.
Qed.

Theorem canonical_normal_forms_semantic_coverage {A : Type} eqb atom_code
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (as_ cs : list (rewpla A)) (r : rewpla A) :
  In r (normal_forms as_ cs) ->
  exists n, In n (canonical_normal_forms eqb atom_code as_ cs) /\
    lang_equiv (rewpla_denote eqb n) (rewpla_denote eqb r).
Proof.
  intro Hr. exists (rewpla_aci_normalize eqb atom_code r). split.
  - unfold canonical_normal_forms.
    apply (proj2 (nodupb_in_iff (rewpla_eqb eqb)
      (rewpla_eqb_spec eqb eqb_spec) _ _)).
    apply in_map. exact Hr.
  - apply rewpla_aci_normalize_correct. exact eqb_spec.
Qed.

Lemma succ_le_two_power n : n + 1 <= 2 ^ n.
Proof. induction n; simpl; lia. Qed.

Lemma pow_two_monotone n m : n <= m -> 2 ^ n <= 2 ^ m.
Proof.
  intro H. induction H; [reflexivity|]. simpl. lia.
Qed.

(** Numerical half of paper Theorem 3 / Eq. (43). *)
Theorem representative_exponent_bound p q n :
  p + q <= n -> (p + 1) * 2 ^ q <= 2 ^ n.
Proof.
  intro Hpq.
  eapply Nat.le_trans.
  - apply Nat.mul_le_mono_r. apply succ_le_two_power.
  - rewrite <- Nat.pow_add_r. now apply pow_two_monotone.
Qed.

Theorem paper_double_exponential_bound p q n :
  p + q <= n ->
  1 + 2 ^ ((p + 1) * 2 ^ q) <= 1 + 2 ^ (2 ^ n).
Proof.
  intro H. apply Nat.add_le_mono_l, pow_two_monotone.
  now apply representative_exponent_bound.
Qed.

(** Paper Eq. (43), p.14, numerical bound instantiated to the executable
    ACI-quotiented candidate universe of a concrete expression. *)
Theorem canonical_normal_forms_general_bound {A : Type} eqb atom_code
    (r : rewpla A) :
  1 + length (canonical_normal_forms eqb atom_code
        (continuation_generators eqb r) (constraint_generators eqb r)) <=
  1 + 2 ^ (2 ^ rewpla_nodes r).
Proof.
  eapply Nat.le_trans.
  - apply Nat.add_le_mono_l, canonical_normal_forms_length_bound.
  - apply paper_double_exponential_bound.
    eapply Nat.le_trans; [apply generator_length_bound|].
    apply rewpla_width_le_nodes.
Qed.

(** The exact width parameter n of paper Eq. (43), rather than the looser
    syntax-node parameter m. *)
Theorem canonical_normal_forms_width_bound {A : Type} eqb atom_code
    (r : rewpla A) :
  1 + length (canonical_normal_forms eqb atom_code
        (continuation_generators eqb r) (constraint_generators eqb r)) <=
  1 + 2 ^ (2 ^ rewpla_width r).
Proof.
  eapply Nat.le_trans.
  - apply Nat.add_le_mono_l, canonical_normal_forms_length_bound.
  - apply paper_double_exponential_bound, generator_length_bound.
Qed.

(** Paper Theorem 3 / Eq. (43): an explicit finite list covers every
    semantic derivative class.  The initial expression covers the empty
    word; Proposition 6 and ACI normalization cover every nonempty word.
    Consequently the quotient [Der_M(r)] has no more classes than this
    list has entries. *)
Theorem semantic_derivatives_finite_cover_and_bound {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  exists states : list (rewpla A),
    length states <=
      1 + 2 ^ ((length (continuation_generators eqb r) + 1) *
        2 ^ length (constraint_generators eqb r)) /\
    length states <= 1 + 2 ^ (2 ^ rewpla_width r) /\
    forall w : list A, exists e,
      In e states /\
      lang_equiv (rewpla_denote eqb (word_derivative eqb w r))
        (rewpla_denote eqb e).
Proof.
  set (canon := canonical_normal_forms eqb atom_code
    (continuation_generators eqb r) (constraint_generators eqb r)).
  exists (r :: canon). repeat split.
  - simpl. apply le_n_S.
    unfold canon. apply canonical_normal_forms_length_bound.
  - change (1 + length canon <= 1 + 2 ^ (2 ^ rewpla_width r)).
    unfold canon. apply canonical_normal_forms_width_bound.
  - intro w. destruct w as [|a w].
    + exists r. split; [now left|apply lang_equiv_refl].
    + destruct (@nonempty_word_residual_normal_form A
        eqb eqb_spec r (a :: w) ltac:(discriminate))
        as [raw [Hraw Hrawsem]].
      destruct (canonical_normal_forms_semantic_coverage
        eqb atom_code eqb_spec
        (continuation_generators eqb r)
        (constraint_generators eqb r) raw Hraw)
        as [e [He Hesem]].
      exists e. split; [right; exact He|].
      eapply lang_equiv_trans; [exact Hrawsem|].
      apply lang_equiv_sym. exact Hesem.
Qed.

(** Paper Eq. (47): a uniform bound on the number of constraint generators
    turns the representative count into a single-exponential function of
    alphabetic width. *)
Theorem bounded_constraint_exponential_bound p q n qmax :
  p + q <= n -> q <= qmax ->
  1 + 2 ^ ((p + 1) * 2 ^ q) <=
    1 + 2 ^ ((n + 1) * 2 ^ qmax).
Proof.
  intros Hsize Hq. apply Nat.add_le_mono_l, pow_two_monotone.
  apply Nat.mul_le_mono; [lia|].
  now apply pow_two_monotone.
Qed.

Theorem semantic_derivatives_bounded_constraint_cover {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) qmax :
  length (constraint_generators eqb r) <= qmax ->
  exists states : list (rewpla A),
    length states <=
      1 + 2 ^ ((rewpla_width r + 1) * 2 ^ qmax) /\
    forall w : list A, exists e,
      In e states /\
      lang_equiv (rewpla_denote eqb (word_derivative eqb w r))
        (rewpla_denote eqb e).
Proof.
  intro Hq.
  destruct (semantic_derivatives_finite_cover_and_bound
    eqb atom_code eqb_spec r) as [states [Hexact [_ Hcover]]].
  exists states. split; [|exact Hcover].
  eapply Nat.le_trans; [exact Hexact|].
  apply bounded_constraint_exponential_bound;
    [apply generator_length_bound|exact Hq].
Qed.

(** Numerical form of the restricted paper Eq. (48), for a constraint
    generator family of size at most one. *)
Lemma at_most_one_constraint_exponent p q n :
  p + q <= n -> q <= 1 -> 1 <= n ->
  (p + 1) * 2 ^ q <= 2 * n.
Proof.
  intros Hpq Hq Hn. destruct q as [|[|q]]; simpl in *; lia.
Qed.

Theorem canonical_normal_forms_single_constraint_bound {A : Type}
    eqb atom_code (r : rewpla A) :
  length (constraint_generators eqb r) <= 1 ->
  1 <= rewpla_width r ->
  1 + length (canonical_normal_forms eqb atom_code
        (continuation_generators eqb r) (constraint_generators eqb r)) <=
  2 ^ (2 * rewpla_width r + 1).
Proof.
  intros Hq Hn. eapply Nat.le_trans.
  - apply Nat.add_le_mono_l, canonical_normal_forms_length_bound.
  - eapply Nat.le_trans with (m := 1 + 2 ^ (2 * rewpla_width r)).
    + apply Nat.add_le_mono_l, pow_two_monotone.
      apply at_most_one_constraint_exponent;
        [apply generator_length_bound|exact Hq|exact Hn].
    + replace (2 ^ (2 * rewpla_width r + 1)) with
        (2 * 2 ^ (2 * rewpla_width r)).
      * assert (Hpow : 2 ^ (2 * rewpla_width r) <> 0).
        { apply Nat.pow_nonzero. lia. }
        lia.
      * rewrite Nat.pow_add_r. simpl. lia.
Qed.

(** Paper Eq. (48), now applied to the actual semantic residual cover rather
    than only to the candidate list. *)
Theorem semantic_derivatives_single_constraint_cover_bound {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (r : rewpla A) :
  length (constraint_generators eqb r) <= 1 ->
  1 <= rewpla_width r ->
  exists states : list (rewpla A),
    length states <= 2 ^ (2 * rewpla_width r + 1) /\
    forall w : list A, exists e,
      In e states /\
      lang_equiv (rewpla_denote eqb (word_derivative eqb w r))
        (rewpla_denote eqb e).
Proof.
  intros Hq Hn.
  destruct (semantic_derivatives_finite_cover_and_bound
    eqb atom_code eqb_spec r) as [states [Hexact [_ Hcover]]].
  exists states. split; [|exact Hcover].
  eapply Nat.le_trans; [exact Hexact|].
  eapply Nat.le_trans with
      (m := 1 + 2 ^ (2 * rewpla_width r)).
  - apply Nat.add_le_mono_l, pow_two_monotone.
    apply at_most_one_constraint_exponent;
      [apply generator_length_bound|exact Hq|exact Hn].
  - replace (2 ^ (2 * rewpla_width r + 1)) with
      (2 * 2 ^ (2 * rewpla_width r)).
    + assert (Hpow : 2 ^ (2 * rewpla_width r) <> 0).
      { apply Nat.pow_nonzero. lia. }
      lia.
    + rewrite Nat.pow_add_r. simpl. lia.
Qed.

(** A finite, executable closure certificate for the general derivative
    explorer.  Equality here is structural equality after normalization; it
    is a sound, intentionally finer test than pair-language equivalence.
    If it succeeds, every explored transition and every further derivative
    stays in the finite list. Lemmas 4--5 establish semantic finiteness; they
    do not assert termination with this finer structural equality test. *)
Definition rewpla_states_closedb {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (alphabet : list A) (states : list (rewpla A)) : bool :=
  forallb (fun q => forallb (fun a =>
    existsb (rewpla_eqb eqb
      (rewpla_normalized_symbol_step eqb atom_code a q)) states)
    alphabet) states.

Theorem rewpla_states_closedb_sound {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    alphabet states :
  rewpla_states_closedb eqb atom_code alphabet states = true ->
  forall q a, In q states -> In a alphabet ->
    In (rewpla_normalized_symbol_step eqb atom_code a q) states.
Proof.
  unfold rewpla_states_closedb. intros H q a Hq Ha.
  apply forallb_forall with (x := q) in H; [|exact Hq].
  apply forallb_forall with (x := a) in H; [|exact Ha].
  apply existsb_exists in H as [t [Ht Heq]].
  apply (proj1 (rewpla_eqb_spec eqb eqb_spec _ _)) in Heq.
  now subst t.
Qed.

Theorem rewpla_states_closedb_all_words {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    alphabet states :
  rewpla_states_closedb eqb atom_code alphabet states = true ->
  forall (r : rewpla A) w, In r states ->
    (forall a, In a w -> In a alphabet) ->
    In (rewpla_normalized_word_step eqb atom_code w r) states.
Proof.
  intros Hclosed r w. revert r.
  induction w as [|a w IH]; intros r Hr Hw; simpl; [exact Hr|].
  apply IH.
  - apply (rewpla_states_closedb_sound eqb atom_code eqb_spec
      alphabet states Hclosed r a Hr). apply Hw. now left.
  - intros b Hb. apply Hw. now right.
Qed.

(** A membership-and-acceptance theorem for every saturated generic table,
    including cases with more than two assertions and arbitrary finite
    alphabets.  The proof uses the actual extracted normalized derivative,
    and no periodic or example-specific model. *)
Theorem rewpla_saturated_dfa_accept_correct {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    alphabet states (r : rewpla A) :
  rewpla_states_closedb eqb atom_code alphabet states = true ->
  In r states ->
  forall w, (forall a, In a w -> In a alphabet) ->
    In (rewpla_normalized_word_step eqb atom_code w r) states /\
    (rewpla_nullable (rewpla_normalized_word_step eqb atom_code w r) = true
      <-> rewpla_language eqb r w).
Proof.
  intros Hclosed Hr w Hw. split.
  - eapply rewpla_states_closedb_all_words; eauto.
  - apply rewpla_normalized_word_step_accept_correct; exact eqb_spec.
Qed.

(** The same finite certificate, now for the Eq. (35) normalization used by
    the generic executable.  The checked transition remains a literal
    derivative of the current state, so shortest-witness replay is exact. *)
Definition rewpla_paper_states_closedb {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (alphabet : list A) (states : list (rewpla A)) : bool :=
  forallb (fun q => forallb (fun a =>
    existsb (rewpla_eqb eqb (rewpla_paper_symbol_step
      eqb atom_code a q)) states) alphabet) states.

Theorem rewpla_paper_states_closedb_sound {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    alphabet states :
  rewpla_paper_states_closedb eqb atom_code alphabet states = true ->
  forall q a, In q states -> In a alphabet ->
    In (rewpla_paper_symbol_step eqb atom_code a q) states.
Proof.
  unfold rewpla_paper_states_closedb. intros H q a Hq Ha.
  apply forallb_forall with (x := q) in H; [|exact Hq].
  apply forallb_forall with (x := a) in H; [|exact Ha].
  apply existsb_exists in H as [t [Ht Heq]].
  apply (proj1 (rewpla_eqb_spec eqb eqb_spec _ _)) in Heq.
  now subst t.
Qed.

Theorem rewpla_paper_states_closedb_all_words {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    alphabet states :
  rewpla_paper_states_closedb eqb atom_code alphabet states = true ->
  forall (r : rewpla A) w, In r states ->
    (forall a, In a w -> In a alphabet) ->
    In (rewpla_paper_word_step eqb atom_code w r) states.
Proof.
  intros Hclosed r w. revert r.
  induction w as [|a w IH]; intros r Hr Hw; simpl; [exact Hr|].
  apply IH.
  - apply (rewpla_paper_states_closedb_sound eqb atom_code eqb_spec
      alphabet states Hclosed r a Hr). apply Hw. now left.
  - intros b Hb. apply Hw. now right.
Qed.

Theorem rewpla_paper_saturated_dfa_accept_correct {A : Type}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    alphabet states (r : rewpla A) :
  rewpla_paper_states_closedb eqb atom_code alphabet states = true ->
  In r states ->
  forall w, (forall a, In a w -> In a alphabet) ->
    In (rewpla_paper_word_step eqb atom_code w r) states /\
    (rewpla_nullable (rewpla_paper_word_step eqb atom_code w r) = true
      <-> rewpla_language eqb r w).
Proof.
  intros Hclosed Hr w Hw. split.
  - eapply rewpla_paper_states_closedb_all_words; eauto.
  - apply rewpla_paper_word_step_accept_correct; exact eqb_spec.
Qed.

(** Mechanization extension: distinguish consuming the main component from
    discharging its stored context.  A canonical pair is encoded by all main
    labels followed by all context labels. *)
Inductive pair_step (A : Type) :=
| MainStep (a : A)
| ContextStep (a : A).

Arguments MainStep {A} _.
Arguments ContextStep {A} _.

Definition tagged_symbol_quotient {A} (x : pair_step A)
  (R : constraint_language A) : constraint_language A :=
  match x with
  | MainStep a => main_symbol_quotient a R
  | ContextStep a => context_symbol_quotient a R
  end.

Fixpoint tagged_word_quotient {A} (w : list (pair_step A))
  (R : constraint_language A) : constraint_language A :=
  match w with
  | [] => R
  | x :: xs => tagged_word_quotient xs (tagged_symbol_quotient x R)
  end.

Definition encode_pair {A} (p : string_constraint A) : list (pair_step A) :=
  map MainStep (fst p) ++ map ContextStep (snd p).

Lemma tagged_main_quotient {A} (u : word A) R x y :
  tagged_word_quotient (map MainStep u) R (x, y) <-> R (u ++ x, y).
Proof.
  revert R x y. induction u as [|a u IH]; intros R x y; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma tagged_context_quotient {A} (v : word A) R y :
  tagged_word_quotient (map ContextStep v) R ([], y) <->
  R ([], v ++ y).
Proof.
  revert R y. induction v as [|a v IH]; intros R y; simpl.
  - reflexivity.
  - rewrite IH. unfold context_symbol_quotient. simpl. tauto.
Qed.

Lemma tagged_word_quotient_app {A} (u v : list (pair_step A)) R :
  tagged_word_quotient (u ++ v) R =
  tagged_word_quotient v (tagged_word_quotient u R).
Proof. revert R. induction u; intros; simpl; [reflexivity|now rewrite IHu]. Qed.

(** Canonical tagged-word membership is exactly full pair-language
    membership.  This is why a decision procedure over both tag kinds tests
    [M]-equivalence, rather than only projected [L_pi]-equivalence. *)
Theorem encode_pair_acceptance {A} (R : constraint_language A) u v :
  tagged_word_quotient (encode_pair (u, v)) R ([], []) <-> R (u, v).
Proof.
  unfold encode_pair. simpl. rewrite tagged_word_quotient_app.
  rewrite tagged_context_quotient. simpl. rewrite tagged_main_quotient.
  repeat rewrite app_nil_r. reflexivity.
Qed.

(** A generic on-demand worklist.  Unlike enumerating a powerset universe,
    it stores only states actually reached before the supplied finite bound.
    Instantiations prove separately that their bound suffices. *)
Section Worklist.
Context {State Label : Type}.
Variable state_eqb : State -> State -> bool.
Variable labels : list Label.
Variable step : State -> Label -> State.

Definition add_fresh (x : State) (seen todo : list State)
  : list State * list State :=
  if existsb (state_eqb x) seen then (seen, todo)
  else (x :: seen, todo ++ [x]).

Fixpoint add_successors (xs : list State) (seen todo : list State)
  : list State * list State :=
  match xs with
  | [] => (seen, todo)
  | x :: xs' =>
      let '(seen', todo') := add_fresh x seen todo in
      add_successors xs' seen' todo'
  end.

Fixpoint explore (fuel : nat) (seen todo : list State) : list State :=
  match fuel, todo with
  | 0, _ => seen
  | S fuel', [] => seen
  | S fuel', q :: todo' =>
      let succs := map (step q) labels in
      let '(seen', todo'') := add_successors succs seen todo' in
      explore fuel' seen' todo''
  end.

Fixpoint explore_result (fuel : nat) (seen todo : list State)
  : list State * list State :=
  match fuel, todo with
  | 0, _ => (seen, todo)
  | S _, [] => (seen, [])
  | S fuel', q :: todo' =>
      let succs := map (step q) labels in
      let '(seen', todo'') := add_successors succs seen todo' in
      explore_result fuel' seen' todo''
  end.

Definition derivative_states (fuel : nat) (initial : State) : list State :=
  explore fuel [initial] [initial].

Definition derivative_state_count (fuel : nat) (initial : State) : nat :=
  length (derivative_states fuel initial).

Hypothesis state_eqb_spec :
  forall x y, state_eqb x y = true <-> x = y.

Lemma existsb_state_eqb x xs :
  existsb (state_eqb x) xs = true <-> In x xs.
Proof.
  rewrite existsb_exists. split.
  - intros [y [Hy Hxy]]. apply state_eqb_spec in Hxy. now subst y.
  - intro Hx. exists x. split; [exact Hx|]. apply state_eqb_spec. reflexivity.
Qed.

Lemma add_fresh_nodup x seen todo :
  NoDup seen -> NoDup (fst (add_fresh x seen todo)).
Proof.
  intro Hseen. unfold add_fresh.
  destruct (existsb (state_eqb x) seen) eqn:Hx; simpl; [exact Hseen|].
  constructor; [|exact Hseen].
  intro Hin. apply (proj2 (existsb_state_eqb x seen)) in Hin. congruence.
Qed.

Lemma add_successors_nodup xs seen todo :
  NoDup seen ->
  NoDup (fst (add_successors xs seen todo)).
Proof.
  revert seen todo. induction xs as [|x xs IH]; intros seen todo Hseen; simpl.
  - exact Hseen.
  - unfold add_fresh. destruct (existsb (state_eqb x) seen) eqn:Hx.
    + now apply IH.
    + apply IH. constructor; [|exact Hseen].
      intro Hin. apply (proj2 (existsb_state_eqb x seen)) in Hin. congruence.
Qed.

Lemma add_successors_result_nodup xs seen todo seen' todo' :
  add_successors xs seen todo = (seen', todo') ->
  NoDup seen -> NoDup seen'.
Proof.
  revert seen todo seen' todo'.
  induction xs as [|x xs IH]; intros seen todo seen' todo' Hresult Hseen; simpl in Hresult.
  - inversion Hresult; subst. exact Hseen.
  - unfold add_fresh in Hresult.
    destruct (existsb (state_eqb x) seen) eqn:Hx.
    + eapply IH; eauto.
    + eapply IH; [exact Hresult|]. constructor; [|exact Hseen].
      intro Hin. apply (proj2 (existsb_state_eqb x seen)) in Hin. congruence.
Qed.

Lemma explore_nodup fuel seen todo :
  NoDup seen -> NoDup (explore fuel seen todo).
Proof.
  revert seen todo. induction fuel as [|fuel IH]; intros seen todo Hseen; simpl.
  - exact Hseen.
  - destruct todo as [|q todo']; [exact Hseen|]. simpl.
    destruct (add_successors (map (step q) labels) seen todo')
      as [seen' todo''] eqn:Hadd.
    apply IH. eapply add_successors_result_nodup; eauto.
Qed.

Theorem derivative_states_nodup fuel initial :
  NoDup (derivative_states fuel initial).
Proof.
  unfold derivative_states. apply explore_nodup. now constructor; [intro H; inversion H|constructor].
Qed.

End Worklist.

(** Mechanization extension: breadth-first exploration retaining the shortest
    witness of every discovered state.  The alphabet list fixes both the
    lexicographic tie-break and transition order, hence extracted debug output
    is deterministic. *)
Section WitnessWorklist.
Context {State Label : Type}.
Variable state_eqb : State -> State -> bool.
Variable labels : list Label.
Variable step : State -> Label -> State.

Record witnessed_state := {
  witnessed_value : State;
  witnessed_word : list Label
}.

Definition witnessed_values (xs : list witnessed_state) : list State :=
  map witnessed_value xs.

Definition add_witnessed (x : witnessed_state)
  (seen todo : list witnessed_state)
  : list witnessed_state * list witnessed_state :=
  if existsb (state_eqb (witnessed_value x)) (witnessed_values seen)
  then (seen, todo)
  else (seen ++ [x], todo ++ [x]).

Fixpoint add_witnessed_successors (xs : list witnessed_state)
  (seen todo : list witnessed_state)
  : list witnessed_state * list witnessed_state :=
  match xs with
  | [] => (seen, todo)
  | x :: xs' =>
      let '(seen', todo') := add_witnessed x seen todo in
      add_witnessed_successors xs' seen' todo'
  end.

Definition witnessed_successors (q : witnessed_state)
  : list witnessed_state :=
  map (fun a =>
    {| witnessed_value := step (witnessed_value q) a;
       witnessed_word := witnessed_word q ++ [a] |}) labels.

Fixpoint explore_witnessed (fuel : nat)
  (seen todo : list witnessed_state) : list witnessed_state :=
  match fuel, todo with
  | 0, _ => seen
  | S _, [] => seen
  | S fuel', q :: todo' =>
      let '(seen', todo'') :=
        add_witnessed_successors (witnessed_successors q) seen todo' in
      explore_witnessed fuel' seen' todo''
  end.

Fixpoint explore_witnessed_result (fuel : nat)
  (seen todo : list witnessed_state)
  : list witnessed_state * list witnessed_state :=
  match fuel, todo with
  | 0, _ => (seen, todo)
  | S _, [] => (seen, [])
  | S fuel', q :: todo' =>
      let '(seen', todo'') :=
        add_witnessed_successors (witnessed_successors q) seen todo' in
      explore_witnessed_result fuel' seen' todo''
  end.

Definition derivative_states_with_witness (fuel : nat) (initial : State)
  : list witnessed_state :=
  let q0 := {| witnessed_value := initial; witnessed_word := [] |} in
  explore_witnessed fuel [q0] [q0].

Hypothesis state_eqb_spec :
  forall x y, state_eqb x y = true <-> x = y.

Lemma witnessed_values_initial initial :
  witnessed_values
    [{| witnessed_value := initial; witnessed_word := [] |}] = [initial].
Proof. reflexivity. Qed.

(** A witness stored by the BFS really replays to its state.  The invariant is
    exposed separately so specialized finite instances can discharge it by
    computation together with saturation. *)
Definition witnessed_replays (initial : State) (q : witnessed_state) : Prop :=
  fold_left step (witnessed_word q) initial = witnessed_value q.

End WitnessWorklist.

(** The concrete residue coalgebra for the requested two-lookahead example.
    A state is a 15-bit truth vector.  Its true positions are the currently
    reachable unions of cyclic shifts of the residues divisible by 3 or 5.
    Reading [b] rotates the vector; reading [a] rotates and also inserts the
    base residue set.  This is the independent semantic characteristic stated
    in the user example, not a hard-coded state count. *)
Module Mod15Example.

Definition bitvec := list bool.

Fixpoint bitvec_eqb (x y : bitvec) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => Bool.eqb a b && bitvec_eqb x' y'
  | _, _ => false
  end.

Definition zeros15 : bitvec :=
  [false; false; false; false; false;
   false; false; false; false; false;
   false; false; false; false; false].

Definition base15 : bitvec :=
  [true; false; false; true; false;
   true; true; false; false; true;
   true; false; true; false; false].

Definition rotate15 (s : bitvec) : bitvec :=
  match s with [] => [] | x :: xs => xs ++ [x] end.

Fixpoint bitvec_union (x y : bitvec) : bitvec :=
  match x, y with
  | a :: x', b :: y' => orb a b :: bitvec_union x' y'
  | _, _ => []
  end.

(** [true] encodes [a], [false] encodes [b]. *)
Definition residue_step (s : bitvec) (is_a : bool) : bitvec :=
  let shifted := rotate15 s in
  if is_a then bitvec_union shifted base15 else shifted.

Definition residue_alphabet : list bool := [true; false].

Definition residue_states : list bitvec :=
  derivative_states bitvec_eqb residue_alphabet residue_step 1000 zeros15.

Definition residue_worklist_result : list bitvec * list bitvec :=
  explore_result bitvec_eqb residue_alphabet residue_step 1000
    [zeros15] [zeros15].

Definition residue_state_count : nat := length residue_states.

Example requested_exact_state_count : residue_state_count = 182.
Proof. vm_compute. reflexivity. Qed.

Example requested_exact_derivative_state_count :
  derivative_state_count bitvec_eqb residue_alphabet residue_step 1000 zeros15 = 182.
Proof. vm_compute. reflexivity. Qed.

Example requested_worklist_is_saturated :
  fst residue_worklist_result = residue_states /\
  snd residue_worklist_result = [].
Proof. vm_compute. now split. Qed.

Definition residue_witnessed_states :
  list (@witnessed_state bitvec bool) :=
  derivative_states_with_witness bitvec_eqb residue_alphabet residue_step
    1000 zeros15.

Fixpoint state_index_from (needle : bitvec) (xs : list bitvec) (n : nat)
  : option nat :=
  match xs with
  | [] => None
  | x :: xs' =>
      if bitvec_eqb needle x then Some n
      else state_index_from needle xs' (S n)
  end.

Definition state_index (needle : bitvec) (xs : list bitvec) : option nat :=
  state_index_from needle xs 0.

Fixpoint true_indices_from (xs : bitvec) (n : nat) : list nat :=
  match xs with
  | [] => []
  | b :: xs' =>
      if b then n :: true_indices_from xs' (S n)
      else true_indices_from xs' (S n)
  end.

Definition true_indices (xs : bitvec) : list nat :=
  true_indices_from xs 0.

Record residue_debug_transition := {
  debug_symbol_is_a : bool;
  debug_main_keeps_suffix_language : bool;
  debug_main_bits : bitvec;
  debug_context_bits : bitvec;
  debug_target : nat
}.

Record residue_debug_state := {
  debug_id : nat;
  debug_witness : list bool;
  debug_accepting : bool;
  debug_representative : bitvec;
  debug_term_ids : list nat;
  debug_transitions : list residue_debug_transition
}.

Definition residue_transition_debug (all : list bitvec)
  (s : bitvec) (is_a : bool) : residue_debug_transition :=
  {| debug_symbol_is_a := is_a;
     debug_main_keeps_suffix_language := true;
     debug_main_bits := if is_a then base15 else zeros15;
     debug_context_bits := rotate15 s;
     debug_target :=
       match state_index (residue_step s is_a) all with
       | Some n => n
       | None => 0
       end |}.

Fixpoint build_residue_debug_states_from
  (all : list bitvec)
  (xs : list (@witnessed_state bitvec bool))
  (n : nat) : list residue_debug_state :=
  match xs with
  | [] => []
  | q :: xs' =>
      let s := witnessed_value q in
      {| debug_id := n;
         debug_witness := witnessed_word q;
         debug_accepting := hd false s;
         debug_representative := s;
         debug_term_ids := true_indices s;
         debug_transitions :=
           map (residue_transition_debug all s) residue_alphabet |}
      :: build_residue_debug_states_from all xs' (S n)
  end.

Definition residue_witnessed_values : list bitvec :=
  map witnessed_value residue_witnessed_states.

(** Public Rocq entry requested for debugging: all 182 semantic residual
    representatives, in deterministic BFS order, with shortest witnesses and
    both main/context contributions for every alphabet symbol. *)
Definition requested_derivative_debug_states : list residue_debug_state :=
  build_residue_debug_states_from residue_witnessed_values
    residue_witnessed_states 0.

Definition replay_witness (w : list bool) : bitvec :=
  fold_left residue_step w zeros15.

Definition debug_state_replaysb (q : residue_debug_state) : bool :=
  bitvec_eqb (replay_witness (debug_witness q))
              (debug_representative q).

Definition all_debug_states_replayb : bool :=
  forallb debug_state_replaysb requested_derivative_debug_states.

Example requested_witnessed_state_count :
  length residue_witnessed_states = 182.
Proof. vm_compute. reflexivity. Qed.

Example requested_debug_state_count :
  length requested_derivative_debug_states = 182.
Proof. vm_compute. reflexivity. Qed.

Example requested_debug_witnesses_replay : all_debug_states_replayb = true.
Proof. vm_compute. reflexivity. Qed.

End Mod15Example.

(** A parameterized version of the residue-vector transition used above.
    The modulus, accepted period divisors, alphabet and trigger symbol are
    data.  The CLI uses these extracted definitions for every expression of
    this periodic-lookahead family instead of loading a fixed state table. *)
Module PeriodicFamily.

Definition bitvec := list bool.

Definition zeros (modulus : nat) : bitvec := repeat false modulus.

Definition base (modulus : nat) (periods : list nat) : bitvec :=
  map (fun i => existsb (fun p => Nat.eqb (i mod p) 0) periods)
    (seq 0 modulus).

Definition rotate (s : bitvec) : bitvec :=
  match s with [] => [] | x :: xs => xs ++ [x] end.

Fixpoint union (x y : bitvec) : bitvec :=
  match x, y with
  | a :: x', b :: y' => orb a b :: union x' y'
  | _, _ => []
  end.

Definition step {A : Type} (eqb : A -> A -> bool)
    (trigger : A) (base_bits s : bitvec) (a : A) : bitvec :=
  let shifted := rotate s in
  if eqb a trigger then union shifted base_bits else shifted.

Lemma zeros_length modulus : length (zeros modulus) = modulus.
Proof. apply repeat_length. Qed.

Lemma base_length modulus periods :
  length (base modulus periods) = modulus.
Proof. unfold base. rewrite map_length, seq_length. reflexivity. Qed.

Lemma rotate_length s : length (rotate s) = length s.
Proof.
  destruct s as [|x xs]; simpl; [reflexivity|].
  rewrite app_length. simpl. lia.
Qed.

Lemma union_length x y :
  length x = length y -> length (union x y) = length x.
Proof.
  revert y. induction x as [|a x IH]; intros [|b y] Hlen;
    simpl in *; try discriminate; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

Theorem step_length {A : Type} (eqb : A -> A -> bool)
    trigger base_bits s a :
  length base_bits = length s ->
  length (step eqb trigger base_bits s a) = length s.
Proof.
  intro Hlen. unfold step.
  destruct (eqb a trigger).
  - rewrite union_length.
    + apply rotate_length.
    + rewrite rotate_length. symmetry. exact Hlen.
  - apply rotate_length.
Qed.

Fixpoint consume {A : Type} (s : bitvec) (w : list A) : bitvec :=
  match w with
  | [] => s
  | _ :: w' => consume (rotate s) w'
  end.

Definition accepts {A : Type} (s : bitvec) (w : list A) : bool :=
  hd false (consume s w).

Lemma union_snoc x y a b :
  length x = length y ->
  union (x ++ [a]) (y ++ [b]) = union x y ++ [orb a b].
Proof.
  revert y. induction x as [|c x IH]; intros [|d y] Hlen;
    simpl in *; try discriminate; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

Lemma rotate_union x y :
  length x = length y ->
  rotate (union x y) = union (rotate x) (rotate y).
Proof.
  intros Hlen. destruct x as [|a x], y as [|b y];
    simpl in Hlen; try discriminate; [reflexivity|].
  unfold rotate. simpl. symmetry. apply union_snoc. lia.
Qed.

Lemma consume_union {A : Type} (x y : bitvec) (w : list A) :
  length x = length y ->
  consume (union x y) w = union (consume x w) (consume y w).
Proof.
  revert x y. induction w as [|a w IH]; intros x y Hlen; simpl.
  - reflexivity.
  - rewrite rotate_union by exact Hlen.
    apply IH. now rewrite !rotate_length.
Qed.

Lemma consume_length {A : Type} (s : bitvec) (w : list A) :
  length (consume s w) = length s.
Proof.
  revert s. induction w as [|a w IH]; intro s; simpl; [reflexivity|].
  rewrite IH. apply rotate_length.
Qed.

Lemma hd_union x y :
  length x = length y ->
  hd false (union x y) = orb (hd false x) (hd false y).
Proof.
  destruct x as [|a x], y as [|b y]; simpl; intros Hlen;
    try discriminate; reflexivity.
Qed.

Lemma accepts_union {A : Type} (x y : bitvec) (w : list A) :
  length x = length y ->
  accepts (union x y) w = orb (accepts x w) (accepts y w).
Proof.
  intro Hlen. unfold accepts.
  rewrite consume_union by exact Hlen.
  apply hd_union. now rewrite !consume_length.
Qed.

Lemma accepts_cons {A : Type} s (a : A) w :
  accepts s (a :: w) = accepts (rotate s) w.
Proof. reflexivity. Qed.

Lemma nth_rotate s i :
  i < length s ->
  nth i (rotate s) false = nth (S i mod length s) s false.
Proof.
  destruct s as [|x xs]; intro Hi; [simpl in Hi; lia|].
  unfold rotate. simpl in Hi.
  destruct (lt_dec i (length xs)) as [Hsmall|Hlast].
  - rewrite app_nth1 by exact Hsmall.
    rewrite Nat.mod_small by (simpl; lia). reflexivity.
  - assert (Hi' : i = length xs) by lia. subst i.
    rewrite app_nth2 by lia. rewrite Nat.sub_diag.
    change (x = nth (S (length xs) mod S (length xs)) (x :: xs) false).
    rewrite Nat.mod_same by lia. reflexivity.
Qed.

Lemma consume_nth {A : Type} (s : bitvec) (w : list A) i :
  i < length s ->
  nth i (consume s w) false =
    nth ((length w + i) mod length s) s false.
Proof.
  revert s i. induction w as [|a w IH]; intros s i Hi; simpl.
  - rewrite Nat.mod_small by exact Hi. reflexivity.
  - rewrite IH by (rewrite rotate_length; exact Hi).
    rewrite rotate_length.
    rewrite nth_rotate by (apply Nat.mod_upper_bound; lia).
    replace (S ((length w + i) mod length s)) with
      (1 + (length w + i) mod length s) by lia.
    rewrite Nat.add_mod_idemp_r by lia.
    replace (1 + (length w + i)) with (S (length w) + i) by lia.
    reflexivity.
Qed.

Theorem accepts_nth {A : Type} (s : bitvec) (w : list A) :
  length s > 0 ->
  accepts s w = nth (length w mod length s) s false.
Proof.
  intro Hpositive. unfold accepts.
  assert (Hhd : hd false (consume s w) = nth 0 (consume s w) false).
  { destruct (consume s w); reflexivity. }
  rewrite Hhd.
  rewrite consume_nth by lia. now rewrite Nat.add_0_r.
Qed.

Definition periodsb (periods : list nat) (n : nat) : bool :=
  existsb (fun p => Nat.eqb (n mod p) 0) periods.

Lemma nth_base modulus periods i :
  i < modulus ->
  nth i (base modulus periods) false = periodsb periods i.
Proof.
  intro Hi. unfold base, periodsb.
  transitivity (nth i
    (map (fun j => existsb (fun p => Nat.eqb (j mod p) 0) periods)
      (seq 0 modulus))
    (existsb (fun p => Nat.eqb (0 mod p) 0) periods)).
  - apply nth_indep. rewrite length_map, length_seq. exact Hi.
  - eapply eq_trans.
    + exact (@map_nth nat bool
        (fun j => existsb (fun p => Nat.eqb (j mod p) 0) periods)
        (seq 0 modulus) 0 i).
    + rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma mod_divisor n modulus p :
  modulus <> 0 -> p <> 0 -> Nat.divide p modulus ->
  (n mod modulus) mod p = n mod p.
Proof.
  intros Hmod Hp [k Hk].
  pose proof (Nat.div_mod n modulus Hmod) as Hdecomp.
  assert (Hn : n = n mod modulus + ((n / modulus) * k) * p) by nia.
  rewrite Hn at 2. rewrite Nat.mod_add by exact Hp. reflexivity.
Qed.

Lemma periodsb_modulus periods n modulus :
  modulus <> 0 ->
  Forall (fun p => p <> 0 /\ Nat.divide p modulus) periods ->
  periodsb periods (n mod modulus) = periodsb periods n.
Proof.
  intros Hmod Hperiods. induction Hperiods as [|p ps [Hp Hdiv] Hps IH];
    unfold periodsb in *; simpl; [reflexivity|].
  rewrite (@mod_divisor n modulus p Hmod Hp Hdiv), IH. reflexivity.
Qed.

(** The base vector is computed from the period list.  This discharges the
    semantic premise of [residual_symbol_quotient] for every positive common
    multiple, including the least common multiple chosen by the CLI. *)
Theorem accepts_base {A : Type} modulus periods (w : list A) :
  modulus <> 0 ->
  Forall (fun p => p <> 0 /\ Nat.divide p modulus) periods ->
  accepts (base modulus periods) w = periodsb periods (length w).
Proof.
  intros Hmod Hperiods.
  rewrite accepts_nth by (rewrite base_length; lia).
  rewrite base_length, nth_base by (apply Nat.mod_upper_bound; exact Hmod).
  now apply periodsb_modulus.
Qed.

Definition ends_in {A : Type} (trigger : A) (u : list A) : Prop :=
  exists prefix, u = prefix ++ [trigger].

Lemma ends_in_singleton_iff {A : Type} (a trigger : A) :
  ends_in trigger [a] <-> a = trigger.
Proof.
  split.
  - intros [prefix H].
    destruct prefix as [|x prefix]; simpl in H; [now inversion H|].
    destruct prefix; simpl in H; discriminate.
  - intros ->. exists []. reflexivity.
Qed.

Lemma ends_in_cons_nonempty_iff {A : Type}
    (a b trigger : A) (u : list A) :
  ends_in trigger (a :: b :: u) <-> ends_in trigger (b :: u).
Proof.
  split; intros [prefix H].
  - destruct prefix as [|x prefix]; [discriminate|].
    inversion H. exists prefix. assumption.
  - exists (a :: prefix). simpl. now rewrite H.
Qed.

Definition residual_language {A : Type} (trigger : A)
    (suffix_acceptb : list A -> bool) (s : bitvec)
    : constraint_language A :=
  fun p =>
    let '(u, v) := p in
    (u <> [] /\ ends_in trigger u /\ suffix_acceptb v = true) \/
    (u = [] /\ accepts s v = true).

(** Generic full-pair semantic correspondence for the extracted periodic
    transition.  The only family-specific premise is that [base_bits]
    recognizes the required suffix predicate; the state update itself and
    its main/context quotient calculation are completely parameterized. *)
Theorem residual_symbol_quotient {A : Type}
    (eqb : A -> A -> bool)
    (eqb_spec : forall x y : A, eqb x y = true <-> x = y)
    (trigger : A) (suffix_acceptb : list A -> bool)
    (base_bits s : bitvec) a :
  length base_bits = length s ->
  (forall v, accepts base_bits v = suffix_acceptb v) ->
  lang_equiv
    (pair_language_symbol_quotient eqb a
      (residual_language trigger suffix_acceptb s))
    (residual_language trigger suffix_acceptb
      (step eqb trigger base_bits s a)).
Proof.
  intros Hlen Hbase [u v].
  rewrite (pair_symbol_quotient_split eqb eqb_spec a
    (residual_language trigger suffix_acceptb s) (u, v)).
  unfold lang_union, main_symbol_quotient, context_symbol_quotient,
    residual_language. simpl.
  destruct u as [|b u].
  - destruct (eqb a trigger) eqn:E.
    + apply eqb_spec in E. subst a. unfold step.
      rewrite (proj2 (eqb_spec trigger trigger)); [|reflexivity].
      rewrite accepts_union.
      2:{ rewrite rotate_length. symmetry. exact Hlen. }
      rewrite Hbase, accepts_cons, Bool.orb_true_iff.
      rewrite ends_in_singleton_iff. intuition discriminate.
    + assert (Hneq : a <> trigger).
      { intro H. subst a.
        pose proof (proj2 (eqb_spec trigger trigger) eq_refl) as Htrue.
        congruence. }
      unfold step. rewrite E, accepts_cons.
      rewrite ends_in_singleton_iff. intuition discriminate.
  - rewrite ends_in_cons_nonempty_iff.
    unfold step. destruct (eqb a trigger); simpl; intuition discriminate.
Qed.

End PeriodicFamily.

(** * Verified residual model for the requested expression

    This section supplies the correspondence that was missing from the first
    version of the development.  It deliberately separates the finite
    15-bit coalgebra from its interpretation as an [M]-quotient. *)
Module RequestedCorrespondence.

Definition bool_eqb_spec : forall x y : bool, Bool.eqb x y = true <-> x = y.
Proof. intros x y. destruct x, y; simpl; intuition congruence. Qed.

Definition sigma_regex : regex bool := Plus (Atom true) (Atom false).

Fixpoint positive_regex_power (r : regex bool) (n : nat) : regex bool :=
  match n with
  | 0 => Eps
  | 1 => r
  | S n' => Concat r (positive_regex_power r n')
  end.

Definition block3_regex := positive_regex_power sigma_regex 3.
Definition block5_regex := positive_regex_power sigma_regex 5.

Definition wab_bool : rewpla bool := WPlus (WAtom true) (WAtom false).
Definition wthree_bool : rewpla bool :=
  WConcat wab_bool (WConcat wab_bool wab_bool).
Definition wfive_bool : rewpla bool :=
  WConcat wab_bool
    (WConcat wab_bool (WConcat wab_bool (WConcat wab_bool wab_bool))).

Definition requested_rewpla_bool : rewpla bool :=
  WConcat
    (WConcat (WConcat (WStar wab_bool) (WAtom true))
      (WLookahead (WStar wthree_bool)))
    (WLookahead (WStar wfive_bool)).

Lemma embed_sigma : embed_regex sigma_regex = wab_bool.
Proof. reflexivity. Qed.

Lemma embed_block3 : embed_regex block3_regex = wthree_bool.
Proof. reflexivity. Qed.

Lemma embed_block5 : embed_regex block5_regex = wfive_bool.
Proof. reflexivity. Qed.

Lemma matches_sigma_iff w : matches sigma_regex w <-> length w = 1.
Proof.
  split.
  - intro H. inversion H; subst;
      match goal with Ha : matches (Atom _) _ |- _ => inversion Ha; reflexivity end.
  - intro H. destruct w as [|b w]; [discriminate|].
    destruct w; [|discriminate]. destruct b; constructor; constructor.
Qed.

Lemma positive_regex_power_length n w :
  n > 0 ->
  matches (positive_regex_power sigma_regex n) w <-> length w = n.
Proof.
  revert w. induction n as [|n IH]; intros w Hpos; [lia|].
  destruct n as [|n].
  - simpl. apply matches_sigma_iff.
  - simpl. split.
    + intro H. inversion H; subst.
      apply matches_sigma_iff in H2.
      apply IH in H4; [|lia]. rewrite length_app, H2, H4. lia.
    + intro Hlen. destruct w as [|b w]; [discriminate|].
      change (matches (Concat sigma_regex
        (positive_regex_power sigma_regex (S n))) ([b] ++ w)).
      constructor.
      * apply matches_sigma_iff. reflexivity.
      * apply IH; [lia|]. simpl in Hlen. lia.
Qed.

Lemma matches_positive_power_star n w :
  n > 0 ->
  matches (Star (positive_regex_power sigma_regex n)) w <->
  exists k, length w = n * k.
Proof.
  intro Hn. split.
  - intro H. remember (Star (positive_regex_power sigma_regex n)) as sr.
    induction H; inversion Heqsr; subst.
    + exists 0. now rewrite Nat.mul_0_r.
    + apply positive_regex_power_length in H0; [|exact Hn].
      destruct IHmatches2 as [k Hk]; [reflexivity|].
      exists (S k). rewrite length_app, H0, Hk. nia.
  - intros [k Hlen]. revert w Hlen. induction k as [|k IH]; intros w Hlen.
    + rewrite Nat.mul_0_r in Hlen. apply length_zero_iff_nil in Hlen.
      subst w. constructor.
    + assert (Hkn : n <= length w) by nia.
      rewrite <- (firstn_skipn n w) at 1.
      apply M_StarApp.
      * intro Hnil. apply (f_equal (@length bool)) in Hnil.
        rewrite length_firstn, Nat.min_l in Hnil; [simpl in Hnil; lia|exact Hkn].
      * apply positive_regex_power_length; [exact Hn|].
        rewrite length_firstn, Nat.min_l by exact Hkn. reflexivity.
      * apply IH. rewrite skipn_length. nia.
Qed.

Definition periodicb (n : nat) : bool :=
  Nat.eqb (n mod 3) 0 || Nat.eqb (n mod 5) 0.

Lemma matches_block3_star w :
  matches (Star block3_regex) w <-> Nat.eqb (length w mod 3) 0 = true.
Proof.
  unfold block3_regex. rewrite matches_positive_power_star by lia.
  rewrite Nat.eqb_eq. symmetry. apply Nat.mod_divides. lia.
Qed.

Lemma matches_block5_star w :
  matches (Star block5_regex) w <-> Nat.eqb (length w mod 5) 0 = true.
Proof.
  unfold block5_regex. rewrite matches_positive_power_star by lia.
  rewrite Nat.eqb_eq. symmetry. apply Nat.mod_divides. lia.
Qed.

Fixpoint consume_context (s : Mod15Example.bitvec) (w : list bool)
  : Mod15Example.bitvec :=
  match w with
  | [] => s
  | _ :: w' => consume_context (Mod15Example.rotate15 s) w'
  end.

Definition context_acceptb (s : Mod15Example.bitvec) (w : list bool) : bool :=
  hd false (consume_context s w).

Lemma consume_context_iter s w :
  consume_context s w = Nat.iter (length w) Mod15Example.rotate15 s.
Proof.
  revert s. induction w as [|a w IH]; intro s; simpl; [reflexivity|].
  rewrite IH, Nat.iter_swap. reflexivity.
Qed.

Definition base_accept_nat (n : nat) : bool :=
  hd false (Nat.iter n Mod15Example.rotate15 Mod15Example.base15).

Lemma base_accept_nat_period n : base_accept_nat (15 + n) = base_accept_nat n.
Proof.
  unfold base_accept_nat. replace (15 + n) with (n + 15) by lia.
  rewrite Nat.iter_add. vm_compute. reflexivity.
Qed.

Lemma periodicb_period n : periodicb (15 + n) = periodicb n.
Proof.
  unfold periodicb.
  assert ((15 + n) mod 3 = n mod 3) as H3.
  { rewrite Nat.add_mod by lia.
    replace (15 mod 3) with 0 by reflexivity. rewrite Nat.add_0_l.
    apply Nat.mod_small.
    apply Nat.mod_upper_bound. lia. }
  assert ((15 + n) mod 5 = n mod 5) as H5.
  { rewrite Nat.add_mod by lia.
    replace (15 mod 5) with 0 by reflexivity. rewrite Nat.add_0_l.
    apply Nat.mod_small.
    apply Nat.mod_upper_bound. lia. }
  now rewrite H3, H5.
Qed.

Lemma base_accept_nat_correct n : base_accept_nat n = periodicb n.
Proof.
  induction n using (well_founded_induction lt_wf).
  destruct (lt_dec n 15) as [Hsmall|Hlarge].
  - do 15 (destruct n as [|n]; [reflexivity|]). lia.
  - assert (Hsplit : n = 15 + (n - 15)) by lia.
    rewrite Hsplit, base_accept_nat_period, periodicb_period.
    apply H. lia.
Qed.

Lemma context_acceptb_base_correct w :
  context_acceptb Mod15Example.base15 w = periodicb (length w).
Proof. unfold context_acceptb. rewrite consume_context_iter. apply base_accept_nat_correct. Qed.

Lemma lookahead_block3_semantics v :
  rewpla_denote Bool.eqb (WLookahead (WStar wthree_bool)) ([], v) <->
  Nat.eqb (length v mod 3) 0 = true.
Proof.
  rewrite <- embed_block3.
  split.
  - intros [p [Hp Hout]].
    apply (proj1 (embed_regex_semantics Bool.eqb bool_eqb_spec
      (Star block3_regex) p)) in Hp.
    destruct Hp as [w [-> Hw]]. simpl in Hout. inversion Hout; subst v.
    unfold constraint_projection. simpl. rewrite app_nil_r.
    now apply (proj1 (matches_block3_star w)).
  - intro Hv. exists (v, []). split.
    + apply (proj2 (embed_regex_semantics Bool.eqb bool_eqb_spec
        (Star block3_regex) (v, []))).
      exists v. split; [reflexivity|now apply (proj2 (matches_block3_star v))].
    + unfold constraint_projection. simpl. now rewrite app_nil_r.
Qed.

Lemma lookahead_block5_semantics v :
  rewpla_denote Bool.eqb (WLookahead (WStar wfive_bool)) ([], v) <->
  Nat.eqb (length v mod 5) 0 = true.
Proof.
  rewrite <- embed_block5.
  split.
  - intros [p [Hp Hout]].
    apply (proj1 (embed_regex_semantics Bool.eqb bool_eqb_spec
      (Star block5_regex) p)) in Hp.
    destruct Hp as [w [-> Hw]]. simpl in Hout. inversion Hout; subst v.
    unfold constraint_projection. simpl. rewrite app_nil_r.
    now apply (proj1 (matches_block5_star w)).
  - intro Hv. exists (v, []). split.
    + apply (proj2 (embed_regex_semantics Bool.eqb bool_eqb_spec
        (Star block5_regex) (v, []))).
      exists v. split; [reflexivity|now apply (proj2 (matches_block5_star v))].
    + unfold constraint_projection. simpl. now rewrite app_nil_r.
Qed.

(** The ordinary prefix [(a+b)*a] consumes a nonempty main string whose
    final letter is [a].  Keeping this property existential avoids any
    dependence on a string indexing convention. *)
Definition ends_in_a (u : list bool) : Prop :=
  exists x, u = x ++ [true].

Definition prefix_regex : regex bool :=
  Concat (Star sigma_regex) (Atom true).

Definition prefix_rewpla : rewpla bool :=
  WConcat (WStar wab_bool) (WAtom true).

Lemma embed_prefix : embed_regex prefix_regex = prefix_rewpla.
Proof. reflexivity. Qed.

Lemma matches_sigma_star w : matches (Star sigma_regex) w.
Proof.
  induction w as [|b w IH].
  - constructor.
  - change (matches (Star sigma_regex) ([b] ++ w)).
    apply M_StarApp.
    + discriminate.
    + apply matches_sigma_iff. reflexivity.
    + exact IH.
Qed.

Lemma matches_prefix_iff u : matches prefix_regex u <-> ends_in_a u.
Proof.
  split.
  - intro H. inversion H; subst. inversion H4; subst.
    exists u0. reflexivity.
  - intros [x ->]. constructor; [apply matches_sigma_star|constructor].
Qed.

Lemma prefix_semantics p :
  rewpla_denote Bool.eqb prefix_rewpla p <->
  exists u, p = (u, []) /\ ends_in_a u.
Proof.
  rewrite <- embed_prefix.
  rewrite embed_regex_semantics by exact bool_eqb_spec.
  split.
  - intros [u [-> Hu]]. exists u. split; [reflexivity|].
    now apply matches_prefix_iff.
  - intros [u [-> Hu]]. exists u. split; [reflexivity|].
    now apply matches_prefix_iff.
Qed.

Lemma lookahead_block3_semantics_pair p :
  rewpla_denote Bool.eqb (WLookahead (WStar wthree_bool)) p <->
  exists v, p = ([], v) /\ Nat.eqb (length v mod 3) 0 = true.
Proof.
  split.
  - intros [q [Hq ->]].
    exists (constraint_projection q). split; [reflexivity|].
    apply (proj1 (lookahead_block3_semantics (constraint_projection q))).
    exists q. now split.
  - intros [v [-> Hv]]. now apply lookahead_block3_semantics.
Qed.

Lemma lookahead_block5_semantics_pair p :
  rewpla_denote Bool.eqb (WLookahead (WStar wfive_bool)) p <->
  exists v, p = ([], v) /\ Nat.eqb (length v mod 5) 0 = true.
Proof.
  split.
  - intros [q [Hq ->]].
    exists (constraint_projection q). split; [reflexivity|].
    apply (proj1 (lookahead_block5_semantics (constraint_projection q))).
    exists q. now split.
  - intros [v [-> Hv]]. now apply lookahead_block5_semantics.
Qed.

Lemma constraint_concat_main_empty_context u c :
  constraint_concat Bool.eqb (u, []) ([], c) = Some (u, c).
Proof.
  unfold constraint_concat. simpl. rewrite app_nil_r.
  destruct c; reflexivity.
Qed.

Lemma constraint_concat_add_context u c d :
  constraint_concat Bool.eqb (u, c) ([], d) =
  option_map (fun t => (u, t)) (join Bool.eqb c d).
Proof.
  unfold constraint_concat. simpl.
  rewrite app_nil_r.
  unfold residual. simpl.
  destruct (join Bool.eqb c d); reflexivity.
Qed.

Definition prefix_la3 : rewpla bool :=
  WConcat prefix_rewpla (WLookahead (WStar wthree_bool)).

Lemma prefix_la3_semantics p :
  rewpla_denote Bool.eqb prefix_la3 p <->
  exists u c, p = (u, c) /\ ends_in_a u /\
    Nat.eqb (length c mod 3) 0 = true.
Proof.
  unfold prefix_la3. simpl. unfold lang_concat.
  split.
  - intros [q1 [q2 [H1 [H2 Hout]]]].
    apply prefix_semantics in H1 as [u [-> Hu]].
    apply lookahead_block3_semantics_pair in H2 as [c [-> Hc]].
    rewrite constraint_concat_main_empty_context in Hout. inversion Hout; subst.
    exists u, c. tauto.
  - intros [u [c [-> [Hu Hc]]]].
    exists (u, []), ([], c). repeat split.
    + apply prefix_semantics. now exists u.
    + apply lookahead_block3_semantics_pair. now exists c.
    + apply constraint_concat_main_empty_context.
Qed.

(** Exact [M]-semantics of the concrete expression requested by the user.
    The two constraints combine by prefix join, so the surviving constraint
    has length divisible by 3 or by 5. *)
Theorem requested_rewpla_semantics u v :
  rewpla_denote Bool.eqb requested_rewpla_bool (u, v) <->
  ends_in_a u /\ periodicb (length v) = true.
Proof.
  unfold requested_rewpla_bool. simpl. unfold lang_concat.
  split.
  - intros [q1 [q2 [H1 [H2 Hout]]]].
    apply prefix_la3_semantics in H1 as [x [c [-> [Hx Hc]]]].
    apply lookahead_block5_semantics_pair in H2 as [d [-> Hd]].
    rewrite constraint_concat_add_context in Hout.
    destruct (join Bool.eqb c d) as [t|] eqn:Hjoin; [|discriminate].
    inversion Hout; subst x t.
    split; [exact Hx|]. unfold periodicb.
    apply (join_result Bool.eqb bool_eqb_spec c d) in Hjoin.
    destruct Hjoin as [[_ ->]|[_ ->]].
    + now rewrite Hd, Bool.orb_true_r.
    + now rewrite Hc, Bool.orb_true_l.
  - intros [Hu Hperiod]. unfold periodicb in Hperiod.
    apply Bool.orb_true_iff in Hperiod as [H3|H5].
    + exists (u, v), ([], []). repeat split.
      * apply prefix_la3_semantics. exists u, v. tauto.
      * apply lookahead_block5_semantics_pair. exists [].
        split; [reflexivity|reflexivity].
      * apply (proj2 (constraint_concat_empty_right Bool.eqb bool_eqb_spec
          (u, v) (u, v))). reflexivity.
    + exists (u, []), ([], v). repeat split.
      * apply prefix_la3_semantics. exists u, [].
        split; [reflexivity|split; [exact Hu|reflexivity]].
      * apply lookahead_block5_semantics_pair. now exists v.
      * apply constraint_concat_main_empty_context.
Qed.

(** Mechanization extension, corresponding to the context summand after one
    [a] in the requested expression: this preserves the paper's original
    two-lookahead syntax instead of expanding all modulo-15 residue classes. *)
Definition requested_context_product : rewpla bool :=
  WConcat (WLookahead (WStar wthree_bool))
    (WLookahead (WStar wfive_bool)).

Theorem requested_context_product_semantics u v :
  rewpla_denote Bool.eqb requested_context_product (u, v) <->
  u = [] /\ periodicb (length v) = true.
Proof.
  unfold requested_context_product. simpl. unfold lang_concat.
  split.
  - intros [q1 [q2 [H1 [H2 Hout]]]].
    apply lookahead_block3_semantics_pair in H1 as [c [-> Hc]].
    apply lookahead_block5_semantics_pair in H2 as [d [-> Hd]].
    rewrite constraint_concat_add_context in Hout.
    destruct (join Bool.eqb c d) as [t|] eqn:Hjoin; [|discriminate].
    inversion Hout; subst u t.
    split; [reflexivity|]. unfold periodicb.
    apply (join_result Bool.eqb bool_eqb_spec c d) in Hjoin.
    destruct Hjoin as [[_ ->]|[_ ->]].
    + now rewrite Hd, Bool.orb_true_r.
    + now rewrite Hc, Bool.orb_true_l.
  - intros [-> Hperiod]. unfold periodicb in Hperiod.
    apply Bool.orb_true_iff in Hperiod as [H3|H5].
    + exists ([], v), ([], []). repeat split.
      * apply lookahead_block3_semantics_pair. now exists v.
      * apply lookahead_block5_semantics_pair. exists [].
        split; reflexivity.
      * apply (proj2 (constraint_concat_empty_right Bool.eqb bool_eqb_spec
          ([], v) ([], v))). reflexivity.
    + exists ([], []), ([], v). repeat split.
      * apply lookahead_block3_semantics_pair. exists [].
        split; reflexivity.
      * apply lookahead_block5_semantics_pair. now exists v.
Qed.

Definition requested_after_a_display : rewpla bool :=
  WPlus requested_rewpla_bool requested_context_product.

(** A boolean form of [ends_in_a], used by the executable residual model. *)
Fixpoint ends_in_ab (u : list bool) : bool :=
  match u with
  | [] => false
  | [a] => a
  | _ :: u' => ends_in_ab u'
  end.

Lemma ends_in_ab_correct u : ends_in_ab u = true <-> ends_in_a u.
Proof.
  induction u as [|a [|b u] IH]; simpl.
  - split; [discriminate|intros [x H]; destruct x; discriminate].
  - split.
    + intro Ha. exists []. destruct a; [reflexivity|discriminate].
    + intros [x Hx].
      pose proof (f_equal (@length bool) Hx) as Hlen.
      rewrite app_length in Hlen. simpl in Hlen.
      destruct x; [simpl in Hx; inversion Hx; reflexivity|].
      simpl in Hlen. lia.
  - rewrite IH. split.
    + intros [x ->]. exists (a :: x). reflexivity.
    + intros [x Hx]. destruct x as [|c x]; [discriminate|].
      inversion Hx. exists x. assumption.
Qed.

(** The finite residual represented by a bitvector.  Nonempty main strings
    retain the common suffix language; an empty main string is accepted by
    the rotating context residual. *)
Definition mod15_residual_language (s : Mod15Example.bitvec)
  : constraint_language bool :=
  fun p =>
    let '(u, v) := p in
    (u <> [] /\ ends_in_ab u = true /\ periodicb (length v) = true) \/
    (u = [] /\ context_acceptb s v = true).

Lemma rotate15_length s :
  length (Mod15Example.rotate15 s) = length s.
Proof.
  destruct s as [|a s]; [reflexivity|].
  unfold Mod15Example.rotate15. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma bitvec_union_length x y :
  length x = length y ->
  length (Mod15Example.bitvec_union x y) = length x.
Proof.
  revert y. induction x as [|a x IH]; intros y H.
  - destruct y; [reflexivity|discriminate].
  - destruct y as [|b y]; [discriminate|].
    simpl in *. f_equal. apply IH. lia.
Qed.

Lemma bitvec_union_snoc x y a b :
  length x = length y ->
  Mod15Example.bitvec_union (x ++ [a]) (y ++ [b]) =
  Mod15Example.bitvec_union x y ++ [orb a b].
Proof.
  revert y. induction x as [|c x IH]; intros y H.
  - destruct y; [reflexivity|discriminate].
  - destruct y as [|d y]; [discriminate|].
    simpl in *. f_equal. apply IH. lia.
Qed.

Lemma rotate15_union x y :
  length x = length y ->
  Mod15Example.rotate15 (Mod15Example.bitvec_union x y) =
  Mod15Example.bitvec_union (Mod15Example.rotate15 x)
    (Mod15Example.rotate15 y).
Proof.
  intros Hlen. destruct x as [|a x], y as [|b y]; simpl in Hlen;
    try discriminate; [reflexivity|].
  unfold Mod15Example.rotate15. simpl.
  symmetry. apply bitvec_union_snoc. lia.
Qed.

Lemma consume_context_union x y w :
  length x = length y ->
  consume_context (Mod15Example.bitvec_union x y) w =
  Mod15Example.bitvec_union (consume_context x w) (consume_context y w).
Proof.
  revert x y. induction w as [|a w IH]; intros x y Hlen; simpl.
  - reflexivity.
  - rewrite rotate15_union by exact Hlen.
    apply IH. now rewrite !rotate15_length.
Qed.

Lemma consume_context_length s w :
  length (consume_context s w) = length s.
Proof.
  revert s. induction w as [|a w IH]; intro s; simpl; [reflexivity|].
  rewrite IH. apply rotate15_length.
Qed.

Lemma hd_bitvec_union x y :
  length x = length y ->
  hd false (Mod15Example.bitvec_union x y) =
  orb (hd false x) (hd false y).
Proof.
  destruct x as [|a x], y as [|b y]; simpl; intros H;
    try discriminate; reflexivity.
Qed.

Lemma context_acceptb_union x y w :
  length x = length y ->
  context_acceptb (Mod15Example.bitvec_union x y) w =
  orb (context_acceptb x w) (context_acceptb y w).
Proof.
  intro Hlen. unfold context_acceptb.
  rewrite consume_context_union by exact Hlen.
  apply hd_bitvec_union.
  now rewrite !consume_context_length.
Qed.

Lemma context_acceptb_cons s a v :
  context_acceptb s (a :: v) =
  context_acceptb (Mod15Example.rotate15 s) v.
Proof. reflexivity. Qed.

Lemma base15_length : length Mod15Example.base15 = 15.
Proof. reflexivity. Qed.

Lemma residue_step_length s a :
  length s = 15 -> length (Mod15Example.residue_step s a) = 15.
Proof.
  intro Hs. destruct a; unfold Mod15Example.residue_step.
  - rewrite bitvec_union_length.
    + now rewrite rotate15_length.
    + rewrite rotate15_length, base15_length. exact Hs.
  - now rewrite rotate15_length.
Qed.

(** The central one-letter correspondence: the executable bitvector step is
    exactly the full pair quotient (main union context), not merely a
    projection-language quotient. *)
Theorem mod15_residual_symbol_quotient s a :
  length s = 15 ->
  lang_equiv
    (pair_language_symbol_quotient Bool.eqb a
      (mod15_residual_language s))
    (mod15_residual_language (Mod15Example.residue_step s a)).
Proof.
  intros Hs [u v].
  rewrite (pair_symbol_quotient_split Bool.eqb bool_eqb_spec a
    (mod15_residual_language s) (u, v)).
  unfold lang_union, main_symbol_quotient, context_symbol_quotient,
    mod15_residual_language. simpl.
  destruct u as [|b u].
  - destruct a; simpl.
    + rewrite context_acceptb_union.
      2:{ rewrite rotate15_length, base15_length. exact Hs. }
      rewrite context_acceptb_base_correct, context_acceptb_cons.
      rewrite Bool.orb_true_iff. simpl. intuition discriminate.
    + rewrite context_acceptb_cons. intuition discriminate.
  - simpl. intuition discriminate.
Qed.

Lemma rotate15_zeros :
  Mod15Example.rotate15 Mod15Example.zeros15 = Mod15Example.zeros15.
Proof. reflexivity. Qed.

Lemma consume_context_zeros w :
  consume_context Mod15Example.zeros15 w = Mod15Example.zeros15.
Proof.
  induction w as [|a w IH]; simpl; [reflexivity|].
  exact IH.
Qed.

Lemma context_acceptb_zeros w :
  context_acceptb Mod15Example.zeros15 w = false.
Proof. unfold context_acceptb. now rewrite consume_context_zeros. Qed.

(** Initial-state correspondence: this theorem mentions the actual REwPLA
    syntax tree and is the base case for every word-derivative proof. *)
Theorem requested_initial_correspondence :
  lang_equiv (rewpla_denote Bool.eqb requested_rewpla_bool)
    (mod15_residual_language Mod15Example.zeros15).
Proof.
  intros [u v]. rewrite requested_rewpla_semantics.
  rewrite <- ends_in_ab_correct.
  unfold mod15_residual_language. rewrite context_acceptb_zeros.
  destruct u as [|a u]; simpl; intuition discriminate.
Qed.

(** A direct, short representative for the derivative after consuming [a].
    This is the user's original expression plus the two original lookaheads,
    *not* the 15-residue union used for later debug representatives. *)
Theorem requested_after_a_display_correspondence :
  lang_equiv (rewpla_denote Bool.eqb requested_after_a_display)
    (mod15_residual_language Mod15Example.base15).
Proof.
  intros [u v]. unfold requested_after_a_display.
  change ((rewpla_denote Bool.eqb requested_rewpla_bool (u, v) \/
    rewpla_denote Bool.eqb requested_context_product (u, v)) <->
    mod15_residual_language Mod15Example.base15 (u, v)).
  rewrite requested_rewpla_semantics, requested_context_product_semantics.
  unfold mod15_residual_language.
  rewrite context_acceptb_base_correct.
  rewrite <- ends_in_ab_correct.
  destruct u as [|a u]; simpl; intuition discriminate.
Qed.

Definition residual_run (s : Mod15Example.bitvec) (w : list bool) :
  Mod15Example.bitvec := fold_left Mod15Example.residue_step w s.

Lemma residual_run_length s w :
  length s = 15 -> length (residual_run s w) = 15.
Proof.
  revert s. induction w as [|a w IH]; intros s Hs; simpl.
  - exact Hs.
  - apply IH. now apply residue_step_length.
Qed.

Theorem mod15_residual_word_quotient s w :
  length s = 15 ->
  lang_equiv
    (pair_language_word_quotient Bool.eqb w
      (mod15_residual_language s))
    (mod15_residual_language (residual_run s w)).
Proof.
  revert s. induction w as [|a w IH]; intros s Hs; simpl.
  - intros q. unfold pair_language_word_quotient. split.
    + intros [p [Hp Hstep]]. inversion Hstep; subst p. exact Hp.
    + intro Hq. exists q. now split.
  - eapply lang_equiv_trans.
    + apply pair_language_word_quotient_cons.
    + eapply lang_equiv_trans.
      * apply pair_language_word_quotient_compat.
        now apply mod15_residual_symbol_quotient.
      * apply IH. now apply residue_step_length.
Qed.

(** Full correspondence promised by the audit: for every projected input
    word, the syntactic derivative's [M]-semantics is exactly the residual
    language carried by the independently executed 15-bit model. *)
Theorem requested_word_derivative_correspondence w :
  lang_equiv
    (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb w requested_rewpla_bool))
    (mod15_residual_language
      (Mod15Example.replay_witness w)).
Proof.
  unfold Mod15Example.replay_witness.
  eapply lang_equiv_trans.
  - apply word_derivative_correct. exact bool_eqb_spec.
  - eapply lang_equiv_trans.
    + apply pair_language_word_quotient_compat.
      exact requested_initial_correspondence.
    + apply mod15_residual_word_quotient. reflexivity.
Qed.

(** Eq. (20)--(22), mechanization extension: the compact expression proposed
    for [D_a(requested)] denotes the exact main/context pair quotient.
    The core derivative may have another AST, so this states the correct
    paper notion of equality, [≡_M], rather than syntactic equality. *)
Theorem requested_after_a_display_derivative_correct :
  lang_equiv
    (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb [true] requested_rewpla_bool))
    (rewpla_denote Bool.eqb requested_after_a_display).
Proof.
  eapply lang_equiv_trans.
  - apply requested_word_derivative_correspondence.
  - replace (Mod15Example.replay_witness [true]) with
      Mod15Example.base15 by (vm_compute; reflexivity).
    apply lang_equiv_sym. exact requested_after_a_display_correspondence.
Qed.

Lemma context_acceptb_repeat_nth s n :
  n < length s ->
  context_acceptb s (repeat false n) = nth n s false.
Proof.
  revert s. induction n as [|n IH]; intros s Hn.
  - destruct s; [inversion Hn|reflexivity].
  - destruct s as [|a s]; [inversion Hn|].
    simpl in Hn. apply Nat.succ_lt_mono in Hn.
    change (context_acceptb (Mod15Example.rotate15 (a :: s))
      (repeat false n) = nth n s false).
    rewrite IH.
    + unfold Mod15Example.rotate15. apply app_nth1. exact Hn.
    + rewrite rotate15_length. simpl. now apply Nat.lt_lt_succ_r.
Qed.

(** No information is lost by the residual interpretation.  Empty-main
    probes of context lengths 0..14 read every bit, fixing both the residue
    orientation and the exact semantic equality criterion. *)
Theorem mod15_residual_language_injective x y :
  length x = 15 -> length y = 15 ->
  lang_equiv (mod15_residual_language x) (mod15_residual_language y) ->
  x = y.
Proof.
  intros Hx Hy Hequiv.
  assert (Hlen : length x = length y) by lia.
  apply (nth_ext x y false false Hlen).
  intros n Hn.
  pose proof (Hequiv ([], repeat false n)) as Hprobe.
  unfold mod15_residual_language in Hprobe. simpl in Hprobe.
  assert (Haccept :
    context_acceptb x (repeat false n) = true <->
    context_acceptb y (repeat false n) = true).
  { intuition discriminate. }
  rewrite context_acceptb_repeat_nth in Haccept by exact Hn.
  rewrite context_acceptb_repeat_nth in Haccept by lia.
  destruct (nth n x false), (nth n y false); simpl in Haccept;
    intuition discriminate.
Qed.

Theorem mod15_residual_language_eq_iff x y :
  length x = 15 -> length y = 15 ->
  (lang_equiv (mod15_residual_language x) (mod15_residual_language y) <->
   x = y).
Proof.
  intros Hx Hy. split.
  - now apply mod15_residual_language_injective.
  - intro Hxy. subst y. apply lang_equiv_refl.
Qed.

Theorem requested_derivatives_equiv_iff w z :
  (lang_equiv
    (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb w requested_rewpla_bool))
    (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb z requested_rewpla_bool)) <->
   Mod15Example.replay_witness w = Mod15Example.replay_witness z).
Proof.
  split.
  - intro Hsem. apply mod15_residual_language_injective.
    + unfold Mod15Example.replay_witness. apply residual_run_length. reflexivity.
    + unfold Mod15Example.replay_witness. apply residual_run_length. reflexivity.
    + intro p.
      pose proof (requested_word_derivative_correspondence w p) as Hw.
      pose proof (requested_word_derivative_correspondence z p) as Hz.
      pose proof (Hsem p) as H. tauto.
  - intro Hbits. intro p.
    pose proof (requested_word_derivative_correspondence w p) as Hw.
    pose proof (requested_word_derivative_correspondence z p) as Hz.
    rewrite Hbits in Hw. tauto.
Qed.

(** Mechanization extension: a finite, readable REwPLA expression reifying
    each of the 15-bit pair-language states.  The concrete expression is a
    common main continuation plus an ordinary length-residue regex inside
    positive lookahead.  No counting syntax is introduced. *)
Definition mod15_block_regex : regex bool :=
  positive_regex_power sigma_regex 15.

Definition residue_class_regex (i : nat) : regex bool :=
  Concat (positive_regex_power sigma_regex i)
    (Star mod15_block_regex).

Definition true_residue_ids (s : Mod15Example.bitvec) : list nat :=
  filter (fun i => nth i s false) (seq 0 15).

Definition selected_residue_regex (s : Mod15Example.bitvec) : regex bool :=
  fold_right (fun i rest => Plus (residue_class_regex i) rest)
    Zero (true_residue_ids s).

Definition mod15_representative (s : Mod15Example.bitvec) : rewpla bool :=
  WPlus requested_rewpla_bool
    (WLookahead (embed_regex (selected_residue_regex s))).

Lemma positive_regex_power_all n w :
  matches (positive_regex_power sigma_regex n) w <-> length w = n.
Proof.
  destruct n as [|n]; [|apply positive_regex_power_length; lia].
  simpl. split.
  - intro H. inversion H. reflexivity.
  - intro H. apply length_zero_iff_nil in H. subst. constructor.
Qed.

Lemma residue_class_regex_correct i w :
  i < 15 ->
  (matches (residue_class_regex i) w <-> length w mod 15 = i).
Proof.
  intro Hi. unfold residue_class_regex, mod15_block_regex. split.
  - intro H. inversion H; subst.
    apply positive_regex_power_all in H2.
    apply (proj1 (matches_positive_power_star (n := 15) v ltac:(lia)))
      in H4 as [k Hk].
    rewrite length_app, H2, Hk.
    replace (i + 15 * k) with (i + k * 15) by lia.
    rewrite Nat.mod_add by lia.
    now apply Nat.mod_small.
  - intro Hmod.
    assert (Hlower : i <= length w).
    { pose proof (Nat.mod_le (length w) 15) as Hle. lia. }
    rewrite <- (firstn_skipn i w) at 1.
    apply M_Concat.
    + apply positive_regex_power_all.
      rewrite length_firstn, Nat.min_l by exact Hlower. reflexivity.
    + apply (proj2 (matches_positive_power_star
        (n := 15) (skipn i w) ltac:(lia))).
      exists (length w / 15).
      rewrite length_skipn.
      pose proof (Nat.div_mod (length w) 15 ltac:(lia)) as Hdiv.
      nia.
Qed.

Lemma selected_residue_regex_correct s w :
  length s = 15 ->
  (matches (selected_residue_regex s) w <->
   nth (length w mod 15) s false = true).
Proof.
  intro Hs. unfold selected_residue_regex, true_residue_ids.
  assert (Hfold : forall ids,
    matches (fold_right (fun i rest => Plus (residue_class_regex i) rest)
      Zero ids) w <->
    exists i, In i ids /\ matches (residue_class_regex i) w).
  { induction ids as [|i ids IH]; simpl.
    - split; [intro H; inversion H|intros [i [H _]]; contradiction].
    - split.
      + intro H. inversion H; subst.
        * exists i. split; [now left|assumption].
        * match goal with
          | Hrest : matches (fold_right
              (fun i rest => Plus (residue_class_regex i) rest)
              Zero ids) w |- _ =>
              apply (proj1 IH) in Hrest as [j [Hj Hmatch]]
          end.
          exists j. split; [now right|exact Hmatch].
      + intros [j [[<-|Hj] Hmatch]].
        * apply M_PlusL. exact Hmatch.
        * apply M_PlusR, (proj2 IH). exists j. now split. }
  rewrite Hfold. split.
  - intros [i [Hin Hmatch]].
    apply filter_In in Hin as [Hseq Hbit].
    apply in_seq in Hseq. simpl in Hseq.
    apply residue_class_regex_correct in Hmatch; [|lia].
    now rewrite Hmatch.
  - intro Hbit. exists (length w mod 15). split.
    + apply filter_In. split.
       * apply in_seq. split; [lia|].
         change (length w mod 15 < 15).
         apply Nat.mod_upper_bound. lia.
      * exact Hbit.
    + apply residue_class_regex_correct;
        [apply Nat.mod_upper_bound; lia|reflexivity].
Qed.

Lemma rotate15_after15 s :
  length s = 15 ->
  Nat.iter 15 Mod15Example.rotate15 s = s.
Proof.
  intro Hs.
  do 15 (destruct s as [|? s]; [simpl in Hs; lia|]).
  destruct s as [|? s]; [reflexivity|simpl in Hs; lia].
Qed.

Lemma context_acceptb_mod15 s w :
  length s = 15 ->
  context_acceptb s w = nth (length w mod 15) s false.
Proof.
  intros Hs. unfold context_acceptb. rewrite consume_context_iter.
  generalize (length w) as n. intro n.
  induction n using (well_founded_induction lt_wf).
  destruct (lt_dec n 15) as [Hsmall|Hlarge].
  - rewrite Nat.mod_small by exact Hsmall.
    pose proof (context_acceptb_repeat_nth s (n := n) ltac:(lia)) as Hnth.
    unfold context_acceptb in Hnth. rewrite consume_context_iter in Hnth.
    now rewrite repeat_length in Hnth.
  - assert (Hsplit : n = 15 + (n - 15)) by lia.
    rewrite Hsplit.
    replace (15 + (n - 15)) with ((n - 15) + 15) by lia.
    rewrite Nat.iter_add, rotate15_after15 by exact Hs.
    rewrite Nat.add_mod by lia.
    replace (15 mod 15) with 0 by reflexivity.
    rewrite Nat.add_0_r, Nat.mod_mod by lia.
    apply H. lia.
Qed.

Theorem mod15_representative_correct s :
  length s = 15 ->
  lang_equiv (rewpla_denote Bool.eqb (mod15_representative s))
    (mod15_residual_language s).
Proof.
  intros Hs [u v]. unfold mod15_representative.
  change ((rewpla_denote Bool.eqb requested_rewpla_bool (u, v) \/
    positive_lookahead (rewpla_denote Bool.eqb
      (embed_regex (selected_residue_regex s))) (u, v)) <->
    mod15_residual_language s (u, v)).
  rewrite requested_rewpla_semantics.
  unfold mod15_residual_language. destruct u as [|a u].
  - rewrite <- ends_in_ab_correct. simpl.
    split.
    + intros [H|[p [Hp Hout]]].
      * destruct H as [H _]. discriminate H.
      * apply (proj1 (embed_regex_semantics Bool.eqb bool_eqb_spec
          (selected_residue_regex s) p)) in Hp.
        destruct Hp as [x [-> Hx]].
        unfold constraint_projection in Hout. simpl in Hout.
        rewrite app_nil_r in Hout. inversion Hout; subst x.
        right. split; [reflexivity|].
        rewrite context_acceptb_mod15 by exact Hs.
        now apply (proj1 (selected_residue_regex_correct s v Hs)).
    + intros [H|[_ H]].
      * destruct H as [H _]. exfalso. apply H. reflexivity.
      * right. exists (v, []). split.
        -- apply (proj2 (embed_regex_semantics Bool.eqb bool_eqb_spec
             (selected_residue_regex s) (v, []))).
           exists v. split; [reflexivity|].
           apply (proj2 (selected_residue_regex_correct s v Hs)).
           now rewrite <- context_acceptb_mod15.
        -- unfold constraint_projection. simpl. now rewrite app_nil_r.
  - rewrite <- ends_in_ab_correct. simpl.
    split.
    + intros [H|[p [_ Hout]]].
      * left. split; [discriminate|exact H].
      * discriminate.
    + intros [H|[H _]]; [left; tauto|discriminate].
Qed.

(** Mechanization extension, after Eq. (30)--(31): the displayed expression
    reifies *every* reachable 15-bit state as a genuine REwPLA derivative
    representative, with full [M]-semantics rather than just [L_pi]. *)
Theorem requested_representative_derivative_correspondence w :
  lang_equiv
    (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb w requested_rewpla_bool))
    (rewpla_denote Bool.eqb
      (mod15_representative (Mod15Example.replay_witness w))).
Proof.
  eapply lang_equiv_trans.
  - apply requested_word_derivative_correspondence.
  - apply lang_equiv_sym. apply mod15_representative_correct.
    unfold Mod15Example.replay_witness. apply residual_run_length.
    reflexivity.
Qed.

(** Preserve the visible derivation trace at the two particularly important
    DFA states: [D_epsilon(r)=r] exactly, and [D_a(r)] in the user's compact
    lookahead form.  Later states retain the certified residue reification. *)
Definition requested_debug_representative
    (w : list bool) (s : Mod15Example.bitvec) : rewpla bool :=
  match w with
  | [] => requested_rewpla_bool
  | [true] => requested_after_a_display
  | _ => mod15_representative s
  end.

Theorem requested_debug_representative_correct w :
  lang_equiv
    (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb w requested_rewpla_bool))
    (rewpla_denote Bool.eqb
      (requested_debug_representative w
        (Mod15Example.replay_witness w))).
Proof.
  destruct w as [|a [|b w]].
  - change (lang_equiv
      (rewpla_denote Bool.eqb requested_rewpla_bool)
      (rewpla_denote Bool.eqb requested_rewpla_bool)).
    apply lang_equiv_refl.
  - destruct a.
    + exact requested_after_a_display_derivative_correct.
    + apply requested_representative_derivative_correspondence.
  - destruct a; cbn [requested_debug_representative];
      apply requested_representative_derivative_correspondence.
Qed.

Theorem mod15_representative_nullable s :
  length s = 15 ->
  rewpla_nullable (mod15_representative s) = nth 0 s false.
Proof.
  intro Hs.
  pose proof (mod15_representative_correct s Hs ([], [])) as Hpair.
  assert (Hempty : mod15_residual_language s ([], []) <->
      nth 0 s false = true).
  { unfold mod15_residual_language.
    rewrite (context_acceptb_mod15 s [] Hs). simpl. tauto. }
  rewrite Hempty in Hpair.
  pose proof (rewpla_nullable_correct Bool.eqb bool_eqb_spec
    (mod15_representative s)) as Hnull.
  destruct (rewpla_nullable (mod15_representative s)) eqn:Hb;
    destruct (nth 0 s false) eqn:Hhead; try reflexivity.
  - exfalso. pose proof (proj1 Hpair
      (proj1 Hnull eq_refl)) as Hcontradiction.
    discriminate Hcontradiction.
  - exfalso. assert (Hd : rewpla_denote Bool.eqb
      (mod15_representative s) ([], [])).
    { apply (proj2 Hpair). reflexivity. }
    pose proof (proj2 Hnull Hd) as Hcontradiction. discriminate.
Qed.

(** Paper Eq. (24) and mechanization extension: the requested derivative
    DFA's final-state bit recognizes exactly the projected language [L_pi].
    Its state equivalence, proved above, remains the stronger full [M] one. *)
Theorem requested_bitvec_dfa_accept_correct w :
  hd false (Mod15Example.replay_witness w) = true <->
  rewpla_language Bool.eqb requested_rewpla_bool w.
Proof.
  pose proof (requested_word_derivative_correspondence w ([], [])) as Hpair.
  unfold mod15_residual_language in Hpair. simpl in Hpair.
  rewrite (context_acceptb_mod15 (Mod15Example.replay_witness w) []
    ltac:(unfold Mod15Example.replay_witness;
      apply residual_run_length; reflexivity)) in Hpair.
  simpl in Hpair.
  rewrite <- (rewpla_acceptb_correct Bool.eqb bool_eqb_spec
    requested_rewpla_bool w).
  unfold rewpla_acceptb.
  rewrite rewpla_nullable_correct by exact bool_eqb_spec.
  unfold Mod15Example.replay_witness in *.
  replace (hd false (fold_left Mod15Example.residue_step w
      Mod15Example.zeros15)) with
    (nth 0 (fold_left Mod15Example.residue_step w
      Mod15Example.zeros15) false)
    by (destruct (fold_left Mod15Example.residue_step w
      Mod15Example.zeros15); reflexivity).
  split.
  - intro Hhead. apply (proj2 Hpair). right.
    split; [reflexivity|exact Hhead].
  - intro Hd. apply (proj1 Hpair) in Hd as [H|[_ H]].
    + destruct H as [H _]. exfalso. apply H. reflexivity.
    + exact H.
Qed.

Lemma bitvec_eqb_spec x y :
  Mod15Example.bitvec_eqb x y = true <-> x = y.
Proof.
  revert y. induction x as [|a x IH]; intros [|b y]; simpl.
  - tauto.
  - split; [discriminate|discriminate].
  - split; [discriminate|discriminate].
  - rewrite Bool.andb_true_iff, Bool.eqb_true_iff, IH.
    split.
    + intros [-> ->]. reflexivity.
    + intro H. inversion H. now split.
Qed.

End RequestedCorrespondence.

(** * Certified enumeration for the requested expression

    The worklist below remains executable data.  Its small boolean
    certificates are reflected into propositions once, yielding reachability,
    closure, coverage and semantic non-duplication without trusting the JSON
    renderer or an external script. *)
Module RequestedStateEnumeration.

Import Mod15Example RequestedCorrespondence.

Definition states := Mod15Example.residue_witnessed_states.
Definition values : list Mod15Example.bitvec :=
  map (fun q => Mod15Example.replay_witness (witnessed_word q)) states.

Definition states_closedb : bool :=
  forallb (fun s =>
    forallb (fun a =>
      existsb (Mod15Example.bitvec_eqb
        (Mod15Example.residue_step s a)) values)
      Mod15Example.residue_alphabet) values.

Fixpoint bitvec_nodupb (xs : list Mod15Example.bitvec) : bool :=
  match xs with
  | [] => true
  | x :: xs' =>
      negb (existsb (Mod15Example.bitvec_eqb x) xs') &&
      bitvec_nodupb xs'
  end.

Example states_closedb_verified : states_closedb = true.
Proof. vm_compute. reflexivity. Qed.

Example states_nodupb_verified : bitvec_nodupb values = true.
Proof. vm_compute. reflexivity. Qed.

Example initial_in_values_verified :
  existsb (Mod15Example.bitvec_eqb Mod15Example.zeros15) values = true.
Proof. vm_compute. reflexivity. Qed.

Example states_count_verified : length states = 182.
Proof. vm_compute. reflexivity. Qed.

Lemma values_spec :
  values = map (fun q =>
    Mod15Example.replay_witness (witnessed_word q)) states.
Proof. reflexivity. Qed.

(** Prevent proof elaboration from repeatedly normalizing the 182-state BFS;
    the checked equations above remain the only reflection boundary. *)
Global Opaque states values.

Lemma existsb_bitvec_eqb x xs :
  existsb (Mod15Example.bitvec_eqb x) xs = true <-> In x xs.
Proof.
  apply existsb_state_eqb. exact bitvec_eqb_spec.
Qed.

Lemma bitvec_nodupb_correct xs : bitvec_nodupb xs = true <-> NoDup xs.
Proof.
  induction xs as [|x xs IH]; simpl; [split; constructor|].
  rewrite Bool.andb_true_iff, Bool.negb_true_iff, IH.
  split.
  - intros [Hfresh Hnd]. constructor; [|exact Hnd].
    intro Hin. apply (proj2 (existsb_bitvec_eqb x xs)) in Hin.
    congruence.
  - intro Hnd. inversion Hnd as [|? ? Hfresh Htail]; subst.
    split; [|exact Htail].
    destruct (existsb (Mod15Example.bitvec_eqb x) xs) eqn:Hex;
      [|reflexivity]. exfalso. apply Hfresh.
    now apply (proj1 (existsb_bitvec_eqb x xs)).
Qed.

Theorem values_nodup : NoDup values.
Proof. apply (proj1 (bitvec_nodupb_correct values)); exact states_nodupb_verified. Qed.

Lemma closedb_sound xs :
  forallb (fun s =>
    forallb (fun a =>
      existsb (Mod15Example.bitvec_eqb
        (Mod15Example.residue_step s a)) xs)
      Mod15Example.residue_alphabet) xs = true ->
  forall s a,
    In s xs -> In a Mod15Example.residue_alphabet ->
    In (Mod15Example.residue_step s a) xs.
Proof.
  intros Hall s a Hs Ha.
  apply forallb_forall with (x := s) in Hall; [|exact Hs].
  apply forallb_forall with (x := a) in Hall; [|exact Ha].
  now apply (proj1 (existsb_bitvec_eqb _ xs)).
Qed.

Theorem values_closed s a :
  In s values ->
  In a Mod15Example.residue_alphabet ->
  In (Mod15Example.residue_step s a) values.
Proof.
  intros Hs Ha. apply (closedb_sound values); [|exact Hs|exact Ha].
  exact states_closedb_verified.
Qed.

Lemma bool_in_residue_alphabet a : In a Mod15Example.residue_alphabet.
Proof. destruct a; simpl; auto. Qed.

Lemma replay_witness_app w a :
  Mod15Example.replay_witness (w ++ [a]) =
  Mod15Example.residue_step (Mod15Example.replay_witness w) a.
Proof.
  unfold Mod15Example.replay_witness. rewrite fold_left_app. reflexivity.
Qed.

(** Every word derivative is covered by the saturated list. *)
Theorem every_replay_in_values w :
  In (Mod15Example.replay_witness w) values.
Proof.
  induction w using rev_ind.
  - apply (proj1 (existsb_bitvec_eqb _ values)).
    exact initial_in_values_verified.
  - rewrite replay_witness_app. apply values_closed; [exact IHw|].
    apply bool_in_residue_alphabet.
Qed.

(** Every returned state has a concrete reaching word. *)
Theorem every_value_is_reachable s :
  In s values -> exists w, Mod15Example.replay_witness w = s.
Proof.
  rewrite values_spec, in_map_iff.
  intros [q [<- Hq]]. now exists (witnessed_word q).
Qed.

Theorem every_value_has_length_15 s :
  In s values -> length s = 15.
Proof.
  intro Hs. destruct (every_value_is_reachable Hs) as [w <-].
  unfold Mod15Example.replay_witness.
  apply residual_run_length. reflexivity.
Qed.

Lemma nodup_map_injective_on
  {X Y : Type} (f : X -> Y) (xs : list X) :
  NoDup (map f xs) ->
  forall x y, In x xs -> In y xs -> f x = f y -> x = y.
Proof.
  intro Hnd. induction xs as [|q qs IH]; intros x y Hx Hy Hxy;
    [contradiction|].
  inversion Hnd as [|? ? Hfresh Htail]; subst.
  destruct Hx as [->|Hx], Hy as [->|Hy]; try reflexivity.
  - exfalso. apply Hfresh. rewrite Hxy. apply in_map. exact Hy.
  - exfalso. apply Hfresh. rewrite <- Hxy. apply in_map. exact Hx.
  - now apply IH.
Qed.

(** Returned worklist entries are pairwise distinct modulo the complete
    pair-language semantics [M]. *)
Theorem requested_states_semantically_unique q r :
  In q states -> In r states ->
  lang_equiv
    (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb (witnessed_word q) requested_rewpla_bool))
    (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb (witnessed_word r) requested_rewpla_bool)) ->
  q = r.
Proof.
  intros Hq Hr Hsem.
  assert (Hnd : NoDup (map
    (fun q => Mod15Example.replay_witness (witnessed_word q)) states)).
  { rewrite <- values_spec. exact values_nodup. }
  eapply nodup_map_injective_on; [exact Hnd|exact Hq|exact Hr|].
  now apply (proj1 (requested_derivatives_equiv_iff
    (witnessed_word q) (witnessed_word r))).
Qed.

(** A structured certified enumeration ties the computed witnesses to the
    concrete syntax tree, so the exact-count statement cannot silently count
    an unrelated transition system. *)
Record semantic_derivative_enumeration := {
  enumeration_root : rewpla bool;
  enumeration_witnesses : list (list bool)
}.

Definition requested_semantic_derivative_enumeration :
  semantic_derivative_enumeration :=
  {| enumeration_root := requested_rewpla_bool;
     enumeration_witnesses := map witnessed_word states |}.

Definition semantic_derivative_state_count
  (e : semantic_derivative_enumeration) : nat :=
  length (enumeration_witnesses e).

Theorem requested_derivative_state_count_exact :
  semantic_derivative_state_count
    requested_semantic_derivative_enumeration = 182.
Proof.
  unfold semantic_derivative_state_count,
    requested_semantic_derivative_enumeration. simpl.
  rewrite map_length. exact states_count_verified.
Qed.

(** [every_replay_in_values], [requested_word_derivative_correspondence] and
    [requested_states_semantically_unique] jointly state coverage, semantic
    interpretation and pairwise uniqueness without forcing Rocq to expand the
    182-entry witness list again in one large proof term. *)

End RequestedStateEnumeration.

(** Mechanization extension: printable Rocq data, including the actual REwPLA
    expression representing each state; the existing debug record supplies
    IDs, shortest witnesses, final bits and both transition targets. *)
Definition requested_derivative_regex_states :
  list (Mod15Example.residue_debug_state * rewpla bool) :=
  map (fun q => (q, RequestedCorrespondence.requested_debug_representative
      (Mod15Example.debug_witness q)
      (Mod15Example.debug_representative q)))
    Mod15Example.requested_derivative_debug_states.

Theorem requested_derivative_regex_states_count :
  length requested_derivative_regex_states = 182.
Proof.
  unfold requested_derivative_regex_states.
  rewrite map_length. exact Mod15Example.requested_debug_state_count.
Qed.

(** The printed expressions are not merely syntactically distinct: no two
    enumerated reaching words yield equivalent full [M] pair languages. *)
Theorem requested_printed_regexes_semantically_unique q r :
  In q RequestedStateEnumeration.states ->
  In r RequestedStateEnumeration.states ->
  lang_equiv
    (rewpla_denote Bool.eqb
      (RequestedCorrespondence.requested_debug_representative
        (witnessed_word q)
        (Mod15Example.replay_witness (witnessed_word q))))
    (rewpla_denote Bool.eqb
      (RequestedCorrespondence.requested_debug_representative
        (witnessed_word r)
        (Mod15Example.replay_witness (witnessed_word r)))) ->
  q = r.
Proof.
  intros Hq Hr Hsem.
  apply (RequestedStateEnumeration.requested_states_semantically_unique
    Hq Hr).
  eapply lang_equiv_trans.
  - apply RequestedCorrespondence.requested_debug_representative_correct.
  - eapply lang_equiv_trans; [exact Hsem|].
    apply lang_equiv_sym.
    apply RequestedCorrespondence.requested_debug_representative_correct.
Qed.

Print Assumptions rewpla_width_le_nodes.
Print Assumptions rewpla_eqb_spec.
Print Assumptions generator_length_bound.
Print Assumptions nodupb_nodup.
Print Assumptions continuation_generators_nodup.
Print Assumptions constraint_generators_nodup.
Print Assumptions raw_generator_inclusion.
Print Assumptions normalized_generator_inclusion.
Print Assumptions aci_union_normalize_correct.
Print Assumptions rewpla_aci_normalize_correct.
Print Assumptions rewpla_aci_equiv_sound_M.
Print Assumptions rewpla_simplify_correct_M.
Print Assumptions rewpla_simplify_aci_correct_M.
Print Assumptions rewpla_normalized_symbol_step_correct_M.
Print Assumptions rewpla_normalized_word_step_correct_M.
Print Assumptions rewpla_normalized_word_step_accept_correct.
Print Assumptions rewpla_semantic_step_congruent.
Print Assumptions rewpla_semantic_run_accept_correct.
Print Assumptions normal_forms_cover_finite_union.
Print Assumptions constraint_terms_empty_main.
Print Assumptions symbol_derivative_represented_all.
Print Assumptions normal_forms_symbol_derivative_closed_M.
Print Assumptions nonempty_word_residual_normal_form.
Print Assumptions semantic_derivatives_finite_cover_and_bound.
Print Assumptions semantic_derivatives_bounded_constraint_cover.
Print Assumptions semantic_derivatives_single_constraint_cover_bound.
Print Assumptions canonical_normal_forms_width_bound.
Print Assumptions canonical_normal_forms_single_constraint_bound.
Print Assumptions rewpla_states_closedb_sound.
Print Assumptions rewpla_saturated_dfa_accept_correct.
Print Assumptions rewpla_lookahead_lift_correct_M.
Print Assumptions rewpla_paper_normalize_correct_M.
Print Assumptions rewpla_paper_word_step_correct_M.
Print Assumptions rewpla_paper_states_closedb_sound.
Print Assumptions rewpla_paper_saturated_dfa_accept_correct.
Print Assumptions normal_forms_length.
Print Assumptions canonical_normal_forms_nodup.
Print Assumptions canonical_normal_forms_length_bound.
Print Assumptions canonical_normal_forms_semantic_coverage.
Print Assumptions canonical_normal_forms_general_bound.
Print Assumptions paper_double_exponential_bound.
Print Assumptions encode_pair_acceptance.
Print Assumptions derivative_states_nodup.
Print Assumptions Mod15Example.requested_exact_state_count.
Print Assumptions Mod15Example.requested_exact_derivative_state_count.
Print Assumptions Mod15Example.requested_worklist_is_saturated.
Print Assumptions RequestedCorrespondence.requested_initial_correspondence.
Print Assumptions RequestedCorrespondence.mod15_residual_symbol_quotient.
Print Assumptions RequestedCorrespondence.requested_word_derivative_correspondence.
Print Assumptions RequestedCorrespondence.mod15_residual_language_injective.
Print Assumptions RequestedCorrespondence.requested_derivatives_equiv_iff.
Print Assumptions RequestedCorrespondence.mod15_representative_correct.
Print Assumptions RequestedCorrespondence.requested_representative_derivative_correspondence.
Print Assumptions RequestedCorrespondence.requested_context_product_semantics.
Print Assumptions RequestedCorrespondence.requested_after_a_display_derivative_correct.
Print Assumptions RequestedCorrespondence.requested_debug_representative_correct.
Print Assumptions RequestedCorrespondence.mod15_representative_nullable.
Print Assumptions RequestedCorrespondence.requested_bitvec_dfa_accept_correct.
Print Assumptions rewpla_lookahead_union.
Print Assumptions rewpla_concat_assoc_M.
Print Assumptions rewpla_concat_one_left_M.
Print Assumptions rewpla_concat_one_right_M.
Print Assumptions rewpla_concat_zero_left_M.
Print Assumptions rewpla_concat_zero_right_M.
Print Assumptions empty_pair_concat_comm.
Print Assumptions empty_pair_concat_is_operand.
Print Assumptions rewpla_constraint_concat_comm.
Print Assumptions rewpla_constraint_concat_idempotent.
Print Assumptions constraint_expression_sound.
Print Assumptions rewpla_lookahead_constraint.
Print Assumptions constraint_concat_lookahead_lift.
Print Assumptions rewpla_lookahead_constraint_concat.
Print Assumptions RequestedStateEnumeration.every_replay_in_values.
Print Assumptions RequestedStateEnumeration.requested_states_semantically_unique.
Print Assumptions RequestedStateEnumeration.requested_derivative_state_count_exact.
Print Assumptions requested_derivative_regex_states_count.
Print Assumptions requested_printed_regexes_semantically_unique.
