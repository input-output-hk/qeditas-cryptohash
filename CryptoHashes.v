(*** Bill White ***)
(*** January 2015 ***)
(*** This code is free for anyone to use for any purpose. ***)

Require Export Coq.Lists.List.
Require Export Coq.Arith.Peano_dec.
Require Export omega.Omega.

Module Type BoolHashValsType.

  Parameter hashval : Type.
  Parameter hashbool : bool -> hashval.

  Axiom hashboolinj : forall m n, hashbool m = hashbool n -> m = n.

  Parameter hashval_eq_dec : forall (h1 h2:hashval), { h1 = h2 } + { h1 <> h2 }.

  Axiom hashval_ind : forall p:hashval -> Prop,
                          p (hashbool false) ->
                          p (hashbool true) ->
                          forall h, p h.

End BoolHashValsType.

Module BoolHashVals : BoolHashValsType.

  Definition hashval : Type := bool.

  Definition hashbool := fun b : bool => b.

  Lemma hashboolinj : forall m n, hashbool m = hashbool n -> m = n.
    intros m n H. exact H.
  Qed.

  Definition hashval_eq_dec (h1 h2:hashval) : { h1 = h2 } + { h1 <> h2 }.
    destruct h1; destruct h2.
    - left. reflexivity.
    - right. discriminate.
    - right. discriminate.
    - left. reflexivity.
  Defined.

  Lemma hashval_ind : forall p:hashval -> Prop,
                        p false ->
                        p true ->
                        forall h, p h.
    intros p H1 H2 [|]; assumption.
  Qed.
  
End BoolHashVals.

Module BoolHashVals2.
  Export BoolHashVals.

  Lemma preimage_exists : forall h:hashval, exists b:bool, hashbool b = h.
    intros h. apply (hashval_ind (fun h => exists b:bool, hashbool b = h)).
    - exists false. reflexivity.
    - exists true. reflexivity.
  Qed.

  (***
  Definition preimage_sig : forall h:hashval, { b:bool | hashbool b = h }.
    intros h. apply (hashval_ind (fun h => exists b:bool, hashbool b = h)).
    - exists false. reflexivity.
    - exists true. reflexivity.
  Defined.
   ***)

  (***
  Lemma preimage_computable : exists p:hashval -> bool, forall h:hashval, hashbool (p h) = h.
    exists (fun h:hashval =>
              match h with
                | false => false
                | true => true
              end). (*** Ill typed because hashval is opaque and cannot be analyzed. ***)
    ***)

  (*** But there's a way around this with bool. ***)
  Definition preimage_sig : forall h:hashval, { b:bool | hashbool b = h }.
    intros h.
    destruct (hashval_eq_dec (hashbool false) h) as [H1|H1].
    - exists false. exact H1.
    - destruct (hashval_eq_dec (hashbool true) h) as [H2|H2].
      + exists true. exact H2.
      + exfalso. revert h H1 H2.
        apply (hashval_ind (fun h => hashbool false <> h -> hashbool true <> h -> False)); tauto.
  Defined.

  Lemma preimage_computable : exists p:hashval -> bool, forall h:hashval, hashbool (p h) = h.
    exists (fun h:hashval =>
              match preimage_sig h with
                | exist b _ => b
              end).
    intros h. destruct (preimage_sig h) as [b H1].
    exact H1.
  Defined.
        
End BoolHashVals2.

Module Type NatHashValsType.

  Parameter hashval : Type.
  Parameter hashnat : nat -> hashval.

  Axiom hashnatinj : forall m n, hashnat m = hashnat n -> m = n.

  Parameter hashval_eq_dec : forall (h1 h2:hashval), { h1 = h2 } + { h1 <> h2 }.

  Axiom hashval_ind : forall p:hashval -> Prop,
                          (forall n, p (hashnat n)) ->
                          forall h, p h.

End NatHashValsType.

Module NatHashVals : NatHashValsType.

  Definition hashval : Type := nat.

  Definition hashnat := fun n : nat => n.

  Lemma hashnatinj : forall m n, hashnat m = hashnat n -> m = n.
    intros m n H. exact H.
  Qed.

  Definition hashval_eq_dec (h1 h2:hashval) : { h1 = h2 } + { h1 <> h2 }.
    destruct (eq_nat_dec h1 h2).
    - left. congruence.
    - right. congruence.
  Defined.

  Lemma hashval_ind : forall p:hashval -> Prop,
                         (forall n, p (hashnat n)) ->
                         forall h, p h.
    intros p H. exact H.
  Qed.
  
End NatHashVals.

Module Type TreeHashValsType.

  Parameter hashval : Type.
  Parameter hashnat : nat -> hashval.
  Parameter hashpair : hashval -> hashval -> hashval.

  Axiom hashnatinj : forall m n, hashnat m = hashnat n -> m = n.
  Axiom hashpairinj : forall h1a h1b h2a h2b, hashpair h1a h1b = hashpair h2a h2b -> h1a = h2a /\ h1b = h2b.
  Axiom hashnatpairdiscr : forall m h1 h2, hashnat m <> hashpair h1 h2.

  Parameter hashval_eq_dec : forall (h1 h2:hashval), { h1 = h2 } + { h1 <> h2 }.

  Axiom hashval_ind : forall p:hashval -> Prop,
                        (forall n, p (hashnat n)) ->
                        (forall h1, p h1 -> forall h2, p h2 -> p (hashpair h1 h2)) ->
                        forall h, p h.

End TreeHashValsType.

Module TreeHashVals : TreeHashValsType.

  Inductive hashval' : Type :=
  | hashnat' : nat -> hashval'
  | hashpair' : hashval' -> hashval' -> hashval'.

  Definition hashval := hashval'.
  Definition hashnat := hashnat'.
  Definition hashpair := hashpair'.

  Lemma hashnatinj : forall m n, hashnat m = hashnat n -> m = n.
    intros m n H. inversion H. reflexivity.
  Qed.

  Lemma hashpairinj : forall h1a h1b h2a h2b, hashpair h1a h1b = hashpair h2a h2b -> h1a = h2a /\ h1b = h2b.
    intros h1a h1b h2a h2b H1. inversion H1. tauto.
  Qed.

  Lemma hashnatpairdiscr : forall m h1 h2, hashnat m <> hashpair h1 h2.
    discriminate.
  Qed.

  Fixpoint hashval_eq_dec (h1 h2:hashval) : { h1 = h2 } + { h1 <> h2 }.
  destruct h1 as [n1|h1a h1b]; destruct h2 as [n2|h2a h2b]; try (right; discriminate).
  - destruct (eq_nat_dec n1 n2).
    + left. congruence.
    + right. congruence.
  - destruct (hashval_eq_dec h1a h2a).
    + destruct (hashval_eq_dec h1b h2b).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  Defined.

  Lemma hashval_ind : forall p:hashval -> Prop,
                         (forall n, p (hashnat n)) ->
                         (forall h1, p h1 -> forall h2, p h2 -> p (hashpair h1 h2)) ->
                         forall h, p h.
    exact hashval'_ind.
  Qed.
  
End TreeHashVals.

Fixpoint bitseq (n:nat) : Type :=
match n with
| 0 => unit
| S n' => (bool * bitseq n')%type
end.

Definition bitseq_eq_dec {n} (bs1 bs2:bitseq n) : { bs1 = bs2 } + { bs1 <> bs2 }.
induction n as [|n IHn].
- destruct bs1, bs2. decide equality.
- destruct bs1 as [b1 bs1], bs2 as [b2 bs2]. repeat decide equality.
Defined.

Definition addr := bitseq 160.

Definition addr_eq_dec (a1 a2: addr) : { a1 = a2 } + { a1 <> a2 }.
apply bitseq_eq_dec.
Defined.

Module Type HashValsType.

  Parameter hashval : Type.
  Parameter hashnat : nat -> hashval.
  Parameter hashaddr : addr -> hashval.
  Parameter hashpair : hashval -> hashval -> hashval.

  Axiom hashnatinj : forall m n, hashnat m = hashnat n -> m = n.
  Axiom hashaddrinj : forall alpha beta, hashaddr alpha = hashaddr beta -> alpha = beta.
  Axiom hashpairinj : forall h1a h1b h2a h2b, hashpair h1a h1b = hashpair h2a h2b -> h1a = h2a /\ h1b = h2b.

  Axiom hashnataddrdiscr : forall m alpha, hashnat m <> hashaddr alpha.
  Axiom hashnatpairdiscr : forall m h1 h2, hashnat m <> hashpair h1 h2.
  Axiom hashaddrpairdiscr : forall alpha h1 h2, hashaddr alpha <> hashpair h1 h2.

  Parameter hashval_eq_dec : forall (h1 h2:hashval), { h1 = h2 } + { h1 <> h2 }.

  Axiom hashval_ind : forall p:hashval -> Prop,
                        (forall n, p (hashnat n)) ->
                        (forall alpha, p (hashaddr alpha)) ->
                        (forall h1, p h1 -> forall h2, p h2 -> p (hashpair h1 h2)) ->
                        forall h, p h.

End HashValsType.

Module HashVals : HashValsType.

  Inductive hashval' : Type :=
  | hashnat' : nat -> hashval'
  | hashaddr' : addr -> hashval'
  | hashpair' : hashval' -> hashval' -> hashval'.

  Definition hashval := hashval'.
  Definition hashnat := hashnat'.
  Definition hashaddr := hashaddr'.
  Definition hashpair := hashpair'.

  Lemma hashnatinj : forall m n, hashnat m = hashnat n -> m = n.
    intros m n H. inversion H. reflexivity.
  Qed.

  Lemma hashaddrinj : forall alpha beta, hashaddr alpha = hashaddr beta -> alpha = beta.
    intros alpha beta H. inversion H. reflexivity.
  Qed.

  Lemma hashpairinj : forall h1a h1b h2a h2b, hashpair h1a h1b = hashpair h2a h2b -> h1a = h2a /\ h1b = h2b.
    intros h1a h1b h2a h2b H1. inversion H1. tauto.
  Qed.

  Lemma hashnataddrdiscr : forall m alpha, hashnat m <> hashaddr alpha.
    discriminate.
  Qed.

  Lemma hashnatpairdiscr : forall m h1 h2, hashnat m <> hashpair h1 h2.
    discriminate.
  Qed.

  Lemma hashaddrpairdiscr : forall alpha h1 h2, hashaddr alpha <> hashpair h1 h2.
    discriminate.
  Qed.

  Fixpoint hashval_eq_dec (h1 h2:hashval) : { h1 = h2 } + { h1 <> h2 }.
  destruct h1 as [n1|alpha1|h1a h1b]; destruct h2 as [n2|alpha2|h2a h2b]; try (right; discriminate).
  - destruct (eq_nat_dec n1 n2).
    + left. congruence.
    + right. congruence.
  - destruct (addr_eq_dec alpha1 alpha2).
    + left. congruence.
    + right. congruence.
  - destruct (hashval_eq_dec h1a h2a).
    + destruct (hashval_eq_dec h1b h2b).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  Defined.

  Lemma hashval_ind : forall p:hashval -> Prop,
                         (forall n, p (hashnat n)) ->
                         (forall alpha, p (hashaddr alpha)) ->
                         (forall h1, p h1 -> forall h2, p h2 -> p (hashpair h1 h2)) ->
                         forall h, p h.
    exact hashval'_ind.
  Qed.

End HashVals.

Export HashVals.

Lemma hashpair_neq_L h1 h2 : hashpair h1 h2 <> h1.
  revert h1 h2. apply (hashval_ind (fun h1 => forall h2, hashpair h1 h2 <> h1)).
  - intros n h2 H. symmetry in H. revert H. apply hashnatpairdiscr.
  - intros alpha h2 H. symmetry in H. revert H. apply hashaddrpairdiscr.
  - intros h1a IHa h1b IHb h2 H. apply hashpairinj in H. destruct H as [H _].
    revert H. apply IHa.
Qed.

Lemma hashpair_neq_R h1 h2 : hashpair h1 h2 <> h2.
  revert h2 h1. apply (hashval_ind (fun h2 => forall h1, hashpair h1 h2 <> h2)).
  - intros n h1 H. symmetry in H. revert H. apply hashnatpairdiscr.
  - intros alpha h1 H. symmetry in H. revert H. apply hashaddrpairdiscr.
  - intros h2a IHa h2b IHb h1 H. apply hashpairinj in H. destruct H as [_ H].
    revert H. apply IHb.
Qed.

Fixpoint hashlist (hl:list hashval) : hashval :=
match hl with
| h::hr => hashpair h (hashlist hr)
| nil => hashnat 0
end.

Lemma hashlistinj : forall hl1 hl2, hashlist hl1 = hashlist hl2 -> hl1 = hl2.
intros hl1. induction hl1 as [|h1 hr1 IH]; intros [|h2 hr2].
- reflexivity.
- simpl. intros H. exfalso. revert H. apply hashnatpairdiscr.
- simpl. intros H. exfalso. symmetry in H. revert H. apply hashnatpairdiscr.
- simpl. intros H3. apply hashpairinj in H3. destruct H3 as [H4 H5].
  subst h2. f_equal.
  apply IH. exact H5.
Qed.

Definition hashopair (h1 h2:option hashval) : option hashval :=
match h1,h2 with
| None,None => None
| Some h1,None => Some (hashpair (hashnat 0) h1)
| None,Some h2 => Some (hashpair (hashnat 1) h2)
| Some h1,Some h2 => Some (hashlist (hashnat 2::h1::h2::nil))
end.

Lemma hashopair_inj h1a h1b h2a h2b : hashopair h1a h1b = hashopair h2a h2b -> h1a = h2a /\ h1b = h2b.
destruct h1a as [h1a|]; destruct h2a as [h2a|];
destruct h1b as [h1b|]; destruct h2b as [h2b|]; simpl; intros H; try (discriminate H).
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashpairinj in H3.
  destruct H3 as [H4 H5]. apply hashpairinj in H5. destruct H5 as [H6 H7].
  split; congruence.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3].
  split; congruence.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3].
  split; congruence.
- split; reflexivity.
Qed.

Lemma hashopair_None_1 (h1 h2:option hashval) : hashopair h1 h2 = None -> h1 = None.
  destruct h1 as [h1|].
  - simpl. destruct h2; discriminate.
  - tauto.
Qed.

Lemma hashopair_None_2 (h1 h2:option hashval) : hashopair h1 h2 = None -> h2 = None.
  destruct h2 as [h2|].
  - destruct h1; discriminate.
  - tauto.
Qed.

Definition hashopair1 (h1:hashval) (h2:option hashval) : hashval :=
match h2 with
  | Some h2 => hashlist (hashnat 2::h1::h2::nil)
  | None => hashpair (hashnat 0) h1
end.

Definition hashopair2 (h1:option hashval) (h2:hashval) : hashval :=
match h1 with
  | Some h1 => hashlist (hashnat 2::h1::h2::nil)
  | None => hashpair (hashnat 1) h2
end.

Inductive subh (h:hashval) : hashval -> Prop :=
| subh_L h' : subh h (hashpair h h')
| subh_R h' : subh h (hashpair h' h)
| subh_PL h1 h2 : subh h h1 -> subh h (hashpair h1 h2)
| subh_PR h1 h2 : subh h h2 -> subh h (hashpair h1 h2)
.

Lemma subh_hashlist h hl : In h hl -> subh h (hashlist hl).
induction hl.
- simpl; tauto.
- intros [H1|H1]; simpl.
  + subst a. apply subh_L.
  + apply subh_PR. now apply IHhl.
Qed.

Lemma subh_tra h1 h2 h3 : subh h1 h2 -> subh h2 h3 -> subh h1 h3.
intros H. revert h3. induction H as [h2|h2|h2 h3 H1 IH1|h2 h3 H1 IH1].
- intros h3 H. induction H as [h3|h3|h3 h4 H2 IH2|h3 h4 H2 IH2].
  + apply subh_PL. apply subh_L.
  + apply subh_PR. apply subh_L.
  + now apply subh_PL.
  + now apply subh_PR.
- intros h3 H. induction H as [h3|h3|h3 h4 H2 IH2|h3 h4 H2 IH2].
  + apply subh_PL. apply subh_R.
  + apply subh_PR. apply subh_R.
  + now apply subh_PL.
  + now apply subh_PR.
- intros h4 H. induction H as [h4|h4|h4 h5 H2 IH2|h4 h5 H2 IH2].
  + apply IH1. apply subh_PL. apply subh_L.
  + apply IH1. apply subh_PR. apply subh_L.
  + now apply subh_PL.
  + now apply subh_PR.
- intros h4 H. induction H as [h4|h4|h4 h5 H2 IH2|h4 h5 H2 IH2].
  + apply IH1. apply subh_PL. apply subh_R.
  + apply IH1. apply subh_PR. apply subh_R.
  + now apply subh_PL.
  + now apply subh_PR.
Qed.

Lemma subh_irrefl h : ~ subh h h.
  revert h. apply hashval_ind.
  - intros n H. inversion H.
    + symmetry in H1. revert H1. apply hashnatpairdiscr.
    + symmetry in H1. revert H1. apply hashnatpairdiscr.
    + symmetry in H0. revert H0. apply hashnatpairdiscr.
    + symmetry in H0. revert H0. apply hashnatpairdiscr.
  - intros alpha H. inversion H.
    + symmetry in H1. revert H1. apply hashaddrpairdiscr.
    + symmetry in H1. revert H1. apply hashaddrpairdiscr.
    + symmetry in H0. revert H0. apply hashaddrpairdiscr.
    + symmetry in H0. revert H0. apply hashaddrpairdiscr.
  - intros h1 IH1 h2 IH2 H. inversion H.
    + revert H1. apply hashpair_neq_L.
    + revert H1. apply hashpair_neq_R.
    + apply IH1. apply subh_tra with (h2 := (hashpair h1 h2)).
      * apply subh_L.
      * apply hashpairinj in H0. destruct H0 as [H0a H0b]. congruence.
    + apply IH2. apply subh_tra with (h2 := (hashpair h1 h2)).
      * apply subh_R.
      * apply hashpairinj in H0. destruct H0 as [H0a H0b]. congruence.
Qed.

Lemma subh_asym h h' : subh h h' -> ~ subh h' h.
intros H1 H2. apply (subh_irrefl h).
now apply subh_tra with (h2 := h').
Qed.

