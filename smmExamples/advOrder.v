Require Import Coq.Lists.List.
Require Import Lia.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.trianglelefteq.

Definition advOrder_base : list (tauTaggedLabel components * tauTaggedLabel components) := 
    (blankTag _ (cor _ smm), blankTag _ (cor _ bios)) ::
    (blankTag _ (cor _ smm), blankTag _ (cor _ boot)) ::
    (blankTag _ (cor _ smm), blankTag _ (cor _ ker)) ::
    (blankTag _ (cor _ smm), blankTag _ (cor _ sinit)) ::
    (blankTag _ (cor _ smm), blankTag _ (cor _ mle)) ::
    (tauTag _ (cor _ smm), tauTag _ (cor _ bios)) ::
    (tauTag _ (cor _ smm), tauTag _ (cor _ boot)) ::
    (tauTag _ (cor _ smm), tauTag _ (cor _ ker)) ::
    (tauTag _ (cor _ smm), tauTag _ (cor _ sinit)) ::
    (tauTag _ (cor _ smm), tauTag _ (cor _ mle)) ::
    nil.

Definition level (comp : components) : nat :=
    match comp with
    | smm => 0
    | app => 0
    | bios => 1
    | boot => 1
    | ker => 1
    | sinit => 1
    | mle => 1
    | stm => 1
    | crtm => 2
    | cpu => 2
    end.

Definition levelAdv (a : advLabel components) : nat :=
    match a with
    | cor _ comp => level comp
    | rep _ comp => level comp
    end.

Definition rank (t : tauTaggedLabel components) : nat :=
    match t with
    | blankTag _ a => 2 * levelAdv a
    | tauTag _ a => 2 * levelAdv a + 1
    end.

Lemma trianglelefteq_base_charac : forall t1 t2,
    @trianglelefteq _ advOrder_base t1 t2 -> 
    t1 = t2 \/ rank t1 < rank t2.
Proof.
    intros t1 t2 H; induction H; auto.
    - simpl; lia.
    - right. simpl in H. repeat destruct H as [H|H]; try contradiction;
      inversion H; subst;
      simpl; lia.
    - destruct IHtrianglelefteq1 as [|IH1], IHtrianglelefteq2 as [|IH2]; subst; auto.
      simpl; lia.
Qed.

Lemma trianglelefteq_base_antisymmetric : forall t1 t2,
    @trianglelefteq _ advOrder_base t1 t2 -> 
    @trianglelefteq _ advOrder_base t2 t1 -> 
    t1 = t2.
Proof.
    intros t1 t2 H12 H21.
    apply trianglelefteq_base_charac in H12; apply trianglelefteq_base_charac in H21.
    destruct H12; auto. destruct H21; auto.
    lia.
Qed.

Definition myOrder_base_fix := @order_fix components (@trianglelefteq _ advOrder_base) (@trianglelefteqDec _ eqDec_components advOrder_base).




Definition advOrder_stm : list (tauTaggedLabel components * tauTaggedLabel components) :=
    (blankTag _ (cor _ smm), blankTag _ (cor _ stm)) ::
    (tauTag _ (cor _ smm), tauTag _ (cor _ stm)) ::
    advOrder_base.

Lemma trianglelefteq_stm_charac : forall t1 t2,
    @trianglelefteq _ advOrder_stm t1 t2 ->
    t1 = t2 \/ rank t1 < rank t2.
Proof.
    intros t1 t2 H; induction H; auto.
    - simpl; lia.
    - right. simpl in H. repeat destruct H as [H|H]; try contradiction;
      inversion H; subst;
      simpl; lia.
    - destruct IHtrianglelefteq1 as [|IH1], IHtrianglelefteq2 as [|IH2]; subst; auto.
      simpl; lia.
Qed.

Lemma trianglelefteq_stm_antisymmetric : forall t1 t2,
    @trianglelefteq _ advOrder_stm t1 t2 ->
    @trianglelefteq _ advOrder_stm t2 t1 ->
    t1 = t2.
Proof.
    intros t1 t2 H12 H21.
    apply trianglelefteq_stm_charac in H12; apply trianglelefteq_stm_charac in H21.
    destruct H12; auto. destruct H21; auto.
    lia.
Qed.

Definition myOrder_stm_fix := @order_fix components (@trianglelefteq _ advOrder_stm) (@trianglelefteqDec _ eqDec_components advOrder_stm).