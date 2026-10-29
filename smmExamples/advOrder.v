Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.make_adversary_ordering.

Require Import ProtocolOrderingExamples.components.

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

Lemma trianglelefteq_base_antisymmetric : forall t1 t2,
    makeTrianglelefteq advOrder_base t1 t2 -> 
    makeTrianglelefteq advOrder_base t2 t1 -> 
    t1 = t2.
Proof.
    rewrite <- (makeTrianglelefteq_antisymmetric_same eqDec_components advOrder_base);
    vm_compute; auto.
Qed.


Definition advOrder_stm : list (tauTaggedLabel components * tauTaggedLabel components) :=
    (blankTag _ (cor _ smm), blankTag _ (cor _ stm)) ::
    (tauTag _ (cor _ smm), tauTag _ (cor _ stm)) ::
    advOrder_base.

Lemma trianglelefteq_stm_antisymmetric : forall t1 t2,
    makeTrianglelefteq advOrder_stm t1 t2 -> 
    makeTrianglelefteq advOrder_stm t2 t1 -> 
    t1 = t2.
Proof.
    rewrite <- (makeTrianglelefteq_antisymmetric_same eqDec_components advOrder_stm);
    vm_compute; auto.
Qed.
