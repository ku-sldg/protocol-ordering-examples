Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.make_adversary_ordering.

Require Import ProtocolOrderingExamples.components.

Definition advOrder : list (tauTaggedLabel components * tauTaggedLabel components) := 
    (blankTag _ (cor _ nwk), blankTag _ (cor _ swk)) ::
    (blankTag _ (cor _ rtlib), blankTag _ (cor _ appm)) ::
    (tauTag _ (cor _ nwk), tauTag _ (cor _ swk)) ::
    (tauTag _ (cor _ rtlib), tauTag _ (cor _ appm)) ::
    nil.

Lemma trianglelefteq_antisymmetric : forall t1 t2,
    makeTrianglelefteq advOrder t1 t2 -> 
    makeTrianglelefteq advOrder t2 t1 -> 
    t1 = t2.
Proof.
    rewrite <- (makeTrianglelefteq_antisymmetric_same eqDec_components advOrder);
    vm_compute; auto.
Qed.
