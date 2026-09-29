Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.advOrder.

Require Import ProtocolOrderingExamples.P1.
Require Import ProtocolOrderingExamples.P2.
Require Import ProtocolOrderingExamples.P3.
Require Import ProtocolOrderingExamples.P4.

Lemma P1_P2 : myOrder_fix P1 P2 = geq.
Proof. auto. Qed.

Lemma P2_P3 : myOrder_fix P2 P3 = equiv.
Proof. auto. Qed.

Lemma P1_P4 : myOrder_fix P1 P4 = leq.
Proof. vm_compute; reflexivity. Qed.

