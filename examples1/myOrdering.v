Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.S1.
Require Import ProtocolOrderingExamples.S2.
Require Import ProtocolOrderingExamples.S3.
Require Import ProtocolOrderingExamples.S4.
Require Import ProtocolOrderingExamples.S5.
Require Import ProtocolOrderingExamples.S6.
Require Import ProtocolOrderingExamples.S7.
Require Import ProtocolOrderingExamples.S8.

Eval compute in (order_fix S1 S1).       (** equiv *)
Eval compute in (order_fix S1 S2).       (** geq *)
Eval compute in (order_fix S1 S3).       (** geq *)
Eval compute in (order_fix S1 S4).       (** equiv *)
Eval compute in (order_fix S1 S5).       (** equiv *)
Eval compute in (order_fix S1 S6).       (** geq *)
Eval compute in (order_fix S1 S7).       (** geq *)
Eval compute in (order_fix S1 S8).       (** geq *)

Eval compute in (order_fix S2 S1).       (** leq *)
Eval compute in (order_fix S2 S2).       (** equiv *)
Eval compute in (order_fix S2 S3).       (** incomparable *)
Eval compute in (order_fix S2 S4).       (** leq *)
Eval compute in (order_fix S2 S5).       (** leq *)
Eval compute in (order_fix S2 S6).       (** incomparable *)
Eval compute in (order_fix S2 S7).       (** incomparable *)
Eval compute in (order_fix S2 S8).

Eval compute in (order_fix S3 S1).       (** leq *)
Eval compute in (order_fix S3 S2).       (** incomparable *)
Eval compute in (order_fix S3 S3).       (** equiv *)
Eval compute in (order_fix S3 S4).       (** leq *)
Eval compute in (order_fix S3 S5).       (** leq *)
Eval compute in (order_fix S3 S6).       (** incomparable *)
Eval compute in (order_fix S3 S7).       (** incomparable *)

Eval compute in (order_fix S4 S1).       (** equiv *)
Eval compute in (order_fix S4 S2).       (** geq *)
Eval compute in (order_fix S4 S3).       (** geq *)
Eval compute in (order_fix S4 S4).       (** equiv *)
Eval compute in (order_fix S4 S5).       (** equiv *)
Eval compute in (order_fix S4 S6).       (** geq *)
Eval compute in (order_fix S4 S7).       (** geq *)