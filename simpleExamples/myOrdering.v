Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.VcSys.
Require Import ProtocolOrderingExamples.KerVcSys.
Require Import ProtocolOrderingExamples.RtmKerVcSys.
Require Import ProtocolOrderingExamples.KerVmVcSys.


Eval compute in (order_fix VcSys VcSys).             (** equiv *)
Eval compute in (order_fix VcSys KerVcSys).          (** leq *)
Eval compute in (order_fix VcSys RtmKerVcSys).       (** leq *)
Eval compute in (order_fix VcSys KerVmVcSys).        (** leq *)

Eval compute in (order_fix KerVcSys VcSys).          (** geq *)
Eval compute in (order_fix KerVcSys KerVcSys).       (** equiv *)
Eval compute in (order_fix KerVcSys RtmKerVcSys).    (** leq *)
Eval compute in (order_fix KerVcSys KerVmVcSys).     (** equiv *)

Eval compute in (order_fix RtmKerVcSys VcSys).       (** geq *)
Eval compute in (order_fix RtmKerVcSys KerVcSys).    (** geq *)
Eval compute in (order_fix RtmKerVcSys RtmKerVcSys). (** equiv *)
Eval compute in (order_fix RtmKerVcSys KerVmVcSys).  (** geq *)

Eval compute in (order_fix KerVmVcSys VcSys).        (** geq *)
Eval compute in (order_fix KerVmVcSys KerVcSys).     (** equiv *)
Eval compute in (order_fix KerVmVcSys RtmKerVcSys).  (** leq *)
Eval compute in (order_fix KerVmVcSys KerVmVcSys).   (** equiv *)


