Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,0) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inr (cor _ sys)
		| 0 => inl (msp _ vc sys)
		| 2 => inr (cor _ vc)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A1 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,0) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inr (cor _ sys)
		| 0 => inl (msp _ vc sys)
		| 2 => inr (cor _ ker)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition VcSys : list (attackgraph components) := 
	A0 :: A1 :: nil.
