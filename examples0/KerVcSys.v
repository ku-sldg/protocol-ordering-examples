Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(3,0) :: (2,0) :: (1,3) :: nil ;
	label := fun ev =>
		match ev with
		| 3 => inr (cor _ vc)
		| 0 => inl (msp _ vc sys)
		| 2 => inr (cor _ sys)
		| 1 => inl (msp _ ker vc)
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
		(3,0) :: (1,3) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 3 => inr (cor _ ker)
		| 0 => inl (msp _ vc sys)
		| 1 => inl (msp _ ker vc)
		| 2 => inr (cor _ sys)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A2 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(3,1) :: (1,0) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 3 => inr (cor _ ker)
		| 1 => inl (msp _ ker vc)
		| 0 => inl (msp _ vc sys)
		| 2 => inr (cor _ sys)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A3 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(3,1) :: (1,0) :: (2,0) :: (4,1) :: nil ;
	label := fun ev =>
		match ev with
		| 3 => inr (cor _ vc)
		| 1 => inl (msp _ ker vc)
		| 0 => inl (msp _ vc sys)
		| 2 => inr (cor _ sys)
		| 4 => inr (cor _ ker)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition KerVcSys : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: nil.
