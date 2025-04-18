Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,0) :: (3,0) :: (1,4) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ vc)
		| 0 => inl (msp _ vc sys)
		| 3 => inr (cor _ sys)
		| 1 => inl (msp _ abc vc)
		| 2 => inl (msp _ lkim ker)
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
		(4,0) :: (1,0) :: (2,4) :: (2,1) :: (3,0) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ ker)
		| 0 => inl (msp _ vc sys)
		| 1 => inl (msp _ abc vc)
		| 2 => inl (msp _ lkim ker)
		| 3 => inr (cor _ sys)
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
		(4,1) :: (1,0) :: (3,0) :: (5,1) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ vc)
		| 1 => inl (msp _ abc vc)
		| 0 => inl (msp _ vc sys)
		| 3 => inr (cor _ sys)
		| 5 => inr (cor _ abc)
		| 2 => inl (msp _ lkim ker)
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
		(4,2) :: (2,1) :: (1,0) :: (3,0) :: (5,2) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ ker)
		| 2 => inl (msp _ lkim ker)
		| 1 => inl (msp _ abc vc)
		| 0 => inl (msp _ vc sys)
		| 3 => inr (cor _ sys)
		| 5 => inr (cor _ lkim)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P4 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: nil.
