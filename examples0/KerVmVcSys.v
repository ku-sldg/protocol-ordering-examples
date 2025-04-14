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
		| 1 => inl (msp _ ker vc)
		| 2 => inl (msp _ ker vm)
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
		(4,0) :: (1,4) :: (2,1) :: (3,0) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ ker)
		| 0 => inl (msp _ vc sys)
		| 1 => inl (msp _ ker vc)
		| 2 => inl (msp _ ker vm)
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
		(4,1) :: (1,0) :: (2,4) :: (3,0) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ ker)
		| 1 => inl (msp _ ker vc)
		| 0 => inl (msp _ vc sys)
		| 2 => inl (msp _ ker vm)
		| 3 => inr (cor _ sys)
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
		(4,2) :: (2,1) :: (1,0) :: (3,0) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ ker)
		| 2 => inl (msp _ ker vm)
		| 1 => inl (msp _ ker vc)
		| 0 => inl (msp _ vc sys)
		| 3 => inr (cor _ sys)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A4 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,1) :: (1,0) :: (3,0) :: (2,5) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ vc)
		| 1 => inl (msp _ ker vc)
		| 0 => inl (msp _ vc sys)
		| 3 => inr (cor _ sys)
		| 2 => inl (msp _ ker vm)
		| 5 => inr (cor _ ker)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A5 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,1) :: (1,0) :: (3,0) :: (2,1) :: (5,2) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ vc)
		| 1 => inl (msp _ ker vc)
		| 0 => inl (msp _ vc sys)
		| 3 => inr (cor _ sys)
		| 2 => inl (msp _ ker vm)
		| 5 => inr (cor _ ker)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A6 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,2) :: (2,5) :: (1,6) :: (6,0) :: (5,1) :: (3,0) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ ker)
		| 2 => inl (msp _ ker vm)
		| 5 => inr (rep _ ker)
		| 0 => inl (msp _ vc sys)
		| 1 => inl (msp _ ker vc)
		| 6 => inr (cor _ ker)
		| 3 => inr (cor _ sys)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition KerVmVcSys : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: A6 :: nil.
