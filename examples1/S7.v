Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(6,0) :: (5,0) :: (4,1) :: (1,6) :: (1,2) :: (3,4) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ vm a2)
		| 1 => inl (msp _ a1 vc)
		| 2 => inl (msp _ a2 ker)
		| 3 => inl (msp _ vm a1)
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
		(6,0) :: (4,1) :: (1,2) :: (3,4) :: (2,6) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ ker)
		| 4 => inl (msp _ vm a2)
		| 1 => inl (msp _ a1 vc)
		| 2 => inl (msp _ a2 ker)
		| 3 => inl (msp _ vm a1)
		| 5 => inr (cor _ sys)
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
		(6,1) :: (1,2) :: (5,0) :: (4,1) :: (7,1) :: (3,4) :: (3,7) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ a1 vc)
		| 2 => inl (msp _ a2 ker)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ vm a2)
		| 7 => inr (cor _ a1)
		| 3 => inl (msp _ vm a1)
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
		(6,2) :: (2,0) :: (4,1) :: (4,7) :: (1,2) :: (7,2) :: (3,4) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ ker)
		| 2 => inl (msp _ a2 ker)
		| 4 => inl (msp _ vm a2)
		| 1 => inl (msp _ a1 vc)
		| 7 => inr (cor _ a2)
		| 3 => inl (msp _ vm a1)
		| 5 => inr (cor _ sys)
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
		(6,2) :: (2,0) :: (4,1) :: (1,2) :: (3,8) :: (8,4) :: (5,0) :: (7,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ ker)
		| 2 => inl (msp _ a2 ker)
		| 4 => inl (msp _ vm a2)
		| 1 => inl (msp _ a1 vc)
		| 3 => inl (msp _ vm a1)
		| 8 => inr (cor _ vm)
		| 5 => inr (cor _ sys)
		| 7 => inr (cor _ a2)
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
		(8,3) :: (3,4) :: (6,1) :: (1,2) :: (5,0) :: (4,1) :: (7,3) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 8 => inr (cor _ vm)
		| 3 => inl (msp _ vm a1)
		| 4 => inl (msp _ vm a2)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ a1 vc)
		| 2 => inl (msp _ a2 ker)
		| 5 => inr (cor _ sys)
		| 7 => inr (cor _ a1)
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
		(6,2) :: (2,0) :: (4,1) :: (1,2) :: (3,4) :: (5,0) :: (8,3) :: (7,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ ker)
		| 2 => inl (msp _ a2 ker)
		| 4 => inl (msp _ vm a2)
		| 1 => inl (msp _ a1 vc)
		| 3 => inl (msp _ vm a1)
		| 5 => inr (cor _ sys)
		| 8 => inr (cor _ vm)
		| 7 => inr (cor _ a2)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A7 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,9) :: (6,1) :: (1,2) :: (5,0) :: (4,1) :: (7,3) :: (9,4) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 8 => inr (cor _ vm)
		| 3 => inl (msp _ vm a1)
		| 9 => inr (rep _ vm)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ a1 vc)
		| 2 => inl (msp _ a2 ker)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ vm a2)
		| 7 => inr (cor _ a1)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition S7 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: A6 :: A7 :: nil.
