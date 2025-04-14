Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(6,0) :: (5,0) :: (4,1) :: (4,2) :: (1,6) :: (2,0) :: (3,1) :: (3,2) :: nil ;
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
		(6,0) :: (4,1) :: (4,2) :: (1,0) :: (2,6) :: (3,1) :: (3,2) :: (5,0) :: nil ;
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
		(6,1) :: (1,0) :: (5,0) :: (4,1) :: (4,2) :: (2,0) :: (7,1) :: (3,2) :: (3,7) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ a1 vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ vm a2)
		| 2 => inl (msp _ a2 ker)
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
		(6,2) :: (2,0) :: (4,1) :: (4,7) :: (1,0) :: (7,2) :: (3,2) :: (3,1) :: (5,0) :: nil ;
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
		(6,1) :: (1,0) :: (5,0) :: (4,1) :: (4,2) :: (2,0) :: (7,3) :: (3,1) :: (3,2) :: (8,4) :: (8,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ a1 vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ vm a2)
		| 2 => inl (msp _ a2 ker)
		| 7 => inr (cor _ a1)
		| 3 => inl (msp _ vm a1)
		| 8 => inr (cor _ vm)
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
		(6,1) :: (1,0) :: (5,0) :: (4,8) :: (8,3) :: (7,3) :: (3,1) :: (3,2) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ a1 vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ vm a2)
		| 8 => inr (cor _ vm)
		| 3 => inl (msp _ vm a1)
		| 7 => inr (cor _ a1)
		| 2 => inl (msp _ a2 ker)
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
		(8,4) :: (8,3) :: (4,2) :: (4,1) :: (3,2) :: (3,1) :: (6,2) :: (2,0) :: (1,0) :: (5,0) :: (7,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 8 => inr (cor _ vm)
		| 4 => inl (msp _ vm a2)
		| 3 => inl (msp _ vm a1)
		| 2 => inl (msp _ a2 ker)
		| 1 => inl (msp _ a1 vc)
		| 6 => inr (cor _ ker)
		| 5 => inr (cor _ sys)
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
		(8,4) :: (4,2) :: (4,1) :: (6,2) :: (2,0) :: (1,0) :: (3,8) :: (5,0) :: (7,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 8 => inr (cor _ vm)
		| 4 => inl (msp _ vm a2)
		| 2 => inl (msp _ a2 ker)
		| 1 => inl (msp _ a1 vc)
		| 6 => inr (cor _ ker)
		| 3 => inl (msp _ vm a1)
		| 5 => inr (cor _ sys)
		| 7 => inr (cor _ a2)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A8 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(6,1) :: (1,0) :: (5,0) :: (4,1) :: (4,2) :: (2,0) :: (7,3) :: (3,9) :: (9,4) :: (8,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ a1 vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ vm a2)
		| 2 => inl (msp _ a2 ker)
		| 7 => inr (cor _ a1)
		| 3 => inl (msp _ vm a1)
		| 9 => inr (rep _ vm)
		| 8 => inr (cor _ vm)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A9 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,4) :: (4,9) :: (6,2) :: (2,0) :: (9,3) :: (3,2) :: (3,1) :: (1,0) :: (5,0) :: (7,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 8 => inr (cor _ vm)
		| 4 => inl (msp _ vm a2)
		| 9 => inr (rep _ vm)
		| 6 => inr (cor _ ker)
		| 2 => inl (msp _ a2 ker)
		| 3 => inl (msp _ vm a1)
		| 1 => inl (msp _ a1 vc)
		| 5 => inr (cor _ sys)
		| 7 => inr (cor _ a2)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition S6 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: A6 :: A7 :: A8 :: A9 :: nil.
