Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(6,0) :: (5,0) :: (3,2) :: (2,1) :: (4,3) :: (1,6) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 5 => inr (cor _ sys)
		| 3 => inl (msp _ mno abc)
		| 2 => inl (msp _ lkim ker)
		| 1 => inl (msp _ abc vc)
		| 4 => inl (msp _ mno lkim)
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
		(6,0) :: (3,2) :: (2,6) :: (2,1) :: (4,3) :: (1,0) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ ker)
		| 3 => inl (msp _ mno abc)
		| 2 => inl (msp _ lkim ker)
		| 1 => inl (msp _ abc vc)
		| 4 => inl (msp _ mno lkim)
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
		(6,1) :: (1,0) :: (5,0) :: (3,7) :: (3,2) :: (7,1) :: (2,1) :: (4,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ abc vc)
		| 5 => inr (cor _ sys)
		| 3 => inl (msp _ mno abc)
		| 7 => inr (cor _ abc)
		| 2 => inl (msp _ lkim ker)
		| 4 => inl (msp _ mno lkim)
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
		(6,2) :: (2,1) :: (3,2) :: (4,3) :: (4,7) :: (7,2) :: (1,0) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ ker)
		| 2 => inl (msp _ lkim ker)
		| 1 => inl (msp _ abc vc)
		| 3 => inl (msp _ mno abc)
		| 4 => inl (msp _ mno lkim)
		| 7 => inr (cor _ lkim)
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
		(6,1) :: (1,0) :: (5,0) :: (3,2) :: (2,1) :: (7,3) :: (4,8) :: (8,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ abc vc)
		| 5 => inr (cor _ sys)
		| 3 => inl (msp _ mno abc)
		| 2 => inl (msp _ lkim ker)
		| 7 => inr (cor _ abc)
		| 4 => inl (msp _ mno lkim)
		| 8 => inr (cor _ mno)
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
		(6,1) :: (1,0) :: (5,0) :: (3,2) :: (2,1) :: (7,3) :: (4,3) :: (8,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ abc vc)
		| 5 => inr (cor _ sys)
		| 3 => inl (msp _ mno abc)
		| 2 => inl (msp _ lkim ker)
		| 7 => inr (cor _ abc)
		| 4 => inl (msp _ mno lkim)
		| 8 => inr (cor _ mno)
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
		(8,4) :: (4,3) :: (6,2) :: (2,1) :: (3,2) :: (1,0) :: (5,0) :: (7,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 8 => inr (cor _ mno)
		| 4 => inl (msp _ mno lkim)
		| 3 => inl (msp _ mno abc)
		| 6 => inr (cor _ ker)
		| 2 => inl (msp _ lkim ker)
		| 1 => inl (msp _ abc vc)
		| 5 => inr (cor _ sys)
		| 7 => inr (cor _ lkim)
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
		(8,4) :: (4,9) :: (6,2) :: (2,1) :: (3,2) :: (9,3) :: (1,0) :: (5,0) :: (7,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 8 => inr (cor _ mno)
		| 4 => inl (msp _ mno lkim)
		| 9 => inr (rep _ mno)
		| 6 => inr (cor _ ker)
		| 2 => inl (msp _ lkim ker)
		| 1 => inl (msp _ abc vc)
		| 3 => inl (msp _ mno abc)
		| 5 => inr (cor _ sys)
		| 7 => inr (cor _ lkim)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P6 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: A6 :: A7 :: nil.
