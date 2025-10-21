Require Import List.
Require Import Classes.RelationClasses.
Require Import FOL.ModelTheory.Core.

(* Non-constructive axioms *)

Definition PI: Prop := forall P, forall p1 p2: P, p1 = p2.
Definition FE  := forall (A B: Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.

Definition injective {X Y :Type} (f: X -> Y) :=
  forall (x x' : X), f x = f x' -> x = x'.

Definition surjective {A B: Type} (f: A -> B) :=
	forall b: B, exists a: A, f a  = b.

Definition injectiveR {X Y: Type} (R: X -> Y -> Prop) :=
  forall x x' y0, R x y0 /\ R x' y0 -> x = x'.

Definition totalR {X Y: Type} (R: X -> Y -> Prop) :=
  forall x, exists y, R x y.

Definition directedR {X: Type} (R: X -> X -> Prop) :=
  forall x x', exists y, R x y /\ R x' y.

Class lessthanT (ltT: Type -> Type -> Prop): Prop := {
  ltT_refl: Reflexive ltT;
  ltT_trans: Transitive ltT;
  ltT_prod: forall X X' Y Y', ltT X Y -> ltT X' Y' -> ltT (X * X')%type (Y * Y')%type;
  ltT_sum: forall X X' Y Y', ltT X Y -> ltT X' Y' -> ltT (X + X')%type (Y + Y')%type;
  ltT_list: forall X Y, ltT X Y -> ltT (list X) (list Y);
  ltT_inj: forall X Y, (exists f: X -> Y, injective f) -> ltT X Y;
  ltT_dsum:
    forall J,
    forall (X Y: J -> Type),
    (exists E: forall j: J, X j -> Y j -> Prop, forall j, totalR (E j) /\ injectiveR (E j)) ->
    ltT (sigT X) (sigT Y);
  ltT_ex_sig: forall J, forall (A: J -> Prop), ltT (exists j, A j) (sig (fun j => A j));
}.


Definition SoS (lt: Type -> Type -> Prop) :=
  forall A B: Type, lt A B -> (exists f: B -> A, surjective f).

Section lt_lemmas.

  Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller}.
  Notation "X ≤ Y" := (smaller X Y) (at level 80) : type_scope.
  Existing Instance smaller_lt.

  #[global] Instance smaller_rfl: Reflexive smaller.
  Proof.
    apply ltT_refl.
  Qed.

  #[global] Instance smaller_trans: Transitive smaller.
  Proof.
    apply ltT_trans.
  Qed.

  #[global] Instance smaller_PO: PreOrder smaller.
  Proof.
    apply Build_PreOrder. apply smaller_rfl. apply smaller_trans.
  Qed.

  Lemma smaller_of_inj:
  forall X Y, (exists f: X -> Y, injective f) -> X ≤ Y.
  Proof.
    apply ltT_inj.
  Qed.

  Fact smaller_prod_incr:
  forall X X' Y Y', X ≤ Y -> X' ≤ Y' -> (X * X')%type ≤ (Y * Y')%type.
  Proof.
    apply ltT_prod.
  Qed.

  Fact smaller_dsum_incr:
  forall J,
  forall (X Y: J -> Type),
  (exists E: forall j: J, X j -> Y j -> Prop, forall j, totalR (E j) /\ injectiveR (E j)) -> sigT X ≤ sigT Y.
  Proof.
    apply ltT_dsum.
  Qed.

  Fact smaller_sum_incr:
  forall X X' Y Y', X ≤ Y -> X' ≤ Y' -> (X + X')%type ≤ (Y + Y')%type.
  Proof.
    apply ltT_sum.
  Qed.
  
  Fact list_incr:
  forall X Y, X ≤ Y -> (list X) ≤ (list Y).
  Proof.
    apply ltT_list.
  Qed.

  Fact smaller_of_sum_incr_l:
  forall X Y Z, (X + Y)%type ≤ Z -> X ≤ Z.
  Proof.
    intros X Y Z H.
    transitivity (X +Y)%type.
    apply smaller_of_inj. exists inl. intros x1 x2 eq. injection eq. apply id.
    apply H.
  Qed. 

  Fact smaller_of_sum_incr_r:
  forall X Y Z, (X + Y)%type ≤ Z -> Y ≤ Z.
    intros X Y Z H.
    transitivity (X +Y)%type.
    apply smaller_of_inj. exists inr. intros x1 x2 eq. injection eq. apply id.
    apply H.
  Qed.

  Fact X_smaller_lX:
  forall X, X ≤ (list X).
  Proof.
    intros X. apply smaller_of_inj.
    exists (fun x => x :: List.nil). intros x1 x2 eq. injection eq. apply id.
  Qed.

  Fact sum_smaller_list:
  forall X, smaller (X + X)%type (list X).
  Proof.
    intros X.
    apply smaller_of_inj.
    exists (fun x => match x with 
    | inl xl => xl :: List.nil 
    | inr xr => xr :: xr :: List.nil
    end).
    intros [xl1|xr1] [xl2|xr2] eq. all: inversion eq. all: reflexivity.
  Qed.

  Fact smaller_sum_assoc:
  forall A B C, (A + B + C)%type ≤ (A + (B + C))%type /\ (A + (B + C))%type ≤ (A + B + C)%type.
  Proof.
    intros A B C. split. all: apply smaller_of_inj.
    + exists (fun x => match x with
      | inl (inl a) => inl a 
      | inl (inr b) => inr (inl b)
      | inr c => inr (inr c)
      end).
      intros [[a1|b1]|c1] [[a2|b2]|c2] eq.
      all: try discriminate eq.
      all: inversion eq.
      all: reflexivity. 
    + exists (fun x => match x with 
      | inl a => inl (inl a)
      | inr (inl b) => inl (inr b)
      | inr (inr c) => inr c 
      end).
      intros [a1|[b1|c1]] [a2|[b2|c2]] eq.
      all: try discriminate eq.
      all: inversion eq.
      all: reflexivity.
  Qed.

  Fact smaller_sum_comm:
  forall A B, (A + B)%type ≤ (B + A)%type.
  Proof.
    intros A B. apply smaller_of_inj.
    exists (fun x => match x with 
      | inl a => inr a 
      |inr b => inl b 
      end).
    intros [a1|b1] [a2|b2 ] eq. 
    all: try discriminate eq. 
    all: inversion eq. 
    all: reflexivity.
  Qed.

End lt_lemmas.

Section DLS.

  Context {s_f: funcs_signature}.
  Context {s_P:  preds_signature}.
  Context (M: model).

  Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller}.
  Notation "X ≤ Y" := (smaller X Y) (at level 80) : type_scope.

  Definition gDLS_on := 
    exists (N: model),
    inhabited N /\ (N ≤ (term + form)%type) /\ N ⪳ M.

End DLS.

Arguments gDLS_on _ _ _ _  : clear implicits.

Section LogicalPrinciples.

  Definition gBDP_on B X :=
    forall (P: X -> Prop),
    exists f: B -> X,
    (forall b, P (f b)) -> (forall x, P x).

  Definition gBEP_on B X :=
    forall (P: X -> Prop),
    exists f: B -> X,
    (exists x, P x) -> (exists b, P (f b)).
  
  Definition gDDC_on B X :=
    forall R: X -> X -> Prop, directedR R ->
    exists f: B -> X, directedR (fun b b' => R (f b) (f b')).
  
  Definition gAC_on B X :=
    forall R: B -> X -> Prop, totalR R ->
    exists f: B -> X, forall b, R b (f b).

  Definition gBDP B := forall X, gBDP_on B X.
  Definition gBEP B := forall X, gBEP_on B X.
  Definition gDDC B := forall X, gDDC_on B X.
  Definition gAC B := forall X, gAC_on B X.

End LogicalPrinciples.