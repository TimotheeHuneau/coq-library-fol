Require Import FOL.ModelTheory.Core.

(* Non-constructive axioms *)

Definition PI: Prop := forall P, forall p1 p2: P, p1 = p2.
Definition LEM: Prop := forall P: Prop, (P \/ ~ P).
Definition AC: Prop :=
  forall (A B: Type) (R: A -> B -> Prop),
  (forall a: A, exists b: B, R a b) ->
  (exists f: A -> B, forall a, R a (f a)).
Definition FE  := forall (A B: Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.


Definition injective {X Y :Type} (f: X -> Y) :=
  forall (x x' : X), f x = f x' -> x = x'.

Record lessthanT (ltT: Type -> Type -> Prop): Prop := {
  ltT_refl: Reflexive ltT;
  ltT_trans: Transitive ltT;
  ltT_prod: forall X X' Y Y', ltT X Y -> ltT X' Y' -> ltT (X * X')%type (Y * Y')%type;
  ltT_sum: forall X X' Y Y', ltT X Y -> ltT X' Y' -> ltT (X + X')%type (Y + Y')%type;
  ltT_list: forall X Y, ltT X Y -> ltT (list X) (list Y);
  ltT_inj: forall X Y, (exists f: X -> Y, injective f) -> ltT X Y;
}.

Section DLS.

  Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller}.
  Notation "X ≤ Y" := (smaller X Y) (at level 80) : type_scope.

  Context {s_f: funcs_signature}.
  Context {s_P:  preds_signature}.
  Context (M: model).

  Definition gDLS_on := 
    exists (N: model),
    (N ≤ (term + form)%type) /\ N ⪳ M.

End DLS.

Section LogicalPrinciples.

  Definition gBDP_on B X :=
    forall (P: X -> Prop),
    exists f: B -> X,
    (forall b, P (f b)) -> (forall x, P x).

  Definition gBEP_on B X :=
    forall (P: X -> Prop),
    exists f: B -> X,
    (exists x, P x) -> (exists b, P (f b)).
  
  Definition gBDP B := forall X, gBDP_on B X.
  Definition gBEP B := forall X, gBEP_on B X.

End LogicalPrinciples.