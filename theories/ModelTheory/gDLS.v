Require Import Lia.
Require Import List.
Require Import Eqdep.
Require Import PeanoNat.
Require Import Sets.Relations_1.
Require Import Classes.RelationClasses.
Require Import Relation_Definitions Morphisms.
Require Import FOL.ModelTheory.Core.
Require Import FOL.ModelTheory.LogicalPrinciples.
Require Import FOL.ModelTheory.ConstructiveLS.
Require Import FOL.ModelTheory.gDLS_defs.

Axiom pi: PI.
Axiom fe: FE.

(* ### *)

Definition set (M: Type) : Type := M -> Prop.

Definition subset {X} (A B: set X) := forall x, (A x -> B x).

Notation "A << B" := (subset A B) (at level 81).

Definition eqset {X} (A B: set X) := (A << B) /\ (B << A).

Notation "A == B" := (eqset A B) (at level 70).

Definition growing {X} (f: set X -> set X) :=
  forall A, A << f A.

Definition increasing {X} (f: set X -> set X) := 
  forall A B, A << B -> f A << f B.

Definition union {X} (A B: set X) :=
  fun x => A x \/ B x.

Definition inter {X} (A B: set X) :=
  fun x => A x /\ B x.

Definition Union {X I} (A_ : I -> set X) :=
  fun x => exists i, A_ i x.

Definition Inter {X I} (A_ : I -> set X) :=
  fun x => forall i, A_ i x.

Section Sets.

  Context {X: Type}.

  Instance subset_rfl: Reflexive (@subset X).
  Proof.
    intros A x. apply id.
  Qed.

  Instance subset_trans: Transitive (@subset X).
  Proof.
    intros A B C hAB hBC x hA. apply hBC, hAB, hA.
  Qed.

  Instance eqset_rfl: Reflexive (@eqset X).
  Proof.
    intros A. split; intros x; apply id.
  Qed.

  Instance eqset_symm: Symmetric (@eqset X).
  Proof.
    intros A B [h1 h2]. split.
    apply h2. apply h1.
  Qed.

  Instance eqset_trans: Transitive (@eqset X).
  Proof.
    intros A B C [hAB hBA] [hBC hCB]. split.
    - apply (subset_trans hAB hBC).
    - apply (subset_trans hCB hBA).
  Qed.

  Instance eqset_Equivalence: Equivalence (@eqset X).
  Proof.
    apply Build_Equivalence.
    apply eqset_rfl.
    apply eqset_symm.
    apply eqset_trans.
  Qed.

  Lemma subset_union {A B C: set X}:
  union A B << C <-> (A << C) /\ (B << C).
  Proof.
    firstorder.
  Qed.

  Fixpoint iteration {Y} (n: nat) (f: Y -> Y) (A: Y):=
    match n with
    | O => A
    | S m => f (iteration m f A)
    end.

  Lemma iteration_succ {Y} (f: Y -> Y): forall n, forall y,
  iteration (S n) f y = iteration n f (f y).
  Proof.
    intros n. induction n as [| n' ih].
    reflexivity.
    intros y. simpl. rewrite <-ih. simpl. reflexivity.
  Qed.

  Definition closure (f: set X -> set X) : set X -> set X :=
    fun A => (Union (fun n => iteration n f A)).  
End Sets.

Section fix_variables.

Context {s_f: funcs_signature}.
Context {s_P:  preds_signature}.
Context {M: model}.

Record of_set (A: set M) := {
  elem :> M;
  helem : A elem;
}.

Section HelperLemmas.

  Definition enveq (n: nat) (rho rho': env M) :=
    forall i, (i < n) -> rho i = rho' i.

  Inductive enveq' : nat -> Relation (env M): Type :=
    | enveq_0 (rho rho': env M): enveq' 0 rho rho'
    | enveq_S (n': nat) (rho rho': env M):
        rho 0 = rho' 0 -> enveq' n' (S >> rho) (S >> rho') -> enveq' (S n') rho rho'.

  Lemma enveq_enveq' (n: nat):
  forall (rho rho': env M), enveq n rho rho' <-> enveq' n rho rho'.
  Proof.
    intros rho rho'. split.
    all: generalize dependent rho'.
    all: generalize dependent rho.
    + induction n as [|n' IHn].
      - intros rho rho' _.  apply enveq_0.
      - intros rho rho' eq. apply (@enveq_S n' rho rho').
        * apply eq. lia. 
        * apply IHn.
          intros i hi.
          apply eq. lia.
    + intros rho rho' eq'. induction eq' as [rho rho' |n rho rho' h0 hn IHhS].
      - intros i hi. lia.
      - intros [|i'] hi.
        * apply h0.
        * apply IHhS. lia.
  Qed.

  #[export] Instance enveq_Equivalence (n: nat): Equivalence (enveq n).
  Proof.
    apply Build_Equivalence.
    + intros rho i _. reflexivity.
    + intros rho rho' H i hi. rewrite (H i hi). reflexivity.
    + intros rho0 rho1 rho2 H01 H12 i hi. rewrite (H01 i hi), (H12 i hi). reflexivity.
  Qed.

  Lemma enveq_of_feq (n: nat) (rho rho': env M):
  feq rho rho' -> enveq n rho rho'.
  Proof.
    intros H i _. apply H.
  Qed. 

  Lemma enveq_n_of_le:
  forall n m, n <= m ->
  forall rho rho', enveq m rho rho' -> enveq n rho rho'.
  Proof.
    intros n m hnm rho rho' H i hi.
    rewrite H. 
    reflexivity.
    unfold "<". transitivity n. apply hi. apply hnm.
  Qed.

  Fixpoint trunc_env (n: nat) (rho: env M): list M := match n with 
    | 0 => List.nil 
    | S n' => (rho 0) :: (trunc_env n' (S >> rho))
    end.
  
  Lemma trunc_env_eq_of_enveq  (n: nat):
  forall rho rho', enveq n rho rho' -> trunc_env n rho = trunc_env n rho'.
  Proof.
    intros rho rho' eq. rewrite enveq_enveq' in eq.
    induction eq as [rho rho'|n rho rho' h0 hn IHhS].
    - reflexivity.
    - simpl. f_equal.
      apply h0.
      apply IHhS.
  Qed.
  
  Fixpoint term_max_var (t: term):= match t with
  | var i => S i 
  | func f v => fold_left max 0 (map term_max_var v)
  end.
  
  Lemma fold_left_max_0' {n} (vt: vec nat n) (vh: nat):
  forall m, fold_left max m (cons nat vh n vt) = max vh (fold_left max m vt).
  Proof.
    induction vt as [|h n t IHvt].
    + intros m. apply PeanoNat.Nat.max_comm. 
    + intros m. simpl. rewrite <-IHvt. 
      rewrite <-PeanoNat.Nat.max_assoc,
        (PeanoNat.Nat.max_comm vh h),
        PeanoNat.Nat.max_assoc. 
      reflexivity.
  Qed.
  
  Lemma fold_left_max_0 {n} (v: vec nat n):
  forall a, In a v ->
  a <= fold_left max 0 v.
  Proof.
    induction v as [|h n t IHv]. all: intros a ha.
    + inversion ha.
    + rewrite fold_left_max_0'. inversion ha as [m0 v0 Hn Hh|m0 h0 vt Havt Hn Hh]. 
      - apply PeanoNat.Nat.le_max_l.
      - transitivity (fold_left max 0 t). apply IHv.
        inversion H. apply Havt.
        apply PeanoNat.Nat.le_max_r.
  Qed.

  Lemma map_In {A B: Type} (f: A -> B) {n} (v: vec A n) (a: A):
  In a v -> In (f a) (map f v).
  Proof.
    induction v.
    + intros H. inversion H.
    + intros H. inversion H. all: simpl.
      - apply In_cons_hd. 
      - apply In_cons_tl. apply IHv. inversion H3. apply H2.
  Qed.

  Lemma term_max_var_le {n} (v: vec term n):
  forall u, In u v ->
  (term_max_var u <= fold_left max 0 (map term_max_var  v)).
  Proof.
    induction v. all: intros u hu.
    + inversion hu .
    + apply fold_left_max_0. 
      apply map_In, hu.
  Qed.

  Lemma term_max_var_prop (t: term):
  forall rho rho', enveq (term_max_var t) rho rho' ->
  t ₜ[M] rho = t ₜ[M] rho'.
  Proof.
    induction t as [i|f v IH]. all: intros rho rho' heq. 
    + apply heq. eauto.
    + simpl. f_equal. apply map_ext_in. intros st hst. apply (IH st hst).
      apply (@enveq_n_of_le (term_max_var st) (term_max_var (func f v))).
      apply (term_max_var_le hst).
      apply heq.
  Qed.   

  Lemma exists_term_max_var:
  forall (u: term), exists i_star,
  forall rho rho', enveq i_star rho rho' -> 
  u ₜ[M] rho = u ₜ[M] rho'.
  Proof.
    intros u. 
    exists (term_max_var u). apply term_max_var_prop.
  Qed.

End HelperLemmas.


Section ModelTheory.

  Definition coe_vec_of_set {A: set M} {n: nat} (v: vec (of_set A) n) := map (@elem A) v.

  Definition coe_env_of_set {A: set M} (rho: env (of_set A)) := rho >> (@elem A).

  (* [FE] is needed here, since we are expecting
  that this square is commutative :

  env (of_set A) × of_set A --coe--> env M × M
  |                                  |
  scons                              scons
  |                                  |
  v                                  v
  env (of_set A)            --coe--> env M
  *)
  Lemma cons_comm_elem {A: set M} (rho: env (of_set A)) (a: of_set A) :
  (a .: rho) >> @elem A = (elem a .: rho >> @elem A).
  Proof.
    apply fe. intros [|n]. all: reflexivity.
  Qed.

  Definition fcl (A: set M) : Prop :=
  forall f : s_f, forall v : vec (of_set A) (ar_syms f),
  A (f ₕ[M] (coe_vec_of_set v)).

  Definition interp_of_fcl {A: set M} (H: fcl A) : interp (of_set A).
  Proof.
    apply B_I.
    + intros f v.
      exists (f ₕ[M] (coe_vec_of_set v)).
      apply H.
    + intros P v.
      apply (P ₚ[M] (coe_vec_of_set v)).
  Defined.

  Definition model_of_fcl {A: set M} (H: fcl A) : model := Build_model (interp_of_fcl H).

  Definition tvcl {fff: falsity_flag} (A: set M) : Prop :=
  (forall phi: form, forall rho : env (of_set A), exists a : of_set A,
  M ⊨[a .: rho] phi -> M ⊨[rho] (∀ phi)) /\
  (forall phi, forall rho : env (of_set A), exists a : of_set A,
  M ⊨[rho] (∃ phi) -> M ⊨[a .: rho] phi).

  (* Coercion behaves expectedly, it commutes with evaluation.*)
  Lemma coe_comm_of_fcl {A: set M} {Hf: fcl A}
  (t: term) (rho: env (of_set A)) :
  (eval M (interp' M) (coe_env_of_set rho)) t =
  (eval _ (interp_of_fcl Hf) rho) t.
  Proof.
    induction t.
    + reflexivity.
    + simpl. f_equal. induction v.
      - reflexivity.
      - simpl. f_equal.
        * apply IH, In_cons_hd.
        * apply IHv. intros t Ht. apply IH, In_cons_tl, Ht. 
  Qed.

  Lemma coe_vec_comm_of_fcl {A: set M} (Hf: fcl A)
  {n: nat} (t: vec term n) (rho: env (of_set A)) :
  map (eval M (interp' M) (coe_env_of_set rho)) t =
  coe_vec_of_set (map (eval _ (interp_of_fcl Hf) rho) t).
  Proof.
    induction t.
    reflexivity.
    simpl. f_equal. apply coe_comm_of_fcl.
    apply IHt.
  Qed.

  Lemma atom_of_tvcl {A: set M} (Hf: fcl A)
  (P: s_P) (T: vec term (ar_preds P)) (rho: env (of_set A)) :
  P ₚ[model_of_fcl Hf] map (eval (of_set A) (interp_of_fcl Hf) rho) T <->
  P ₚ[ M] map (eval M (interp' M) (coe_env_of_set rho)) T.
  Proof.
    split.
    + intros HA. simpl in *. rewrite (coe_vec_comm_of_fcl Hf). apply HA.
    + intros HA. simpl in *. rewrite <-(coe_vec_comm_of_fcl Hf). apply HA.
  Qed.

  Theorem elemsubm_of_tvcl' {ff: falsity_flag} {A: set M} {Hf: fcl A} (Htv: tvcl A):
  model_of_fcl Hf ⪳[@elem A] M.
  Proof.
    intros phi. induction phi.
    all: intros rho; split; intros HA.
    + firstorder.
    + firstorder.
    + eapply atom_of_tvcl, HA.
    + eapply atom_of_tvcl, HA.
    + destruct b0; firstorder. 
    + destruct b0; firstorder.
    + destruct q.
      - destruct Htv as [Hall Hex].
        destruct (Hall phi rho) as [wall hwall].
        eapply hwall, IHphi, HA.
        firstorder.
      - destruct HA as [a ha].
        exists a. simpl in *. rewrite <-(cons_comm_elem _ _). apply IHphi, ha. apply Htv.
    + destruct q.
      - intros a. simpl in *. apply IHphi. apply Htv.
        rewrite (cons_comm_elem _ _). apply (HA a).
      - destruct Htv as [Hall Hex]. assert (Htv := conj Hall Hex).
        destruct (Hex phi rho) as [wex hwex].
        exists wex. apply (IHphi Htv), hwex, HA.
  Qed.

  Theorem elemsubm_of_tvcl {ff: falsity_flag} {A: set M} {Hf: fcl A} (Htv: tvcl A):
  model_of_fcl Hf ⪳ M.
  Proof.
    exists (@elem A).
    apply (elemsubm_of_tvcl' Htv).
  Qed.

  Definition isTarskiVaught_all (F: (env M) -> form -> M) : Prop :=
    forall rho phi,
    (M ⊨[(F rho phi) .: rho] phi) -> M ⊨[rho] ∀ phi.


  Definition isTarskiVaught_ex (F: (env M) -> form -> M) : Prop :=
    forall rho phi,
    M ⊨[rho] (∃ phi) -> M ⊨[(F rho phi) .: rho] phi.

  Definition form_max_var := fun phi => proj1_sig (find_bounded phi).

  Definition respectsFormEnvInvariance (F: (env M) -> form -> M): Prop :=
    forall (phi: form), forall (rho rho': env M),
    enveq (form_max_var phi) rho rho' -> F rho phi = F rho' phi.

  Record FEI : Type := 
    {
      fFEI :> env M -> form -> M;
      hFEI : respectsFormEnvInvariance fFEI;
    }.

  Record TV_all : Type :=
    {
      F_all:> FEI ;
      hwit_all: isTarskiVaught_all F_all;
    }.

  Record TV_ex : Type :=
    {
      F_ex :> FEI;
      hwit_ex : isTarskiVaught_ex F_ex;
    }.

  Definition tvcl' (Fall: TV_all) (Fex: TV_ex) (A: set M) : Prop :=
  (forall phi, forall rho : env (of_set A),
  A (Fall (coe_env_of_set rho) phi)) /\
  (forall phi, forall rho : env (of_set A),
  A (Fex  (coe_env_of_set rho) phi)).

  (* Poor proof style *)
  Theorem tvcl_of_tvcl' (A: set M): 
  forall Fall Fex, tvcl' Fall Fex A -> tvcl A.
  Proof.
    intros Fall Fex.
    intros [Hall Hex]. split. all: intros phi rho.
    + exists (@Build_of_set A _ (Hall phi rho)).
      intros h. intros a.
      apply (@hwit_all Fall).
      assert (elem (Build_of_set (Hall phi rho)) = (Fall rho phi)). eauto.
      rewrite <-H.
      assert
        ((fun n => elem ((Build_of_set (Hall phi rho) .: rho) n)) =
        ((Fall (coe_env_of_set rho) phi) .: (fun n => rho n))).
        apply cons_comm_elem.
      simpl.
      rewrite <-H0. apply h.
    + exists (@Build_of_set A _ (Hex phi rho)).
      intros [a h].
      assert
        ((fun n => elem ((Build_of_set (Hex phi rho) .: rho) n)) =
        ((Fex (coe_env_of_set rho) phi) .: (fun n => rho n))).
        apply cons_comm_elem.
      rewrite H.
      assert (elem (Build_of_set (Hall phi rho)) = (Fall rho phi)). eauto.
      apply (@hwit_ex Fex).
      exists a.
      apply h.
  Qed.

  Definition stepForm (Fall: TV_all) (Fex: TV_ex) (A : set M) := (fun m =>
    (exists (phi: form) (rho: env M),
    (forall n, A (rho n)) /\ (m = (Fall rho phi) \/ m = (Fex rho phi)))).

  Definition stepTerm  (A: set M) := (fun m =>
    (exists (t: term) (rho: env M),
    (forall n, A (rho n)) /\ m = t ₜ[M] rho)).

  Definition step (Fall: TV_all) (Fex: TV_ex) (A : set M):
  set M :=
  union (stepForm Fall Fex A) (stepTerm A).

  Definition Step (Fall: TV_all) (Fex: TV_ex) (A : set M):
  set M :=
  closure (step Fall Fex) A.

  Lemma Step_grow (Fall: TV_all) (Fex: TV_ex):
  growing (Step Fall Fex).
  Proof.
    intros A x hA. exists 0. apply hA.
  Qed.
  
  Definition nefp_step (Fall: TV_all) (Fex: TV_ex) (A: set M) :=
  inhabited (of_set A) /\ (A == step Fall Fex A).

  Fixpoint vec_n_nat (n: nat) := match n with 
    | O => nil nat 
    | S n' => cons nat 0 _ (map S (vec_n_nat n'))
    end.

  Definition vec_n_term (n: nat) := map var (vec_n_nat n).

  Fixpoint vec2env {X: Type} {n: nat} (v: vec X n) (fill: X):= match v with 
    | nil _ => fun n => fill 
    | cons _ h _ t => h .: (vec2env t fill)
    end.

  Lemma env_n_in_A {A: set M} (rho: env (of_set A)):
  forall n, A (rho n).
  Proof.
    intros n. apply (helem (rho n)).
  Qed.

  Fact only_nil_of_vec_0 {X: Type}:
  forall v: vec X 0, v = nil X.
  Proof.
    intros v. apply (case0 (fun u => u = nil X)). reflexivity.
  Qed.

  Fact eval_up_down (n: nat) (h: M) (rho: env M):
  map (eval M interp' (h.:rho)) (map var (map S (vec_n_nat n))) =
  map (eval M interp' rho) (map var (vec_n_nat n)).
  Proof.
    rewrite map_map. rewrite map_map. rewrite map_map. simpl. reflexivity.
  Qed.

  Fact eval_vec2env_vec_n_term {n: nat} (v: vec M n):
  forall m,
  v = map (eval M (@interp' _ _ M) (vec2env v m)) (vec_n_term n).
  Proof.
    intros m.
    induction v. apply only_nil_of_vec_0.
    simpl. f_equal. rewrite eval_up_down. apply IHv.
  Qed.

  Fact coe_comm_vec2env {n: nat} (A: set M) (v: vec (of_set A) n) (a0: of_set A):
  coe_env_of_set (vec2env v a0) = vec2env (coe_vec_of_set v) (elem a0).
  Proof.
    apply fe.
    induction v.
    reflexivity.
    intros n'. simpl. destruct n'. simpl. reflexivity.
    simpl. unfold coe_env_of_set, ".:", ">>". apply IHv.
  Qed.

  Fact coe_comm_vec2env' {n: nat} (A: set M) (v: vec (of_set A) n) (a0: of_set A):
  (fun i => elem (vec2env v a0 i)) = coe_env_of_set (vec2env v a0).
  Proof.
    apply fe.
    intros [|i']. all: reflexivity.
  Qed. 

  Fact eval_vec2env_vec_n_term' {A: set M} {n: nat} (v: vec (of_set A) n):
  forall m,
  coe_vec_of_set v = map (eval M (@interp' _ _ M) (vec2env v m)) (vec_n_term n).
  Proof.
    intros m. rewrite coe_comm_vec2env'. induction v.
    + apply only_nil_of_vec_0.
    + simpl. f_equal. unfold coe_env_of_set.
      rewrite cons_comm_elem, eval_up_down. apply IHv.
  Qed.

  Lemma fcl_of_nefp_step {Fall: TV_all} {Fex: TV_ex} {A: set M} (H: nefp_step Fall Fex A):
  fcl A.
  Proof.
    destruct H as [[a0] [_ hfp']].
    intros f v.
    apply hfp'.
    right.
    exists (func f (vec_n_term (ar_syms f))).
    exists (vec2env v a0).
    split.
    apply env_n_in_A.
    simpl. f_equal.
    unfold coe_vec_of_set.
    rewrite <-(eval_vec2env_vec_n_term').
    reflexivity.
  Qed.

  Theorem tvcl'_of_nefp_step {Fall: TV_all} {Fex: TV_ex} {A: set M} (H: nefp_step Fall Fex A):
  tvcl' Fall Fex A.
  Proof.
    destruct H as [[a0] [_ hfp']]. split.
    all: intros phi rho.
    all: apply hfp'.
    all: left.
    all: exists phi, rho.
    all: split.
    1,3: apply env_n_in_A.
    1: left. 2: right.
    all: reflexivity.
  Qed.

  Theorem elemsubm_of_nefp_step {Fall: TV_all} {Fex: TV_ex} {A: set M}
  (H: nefp_step Fall Fex A):
  (fcl_of_nefp_step >> model_of_fcl) H ⪳ M.
  Proof.
    apply elemsubm_of_tvcl.
    apply (tvcl_of_tvcl' (tvcl'_of_nefp_step H)).
  Qed.

  Fact step_grow:
  forall (Fall: TV_all) (Fex: TV_ex),
  growing (step Fall Fex).
  Proof.
    intros Fall Fex.
    intros A x hxA.
    right. exists ($ 0), (fun _ => x). split.
    intros _. apply hxA.
    reflexivity.
  Qed.

  Fact step_incr :
  forall (Fall: TV_all) (Fex: TV_ex),
  forall (A B: set M), (A << B) -> (step Fall Fex A << step Fall Fex B) .
  Proof.
    intros Fall Fex.
    intros A B hAB x [[phi [rho [hrho hx]]]|[t [rho [hrho hx]]]].
    left. exists phi, rho. split. intros n. apply hAB, hrho.
    apply hx.
    right. exists t, rho. split. intros n. apply hAB, hrho.
    apply hx.
  Qed.
  
  Lemma iteration_grow_n {f: set M -> set M}:
  growing f -> forall n m, n <= m -> forall A, iteration n f A << iteration m f A.
  Proof.
    intros hgf n m. generalize dependent n. induction m. all: intros n h A x H. 
    + inversion h. rewrite H0 in H. apply H.
    + inversion h.
      - rewrite <-H0. apply H.
      - simpl. apply hgf. 
        apply (IHm n H1). apply H.
  Qed.

  Lemma step_n_grow {n: nat} (Fall: TV_all) (Fex: TV_ex):
  growing (iteration n (step Fall Fex)).
  Proof.
    intros A.
    apply (iteration_grow_n (step_grow Fall Fex) (n:=0)). lia.
  Qed.

End ModelTheory.

Record infT (ltT: Type -> Type -> Prop): Type := {
  infty:> Type -> Prop;
  infty_nat: infty nat;
  infty_up_ltT: forall X Y, infty X -> ltT X Y -> infty Y;
  infty_sum: forall X, infty X -> ltT (X + X)%type X;
  infty_prod: forall X, infty X -> ltT (X * X)%type X;
  infty_list: forall X, infty X -> ltT (list X) X;
}.

Definition smaInjR (X Y: Type) := exists R: X -> Y -> Prop, totalR(R) /\ injectiveR(R).

Lemma ltTsmaInjR: lessthanT smaInjR.
Proof.
  apply Build_lessthanT.
  + intros X. exists eq. split.
    - intros x. exists x. reflexivity.
    - intros x x' x0 [eqx eqx']. rewrite eqx, eqx'. reflexivity.
  + intros X Y Z [RXY [htXY hiXY]] [RYZ [htYZ hiYZ]].
    exists (fun x z => exists y, RXY x y /\ RYZ y z). split.
    - intros x. destruct (htXY x) as [y hy]. destruct (htYZ y) as [z hz].
      exists z, y. auto.
    - intros x x' z [[y [hxy hyz]] [y' [hx'y' hy'z]]].
      assert (hyy': y = y'). apply (hiYZ y y' z (conj hyz hy'z)).
      rewrite <-hyy' in hx'y'. apply (hiXY x x' y  (conj hxy hx'y')).
  + intros X X' Y Y' [R [htR hiR]] [R' [htR' hiR']].
    exists (fun x0 y0 => match x0,y0 with | pair x x', pair y y' => R x y /\ R' x' y' end). split.
    - intros [x x']. destruct (htR x) as [y hy]. destruct (htR' x') as [y' hy'].
      exists (pair y y'). apply (conj hy hy').
    - intros [x1 x1'] [x2 x2'] [y y'] [[h1 h1'] [h2 h2']].
      f_equal.
      apply (hiR x1 x2 y (conj h1 h2)). apply (hiR' x1' x2' y' (conj h1' h2')).
  + intros X X' Y Y' [R [htR hiR]] [R' [htR' hiR']].
    exists (fun x0 y0 => match x0, y0 with 
      | inl x, inl y => R x y 
      | inr x', inr y' => R' x' y' 
      | _,_ => False 
      end). split.
    - intros [x|x'].
      * destruct (htR x) as [y hy].
        exists (inl y). apply hy.
      * destruct (htR' x') as [y' hy'].
        exists (inr y'). apply hy'.
    - intros [x1|x1'] [x2|x2'] [y| y'] [hr1 hr2].
      all: try inversion hr1; try inversion hr2.
      all: f_equal.
      * apply (hiR x1 x2 y (conj hr1 hr2)).
      * apply (hiR' x1' x2' y' (conj hr1 hr2)).
  + intros X Y [R [htR hiR]].
    exists (fix Rl (lx: list X) ly := match lx, ly with 
      | List.nil, List.nil => True
      | hx :: tx, hy :: ty => R hx hy /\ Rl tx ty 
      | _, _ => False 
      end). split.
    all: intros lx; induction lx as [|hx tx ih].
    - exists List.nil. auto.
    - destruct (htR hx) as [hy Hhy].
      destruct (ih) as [ty Hty].
      exists (hy :: ty). split. exact Hhy. exact Hty.
    - intros [|hx' tx'] [|hy ty].
      all: intros [abs1 abs2].
      1: reflexivity.
      all: try inversion abs1; try inversion abs2.
    - intros [|hx' tx'] [|hy ty].
      all: intros [abs abs'].
      1-3: try inversion abs; try inversion abs'.
      destruct abs as [Hhx Htx].
      destruct abs' as [Hhx' Htx'].
      f_equal.
      * apply (hiR hx hx' hy (conj Hhx Hhx')).
      * apply (ih tx' ty (conj Htx Htx')).
  + intros X Y [f hf].
    exists (fun x y => f x = y). split.
    - intros x. exists (f x). reflexivity.
    - intros x x' y [h h'].
      apply hf. rewrite h, h'. reflexivity.
  + intros J X Y [E hE].
    exists (
      fun dx dy => match dx, dy return Prop with
        | existT _ jx x, existT _ jy y =>
          (exists e: jy = jx, E jx x (eq_rect jy Y y jx e ))
      end). split.
    - intros [jx x]. destruct (hE jx) as [htEj hiEj].
      destruct (htEj x) as [y hy].
      exists (existT _ jx y). exists (eq_refl _). apply hy.
    - intros [jx x] [jx' x'] [jy y] [[e he] [e' he']].
      destruct e. destruct e'. f_equal. simpl in he, he'.
      destruct (hE jy) as [htEjy hiEjy]. apply (hiEjy x x' y (conj he he')).
  + intros J A.
    exists (fun ds st => True). split.
    - intros [j h]. exists (exist _ j h). exact I.
    - intros [j h] [j' h'] [j0 h0] [[] []]. apply pi.
Qed.

Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller}.
Notation "X ≤ Y" := (smaller X Y) (at level 80) : type_scope.

Section FixCardOrder.

Context {seqinf: infT smaller}.


Definition smallersi (X Y: Type) := 
forall W, seqinf W -> Y ≤ W -> X ≤ W.

Section Sizes.

Section Size_lemmas.

  Lemma smallersi_of_smaller:
  forall X Y, X ≤ Y -> smallersi X Y.
  Proof.
  intros X Y H W _ h.
  transitivity Y. apply H. apply h.
  Qed.

  #[global] Instance smallersi_rfl: Reflexive smallersi.
  Proof.
    intros X. apply smallersi_of_smaller. reflexivity.
  Qed.

  #[export] Instance smallersi_trans: Transitive smallersi.
  Proof.
    intros X Y Z h1 h2 W hW H.
    transitivity (W).
    apply h1. apply hW.
    apply h2. apply hW.
    apply H. reflexivity.
  Qed.

  Lemma smallersi_PO: Preorder Type smallersi.
  Proof.
    apply (Definition_of_preorder Type smallersi
      smallersi_rfl smallersi_trans).
  Qed.

  Lemma nat_smaller_term_form:
  nat ≤ (term + form)%type.
  Proof.
    apply smaller_of_inj.
    exists (fun n => inl ($n)).
    intros n1 n2 eqn. injection eqn. apply id.
  Qed.

  Lemma term_smaller_term_form:
  term ≤ (term + form)%type.
  Proof.
    apply smaller_of_inj.
    exists inl.
    intros t1 t2 eqt. injection eqt. apply id.
  Qed.

  Lemma form_smaller_term_form:
  form ≤ (term + form)%type.
  Proof.
    apply smaller_of_inj.
    exists inr.
    intros phi1 phi2 eqphi. injection eqphi. apply id.
  Qed.

  Fact ex_smaller_sigT:
  forall J, forall X (A: J -> set X),
  {x | exists j, A j x} ≤ (sigT (fun j => {x | A j x})).
  Proof.
    intros J X A.
    transitivity {x & {j & A j x}}.
    transitivity {x & exists j, A j x}.
    - apply smaller_of_inj.
      exists (fun ds => match ds with | exist _ x h => existT _ x h end).
      intros [x h] [x' h'] e. injection e as e'. destruct e'. rewrite (pi h h'). reflexivity.
    - apply (ltT_dsum).
      exists (fun x ej dj => True). intros x. split.
      * intros [j h]. exists (existT _ j h). exact I.
      * intros [j h] [j' h'] [j0 h0] [[] []]. apply pi.
    - apply smaller_of_inj.
      exists (fun a => match a with
        | existT _ x (existT _ j h) =>  (existT (fun j0 => sig _) j (exist _ x h))
      end).
      intros [x [j h]] [x' [j' h']] e. inversion e as [e']. destruct e'. destruct H.
      f_equal. f_equal. apply pi.
  Qed.

  Fact ex_smaller_sigT_nat:
  forall X,
  forall (A: nat -> set X), {x | exists n, A n x} ≤ (sigT (fun n => {x | A n x})).
  Proof.
    apply ex_smaller_sigT.
  Qed.

  Fact Union_smaller_sigT:
  forall J,
  forall A: J -> set M, of_set (Union A) ≤ sigT (fun n => of_set (A n)).
  Proof.
    intros J A.
    unfold Union.
    transitivity {n & {m | A n m}}.
    transitivity {m | exists n, A n m}.
    + apply smaller_of_inj.
      exists (fun x => match x with 
        | @Build_of_set _ m hm => exist _ m hm
        end).
      intros [m1 h1] [m2 h2] eqmh.
      injection eqmh as eqm.
      subst m1.
      rewrite (pi h1 h2).
      reflexivity.
    + apply ex_smaller_sigT.
    + apply smaller_dsum_incr.
      exists (fun j m0 x0 => match m0, x0 with
        | exist _ m _, @Build_of_set _ x _ => m = x 
        end).
      intros j. split.
      - intros [m hm]. exists (Build_of_set hm). reflexivity.
      - intros [m hm] [m' hm'] [x hx] [e e'].
      rewrite <-e' in e. destruct e.
      rewrite (pi hm hm'). reflexivity.
  Qed.

  Lemma or_iff_bool_ex:
  forall (A B: set M), (union A B) << (Union (fun c: bool => if c then A else B)).
    intros A B x [hA|hB].
    + exists true. apply hA.
    + exists false. apply hB.
  Qed.

  Fact or_smaller_sum:
  forall (A B: set M), of_set (union A B) ≤ (of_set A + of_set B)%type.
  Proof.
    intros A B.
    transitivity {c: bool & of_set (if c then A else B)}.
    transitivity (of_set (Union (fun c: bool => if c then A else B))).
    + apply smaller_of_inj.
      exists (fun u => match u with 
        | Build_of_set h => Build_of_set (or_iff_bool_ex h) 
        end ).
      intros [x1 h1] [x2 h2] eqxh.
      injection eqxh as eqx.
      subst x1. rewrite (pi h1 h2). reflexivity.
    + apply Union_smaller_sigT.
    + apply smaller_of_inj.
      exists (fun dp => match dp with 
        | existT _ true a => inl a 
        | existT _ false b => inr b
        end).
      intros [[|] x1] [[|] x2] eqx.
      all: try discriminate.
      all: injection eqx as eqx'.
      all: subst x1. all: reflexivity.
  Qed.

  Fact seqinf_up:
  forall X Y, seqinf X -> X ≤ Y -> seqinf Y.
  Proof.
    apply infty_up_ltT.
  Qed.

  Lemma smaller_iff_smallersi_of_sequinf:
  forall X Y, seqinf Y -> smallersi X Y <-> smaller X Y.
  Proof.
    intros X Y hsiY. split.
    + intros H. apply (H _ hsiY (smaller_rfl Y)).
    + apply smallersi_of_smaller.
  Qed.

  Fact prod_of_seqinf:
  forall X, seqinf X -> (X * X)%type ≤ X.
  Proof.
    apply infty_prod.
  Qed.

  Fact sum_of_seqinf:
  forall X, seqinf X -> (X + X)%type ≤ X.
  Proof.
    apply infty_sum.
  Qed.
  
  Fact list_smallersi:
  forall X, smallersi (list X) X.
  Proof.
    intros X W hsiW hXW.
    transitivity (list W).
    + apply (@ltT_list smaller smaller_lt _ _ hXW).
    + apply (infty_list hsiW).
  Qed.
  
  Fact vec_smaller_seqinf:
  forall W, seqinf W -> forall X, X ≤ W -> forall n, vec X n ≤ W.
  Proof.
    intros W hsiW X H n.
    transitivity (list X).
    + apply smaller_of_inj.
      exists to_list.
      intros l1 l2 eq.
      apply (to_list_inj _ _ _ _ eq).
    + apply (list_smallersi hsiW H).
  Qed.
  
  Fact smallersi_prod_incr:
  forall X X' Y Y',
  Y -> Y' ->
  smallersi X Y -> smallersi X' Y' -> smallersi (X * X')%type (Y * Y')%type.
  Proof.
    intros X X' Y Y' y0 y0' h h' W hsiW H.
    transitivity (W * W)%type.
    + apply smaller_prod_incr.
      - apply (h W hsiW).
        transitivity (Y * Y')%type.
        apply smaller_of_inj.
        exists (fun y => pair y y0'). intros y1 y2 eqy. 
        injection eqy. apply id.
        apply H.
      - apply (h' W hsiW).
        transitivity (Y * Y')%type.
        apply smaller_of_inj.
        exists (fun y' => pair y0 y'). intros y1 y2 eqy. 
        injection eqy. apply id.
        apply H.
    + apply (prod_of_seqinf hsiW).
  Qed.

  

  Lemma seqinf_nat: seqinf nat.
  Proof.
    apply infty_nat.
  Qed.

  Fact nat_smaller_seqinf:
  forall X, seqinf X -> nat ≤ X.
  Proof.
    intros X hsiX.
    transitivity (list X).
    transitivity (list (list X)).
    + apply smaller_of_inj.
      exists (fix r n := match n with | 0 => List.nil | S n' => List.nil :: r n' end).
      intros n1. induction n1 as [|n1' IH1]. all: intros [|n2] eqnn.
      all: try discriminate.
      - reflexivity.
      - f_equal. apply IH1. injection eqnn. apply id.
    + apply (infty_list (infty_up_ltT hsiX (X_smaller_lX X))).
    + apply (infty_list hsiX).    
  Qed.

  Fact nat_smallersi (X: Type):
  smallersi nat X.
  Proof.
    intros W hsiW H.
    apply (nat_smaller_seqinf hsiW).
  Qed.

  Fact smallersi_sum_incr:
  forall X X' Y Y', smallersi X Y -> smallersi X' Y' -> smallersi (X + X') (Y + Y').
  Proof.
    intros X X' Y Y' h h' W hsiW HW.
    transitivity (W + W)%type.
    apply smaller_sum_incr.
    1: apply (h _ hsiW). 
    2: apply (h' _ hsiW). 1,2: transitivity (Y + Y')%type.
    1,3: apply smaller_of_inj.
    1: exists inl. 2: exists inr. 
    1,2: intros x1 x2 eq; injection eq; apply id.
    1,2: apply HW.
    apply (sum_of_seqinf hsiW).
  Qed.

  
  

  Fact sum_smallersi:
  forall X, smallersi (X + X) X.
  Proof.
    intros X.
    transitivity (list X).
    apply smallersi_of_smaller, sum_smaller_list.
    apply list_smallersi.
  Qed.

  Fact prod_smallersi_sum:
  forall X Y, smallersi (X * Y) (X + Y).
  Proof.
    intros X Y W hsiW Hprod.
    transitivity (W * W)%type.
    apply smaller_prod_incr. 
    apply (smaller_of_sum_incr_l Hprod).
    apply (smaller_of_sum_incr_r Hprod).
    apply (prod_of_seqinf hsiW).
  Qed.

  Fact prod_smallersi:
  forall X, smallersi (X * X) X.
  Proof.
    intros X.
    transitivity (X + X)%type.
    + apply prod_smallersi_sum.
    + apply sum_smallersi.
  Qed.
  
  Fact seqinf_term_form:
  seqinf (term + form)%type.
  Proof.
    apply (@seqinf_up nat).
    + apply seqinf_nat.
    + apply smaller_of_inj.
      exists (fun n => inl ($n)).
      intros n1 n2 eqe. injection eqe. apply id.
  Qed.


End Size_lemmas.

  
  (* The singleton set containing a given element [m0] *)
  Definition singl (m0: M): set M := fun m => m = m0.

  Fact singl_prop:
  forall m, forall a a': of_set (singl m), a  = a'.
  Proof.
    intros m0 [m1 h1] [m2 h2]. unfold singl in h1, h2.
    subst m1 m2. reflexivity.
  Qed.

  Fact singl_smaller_nat:
  forall m0, of_set (singl m0) ≤ nat. 
  Proof.
    intros m0. apply smaller_of_inj.
    exists (fun _ => 0).
    intros [x1 []] [x2 []] _.
    reflexivity.
  Qed.

  Definition stepTerm' (A: set M) (m0: M) :=
    Union (fun (t: term) => 
    Union (fun (v: vec (of_set A) (term_max_var t)) =>
    fun m => m = t ₜ[M] (vec2env (coe_vec_of_set v) m0))).

  Definition stepForm' (Fall: TV_all) (Fex: TV_ex) (A: set M) (m0: M) :=
    Union (fun (phi: form) =>
    Union (fun (v: vec (of_set A) (form_max_var phi)) => 
    fun m =>
      (m = (Fall (vec2env (coe_vec_of_set v) m0) phi) \/
      m = (Fex (vec2env (coe_vec_of_set v) m0) phi)))).

  Fixpoint env2vec {X: Type} (n: nat) (rho: env X): vec X n := match n with
    | 0 => nil X 
    | S n' => cons X (rho 0) n' (env2vec n' (S >> rho))
    end.

  Lemma coe_comm_env2vec (A: set M):
  forall n (rho: env (of_set A)), 
  coe_vec_of_set (env2vec n rho) = env2vec n (coe_env_of_set rho).
  Proof.
    induction n as [|n' IHn].
    all: intros rho.
    + reflexivity.
    + simpl. f_equal. apply IHn.
  Qed.

  Lemma enveq_vec2env_env2vec:
  forall n, forall (rho: env M) (x: M), enveq n (vec2env (env2vec n rho) x) rho.
  Proof. 
    intros n rho m.
    rewrite enveq_enveq'.
    generalize dependent m.
    generalize dependent rho.
    induction n as [|n']. all: intros rho m.
    + apply enveq_0.
    + apply (@enveq_S n').
      - reflexivity.
      - apply IHn'.
  Qed.

  Lemma stepTerm_iff_stepTerm':
  forall (A: set M) (a0: of_set A), forall m, stepTerm A m <-> stepTerm' A a0 m.
  Proof.
    intros A m0 m. split.
    + intros [t [rho [H eq]]].
      pose (v := env2vec (term_max_var t) (fun n => Build_of_set (H n))).
      exists t, v.
      rewrite eq. apply term_max_var_prop.
      symmetry.
      unfold v.
      rewrite (coe_comm_env2vec).
      transitivity (coe_env_of_set (fun n => Build_of_set (H n))).
      - apply enveq_vec2env_env2vec.
      - unfold coe_env_of_set. intros i _.
        unfold ">>". reflexivity.
    + intros [t [v H]].
      pose (rho := vec2env v m0).
      exists t, rho. split.
      - apply rho.
      - rewrite H. f_equal.
        unfold rho.
        apply fe. intros n.
        rewrite <-coe_comm_vec2env. reflexivity.
  Qed.

  Lemma stepForm_iff_stepForm' (Fall: TV_all) (Fex: TV_ex):
  forall (A: set M) (a0: of_set A), forall m,
  stepForm Fall Fex A m <-> stepForm' Fall Fex A a0 m.
  Proof.
    intros A m0 m. split.
    + intros [phi [rho [H [eq|eq]]]].
      all: pose (v := env2vec (form_max_var phi) (fun n => Build_of_set (H n))).
      all: exists phi, v.
      1: left. 2: right.
      all: rewrite eq.
      all: apply hFEI.
      all: symmetry.
      all: unfold v. 
      all: rewrite coe_comm_env2vec.
      all: transitivity (coe_env_of_set (fun n => Build_of_set (H n))).
      1,3: apply enveq_vec2env_env2vec.
      all: unfold coe_env_of_set; intros i _; unfold ">>"; reflexivity.
    + intros [phi [v H]].
      pose (rho := vec2env v m0).
      exists phi, rho. split.
      - apply rho.
      - destruct H as [H'|H'].
        1: left. 2: right.
        all: rewrite H'.
        all: f_equal.
        all: unfold rho.
        all: apply fe; intros n. 
        all: rewrite <-coe_comm_vec2env; reflexivity.
  Qed.

  Lemma stepTerm'_smaller_term_vec:
  forall (A: set M) (a0: of_set A),
  of_set (stepTerm' A a0) ≤ (sigT (fun t => vec (of_set A) (term_max_var t))).
  Proof.
    intros A a0.
    unfold stepTerm'.
    transitivity 
      {t: term &
      of_set (Union (fun v: vec (of_set A) (term_max_var t) =>
      (fun m => m = t ₜ[ M] vec2env (coe_vec_of_set v) a0)))}.
    + apply (Union_smaller_sigT).
    + apply (smaller_dsum_incr).
      exists (fun t m0 v => match m0 with 
          | @Build_of_set _ m _ => m = t ₜ[ M] vec2env (coe_vec_of_set v) a0
        end).
      intros t. split.
      - intros [m hm]. apply hm.
      - intros [m hm] [m' hm'] v [e e'].
        rewrite <-e' in e. destruct e. rewrite (pi hm hm'). reflexivity.
  Qed.

  Lemma stepForm'_smaller_form_vec (Fall: TV_all) (Fex: TV_ex):
  forall (A: set M) (a0: of_set A), 
  of_set (stepForm' Fall Fex A a0) ≤ 
  (sigT (fun phi => vec (of_set A) (form_max_var phi)) +
   sigT (fun phi => vec (of_set A) (form_max_var phi)))%type.
  Proof.
    intros A a0.
    transitivity (sigT (fun phi =>
      (vec (of_set A) (form_max_var phi) +
      vec (of_set A) (form_max_var phi))%type)).
    transitivity
      ({phi: form &
      of_set (Union (fun v: vec (of_set A) (form_max_var phi) =>
      (fun m =>
        m = Fall (vec2env (coe_vec_of_set v) a0) phi \/
        m = Fex (vec2env (coe_vec_of_set v) a0) phi)))})%type.
    + apply (Union_smaller_sigT).
    + apply (smaller_dsum_incr).
      exists (
        fun phi m v => match m, v with 
          | @Build_of_set _ m hm, inl v => m = Fall (vec2env (coe_vec_of_set v) a0) phi
          | @Build_of_set _ m hm, inr v => m = Fex (vec2env (coe_vec_of_set v) a0) phi
        end    
      ).
      intros phi. split.
      - intros [m [v0 [hmvall|hmvex]]].
        * exists (inl v0). apply hmvall.
        * exists (inr v0). apply hmvex.
      - intros [m hm] [m' hm'] v [e e'].
        destruct v as [v0|v0].
        all: rewrite <-e' in e.
        all: destruct e.
        all: rewrite (pi hm hm').
        all: reflexivity.
    + apply smaller_of_inj.
      exists (fun dp => match dp with
        | existT _ phi (inl v) => inl (existT _ phi v)
        | existT _ phi (inr v) => inr (existT _ phi v)
        end).
      intros [phi1 [v1|v1]] [phi2 [v2|v2]] eqx.
      all: try discriminate.
      all: injection eqx as eqphi eqv.
      all: subst phi1.
      all: apply inj_pair2 in eqv.
      all: subst v1.
      all: reflexivity.
  Qed.

  Lemma term_vec_smaller_term_list:
  forall A: set M,
  {t: term & vec (of_set A) (term_max_var t)} ≤ (term * list (of_set A))%type.
  Proof.
    intros A. apply smaller_of_inj.
    pose (f := fun p => match p return (term * list (of_set A)) with 
      | existT _ t v => (t, @to_list _ (term_max_var t) v)
      end).
    exists f. 
    intros x1 x2 eqf.
    unfold f in eqf.
    destruct x1 as [t1 v1].
    destruct x2 as [t2 v2].
    injection eqf as eqt eql.
    subst t1.
    assert (Hl: v1 = v2).
    apply (to_list_inj).
    apply eql.
    subst v1.
    reflexivity.
  Qed.

  Lemma form_vec_smaller_form_list:
  forall A: set M,
  {phi: form & vec (of_set A) (form_max_var phi)} ≤ (form * list (of_set A))%type.
  Proof.
    intros A. apply smaller_of_inj.
    pose (f := fun p => match p return (form * list (of_set A)) with 
      | existT _ phi v => (phi, @to_list _ (form_max_var phi) v)
      end).
    exists f. 
    intros x1 x2 eqf.
    unfold f in eqf.
    destruct x1 as [phi1 v1].
    destruct x2 as [phi2 v2].
    injection eqf as eqt eql.
    subst phi1.
    assert (Hl: v1 = v2).
    apply (to_list_inj).
    apply eql.
    subst v1.
    reflexivity.
  Qed.

  Lemma stepTerm_smallersi:
  forall A, (of_set A) -> of_set A ≤ (term + form)%type ->
  smallersi (of_set (stepTerm A)) (term + form)%type.
  Proof. 
    intros A a0 h.
    transitivity ((term + form) * (term + form))%type.
    transitivity (term * of_set A)%type.
    transitivity (term * list (of_set A))%type.
    transitivity {t: term & vec (of_set A) (term_max_var t)}.
    transitivity (of_set (stepTerm' A a0)).
    + apply smallersi_of_smaller, smaller_of_inj.
      pose (f := fun (x: of_set (stepTerm A)) =>
        match @stepTerm_iff_stepTerm' A a0 x return (of_set (stepTerm' A a0)) with 
        | conj mp _ => Build_of_set (mp (helem x))
        end).
      exists f.
      intros ox1 ox2 eqf.
      unfold f in eqf.
      destruct ox1 as [x1 hx1].
      destruct ox2 as [x2 hx2].
      destruct (stepTerm_iff_stepTerm' a0 (Build_of_set hx1)) as [mp1 rmp1].
      destruct (stepTerm_iff_stepTerm' a0 (Build_of_set hx2)) as [mp2 rmp2].
      inversion eqf as [H]. destruct eqf. 
      subst x1.
      rewrite (pi hx1 hx2).
      reflexivity.
    + apply smallersi_of_smaller. 
      apply stepTerm'_smaller_term_vec.
    + apply smallersi_of_smaller.
      apply term_vec_smaller_term_list.
    + apply smallersi_prod_incr. apply $0. apply a0. reflexivity. apply list_smallersi.
    + apply (smallersi_prod_incr (inl $0) (inl $0)).
      - apply smallersi_of_smaller, term_smaller_term_form.
      - apply smallersi_of_smaller, h.
    + apply prod_smallersi.
  Qed.

  Lemma stepForm_smallersi (Fall: TV_all) (Fex: TV_ex):
  forall A, (of_set A) -> of_set A ≤ (term + form)%type ->
  smallersi (of_set (stepForm Fall Fex A)) (term + form)%type.
  Proof.
    intros A a0 h.
    transitivity ((term + form) * (term + form))%type.
    transitivity (form * of_set A)%type.
    transitivity (form * list (of_set A))%type.
    transitivity {phi: form & vec (of_set A) (form_max_var phi)}.
    transitivity
      ({phi: form & vec (of_set A) (form_max_var phi)} +
      {phi: form & vec (of_set A) (form_max_var phi)})%type.
    transitivity (of_set (stepForm' Fall Fex A a0)).
    + apply smallersi_of_smaller, smaller_of_inj.
      pose (f := fun (x: of_set (stepForm Fall Fex A)) =>
        match @stepForm_iff_stepForm' Fall Fex A a0 x return (of_set (stepForm' Fall Fex A a0)) with 
        | conj mp _ => Build_of_set (mp (helem x))
        end).
      exists f.
      intros ox1 ox2 eqf.
      unfold f in eqf.
      destruct ox1 as [x1 hx1].
      destruct ox2 as [x2 hx2].
      destruct (stepForm_iff_stepForm' Fall Fex a0 (Build_of_set hx1)) as [mp1 rmp1].
      destruct (stepForm_iff_stepForm' Fall Fex a0 (Build_of_set hx2)) as [mp2 rmp2].
      inversion eqf as [H]. destruct eqf. 
      subst x1.
      rewrite (pi hx1 hx2).
      reflexivity.
    + apply smallersi_of_smaller. 
      apply stepForm'_smaller_form_vec.
    + apply sum_smallersi.
    + apply smallersi_of_smaller.
      apply form_vec_smaller_form_list.
    + apply smallersi_prod_incr.
      apply falsity. apply a0. reflexivity. apply list_smallersi.
    + apply (smallersi_prod_incr (inr falsity) (inr falsity)).
      - apply smallersi_of_smaller, form_smaller_term_form.
      - apply smallersi_of_smaller, h.
    + apply prod_smallersi.
  Qed.


  (* Plain, boring, uninteresting, algebraic manipulations *)
  Lemma step_smaller (Fall: TV_all) (Fex: TV_ex):
  forall A, of_set A -> of_set A ≤ (term + form)%type->
  smaller (of_set (step Fall Fex A)) (term + form).
  Proof.
    intros A a0 h.
    transitivity
      ((term + form) + 
      (term + form))%type.
    transitivity (of_set (stepForm Fall Fex A) + of_set (stepTerm A))%type.
    + apply or_smaller_sum.
    + apply smaller_sum_incr.
      - apply (stepForm_smallersi _ _ a0 h). apply seqinf_term_form. reflexivity.
      - apply (stepTerm_smallersi a0 h). apply seqinf_term_form. reflexivity.
    + apply sum_smallersi. apply seqinf_term_form. reflexivity.  
  Qed.

  Lemma iter_step_smaller (Fall: TV_all) (Fex: TV_ex):
  forall n, forall (A: set M), of_set A -> of_set A ≤ (term + form)%type ->
  smaller (of_set (iteration n (step Fall Fex) A)) (term + form).
  Proof.
    intros n. induction n as [|n' IHn].
    + intros A a0 h. 
      apply h.
    + intros A a0 h. simpl.
      apply step_smaller.
      - assert (h0n' : 0 <= n'). lia.
        apply
          (Build_of_set
            (@iteration_grow_n
              _
              (step_grow Fall Fex)
              0
              n'
              h0n'
              A
              a0
              (helem a0))).
      - apply (IHn A a0 h).
  Qed.

  (* Lemma Union_smallersi: forall (W: Type) (w0: W) (A: nat -> set M),
  (forall (n: nat), smallersi (of_set (A n)) W) -> smallersi (of_set (Union A)) W.
  Proof.
    intros W w0 A H.
    transitivity (W * W)%type.
    transitivity (nat * W)%type.
    transitivity {n: nat & of_set (A n)}.
    + apply smallersi_of_smaller.
      apply Union_smaller_sigT.
    + transitivity {_: nat & W}.
      - apply smallersi_dsum_nat_incr, H.
      - apply smallersi_of_smaller, smaller_of_inj.
        exists (fun jw => match jw with 
          | existT _ j w => (j, w) 
          end).
        {
          intros [j1 w1] [j2 w2] eqjw. injection eqjw as eqj eqw. 
          subst j1 w1. reflexivity.
        }
    + apply (smallersi_prod_incr w0 w0).
      - apply nat_smallersi.
      - reflexivity.
    + apply prod_smallersi.
  Qed. *)

  Definition alpha := fun x: term + form => match x with | inl _ => unit | inr _ => bool end.
  Definition nux := fun x =>  match x with | inl t => term_max_var t | inr phi => form_max_var phi end.

Lemma coe_enveq: forall A: set M, forall a0 : of_set A,
forall k,
forall rho: env M,
forall H:(forall n, A (rho n)),
enveq k (fun i => @elem A (vec2env (env2vec k (fun j => Build_of_set (H j))) a0 i)) (fun i => rho i).
Proof.
  intros A a0 k. induction k as [|k' hk].
  all: intros rho H .
  all: rewrite enveq_enveq'.
  + apply enveq_0.
  + apply enveq_S. reflexivity. 
    assert (h := hk (fun n => rho (S n)) (fun n => H (S n))).
    rewrite enveq_enveq' in h.
    apply h.
Qed.

  Lemma step_siR_term_form_vec (Fall: TV_all) (Fex: TV_ex):
    forall A, of_set A ->
    smaInjR 
      (of_set (step Fall Fex A))
      {x: term + form & (alpha x * vec (of_set A) (nux x))%type}.
  Proof.
    intros A a0.
    exists (fun m0 dx => match m0, dx with 
      | @Build_of_set _ m hm, existT _ (inl t) (pair _ v) => m = t ₜ[M] (vec2env v a0 )
      | @Build_of_set _ m hm, existT _ (inr phi) (pair true v) =>
        (m = (F_all Fall) (vec2env v a0) phi)
      | @Build_of_set _ m hm, existT _ (inr phi) (pair false v) =>
        (m = (F_ex Fex) (vec2env v a0) phi)
      end). split.
    - intros [x [[phi [rho [hrho [hphi|hphi]]]]|[t [rho [hrho ht]]]]].
      * exists (existT
          _
          (inr phi)
          (pair true (env2vec (form_max_var phi) (fun n => Build_of_set (hrho n))))).
        rewrite hphi.
        apply (hFEI). symmetry. apply coe_enveq.
      * exists (existT
          _
          (inr phi)
          (pair false (env2vec (form_max_var phi) (fun n => Build_of_set (hrho n))))).
        rewrite hphi.
        apply (hFEI). symmetry. apply coe_enveq.
      * exists (existT
          _
          (inl t)
          (pair tt (env2vec (term_max_var t) (fun n => Build_of_set (hrho n))))).
        rewrite ht.
        apply term_max_var_prop. symmetry. apply coe_enveq.
    - intros [x hx] [x' hx'] [[t0|phi0] [b v0]] [e e'].
      2: destruct b.
      all: destruct e.
      all: destruct e'.
      all: rewrite (pi hx hx').
      all: reflexivity.
  Qed. 

Definition nuxx := fun x =>  match x with
  | inl t => term_max_var t
  | inr (inl phi) | inr (inr phi) => form_max_var phi
end.


  Lemma step_siR_term_form_form_vec (Fall: TV_all) (Fex: TV_ex):
    forall A, of_set A ->
    smaInjR 
      (of_set (step Fall Fex A))
      {x:(term + (form + form)) & vec (of_set A) (nuxx x)}.
  Proof.
    intros A a0.
    exists (fun m0 px => match m0, px with 
      | @Build_of_set _ m hm, existT _ (inl t) v => m = t ₜ[M] (vec2env v a0 )
      | @Build_of_set _ m hm, existT _ (inr (inl phi)) v => (m = (F_all Fall) (vec2env v a0) phi)
      | @Build_of_set _ m hm, existT _ (inr (inr phi)) v => (m = (F_ex Fex) (vec2env v a0) phi)
      end). split.
    - intros [x [[phi [rho [hrho [hx|hx]]]]|[t [rho [hrho hx]]]]].
      1: exists (existT 
          _
          (inr (inl phi))
          ((env2vec (form_max_var phi) (fun n => Build_of_set (hrho n))))).
      2: exists (existT
          _
          (inr (inr phi))
          ((env2vec (form_max_var phi) (fun n => Build_of_set (hrho n))))).
      3: exists (existT
          _
          (inl t)
          ((env2vec (term_max_var t) (fun n => Build_of_set (hrho n))))).
      all: rewrite hx.
      1,2: apply hFEI.
      3: apply term_max_var_prop.
      all: symmetry.
      all: apply coe_enveq.
    - intros [x hx] [x' hx'] [[t0|[phi0|phi0]] v0] [e e'].
      all: destruct e.
      all: destruct e'.
      all: rewrite (pi hx hx').
      all: reflexivity.
  Qed.

  Lemma Step_smaller (Fall: TV_all) (Fex: TV_ex):
  forall A, of_set A -> of_set A ≤ (term + form)%type ->
  smaller (of_set (Step Fall Fex A)) (term + form).
  Proof.
    intros A a0 h.
    transitivity {n: nat & of_set (iteration n (step Fall Fex) A)}.
    apply Union_smaller_sigT.
    transitivity {n: nat & (term + form)%type}.
  Admitted.
  
  Lemma Step_singl_smaller_term_form (Fall: TV_all) (Fex: TV_ex):
  forall (m0: M),
  smaller
  (of_set (Step Fall Fex (singl m0))) (term + form).
  Proof.
    intros m0.
    apply (Step_smaller _ _ (@Build_of_set (singl m0) m0 (eq_refl))).
    transitivity nat.
    apply singl_smaller_nat.
    apply nat_smaller_term_form.
  Qed.

  (* ### *)

  Lemma step_eval {Fall: TV_all} {Fex: TV_ex}:
  forall (u: term) (A: set M) (rho: env M),
  (forall i, A (rho i)) ->
  (step Fall Fex A (u ₜ[M] rho)).
  Proof.
    intros u A rho hrho.
    right. exists u, rho. split.
    apply hrho.
    reflexivity.
  Qed.
  
  Lemma nleb_le (n m: nat): (n <=? m) = false <-> ~ (n <= m).
  Proof.
    induction (n <=? m) eqn: eq.
    + split.
      intros abs. discriminate abs. 
      intros abs. rewrite Nat.leb_le  in eq. exfalso. apply (abs eq).
    + split.
      intros _ H. rewrite <-Nat.leb_le in H. rewrite H in eq. discriminate eq.
      intros _. reflexivity.
  Qed.

  Lemma exists_env_Step_max_iteration {Fall: TV_all} {Fex: TV_ex}:
  forall (rho: env M) (A: set M),
  (forall i, Step Fall Fex A (rho i)) ->
  forall i, exists n_star rho',
  enveq i rho rho' /\ (forall j, iteration n_star (step Fall Fex) A (rho' j)).
  Proof.
    intros rho A hrho i. induction i as [|i' IHi].
    + destruct (hrho 0) as [n0 hiter0].
      exists n0. exists (fun _ => rho 0). split.
      - intros i hi. inversion hi.
      - intros _. apply hiter0.
    + destruct IHi as [n_prev [rho' [heq hrho']]].
      destruct (hrho i') as [n_i hiteri].
      exists (max n_prev n_i).
      exists (fun  k => match (k <? i') with true => rho k | false => rho i' end). split.
      - intros j hj. destruct (j <? i') eqn: eqji'.
        reflexivity. unfold "<?" in eqji'.
        rewrite nleb_le in eqji'. unfold "<" in hj. 
        apply le_S_n in hj. rewrite Nat.le_lteq in hj. destruct hj.
        * exfalso. apply eqji', H.
        * rewrite H. reflexivity.
      - intros j. destruct (j <? i') eqn: eqji'. rewrite heq. 
        apply (iteration_grow_n (step_grow Fall Fex) (PeanoNat.Nat.le_max_l n_prev n_i)).
        apply hrho'.
        unfold "<"; unfold "<?" in eqji'.
        rewrite <-Nat.leb_le. apply eqji'.
        apply (iteration_grow_n (step_grow Fall Fex) (PeanoNat.Nat.le_max_r n_prev n_i)).
        apply hiteri.
  Qed.

  Fixpoint make_const_env_at (n: nat) (rho: env M): env M :=
    match n with 
    | 0 => fun _ => rho 0
    | S m => (rho 0) .: (make_const_env_at m (S >> rho))
    end.

  Lemma enveq_env_const_env (n: nat):
  forall rho, 
  enveq n rho (make_const_env_at n rho).
  Proof.
    induction n as [|n' ih].
    intros rho i hi. inversion hi.
    intros rho i hi. simpl.
    destruct i as [|i']. reflexivity.
    simpl. rewrite <-ih. reflexivity.
    lia.
  Qed.

  Lemma const_env_is_const (n: nat) (rho: env M):
  forall i: nat, n <= i ->
  make_const_env_at n rho i = make_const_env_at n rho n.
  Proof.
    generalize dependent rho.
    induction n. all: intros rho i h. 
    + reflexivity.
    + destruct i as [|i']. inversion h.
      apply IHn. apply le_S_n, h.
  Qed.   

  Lemma const_env_is_env (n: nat) (rho: env M):
  forall i, i <= n ->
  make_const_env_at n rho i = rho i.
  Proof.
    generalize dependent rho.
    induction n. all: intros rho i h.
    + apply Nat.le_0_r in h. rewrite h. reflexivity.
    + destruct i. reflexivity.
      simpl. rewrite IHn. reflexivity. apply le_S_n, h.
  Qed.

  Lemma increasing_prop_max:
  forall (P: nat -> Prop), (forall n m:nat, n <= m -> P n -> P m) ->
  forall n m: nat, P n \/ P m -> P (max n m).
  Proof.
    intros P hP n m [hPn|hPm].
    all: destruct (Nat.max_dec n m) as [h|h]. all: rewrite h.
    + apply hPn.
    + apply (hP n m). rewrite <-Nat.max_r_iff. apply h. apply hPn.
    + apply (hP m n). rewrite <-Nat.max_l_iff. apply h. apply hPm.
    + apply hPm.
  Qed.

  Definition in_iter (Fall: TV_all) (Fex: TV_ex) (A: set M)
  (m: M) (k: nat) := 
  iteration k (step Fall Fex) A m.

  Lemma in_iter_incr (Fall: TV_all) (Fex: TV_ex) (A: set M) (m: M):
  forall k l, k <= l ->
  in_iter Fall Fex A m k -> in_iter Fall Fex A m l.
  Proof.
    intros k l. generalize dependent k. induction l as [|l' IHl]. all: intros k hk H.
    + apply Nat.le_0_r in hk. rewrite hk in H. apply H.
    + destruct (Nat.eq_dec k (S l')) as [e|e].
      - rewrite <-e. apply H.
      - unfold in_iter. simpl. apply step_grow. apply (IHl k). 
        apply le_S_n. apply Nat.le_neq. apply (conj hk e).
        apply H.
  Qed.

  Lemma squish_env {Fall: TV_all} {Fex: TV_ex} (rho: env M) (A: set M):
  (forall n, Step Fall Fex A (rho n)) ->
  forall k, exists z,
  (forall i, i <= k -> iteration z (step Fall Fex) A ((make_const_env_at k rho) i)).
  Proof.
    intros H k. induction k as [|k' hk].
    + destruct (H 0) as [z0 hz0].
      exists z0. intros i hi. inversion hi. apply hz0.
    + destruct hk as [z hz].
      destruct (H (S k')) as [zk' hzk'].
      exists (max z zk'). 
      intros i hi.
      destruct (Nat.eq_dec i (S k')) as [e | ].
      - rewrite const_env_is_env. 2: apply hi.
        apply (increasing_prop_max).
        * apply in_iter_incr.
        * right. rewrite e. apply hzk'.
      - apply increasing_prop_max.
        * apply in_iter_incr.
        * left.
          assert (hi': i <= k') by lia.
          assert (iteration z (step Fall Fex) A (rho i)).
          { rewrite <-(const_env_is_env rho hi'). apply hz. apply hi'. }
          rewrite const_env_is_env. 1: assumption. assumption.
  Qed.

  Theorem Step_is_step_fp {Fall: TV_all} {Fex: TV_ex}:
  forall A, Step Fall Fex A == step Fall Fex (Step Fall Fex A).
  Proof.
    intros A. split. all: intros x H.
    + apply step_grow, H.
    + destruct H as [[phi [rho [hrho hxTV]]]|[t [rho [hrho hxt]]]].
      - pose (i_star := form_max_var phi).
        destruct (squish_env hrho (i_star)) as [n_star hns].
        exists (1 + n_star). simpl.
        left. exists phi, (make_const_env_at (i_star) rho). split.
        * intros i. 
          destruct (i <? i_star) eqn: eqi.
          { apply hns. unfold "<". 
          transitivity (S i). apply le_S, le_n.
          rewrite Nat.ltb_lt in eqi. apply eqi. }
          rewrite Nat.ltb_ge in eqi.
          rewrite (const_env_is_const _ eqi). apply hns, le_n.
        * assert (heq: enveq i_star rho (make_const_env_at i_star rho)).
          apply enveq_env_const_env.
          rewrite <-(hFEI Fall heq), <-(hFEI Fex heq). apply hxTV.
      - destruct (exists_term_max_var t) as [i_star hi].
        destruct (exists_env_Step_max_iteration hrho i_star) as [n_star [rho' [henveq hrho']]].
        exists (S n_star). rewrite hxt. rewrite (hi _ rho' henveq). 
        apply (step_eval t hrho').
  Qed.
  
  Lemma nefp_step_of_Step {Fall: TV_all} {Fex: TV_ex} (A: set M) (hA: inhabited (of_set A)):
  nefp_step Fall Fex (Step Fall Fex A).
  Proof.
    destruct hA as [[a ha]].
    split.
    + apply (Step_grow Fall Fex) in ha. apply inhabits, (Build_of_set ha).
    + apply Step_is_step_fp.
  Qed.

  Definition model_of_inhabited_set
  {Fall: TV_all} {Fex: TV_ex} (A: set M) (hA: inhabited (of_set A)) :=
  model_of_fcl (@fcl_of_nefp_step Fall Fex _ (nefp_step_of_Step ( hA))).

  Fact singleton_smaller_term_form {m0: M}:
  (of_set (fun m => m = m0) ≤ term + form)%type.
  Proof.
    apply smaller_of_inj.
    exists (fun _ => inl $0).
    intros [m hm] [m' hm'] _.
    rewrite hm, hm'. reflexivity.
  Qed. 

End Sizes.

End FixCardOrder.

Section DLS.

Theorem DLS'_of_TV:
infT smaller -> inhabited (TV_all) -> inhabited (TV_ex) -> inhabited M -> gDLS_on _ _ M smaller.
Proof.
  intros seqinf [Fall] [Fex] [m0].
  pose (A0 := fun m => m = m0).
  assert (hm := eq_refl m0 : A0 m0).
  assert (hA0 := inhabits (Build_of_set hm)).
  pose (N := @model_of_inhabited_set Fall Fex _ hA0).
  exists N. split. 2: split.
  + apply inhabits.
    assert (H: Step Fall Fex A0 m0). exists 0. apply hm.
    apply (Build_of_set H).
  + apply (@Step_singl_smaller_term_form seqinf).
  + apply elemsubm_of_nefp_step.
Qed.

End DLS.

End fix_variables.

Check @DLS'_of_TV.
