From CHKC Require Import
  Coqlib
  Tactics
  ListUtil
  Map
  CheckedCDef
  CheckedCProp.
  (* CheckedCPropDev. *)

Require Export Bool.
Require Export Arith.
Require Export Psatz.
Require Export Program.
Require Export List.
Require Import ZArith.
Require Import ZArith.BinIntDef.
Require Export BinNums.
Require Import BinPos BinNat.

#[global]
Hint Unfold rheap_consistent : Preservation.
Hint Unfold heap_consistent_checked : Preservation.
Local Open Scope Z_scope.

Ltac solve_ctxt :=
  match goal with
  | [E : ctxt |- _] =>
      destruct E; try congruence; solve_step
  end.  
         

Lemma step_implies_reduces : forall D F H s e H' s' r E m,
    mode_of E = m ->
    @step D F (s,H) e (s',H') r ->
    reduces D F (s,H) (in_hole e E) m.
Proof.
  intros.
  destruct r.
  exists (s',H'), (RExpr (in_hole e0 E)).
  constructor; easy.
  exists (s',H'), RNull.
  constructor; easy.
  exists (s',H'), RBounds.
  constructor; easy.
Qed.

Lemma step_implies_reduces_1 : forall D F H s e H' s' E m e',
    mode_of E = m ->
    @step D F (s,H) e (s',H') (RExpr e') ->
    reduce D F (s,H) (in_hole e E) m (s',H') (RExpr (in_hole e' E)).
Proof.
  intros.
  constructor; easy.
Qed.

Hint Resolve step_implies_reduces : Preservation.

(*
Lemma reduces_congruence : forall D F H s e0 e,
    (exists E, in_hole e0 E = e) ->
    reduces D F (s,H) e0 ->
    reduces D F (s,H) e.
Proof.
  intros.
  destruct H0 as [ E Hhole ].
  destruct H1 as [ m' [ H' [r  HRed ]] ].
  inv HRed as [ ? e0' ? ? e0'' E' | ? e0' ? ? E' | ? e0' ? ? E'  | ? e0' ? ? E' ]; rewrite compose_correct; eauto 20.
Admitted.

Hint Resolve reduces_congruence : Preservation.
*)
Lemma eval_arg_lit: forall S e t e', eval_arg S e t e' -> exists n, e' = ELit n t.
Proof.
 intros. inv H. exists n; easy. exists n; easy.
Qed.


Lemma eval_arg_same: forall S e t t' v v', eval_arg S e t (ELit v t) -> eval_arg S e t' (ELit v' t') -> v = v'.
Proof.
 intros. inv H. inv H0. easy.
 inv H0. apply Stack.mapsto_always_same with (v1 := (v', t'1)) in H4; try easy.
 inv H4. easy.
Qed.

Lemma eval_el_vl_1: forall S es tvl xl e t ea ta, 
   eval_el S es tvl xl e t ea ta -> 
   (exists vl, Forall2 (fun e v => forall t v', eval_arg S e t (ELit v' t) -> v = v') es vl).
Proof.
  intros.
  induction H;simpl in *.
  exists []. constructor.
  apply eval_arg_lit in H0 as X1.
  destruct X1; subst.
  destruct IHeval_el. exists (x0::x1).
  constructor;try easy.
  intros. apply eval_arg_same with (t := t) (v := x0) in H3; try easy.
  destruct IHeval_el. exists (v::x0).
  constructor;try easy.
  intros. apply eval_arg_same with (t := TNat) (v := v) in H2; try easy.
Qed.

Lemma eval_el_vl: forall S es vl tvl xl e t ea ta, 
   Forall2 (fun e v => forall t v', eval_arg S e t (ELit v' t) -> v = v') es vl ->
   eval_el S es tvl xl e t ea ta -> eval_vl vl tvl xl e t ea ta.
Proof.
  intros.
  generalize dependent tvl.
  generalize dependent xl.
  generalize dependent e.
  generalize dependent t.
  generalize dependent ea.
  generalize dependent ta.
  induction H; intros;simpl in *.
  inv H0. constructor.
  inv H1.
  apply  eval_arg_lit in H5 as X1. destruct X1; subst.
  apply H  in H5 as X2. subst.
  apply eval_vl_many_1; try easy.
  apply IHForall2; try easy.
  apply H  in H4 as X2. subst.
  apply eval_vl_many_2; try easy.
  apply IHForall2; try easy.
Qed.

Lemma split_zero {A B:Type}: forall (l:list (A*B)), (List.split l).2 = [] -> l = [].
Proof.
  induction l;intros;simpl in *; try easy.
  destruct a. 
  destruct (split l) eqn:eq1. inv H.
Qed.

(*
Lemma well_typed_arg_ex: forall D U Q H env m e t x t',
                  @well_typed_arg D U Q H env m e t
           -> @well_typed_arg D U Q H (Env.add x t' env) m e t.
Proof.
  intros. inv H0; simpl in *.
  constructor; try easy.
  constructor.
Qed.
*)

Lemma well_typed_args_ex: forall D U H env m es vl xl t ta x t',
                  @well_typed_args D U H env m es vl xl t ta
           -> @well_typed_args D U H (Env.add x t' env) m es vl xl t ta.
Proof.
  intros. induction H0; simpl in *.
  constructor.
  constructor; try easy.
Admitted.

Lemma well_typed_eval_vs: forall D F Q R env S m es xl ts tvl t t' ta ta' e ea,
    (forall x n, Stack.MapsTo x (n,TNat) S -> Theta.MapsTo x (NumEq n) Q) ->
    subtype D empty_theta t' t ->
    Forall2 (subtype D empty_theta) ts ((split tvl).2) ->
    @well_typed_args D F R env m es ts xl t ta -> eval_el S es tvl xl e t' ea ta'
    -> eq_subtype D Q ta' ta.
Proof.
 intros.
  generalize dependent e.
  generalize dependent t'.
  generalize dependent ea.
  generalize dependent ta'.
  generalize dependent tvl.
 induction H2;intros;simpl in *.
 inv H3. unfold eq_subtype. exists ta'. split. 
 apply type_eq_refl.
 apply subtype_q_empty.  easy.
 inv H5. inv H3.
 destruct (split tvl0) eqn:eq1. inv H7.
 apply IHwell_typed_args with (tvl := tvl0) (ea := ea') (t' := t') (e:= e0); try easy.
 rewrite eq1; easy.
 inv H3.
 destruct (split tvl0) eqn:eq1. inv H7.
 apply subtype_nat in H9; subst. easy.
 inv H5.
 inv H3.
 destruct (split tvl0) eqn:eq1. inv H7.
 apply subtype_nat_1 in H10; subst. easy.
 inv H3.
 destruct (split tvl0) eqn:eq1. inv H7.
 apply IHwell_typed_args with (tvl := (map (fun a : var * type => (a.1, subst_type a.2 x (Num v)))
           tvl0)) (t' := (subst_type t' x (Num v))) (ea := ea') (e:= e0); try easy.
 assert ((split
     (map (fun a : var * type => (a.1, subst_type a.2 x (Num v)))
        tvl0)).2 = map (fun a => subst_type a x (Num v)) l0).
 clear H H0 H1 H2 IHwell_typed_args H4 H15 H16 H8 H9.
 assert (l0 = (split tvl0).2). rewrite eq1. easy. rewrite H. clear eq1 H.
 induction tvl0;intros;simpl in *; try easy.
 destruct (split
     (map (fun a : var * type => (a.1, subst_type a.2 x (Num v)))
        tvl0)) eqn:eq3.
 destruct a. destruct (split tvl0) eqn:eq2.
 simpl in *. rewrite  IHtvl0. easy.
 rewrite H3. clear H3.
 clear H2 IHwell_typed_args H16 H8 H4 eq1.
 induction H9; simpl in *. constructor.
 constructor; try easy.
 inv H15. simpl in *. inv H0.
Admitted.


Lemma well_typed_args_sub : forall D F Q R R' env m es xl ts tlb t tb ta, 
       rheap_consistent D F R' R ->
       subtype D empty_theta tb t ->
       Forall2 (subtype D empty_theta) ts tlb ->
       @well_typed_args D F R env m es ts xl t ta -> 
       (exists ta', @well_typed_args D F R' env m es tlb xl tb ta' /\ subtype D Q ta' ta). 
Proof.
Admitted.

Lemma replicate_gt_eq : forall x t, 0 < x -> Z.of_nat (length (Zreplicate (x) t)) = x.
Proof.
  intros.
  unfold Zreplicate.
  destruct x eqn:eq1. lia.
  simpl. 
  rewrite replicate_length. lia.
  lia.
Qed.

Lemma replicate_nth_anti {A:Type} : forall (n k : nat) (x : A),
    (k < n)%nat -> nth_error (replicate n x) k = Some x.
  Proof.
    induction n; intros k w H.
    - lia.
    - simpl. destruct k. simpl. easy.
      assert (k < n)%nat by lia.
      apply IHn with (x := w) in H0. simpl. easy. 
Qed.

(** Type Preservation Theorem. *)
Section Preservation. 
  Variable D : structdef.
  Variable F : FEnv.
  Hypothesis HDwf : structdef_wf D.
  Lemma preservation : forall s R env Q e t s' R' e',
      rheap_wf R ->
      rheap_wt_all D F R ->
      expr_wf D Checked e ->
      stack_wt D Checked s ->
      env_wt D Checked env ->
      theta_wt Q env s ->
      sub_domain env s ->
      stack_wf D Q env s ->
      stack_rheap_consistent D F R s ->
      fun_wf D F R ->
      well_typed D F R env Q Checked e t ->
      reduce D F
        (s, R) e Checked
        (s', R') (RExpr e') ->
      exists t',
        sub_domain env s'
        /\ stack_wf D Q env s'
        /\ theta_wt Q env s'
        /\ stack_rheap_consistent D F R s'
        /\ rheap_consistent D F R' R
        /\ well_typed D F R' env Q Checked e' t'
        /\ eq_subtype D Q t' t.
  Proof with (eauto with ty sem heap Preservation).
    intros s R env Q e t s' R' e'
      HRwf HRWt HEwf Hswt Henvt HQt HsubDom Hswf HsHwf Hwf Hwt.
    generalize dependent R'. generalize dependent s'.  generalize dependent e'.
    remember Checked as m.
    induction Hwt as
      [
        env Q n t Hmode HQ HTyLit                                  | (* Literals Checked *)
        env Q n t Hmode HQ                                         | (* Literals Tainted *)
        env Q n t                                                  | (* Literals-Unchecked *)
        env Q m x t Hx                                             | (* Variables *)
        env Q m m' es x xl ts t ta HMode Wb HTyf IH1 HArgs         | (* Call *)
        env Q x m m' h l t Wb HMode                                | (* Strlen *)
        env Q m x y e l h t ta Alpha Wb HTy IH Hx                  | (* LetStrlen *)
        env Q m x e1 e2 t b HTy1 IH1 HTy2 IH2 Hx Hdept             | (* Let-Nat-Expr *)
        env Q m x e1 t1 e2 t HTy1 IH1 HTy2 IH2 Hx                  | (* Let-Expr *)
        env Q m x na a e t HIn Hx HTy1 IH1                         | (* RetNat *)
        env Q m x na ta a e t HIn HTy1 IH1 Hx                      | (* Ret *)
        env Q m e1 e2 HTy1 IH1 HTy2 IH2                            | (* Addition *)
        env Q m t e1 e2 HTyfun HTy1 IH1 HTy2 IH2                   | (* Addition Index *)
        env Q m e m' T fs i fi ti HTy IH HWf1 HWf2                 | (* Field Addr *)
       (* env Q m w Wb                                               | (* Malloc *) *)
        env Q m e t HTy IH                                         | (* Unchecked *)
        env Q m e t HTy IH                                         | (* checked *)
        env Q m t e t' Wb HChkPtr HTy IH                           | (* Cast - nat *)
        env Q m t e t' Wb HTy IH HSub                              | (* Cast - subtype *)
        env Q m e x y u v t t' Wb HTy IH Teq                       | (* DynCast - ptr array *)
        env Q m e x y t t' HNot Teq Wb HTy IH                      | (* DynCast - ptr array from ptr *)
        env Q m e x y u v t t' Wb Teq HTy IH                       | (* DynCast - ptr nt-array *)
        env Q m e m' t l h t' t'' HTy IH HSub HPtrType HMode       | (* Deref *)
        env Q m e1 m' l h e2 t WT Twf HTy1 IH1 HTy2 IH2 HMode                      | (* Index for array pointers *)
        env Q m e1 m' l h e2 t WT Twf HTy1 IH1 HTy2 IH2 HMode                      | (* Index for ntarray pointers *)
        env Q m e1 e2 m' t t1 HSub WT HTy1 IH1 HTy2 IH2 HMode                      | (* Assign normal *)
        env Q m e1 e2 m' t ts HTy1 IH1 HTy2 IH2 HMode HZero                        | (* Assign function *)
        env Q m e1 e2 m' l h t t' WT Twf HSub HTy1 IH1 HTy2 IH2 HMode              | (* Assign array *)
        env Q m e1 e2 m' l h t t' WT Twf HSub HTy1 IH1 HTy2 IH2 HMode              | (* Assign nt-array *)
        
        env Q m e1 e2 e3 m' l h t t' WT Twf TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for array pointers *)
        env Q m e1 e2 e3 m' l h t t' WT Twf TSub HTy1 IH1 HTy2 IH2 HTy3 IH3 HMode      |  (* IndAssign for ntarray pointers *)
        env Q m m' x t t1 e1 e2 t2 t3 t4 HEnv TSub HPtr HTy1 IH1 HTy2 IH2 HJoin HMode  | (* IfDef *)
        env Q m m' x l t e1 e2 t2 t3 t4 HEnv HTy1 IH1 HTy2 IH2 HJoin HMode             | (* IfDefNT *)
        env Q m e1 e2 e3 t2 t3 t4 HTy1 IH1 HTy2 IH2 HTy3 IH3 HJoin                       (* If *)
      ]; intros e' s' R' Hreduces; subst.
    (* T-Lit, impossible because values do not step *)
    - inv Hreduces; solve_ctxt.
    (* T-LitTainted *)
    - inv Hreduces; solve_ctxt.
    (* T-LitUnchecked *)
    - inv Hreduces; solve_ctxt.
    (* T-Var *)
    -  inv Hreduces; solve_ctxt.
      inv H5. exists t0.
      destruct R' as [Hchk Htnt]; subst; intuition...
      cbn.
      apply Hswt in H4 as eq1. destruct eq1 as [X1 [X2 X3]].
      inv X1.
      constructor. constructor. constructor.
      constructor. destruct m;try easy.
      constructor. constructor. easy.
      intuition...
      apply TyLitTainted. intros R. inv R. easy.
      apply TyLitTainted. intros R. inv R. easy.
      apply Hswf in Hx. destruct Hx as [v1 [t1 [HSub1 HM]]]. 
      apply Stack.mapsto_always_same with (v1 := (v1, t1)) in H4; try easy.
      inv H4. easy.
    (*T-Call*)
    - destruct HMode. assert (Checked = Checked) by easy.
      apply H in H1.
      inv Hreduces. destruct E; try congruence; try solve [solve_step].
      simpl in *; subst.
      inv  H5. inv HTyf.
      inv H15; eauto; try easy.
      destruct Hwf. rewrite H2 in H6. easy. rewrite H6 in H7.
      inv H7.
      apply subtype_fun in H10 as Y1; try easy. destruct Y1 as [yl [tb [tlb Y1]]];subst.
      specialize (get_fun_type_fun tvl0 ta0 Checked) as X1.
      rewrite X1 in H10. rewrite X1 in Y1.
      inv Y1.
      apply subtype_fun_1 in H10 as X2; try easy.
      destruct X2 as [X2 [X3 X4]]; subst.
      exists ta'.
      split; try easy. split; try easy.
      split; try easy. split; try easy.
      split. apply rheap_consistent_refl.
      apply eval_el_vl_1 in H12 as X5.
      destruct X5 as [vl X5].
      apply eval_el_vl with (xl := (get_xl tvl0)) (tvl := tvl0) (e := e0) 
        (t := tb) (ea:=e'0) (ta:=ta') in X5 as X6; try easy.
      destruct Hwf as [Y1 Y2].
      assert (mode_leq Checked Checked) by easy.
      destruct (Y2 env Q x0 tvl0 tb ta' 
        e0 vl e'0 Checked Checked H2 H6 X6) as [Y3 [Y4 [Y5 [Y6 [Y7 [Y8 Y9]]]]]].
      clear H2.
      split; try easy.
      eapply well_typed_eval_vs with (F := F) (R := R') (env := env) (S := s').
      destruct HQt as [eq1 [eq2 eq3]].
      intros. apply eq3. easy.
      apply X3. apply X4. apply HArgs. apply H12.
      apply subtype_fun in H5.
      destruct H5 as [yl [tb [tlb Y1]]];subst. inv Y1.
      unfold is_fun_type in *. easy.
      assert (CheckedCDef.is_checked (TPtr Checked (TFun xl t ts))).
      constructor. easy.
      inv HTyf. inv H13.
      inv H15; eauto; try easy.
      destruct Hwf. rewrite H4 in H11. easy. rewrite H11 in H9.
      inv H9.
      apply subtype_fun in H13 as Y1; try easy. destruct Y1 as [yl [tb [tlb Y1]]];subst.
      specialize (get_fun_type_fun tvl0 ta0 Tainted) as X1.
      rewrite X1 in H13. rewrite X1 in Y1.
      inv Y1.
      apply subtype_fun_1 in H13 as X2; try easy.
      destruct X2 as [X2 [X3 X4]]; subst.
      exists ta'.
      split; try easy. split; try easy.
      split; try easy. split; try easy.
      split. apply rheap_consistent_refl.
      apply eval_el_vl_1 in H14 as X5.
      destruct X5 as [vl X5].
      apply eval_el_vl with (xl := (get_xl tvl0)) (tvl := tvl0) (e := e0) 
        (t := tb) (ea:=e'0) (ta:=ta') in X5 as X6; try easy.
      destruct Hwf as [Y1 Y2].
      assert (mode_leq Tainted Checked) by easy.
      destruct (Y2 env Q x0 tvl0 tb ta' 
        e0 vl e'0 Checked Tainted H4 H11 X6) as [Y3 [Y4 [Y5 [Y6 [Y7 [Y8 Y9]]]]]].
      clear H4.
      split; try easy.
      eapply well_typed_eval_vs with (F := F) (R := (H2, H3)) (env := env) (S := s').
      destruct HQt as [eq1 [eq2 eq3]].
      intros. apply eq3. easy.
      apply X3. apply X4. apply HArgs. apply H14.
      apply subtype_fun in H7.
      destruct H7 as [yl [tb [tlb Y1]]];subst. inv Y1.
      unfold is_fun_type in *. easy.
      inv HTyf; easy.
      inv H2.
      edestruct IH1; try easy.
      inv HEwf; easy. apply step_implies_reduces_1; try easy. apply H5.
      destruct H2 as [X1 [X2 [X3 [X4 [X5 [X6 X7]]]]]].
      simpl. apply eq_subtype_fun in X7.
      destruct X7 as [tb [tlb [X8 [X9 X10]]]];subst; try easy.
      apply well_typed_args_sub with (tlb := tlb) (tb := tb) (Q := Q) (R' := R') in HArgs as X11; try easy.
      destruct X11 as [ta' [X11 X12]].
      exists ta'.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split; try easy.
      split.
      apply TyCall with (m' := m') (xl := xl) (ts := tlb) (t := tb); try easy.
      unfold eq_subtype. exists ta'. split. apply type_eq_refl.
      easy.
    (*T-Strlen*)
    - inv HMode. inv Hreduces; solve_ctxt.
      inv H7. 
     *
      exists TNat; simpl in *.
      unfold stack_wf in Hswf.
      apply Hswf in Wb as X1; try easy.
      destruct X1 as [va [ta [X1 X2]]].
      apply Stack.mapsto_always_same with (v1 := (va, ta)) in H15 as X3; try easy.
      inv X3.
      split.
      unfold sub_domain,change_strlen_stack; intros.
      destruct (n' <=? h0 ) eqn:eq1.
      apply HsubDom; easy.
      destruct (Nat.eq_dec x0 x); subst.
      exists (n, TPtr Checked (TNTArray (Num l0) (Num n') t0)).
      apply Stack.add_1. easy.
      apply HsubDom in H1. destruct H1.
      exists x1.
      apply Stack.add_2. lia. easy.
      split. unfold stack_wf,change_strlen_stack in *. intros.
      destruct (Nat.eq_dec x0 x); subst.
      apply Env.mapsto_always_same with (v1 := t2) in Wb as X4; try easy;subst.
      destruct (n' <=? h0 ) eqn:eq1.
      exists n,(TPtr Checked (TNTArray (Num l0) (Num h0) t0)); easy.
      exists n,(TPtr Checked (TNTArray (Num l0) (Num n') t0)).
      split. apply eq_subtype_trans with (t2:=(TPtr Checked (TNTArray (Num l0) (Num h0) t0))); try easy.
      unfold eq_subtype. exists (TPtr Checked (TNTArray (Num l0) (Num n') t0)).
      split. apply type_eq_refl.
      constructor. apply SubTyNtSubsume; try easy.
      constructor. easy.
      constructor. lia.
      apply Stack.add_1. easy.
      apply Hswf in H1. destruct H1 as [va [ta [Y1 Y2]]].
      exists va, ta; try easy.
      split. easy.
      destruct (n' <=? h0). try easy.
      apply Stack.add_2. lia. easy.
      split. unfold theta_wt in *.
      destruct HQt.
      split. easy. split.
      destruct H4. intros.
      unfold change_strlen_stack in *.
      destruct (n' <=? h0).
      apply H4 with (x := x0); try easy.
      destruct (Nat.eq_dec x x0). subst.
      apply Stack.mapsto_add1 in H7. inv H7.
      apply Stack.add_3 in H7.
      apply H4 with (x := x0); try easy. easy.
      intros.
      unfold change_strlen_stack in *. destruct H4.
      destruct (n' <=? h0). 
      apply H6 with (x := x0); try easy.
      destruct (Nat.eq_dec x x0). subst.
      apply Stack.mapsto_add1 in H5. inv H5.
      apply Stack.add_3 in H5.
      apply H6 with (x := x0); try easy. easy.
      split.
      unfold stack_rheap_consistent, change_strlen_stack in *.
      intros.
      destruct (n' <=? h0) eqn:eq1.
      eapply HsHwf. apply H1. apply H4.
      destruct (Nat.eq_dec x x0); subst.
      apply Stack.mapsto_add1 in H4. inv H4.
      apply HsHwf with (Hchk := Hchk) (Htnt := Htnt) in X2; try easy. inv H1.
      apply Hswt in H15. destruct H15 as [Y3 [Y4 Y5]].
      inv X2; try easy. apply TyLitZero_C. 
      unfold scope_set_add in *. inv H4. inv H1. inv H5.
      apply TyLitC_C with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. apply SubTyRefl. simpl.
      intros.
      unfold scope_set_add.
      rewrite replicate_gt_eq in H1; try lia.
      assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H4 in H1. clear H4.
      destruct (Z.eq_dec n' 0). subst.
      rewrite replicate_gt_eq in H9; try lia.
      specialize (H16 n) as eq2.
      assert (n <= n < n + n') by lia.
      apply eq2 in H4. clear eq2.
      specialize (H9 0) as eq2.
      assert (l0 <= 0 < l0 + Z.of_nat (length (Zreplicate (h0 - l0 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H5. clear eq2.
      destruct H5 as [na [ta [A1 [A2 A3]]]].
      destruct H4 as [nb [A4 A5]].
      rewrite Z.add_0_r in A2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in A2; try easy. inv A2.
      symmetry in A1.
      destruct (h0 - l0 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in A1.
      apply replicate_nth in A1. subst.
      destruct (Z_ge_dec h0 k).
      specialize (H9 k).
      assert (l0 <= k < l0 + Z.of_nat (length (Zreplicate (Z.pos p1) ta))).
      rewrite replicate_gt_eq; try lia.
      apply H9 in H4. destruct H4 as [nc [tc [B1 [B2 B3]]]].
      exists nc. exists tc.
      split. unfold Zreplicate in *.
      symmetry in B1.
      apply replicate_nth in B1. subst.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_nth_anti; try easy. lia. easy.
      destruct (Z.eq_dec n' k). subst.
      exists 0. exists ta.
      destruct (k - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      unfold Zreplicate. split.
      rewrite replicate_nth_anti; try easy. lia. split. easy.
      constructor.
      specialize (H16 (n+k)).
      assert (n <= n + k < n + n') by lia.
      apply H16 in H4.
      destruct H4 as [nb [Y1 Y2]].
      destruct HRWt with (Hchk0 := Hchk) (Htnt0 := Htnt); try easy.
      apply H4 in Y1 as eq2.
      exists nb. exists ta.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      split. unfold Zreplicate.
      rewrite replicate_nth_anti; try easy. lia. easy.
      inv H10. inv H10. apply simple_type_tnt in H2.
      destruct H2 as [l2 [h2 [A1 A2]]];subst. inv H18. inv H10.
      destruct (Z_ge_dec h2 n').
      apply checked_subtype_well_type
        with (t := (TPtr Checked (TNTArray (Num l2) (Num h2) t0))); try easy.
      inv Y4. inv H8. constructor. constructor; easy. easy.
      apply TyLitC_C with (w := (TNTArray (Num l2) 
           (Num h2) t0)) (b := l2) (ts := Zreplicate (h2 - l2 + 1) t0); try easy.
      constructor. constructor.
      intros.
      unfold scope_set_add.
      inv H5.
      specialize (H9 k H1). easy.
      exists ((TPtr Checked (TNTArray (Num l2) (Num h2) t0))). split. apply type_eq_refl.
      constructor. apply SubTyNtSubsume. constructor. lia. constructor. lia.
      inv H5.
      apply TyLitC_C with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. constructor.
      intros.
      unfold scope_set_add.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_gt_eq in H1; try easy.
      rewrite <- Hp in *. assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H2 in H1. clear H2.
      destruct (Z.eq_dec n' 0). subst. lia.
      specialize (H16 n) as eq2.
      assert (n <= n < n + n') by lia.
      apply eq2 in H2. clear eq2.
      specialize (H9 0) as eq2.
      assert (l2 <= 0 < l2 + Z.of_nat (length (Zreplicate (h2 - l2 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H5. clear eq2.
      destruct H5 as [na [ta [A1 [A2 A3]]]].
      destruct H2 as [nb [A4 A5]].
      rewrite Z.add_0_r in A2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in A2; try easy. inv A2.
      symmetry in A1.
      destruct (h2 - l2 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in A1.
      apply replicate_nth in A1. subst.
      destruct (Z_ge_dec h2 k).
      specialize (H9 k).
      assert (l2 <= k < l2 + Z.of_nat (length (Zreplicate (Z.pos p1) ta))).
      rewrite replicate_gt_eq; try lia.
      apply H9 in H2. destruct H2 as [nc [tc [B1 [B2 B3]]]].
      exists nc. exists tc.
      rewrite Hp.
      split. unfold Zreplicate in *.
      symmetry in B1.
      apply replicate_nth in B1. subst.
      rewrite replicate_nth_anti; try easy. lia. easy.
      destruct (Z.eq_dec n' k). subst.
      exists 0. exists ta.
      unfold Zreplicate.
      destruct (k - l0 + 1) as [| p2 | ?] eqn:Hp2; zify; [lia | |lia].
      rewrite replicate_nth_anti; try easy. lia.
      split. easy. split. easy. apply TyLitZero_C.
      specialize (H16 (n+k)).
      assert (n <= n + k < n + n') by lia.
      apply H16 in H2.
      destruct H2 as [nb [Y1 Y2]].
      destruct HRWt with (Hchk0 := Hchk) (Htnt0 := Htnt); try easy.
      apply H2 in Y1 as eq2.
      exists nb. exists ta.
      split. unfold Zreplicate. rewrite Hp.
      rewrite replicate_nth_anti; try easy. lia. easy.
      apply Stack.add_3 in H4. apply HsHwf with (Hchk := Hchk) (Htnt := Htnt) in H4; try easy.
      easy. unfold rheap_consistent.
      split. intros. inv H1. inv H4. unfold heap_consistent_checked. intros. easy.
      split. constructor. constructor. easy. constructor.
      exists TNat. split. apply type_eq_refl. constructor. constructor.      
    *
      exists TNat; simpl in *.
      unfold stack_wf in Hswf.
      apply Hswf in Wb as X1; try easy.
      destruct X1 as [va [ta [X1 X2]]].
      apply Stack.mapsto_always_same with (v1 := (va, ta)) in H15 as X3; try easy.
      inv X3.
      split.
      unfold sub_domain,change_strlen_stack; intros.
      destruct (n' <=? h0 ) eqn:eq1.
      apply HsubDom; easy.
      destruct (Nat.eq_dec x0 x); subst.
      exists (n, TPtr Tainted (TNTArray (Num l0) (Num n') t0)).
      apply Stack.add_1. easy.
      apply HsubDom in H1. destruct H1.
      exists x1.
      apply Stack.add_2. lia. easy.
      split. unfold stack_wf,change_strlen_stack in *. intros.
      destruct (Nat.eq_dec x0 x); subst.
      apply Env.mapsto_always_same with (v1 := t2) in Wb as X4; try easy;subst.
      destruct (n' <=? h0 ) eqn:eq1.
      exists n,(TPtr Tainted (TNTArray (Num l0) (Num h0) t0)); easy.
      exists n,(TPtr Tainted (TNTArray (Num l0) (Num n') t0)).
      split. apply eq_subtype_trans with (t2:=(TPtr Tainted (TNTArray (Num l0) (Num h0) t0))); try easy.
      unfold eq_subtype. exists (TPtr Tainted (TNTArray (Num l0) (Num n') t0)).
      split. apply type_eq_refl.
      constructor. apply SubTyNtSubsume; try easy.
      constructor. easy.
      constructor. lia.
      apply Stack.add_1. easy.
      apply Hswf in H1. destruct H1 as [va [ta [Y1 Y2]]].
      exists va, ta; try easy.
      split. easy.
      destruct (n' <=? h0). try easy.
      apply Stack.add_2. lia. easy.
      split. unfold theta_wt in *.
      destruct HQt.
      split. easy. split.
      destruct H4. intros.
      unfold change_strlen_stack in *.
      destruct (n' <=? h0).
      apply H4 with (x := x0); try easy.
      destruct (Nat.eq_dec x x0). subst.
      apply Stack.mapsto_add1 in H8. inv H8.
      apply Stack.add_3 in H8.
      apply H4 with (x := x0); try easy. easy.
      intros.
      unfold change_strlen_stack in *. destruct H4.
      destruct (n' <=? h0). 
      apply H6 with (x := x0); try easy.
      destruct (Nat.eq_dec x x0). subst.
      apply Stack.mapsto_add1 in H5. inv H5.
      apply Stack.add_3 in H5.
      apply H6 with (x := x0); try easy. easy.
      split.
      unfold stack_rheap_consistent, change_strlen_stack in *.
      intros.
      destruct (n' <=? h0) eqn:eq1.
      eapply HsHwf. apply H1. apply H4.
      destruct (Nat.eq_dec x x0); subst.
      apply Stack.mapsto_add1 in H4. inv H4.
      destruct (Z.eq_dec n' 0). subst.
      rewrite Z.add_0_r in H17.
      apply TyLitC_T with (w := ((TNTArray (Num 0) (Num 0) t0)))
       (b := 0) (ts := (Zreplicate 1 t0)); eauto.

      apply HsHwf with (Hchk := Hchk) (Htnt := Htnt) in X2; try easy. inv H1.
      apply Hswt in H15. destruct H15 as [Y3 [Y4 Y5]].
      inv X2; try easy. apply TyLitZero_C. 
      unfold scope_set_add in *. inv H4. inv H1. inv H5.
      apply TyLitC_C with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. apply SubTyRefl. simpl.
      intros.
      unfold scope_set_add.
      rewrite replicate_gt_eq in H1; try lia.
      assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H4 in H1. clear H4.
      destruct (Z.eq_dec n' 0). subst.
      rewrite replicate_gt_eq in H9; try lia.
      specialize (H16 n) as eq2.
      assert (n <= n < n + n') by lia.
      apply eq2 in H4. clear eq2.
      specialize (H9 0) as eq2.
      assert (l0 <= 0 < l0 + Z.of_nat (length (Zreplicate (h0 - l0 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H5. clear eq2.
      destruct H5 as [na [ta [A1 [A2 A3]]]].
      destruct H4 as [nb [A4 A5]].
      rewrite Z.add_0_r in A2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in A2; try easy. inv A2.
      symmetry in A1.
      destruct (h0 - l0 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in A1.
      apply replicate_nth in A1. subst.
      destruct (Z_ge_dec h0 k).
      specialize (H9 k).
      assert (l0 <= k < l0 + Z.of_nat (length (Zreplicate (Z.pos p1) ta))).
      rewrite replicate_gt_eq; try lia.
      apply H9 in H4. destruct H4 as [nc [tc [B1 [B2 B3]]]].
      exists nc. exists tc.
      split. unfold Zreplicate in *.
      symmetry in B1.
      apply replicate_nth in B1. subst.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_nth_anti; try easy. lia. easy.
      destruct (Z.eq_dec n' k). subst.
      exists 0. exists ta.
      destruct (k - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      unfold Zreplicate. split.
      rewrite replicate_nth_anti; try easy. lia. split. easy.
      constructor.
      specialize (H16 (n+k)).
      assert (n <= n + k < n + n') by lia.
      apply H16 in H4.
      destruct H4 as [nb [Y1 Y2]].
      destruct HRWt with (Hchk0 := Hchk) (Htnt0 := Htnt); try easy.
      apply H4 in Y1 as eq2.
      exists nb. exists ta.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      split. unfold Zreplicate.
      rewrite replicate_nth_anti; try easy. lia. easy.
      inv H10. inv H10. apply simple_type_tnt in H2.
      destruct H2 as [l2 [h2 [A1 A2]]];subst. inv H18. inv H10.
      destruct (Z_ge_dec h2 n').
      apply checked_subtype_well_type
        with (t := (TPtr Checked (TNTArray (Num l2) (Num h2) t0))); try easy.
      inv Y4. inv H8. constructor. constructor; easy. easy.
      apply TyLitC_C with (w := (TNTArray (Num l2) 
           (Num h2) t0)) (b := l2) (ts := Zreplicate (h2 - l2 + 1) t0); try easy.
      constructor. constructor.
      intros.
      unfold scope_set_add.
      inv H5.
      specialize (H9 k H1). easy.
      exists ((TPtr Checked (TNTArray (Num l2) (Num h2) t0))). split. apply type_eq_refl.
      constructor. apply SubTyNtSubsume. constructor. lia. constructor. lia.
      inv H5.
      apply TyLitC_C with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. constructor.
      intros.
      unfold scope_set_add.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_gt_eq in H1; try easy.
      rewrite <- Hp in *. assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H2 in H1. clear H2.
      destruct (Z.eq_dec n' 0). subst. lia.
      specialize (H16 n) as eq2.
      assert (n <= n < n + n') by lia.
      apply eq2 in H2. clear eq2.
      specialize (H9 0) as eq2.
      assert (l2 <= 0 < l2 + Z.of_nat (length (Zreplicate (h2 - l2 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H5. clear eq2.
      destruct H5 as [na [ta [A1 [A2 A3]]]].
      destruct H2 as [nb [A4 A5]].
      rewrite Z.add_0_r in A2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in A2; try easy. inv A2.
      symmetry in A1.
      destruct (h2 - l2 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in A1.
      apply replicate_nth in A1. subst.
      destruct (Z_ge_dec h2 k).
      specialize (H9 k).
      assert (l2 <= k < l2 + Z.of_nat (length (Zreplicate (Z.pos p1) ta))).
      rewrite replicate_gt_eq; try lia.
      apply H9 in H2. destruct H2 as [nc [tc [B1 [B2 B3]]]].
      exists nc. exists tc.
      rewrite Hp.
      split. unfold Zreplicate in *.
      symmetry in B1.
      apply replicate_nth in B1. subst.
      rewrite replicate_nth_anti; try easy. lia. easy.
      destruct (Z.eq_dec n' k). subst.
      exists 0. exists ta.
      unfold Zreplicate.
      destruct (k - l0 + 1) as [| p2 | ?] eqn:Hp2; zify; [lia | |lia].
      rewrite replicate_nth_anti; try easy. lia.
      split. easy. split. easy. apply TyLitZero_C.
      specialize (H16 (n+k)).
      assert (n <= n + k < n + n') by lia.
      apply H16 in H2.
      destruct H2 as [nb [Y1 Y2]].
      destruct HRWt with (Hchk0 := Hchk) (Htnt0 := Htnt); try easy.
      apply H2 in Y1 as eq2.
      exists nb. exists ta.
      split. unfold Zreplicate. rewrite Hp.
      rewrite replicate_nth_anti; try easy. lia. easy.
      apply Stack.add_3 in H4. apply HsHwf with (Hchk := Hchk) (Htnt := Htnt) in H4; try easy.
      easy. unfold rheap_consistent.
      split. intros. inv H1. inv H4. unfold heap_consistent_checked. intros. easy.
      split. constructor. constructor. easy. constructor.
      exists TNat. split. apply type_eq_refl. constructor. constructor. 

      apply TyLitC_C with (w := ((TNTArray (Num l0) (Num n') t0)))
        (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. constructor. simpl. easy. apply SubTyRefl.
       intros.
      unfold scope_set_add.


      apply checked_subtype_well_type with (t := (TPtr Checked (TNTArray (Num l0) (Num h0) t0))); try easy.
      inv Y4; try easy. inv H3. constructor. constructor; try easy.
      unfold eq_subtype. exists (TPtr Checked (TNTArray (Num l0) (Num n') t0)).
      split. apply type_eq_refl.
      constructor. apply SubTyNtSubsume; try easy.

      apply HsubDom; easy.

      destruct R' as [Hchk Htnt]; subst; intuition...
      cbn.
      apply Hswt in H4 as eq1. destruct eq1 as [X1 [X2 X3]].
      inv X1.
      constructor. constructor. constructor.
      constructor. destruct m;try easy.
      constructor. constructor. easy.
      intuition...
      apply TyLitTainted. intros R. inv R. easy.
      apply TyLitTainted. intros R. inv R. easy.
      apply Hswf in Hx. destruct Hx as [v1 [t1 [HSub1 HM]]]. 
      apply Stack.mapsto_always_same with (v1 := (v1, t1)) in H4; try easy.
      inv H4. easy.
  Abort.



          (* **************************************** *)
specialize (gen_arg_env_good tvl env) as [env' HGen].
        exists env', Q. 
        split.
        { exact (sub_domain_grows tvl es env env' s s' AS HGen H11 HsubDom). }
        split.
        
      +
        rewrite H6 in HMap. inv HMap.
      specialize (gen_arg_env_good tvl env) as X1.
      destruct X1 as [enva X1]. rewrite H10 in HGen. inv HGen.
      specialize (sub_domain_grows tvl es env enva s s' AS X1 H13 HSubDom) as X2.
      exists enva. exists Q.
      split. easy.
      split. 
      apply (stack_wf_trans D Q H' env enva s s' AS tvl es); try easy.
      unfold fun_wf in *.
      destruct (HFun env enva x tvl t e m' H6 X1) as [Y1 [Y2 Y3]]. easy.
      destruct (HFun env enva x tvl t e m' H6 X1) as [Y1 [Y2 Y3]]. easy.
      intros.
      specialize (gen_arg_env_has_all tvl env enva X1 x0 t0 H) as eq1. easy.
      unfold theta_wt in *. destruct HQt. easy.
      inv HEwf. easy.
      split.
      apply (stack_heap_consistent_trans tvl es D Q H' env AS s s'); try easy.
      unfold fun_wf in *.
      destruct (HFun env enva x tvl t e m' H6 X1) as [Y1 [Y2 Y3]]. easy.
      unfold stack_wf in *. intros. specialize (HSwf x0 t0 H).
      destruct HSwf as [va [tc [td [Y1 [Y2 Y3]]]]].
      apply Stack.mapsto_always_same with (v1 := (n,ta)) in Y3; try easy. inv Y3.
      exists tc. easy.
      unfold theta_wt in *. destruct HQt. easy.
      destruct (HFun env enva x tvl t e m' H6 X1) as [Y1 [Y2 Y3]]. easy.
      inv HEwf. easy.
      split.
      easy.
      destruct (HFun env enva x tvl t e m' H6 X1) as [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 Y8]]]]]]].
      left. destruct m'. 2: { assert (Unchecked = Unchecked) by easy. apply HMode in H. easy. } 
      specialize (gen_rets_type_exists tvl D Q H' env es AS s t HSubDom H10 HArg) as eq1.
      destruct eq1.
      specialize (gen_rets_as_cast_same tvl D Q H' env es AS s t x0 H10 HSwf H Y6 HArg) as eq1.
      apply theta_grow_type with (Q := Q) in Y8.
      assert (forall x t', In (x,t') tvl -> word_type t' /\ type_wf D t').
      intros. apply Y1 in H1. easy.
      specialize (expr_wf_gen_rets tvl es D fenv s AS e e' Hswt Y7 H14 H1) as eq2.
      specialize (gen_arg_env_same env tvl enva X1 Y3) as eq3.
      specialize (well_typed_gen_rets tvl es D (fenv) s s' H' AS enva
                 Q Checked e t e' x0 eq2 Y8 H14 H eq3) as eq4.
      specialize (call_t_in_env tvl D Q H' env es AS t Y6 H10 HArg) as eq5.
      assert (length tvl = length es) as eq6.
      rewrite (well_typed_args_same_length D Q H' env AS es tvl); try easy.
      specialize (stack_consist_trans s s' env tvl es AS HSubDom Y2 eq6 H13) as eq7.
      inv Y4.
      apply TyCast1 with (t' := x0); try easy.
     assert (forall AS, subst_type AS TNat = TNat).
     {
      intros. induction AS0. simpl. easy.
      simpl. easy.
     }
     rewrite H2. constructor.
     destruct m. simpl. 
     apply TyCast2 with (t' := x0); try easy.
     apply well_type_bound_grow_env with (env := env).
     apply gen_arg_env_grow_1 with (tvl := tvl); try easy.
     inv eq5. easy.
     simpl in eq1.
     apply subtype_left with (t2' := x0).
     apply cast_means_simple_type in eq1. easy.
     apply stack_grow_cast_type_same with (env := env) (S := s); try easy.
     constructor.
      apply TyCast1 with (t' := x0); try easy.
     simpl in *.
     apply well_type_bound_grow_env with (env := env).
     apply gen_arg_env_grow_1 with (tvl := tvl); try easy.
     easy.
    (*T-Strlen*)
    - inv Hreduces.
      destruct E; inversion H1; simpl in *; subst. inv H5. exists env. exists Q.
      split.
      unfold change_strlen_stack.
      unfold sub_domain in *.
      intros. destruct (n' <=? h0).
      apply HSubDom. easy.
      destruct (Nat.eq_dec x0 x). subst.
      exists (n, TPtr m (TNTArray (Num l0) (Num n') t0)).
      apply Stack.add_1. easy.
      apply HSubDom in H.
      destruct H.
      exists x1.
      apply Stack.add_2. lia. easy.
      split.
      unfold stack_wf in *. intros.
      unfold change_strlen_stack. 
      destruct (Nat.eq_dec x0 x). subst.
      unfold stack_wt in *.
      apply Hswt in H8 as eq1. destruct eq1 as [X1 [X2 X3]].
      destruct (n' <=? h0) eqn:eq1. apply Z.leb_le in eq1.
      specialize (HSwf x t2 H). easy.
      apply Z.leb_nle in eq1.
      specialize (HSwf x (TPtr Checked (TNTArray h l t)) Wb).
    destruct HSwf as [va [ta [tb [Y1 [Y2 Y3]]]]].
      apply Stack.mapsto_always_same with (v1 := (va,tb)) in H8; try easy.
      inv H8.
      apply Env.mapsto_always_same with (v1 := t2) in Wb; try easy. subst.
      exists n. exists ta. exists (TPtr m (TNTArray (Num l0) (Num n') t0)).
      assert (subtype D Q (TPtr m (TNTArray (Num l0) (Num n') t0)) (TPtr m (TNTArray (Num l0) (Num h0) t0))).
      apply SubTyNtSubsume.
      constructor. easy. constructor. lia.
      split. apply Henvt in H as eq2. destruct eq2 as [Y5 [Y6 Y7]].
      apply eval_type_bound_not_nat with (env := env) (m := Checked) (tb := ((TNTArray h l t))); try easy.
      split.
      apply subtype_trans with (m := m) (w := (TNTArray (Num l0) (Num h0) t0)); try easy.
      apply Stack.add_1. easy.
      specialize (HSwf x0 t2 H).
      destruct HSwf as [va [ta [tb [X1 [X2 X3]]]]].
      exists va.  exists ta. exists tb.
      split.
      destruct (n' <=? h0) eqn:eq1. apply Z.leb_le in eq1. easy.
      apply Z.leb_nle in eq1.
      apply eval_type_bound_not_nat with (env := env) (m := Checked) (tb := ((TNTArray h l t))); try easy.
      apply Henvt in H as eq2. destruct eq2 as [Y5 [Y6 Y7]]. easy.
      split. easy.
      destruct (n' <=? h0) eqn:eq1. apply Z.leb_le in eq1. easy.
      apply Z.leb_nle in eq1.
      apply Stack.add_2. lia. easy.
      split.
      unfold stack_heap_consistent in *.
      intros.
      unfold change_strlen_stack in H.
      destruct (n' <=? h0) eqn:eq1. apply Z.leb_le in eq1.
      apply HSHwf with (x := x0); try easy.
      apply Z.leb_nle in eq1.
      destruct (Nat.eq_dec x0 x). subst.
      apply Stack.mapsto_add1 in H. inv H.
      apply HSHwf in H8 as eq3. inv eq3. constructor. constructor.
      solve_empty_scope.
      unfold allocate_meta in *. 
      unfold scope_set_add in *. inv H3. inv H2. inv H11.
      apply TyLitC with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. easy. apply SubTyRefl.
      intros.
      unfold scope_set_add.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_gt_eq in H; try easy.
      rewrite <- Hp in *. assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H2 in *. clear H2.
      specialize (H12 n) as eq2.
      assert (n <= n < n + n' + 1) by lia.
      apply eq2 in H2. clear eq2.
      specialize (H13 0) as eq2.
      assert (l0 <= 0 < l0 + Z.of_nat (length (Zreplicate (h0 - l0 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H3. clear eq2.
      destruct H3 as [na [ta [X1 [X2 X3]]]].
      destruct H2 as [nb [X4 X5]].
      rewrite Z.add_0_r in X2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in X2; try easy. inv X2.
      symmetry in X1.
      destruct (h0 - l0 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in X1.
      apply replicate_nth in X1. subst.
      destruct (Z_ge_dec h0 k).
      specialize (H13 k).
      assert (l0 <= k < l0 + Z.of_nat (length (Zreplicate (Z.pos p1) ta))).
      rewrite replicate_gt_eq; try lia.
      apply H13 in H2. destruct H2 as [nc [tc [Y1 [Y2 Y3]]]].
      exists nc. exists tc.
      split. unfold Zreplicate in *.
      symmetry in Y1.
      apply replicate_nth in Y1. subst.
      rewrite Hp.
      rewrite replicate_nth_anti. easy. lia. easy.
      specialize (H12 (n+k)).
      assert (n <= n + k < n + n' + 1) by lia.
      apply H12 in H2.
      destruct H2 as [nb [Y1 Y2]].
      apply HHWt in Y1 as eq2.
      exists nb. exists ta.
      split. unfold Zreplicate. rewrite Hp.
      rewrite replicate_nth_anti. easy. lia. easy.
      inv H10. inv H10. inv H2. inv H17. inv H10.
      destruct (Z_ge_dec h2 n').
      apply subtype_well_type with (t := (TPtr Checked (TNTArray (Num l2) (Num h2) t0))); try easy.
      constructor. constructor. easy.
      constructor. apply Hswt in H8. constructor.
      destruct H8. destruct H2. inv H2. inv H14. easy.
      destruct H8 as [Y1 [Y2 Y3]]. inv Y2. inv H2. easy.
      apply TyLitC with (w := (TNTArray (Num l2) 
             (Num h2) t0)) (b := l2) (ts := Zreplicate (h2 - l2 + 1) t0); try easy.
      constructor. easy.
      constructor. intros.
      unfold scope_set_add.
      inv H11.
      specialize (H13 k H). easy.
      apply SubTyNtSubsume. constructor. lia. constructor. lia.
      inv H11.
      apply TyLitC with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. easy. apply SubTyRefl.
      intros.
      unfold scope_set_add.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_gt_eq in H; try easy.
      rewrite <- Hp in *. assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H2 in *. clear H2.
      specialize (H12 n) as eq2.
      assert (n <= n < n + n' + 1) by lia.
      apply eq2 in H2. clear eq2.
      specialize (H13 0) as eq2.
      assert (l2 <= 0 < l2 + Z.of_nat (length (Zreplicate (h2 - l2 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H10. clear eq2.
      destruct H10 as [na [ta [X1 [X2 X3]]]].
      destruct H2 as [nb [X4 X5]].
      rewrite Z.add_0_r in X2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in X2; try easy. inv X2.
      symmetry in X1.
      destruct (h2 - l2 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in X1.
      apply replicate_nth in X1. subst.
      destruct (Z_ge_dec h2 k).
      specialize (H13 k).
      assert (l2 <= k < l2 + Z.of_nat (length (Zreplicate (Z.pos p1) ta))).
      rewrite replicate_gt_eq; try lia.
      apply H13 in H2. destruct H2 as [nc [tc [Y1 [Y2 Y3]]]].
      exists nc. exists tc.
      rewrite Hp.
      split. unfold Zreplicate in *.
      symmetry in Y1.
      apply replicate_nth in Y1. subst.
      rewrite replicate_nth_anti. easy. lia. easy.
      specialize (H12 (n+k)).
      assert (n <= n + k < n + n' + 1) by lia.
      apply H12 in H2.
      destruct H2 as [nb [Y1 Y2]].
      apply HHWt in Y1 as eq2.
      exists nb. exists ta.
      split. unfold Zreplicate. rewrite Hp.
      rewrite replicate_nth_anti. easy. lia. easy.
      apply Stack.add_3 in H. apply HSHwf in H. easy. lia.
      split. easy.
      left. constructor. constructor.
    (*T-LetStrlen*)
    - inv Hreduces.
      destruct E; inversion H1; simpl in *; subst. inv H5. 
      assert (forall E' e', in_hole e' E' = EStrlen y -> E' = CHole).
      { induction E';intros;simpl in *;eauto.
        1-12:inv H0.
      }
      apply H0 in H3 as eq1. subst. rewrite hole_is_id in *. subst.
      inv H5.
      simpl in *. 
      exists (Env.add y (TPtr Checked (TNTArray l (Num n') ta)) env). exists Q.
      split.
      unfold change_strlen_stack.
      unfold sub_domain in *.
      intros. destruct (n' <=? h0).
      apply HSubDom.
      destruct (Nat.eq_dec x0 y). subst.
      exists (TPtr Checked (TNTArray l h ta)). easy.
      destruct H. apply Env.add_3 in H. exists x1. easy. lia.
      destruct (Nat.eq_dec x0 y). subst.
      exists (n, TPtr m (TNTArray (Num l0) (Num n') t0)).
      apply Stack.add_1. easy.
      destruct H. apply Env.add_3 in H.
      assert (Env.In x0 env). exists x1. easy.
      apply (HSubDom) in H2.
      destruct H2.
      exists x2.
      apply Stack.add_2. lia. easy. lia.
      split.
      unfold stack_wf in *. intros.
      unfold change_strlen_stack. 
      destruct (Nat.eq_dec x0 y). subst.
      unfold stack_wt in *.
      apply Hswt in H10 as eq1. destruct eq1 as [X1 [X2 X3]].
      destruct (n' <=? h0) eqn:eq1. apply Z.leb_le in eq1.
      apply Env.mapsto_add1 in H as eq2. subst.
      specialize (HSwf y (TPtr Checked (TNTArray l h ta)) Wb).
      destruct HSwf as [va [ta' [tb [Y1 [Y2 Y3]]]]].
      inv Y1. inv H5.
      apply Stack.mapsto_always_same with (v1 := (va,tb)) in H10; try easy.
      inv H10. inv Y2.
      exists n. exists (TPtr Checked (TNTArray (Num l0) (Num n') t'0)).
      exists (TPtr Checked (TNTArray (Num l0) (Num h0) t'0)).
      split. constructor. constructor.
      easy. easy. easy. split. apply SubTyNtSubsume. constructor. easy. constructor. easy. easy.
      inv X2. inv H3. inv H10. inv H4.
      exists n. exists (TPtr Checked (TNTArray (Num h1) (Num n') t'0)).
      exists (TPtr Checked (TNTArray (Num l0) (Num h0) t'0)).
      split. constructor. constructor.
      easy. easy. easy. split. apply SubTyNtSubsume. constructor. easy. constructor. easy. easy.
      unfold cast_bound in H11. destruct l. inv H11. destruct (Stack.find (elt:=Z * type) v s).
      destruct p. inv H11. inv H11.
      apply Z.leb_nle in eq1.
      specialize (HSwf y (TPtr Checked (TNTArray l h ta)) Wb).
      destruct HSwf as [va [ta' [tb [Y1 [Y2 Y3]]]]].
      apply Stack.mapsto_always_same with (v1 := (va,tb)) in H10; try easy.
      inv H10.
      apply Env.mapsto_add1 in H as eq2. subst. inv Y2.
      exists n. exists  (TPtr m (TNTArray (Num l0) (Num n') t0)). exists (TPtr m (TNTArray (Num l0) (Num n') t0)).
      assert (subtype D Q (TPtr m (TNTArray (Num l0) (Num n') t0)) (TPtr m (TNTArray (Num l0) (Num n') t0))).
      constructor. split.
      apply eval_type_bound_not_nat with (env := (Env.add y (TPtr Checked (TNTArray l (Num n') ta)) env)) 
       (m := Checked) (tb := (TNTArray l (Num n') ta)); try easy.
      unfold sub_domain. intros. destruct H3.
      destruct (Nat.eq_dec x0 y). subst. 
      exists ((n, TPtr m (TNTArray (Num l0) (Num h0) t0)) ). easy.
      apply Env.add_3 in H3. apply HSubDom. exists x1. easy. lia.
      apply weakening_type_bound with (ta := (TPtr Checked (TNTArray l h ta))); try easy.
      apply Henvt in Wb as eq2. destruct eq2 as [Y5 [Y6 Y7]].
      inv Y7. inv H5. constructor. constructor. easy. constructor. easy.
      inv Y1. inv H4. constructor. constructor; try easy.
      split. constructor. apply Stack.add_1. easy. inv H4.
      inv Y1. inv H3. inv H11. inv Y1. inv H3. inv H11. inv H12.
      inv Y1. inv H4.
      exists n. exists  (TPtr Checked (TNTArray (Num h1) (Num n') t0)).
      exists (TPtr Checked (TNTArray (Num l0) (Num n') t0)).
      split.
      apply eval_type_bound_not_nat with (env := (Env.add y (TPtr Checked (TNTArray (Num l0) (Num n') ta)) env)) 
       (m := Checked) (tb := (TNTArray (Num l0) (Num n') ta)); try easy.
      unfold sub_domain. intros. destruct H2.
      destruct (Nat.eq_dec x0 y). subst. 
      exists ((n, TPtr Checked (TNTArray (Num l0) (Num h0) t0)) ). easy.
      apply Env.add_3 in H2. apply HSubDom. exists x1. easy. lia.
      apply weakening_type_bound with (ta := (TPtr Checked (TNTArray l h ta))); try easy.
      apply Henvt in Wb as eq2. destruct eq2 as [Y5 [Y6 Y7]].
      inv Y7. inv H10. constructor. constructor. easy. constructor. easy.
      apply Env.add_1. easy.
      constructor. constructor; try easy.
      split. constructor. constructor. easy. constructor. easy.
      apply Stack.add_1. easy.
      inv Y1. inv H5.
      destruct l. inv H15. unfold cast_bound in H15.
      destruct (Stack.find (elt:=Z * type) v s). destruct p. inv H15. inv H15.
      apply Env.add_3 in H; try lia. apply HSwf in H as eq1.
      destruct eq1 as [va [ta' [tb [Y5 [Y6 Y7]]]]].
      exists va. exists ta'. exists tb.
      destruct (n' <=? h0) eqn:eq1. apply Z.leb_le in eq1.
      easy.
      apply Z.leb_nle in eq1.
      split. 
      apply eval_type_bound_not_nat with (env := env) 
       (m := Checked) (tb := (TNTArray l h ta)); try easy.
      apply Henvt in H. easy.
      split. easy.
      apply Stack.add_2. lia. easy.
      split.
      unfold stack_heap_consistent in *.
      intros.
      unfold change_strlen_stack in H.
      destruct (n' <=? h0) eqn:eq1. apply Z.leb_le in eq1.
      apply HSHwf with (x := x0); try easy.
      apply Z.leb_nle in eq1.
      destruct (Nat.eq_dec x0 y). subst.
      apply Stack.mapsto_add1 in H. inv H.
      apply HSHwf in H10 as eq3. inv eq3. constructor. constructor.
      solve_empty_scope.
      unfold allocate_meta in *. 
      unfold scope_set_add in *. inv H4. inv H3. inv H12.
      apply TyLitC with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. easy. apply SubTyRefl.
      intros.
      unfold scope_set_add.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_gt_eq in H; try easy.
      rewrite <- Hp in *. assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H3 in *. clear H3.
      specialize (H13 n) as eq2.
      assert (n <= n < n + n' + 1) by lia.
      apply eq2 in H3. clear eq2.
      specialize (H14 0) as eq2.
      assert (l0 <= 0 < l0 + Z.of_nat (length (Zreplicate (h0 - l0 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H4. clear eq2.
      destruct H4 as [na [ta' [X1 [X2 X3]]]].
      destruct H3 as [nb [X4 X5]].
      rewrite Z.add_0_r in X2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in X2; try easy. inv X2.
      symmetry in X1.
      destruct (h0 - l0 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in X1.
      apply replicate_nth in X1. subst.
      destruct (Z_ge_dec h0 k).
      specialize (H14 k).
      assert (l0 <= k < l0 + Z.of_nat (length (Zreplicate (Z.pos p1) ta'))).
      rewrite replicate_gt_eq; try lia.
      apply H14 in H3. destruct H3 as [nc [tc [Y1 [Y2 Y3]]]].
      exists nc. exists tc.
      split. unfold Zreplicate in *.
      symmetry in Y1.
      apply replicate_nth in Y1. subst.
      rewrite Hp.
      rewrite replicate_nth_anti. easy. lia. easy.
      specialize (H13 (n+k)).
      assert (n <= n + k < n + n' + 1) by lia.
      apply H13 in H3.
      destruct H3 as [nb [Y1 Y2]].
      apply HHWt in Y1 as eq2.
      exists nb. exists ta'.
      split. unfold Zreplicate. rewrite Hp.
      rewrite replicate_nth_anti. easy. lia. easy.
      inv H11. inv H11. inv H3. inv H18. inv H11.
      destruct (Z_ge_dec h2 n').
      apply subtype_well_type with (t := (TPtr Checked (TNTArray (Num l2) (Num h2) t0))); try easy.
      constructor. constructor. easy.
      constructor. apply Hswt in H10. constructor.
      destruct H10. destruct H3. inv H3. inv H15. easy.
      destruct H10 as [Y1 [Y2 Y3]]. inv Y2. inv H3. easy.
      apply TyLitC with (w := (TNTArray (Num l2) 
             (Num h2) t0)) (b := l2) (ts := Zreplicate (h2 - l2 + 1) t0); try easy.
      constructor. easy.
      constructor. intros.
      unfold scope_set_add.
      inv H12.
      specialize (H14 k H). easy.
      apply SubTyNtSubsume. constructor. lia. constructor. lia.
      inv H12.
      apply TyLitC with (w := ((TNTArray (Num l0) (Num n') t0)))
       (b := l0) (ts := (Zreplicate (n' - l0 + 1) t0)); eauto.
      constructor. easy. apply SubTyRefl.
      intros.
      unfold scope_set_add.
      destruct (n' - l0 + 1) as [| p | ?] eqn:Hp; zify; [lia | |lia].
      rewrite replicate_gt_eq in H; try easy.
      rewrite <- Hp in *. assert (l0 + (n' - l0 + 1) = n' + 1) by lia.
      rewrite H3 in *. clear H3.
      specialize (H13 n) as eq2.
      assert (n <= n < n + n' + 1) by lia.
      apply eq2 in H3. clear eq2.
      specialize (H14 0) as eq2.
      assert (l2 <= 0 < l2 + Z.of_nat (length (Zreplicate (h2 - l2 + 1) t0))).
      rewrite replicate_gt_eq; try lia.
      apply eq2 in H11. clear eq2.
      destruct H11 as [na [ta' [X1 [X2 X3]]]].
      destruct H3 as [nb [X4 X5]].
      rewrite Z.add_0_r in X2.
      apply Heap.mapsto_always_same with (v1 := (nb,t1)) in X2; try easy. inv X2.
      symmetry in X1.
      destruct (h2 - l2 + 1) as [| p1 | ?] eqn:Hp1; zify; [lia | |lia].
      unfold Zreplicate in X1.
      apply replicate_nth in X1. subst.
      destruct (Z_ge_dec h2 k).
      specialize (H14 k).
      assert (l2 <= k < l2 + Z.of_nat (length (Zreplicate (Z.pos p1) ta'))).
      rewrite replicate_gt_eq; try lia.
      apply H14 in H3. destruct H3 as [nc [tc [Y1 [Y2 Y3]]]].
      exists nc. exists tc.
      rewrite Hp.
      split. unfold Zreplicate in *.
      symmetry in Y1.
      apply replicate_nth in Y1. subst.
      rewrite replicate_nth_anti. easy. lia. easy.
      specialize (H13 (n+k)).
      assert (n <= n + k < n + n' + 1) by lia.
      apply H13 in H3.
      destruct H3 as [nb [Y1 Y2]].
      apply HHWt in Y1 as eq2.
      exists nb. exists ta'.
      split. unfold Zreplicate. rewrite Hp.
      rewrite replicate_nth_anti. easy. lia. easy.
      apply Stack.add_3 in H. apply HSHwf in H. easy. lia.
      split. easy.
      left. apply TyLet with (t2 := TNat); try easy.
      intros R. destruct R. apply Env.add_3 in H.
      assert (Env.In (elt:=type) x env). exists x0. easy. contradiction.
      intros R. subst.
      assert (Env.In (elt:=type) x env). exists (TPtr Checked (TNTArray l h ta)).
      easy. contradiction.
      apply TyLit. constructor.
      apply well_typed_exchange_strlen; try easy.
    (* T-Let *)
  
    - inv Hreduces.
      destruct E; inversion H1; simpl in *; subst.
      + clear H0. clear H9. rename e'0 into e'.
        specialize (stack_grow_prop D F s H s' H' (ELet x e1 e2) e' HSSA H5) as eq1.
        specialize (stack_simple_prop D F s H s' H' (ELet x e1 e2) e' SSimple H5) as eq2.
        inv H5. exists (Env.add x t0 env). inv HEwf.
        assert (Ht : t0 = t1). {
          inv HTy1. reflexivity.
        } rewrite Ht in *. clear Ht.
        split. econstructor.
        inv HSSA.
        destruct H. destruct H0.
        inv H0.
        unfold sub_domain in HSubDom.
        intros R. apply HSubDom in R.
        apply H in R. contradiction.
        split. unfold sub_domain in *.
        intros. 
        destruct (Nat.eq_dec x0 x). subst.
        unfold Stack.In,Stack.Raw.PX.In.
        exists (n, t').
        apply Stack.add_1. reflexivity.
        assert (Stack.In (elt:=Z * type) x0 s -> Stack.In (elt:=Z * type) x0 (Stack.add x (n, t') s)).
        intros. 
        unfold Stack.In,Stack.Raw.PX.In in *.
        destruct H0. exists x1.
        apply Stack.add_2. lia. assumption.
        apply H0. apply HSubDom.
        unfold Env.In,Env.Raw.PX.In in *.
        destruct H.
        apply Env.add_3 in H.
        exists x1. assumption. lia.
        split. apply (new_sub D F).
        assumption. assumption.
        assumption. assumption.
        assumption.
        split. unfold heap_consistent. eauto.
        left. apply (stack_grow_well_typed D F s).
        assumption.
        assumption.
      + clear H1.
        assert (~ Stack.In x s) as eqa.
        inv HSSA. destruct H0. destruct H1.
        inv H1.
        intros R. apply H0 in R. contradiction.
        apply ty_ssa_stack_small_let in HSSA.
        specialize (ty_ssa_stack_in_hole s e E HSSA) as eq3.
        specialize (stack_grow_prop D F s H s' H' e e'0 eq3 H5) as eq1.
        edestruct IH1...
        inv HEwf;eauto.
        exists x0. destruct H0 as [He [Hdom [Hs' [Hh Hwt]]]]. split. eauto. split.
        eauto. split. eauto. split. eauto.
        destruct Hwt.
        left. econstructor. apply H0.
        inv He. apply (stack_grow_well_typed D F s).
        assumption. 
        apply (heapWF D F s H).
        assumption. assumption.
        destruct (Nat.eq_dec x  x1).
        subst.
        eapply equiv_env_wt.
        assert (Env.Equal (Env.add x1 t1 (Env.add x1 t0 env)) (Env.add x1 t1 env)).
        apply env_shadow. apply env_sym in H2.
        apply H2.
        apply (stack_grow_well_typed D F s s') in HTy2.
        apply (heapWF D F s' H). assumption.
        assumption. assumption.
        apply (equiv_env_wt D F s' H' 
                 (Env.add x1 t0 (Env.add x t1 env)) (Env.add x t1 (Env.add x1 t0 env))).
        apply env_neq_commute_eq.
        unfold Env.E.eq. lia. easy.
        apply well_typed_grow.
        intros R. 
        unfold Env.In,Env.Raw.PX.In in *.
        destruct R.
        apply Env.add_3 in H2.
        destruct H1.
        exists x0. assumption. assumption.
        apply (stack_grow_well_typed D F s s') in HTy2.
        apply (heapWF D F s' H). assumption.
        assumption. assumption.
        destruct H0.
        destruct H0.
        destruct H0. destruct H1.
        assert (@well_typed D F s' H' (Env.add x t1 env) Checked e2 t).
        apply (stack_grow_well_typed D F s s') in HTy2.
        apply (heapWF D F s' H). assumption. assumption. assumption.
        specialize (@well_typed_subtype D F s' H' env
                      Checked e2 t x t1 x1 x2 H3 H0 H1) as eqb.
        destruct eqb. left. econstructor.
        apply H2. inv He. 
        apply well_typed_grow.
        destruct (Nat.eq_dec x  x3).
        subst.
        eapply equiv_env_wt.
        assert (Env.Equal (Env.add x3 x2 (Env.add x3 t0 env)) (Env.add x3 x2 env)).
        apply env_shadow. apply env_sym in H7.
        apply H7. assumption.
        apply (equiv_env_wt D s' H' 
                 (Env.add x3 t0 (Env.add x x2 env)) (Env.add x x2 (Env.add x3 t0 env))).
        apply env_neq_commute_eq.
        unfold Env.E.eq. lia. easy.
        apply well_typed_grow.
        intros R. 
        unfold Env.In,Env.Raw.PX.In in *.
        destruct R.
        apply Env.add_3 in H7.
        destruct H6.
        exists x0. assumption. assumption. assumption.
        destruct H4.
        destruct H4.
        destruct H4.
        destruct H6.
        right. exists x3. exists x4.
        split. eauto. split. eauto.
        econstructor. apply H2.
        inv He. assumption.
        destruct (Nat.eq_dec x  x5).
        subst.
        eapply equiv_env_wt.
        assert (Env.Equal (Env.add x5 x2 (Env.add x5 t0 env)) (Env.add x5 x2 env)).
        apply env_shadow. apply env_sym in H10.
        apply H10. assumption.
        apply (equiv_env_wt D s' H' 
                 (Env.add x5 t0 (Env.add x x2 env)) (Env.add x x2 (Env.add x5 t0 env))).
        apply env_neq_commute_eq.
        unfold Env.E.eq. lia. easy.
        apply well_typed_grow.
        intros R. 
        unfold Env.In,Env.Raw.PX.In in *.
        destruct R.
        apply Env.add_3 in H10.
        destruct H8.
        exists x0. assumption. assumption. assumption.
    (* T-FieldAddr *)
    - inv Hreduces.
      destruct E; inversion H2; simpl in *; subst. exists env. 
      + clear H0. clear H10. inv H6.
        * inv HTy.
          (* Gotta prove some equalities *)
          assert (fs = fs0).
          { apply StructDef.find_1 in HWf1.
            match goal with
            | [ H : StructDef.MapsTo _ _ _ |- _ ] =>
              apply StructDef.find_1 in H; rewrite HWf1 in H; inv H
            end; auto.
          } 
          subst.
          assert (fields_wf D fs0) by eauto.
  
          (* assert (i = i0).
          { edestruct H; eauto. destruct H0. eapply H0. apply HWf2. apply H9. } *)
          subst.
          assert (ti = ti0).
          { apply Fields.find_1 in HWf2.
            apply Fields.find_1 in H9.
            rewrite HWf2 in H9.
            inv H9.
            reflexivity. }
          subst.
          rename fs0 into fs.
          clear i.
          rename i0 into i. 
          rename ti0 into ti. 
  
          (* The fact that n^(ptr C struct T) is well-typed is all we need *)
          split; eauto.
          inv HHwf.
          constructor. eapply preservation_fieldaddr; eauto. omega.
        * inv HTy.
          (* Gotta prove some equalities *)
          assert (fs = fs0).
          { apply StructDef.find_1 in HWf1.
            apply StructDef.find_1 in H7.
            rewrite HWf1 in H7.
            inv H7.
            reflexivity. }
          subst. 
          assert (fields_wf D fs0) by eauto.
          assert (ti = ti0).
          { eauto using FieldFacts.MapsTo_fun. }
          clear i.
          rename fs0 into fs.
          rename i0 into i.
          subst; rename ti0 into ti.
          (* Since it is an unchecked pointer, well-typedness is easy *)
          idtac...
      + clear H2. rename e0 into e1_redex. rename e'0 into e1_redex'.
        edestruct IH; eauto.
        inv HHwf; eauto.
    (* T-Plus *)
    - inv Hreduces.
      destruct E; inversion H1; simpl in *; subst.
      + clear H0. clear H7. rename e'0 into e'. inv H4.
        * inversion HTy1.
        * inv HTy1...
      + clear H1. rename e into e1_redex. rename e'0 into e1_redex'. edestruct IH1; idtac...
        inv HHwf; eauto.
      + clear H1. rename e into e2_redex. rename e'0 into e2_redex'. edestruct IH2; idtac...
        inv HHwf; eauto.
    (* T-Malloc *)
    - inv Hreduces.
      destruct E; inversion H2; simpl in *; subst.
      clear H0. clear H8.
      inv H5.
      split; eapply alloc_correct; eauto.
    (* T-Unchecked *)
    - inv Hreduces.
      destruct E; inversion H1; simpl in *; subst.
      + clear H0. clear H7. inv H4. inv HTy...
      + inversion H7; inversion H0.
    (* T-Cast *)
    - inv Hreduces.
      destruct E; inversion H1; simpl in *; subst.
      + clear H0. clear H7. inv H4. inv HTy.
        inv HHwf.
        inv H1.
        * idtac...
        * destruct m.
          { specialize (HChkPtr eq_refl w). exfalso. apply HChkPtr. reflexivity. }
          { idtac... }
      + clear H1. rename e0 into e1_redex. rename e'0 into e1_redex'. edestruct IH; idtac...
        inv HHwf; eauto.
    (* T-Deref *) 
    - destruct m'; try (specialize (HMode eq_refl); inversion HMode).
      clear HMode.
      inv HHwf.
      specialize (IH H1 eq_refl).
      inv Hreduces.
      destruct E eqn:He; inversion H2; simpl in *; try congruence.
      + 
        subst.
        clear IH.
        inv H5.
        split; eauto.
        destruct HPtrType as [[Hw Eq] | Hw]; subst.
        *   inv HSubType.  
           ** { inv HTy.
              remember H7 as Backup; clear HeqBackup.
              inv H7.
             - exfalso.
              eapply heap_wf_maps_nonzero; eauto.
             - inv H2.
              
             - inv Hw; simpl in*; subst; simpl in *.
              + inv H0; simpl in *.
                destruct (H5 0) as [N [T' [HT' [HM' HWT']]]]; [inv H2; simpl; omega | ].
               
                inv HT'.
                rewrite Z.add_0_r in HM'.
                assert (Hyp: (N, TNat) = (n1, t1)). {
                eapply HeapFacts.MapsTo_fun. inv H2. inv H0.
                exact HM'. exact H9. }
                inv Hyp; subst; eauto.
              + inv H0; simpl in *.
                destruct (H5 0) as [N [T' [HT' [HM' HWT']]]]; [inv H2; simpl; omega | ].
                inv HT'.
                rewrite Z.add_0_r in HM'.
                assert (Hyp: (N, TPtr m w) = (n1, t1)). {
                  eapply HeapFacts.MapsTo_fun. inv H2.
                  inv H0. exact HM'. exact H9. }
                inv Hyp; subst; eauto.
                apply TyLit.
  
                assert (Hyp: set_remove_all (n, TPtr Checked (TPtr m w))
                                       ((n,TPtr Checked (TPtr m w))::nil) = empty_scope).
                { 
                  destruct (eq_dec_nt (n, TPtr Checked (TPtr m w)) (n, TPtr Checked (TPtr m w))) eqn:EQ; try congruence.
                  unfold set_remove_all.
                  rewrite EQ.
                  auto.
                }
  
                rewrite <- Hyp.
                apply scope_strengthening. inv H2. inv H0.
                exact HWT'. exact HEwf. exact Backup.
              }
             ** { inv HTy.
                remember H10 as Backup; clear HeqBackup.
                inv H10.
                - exfalso.
                  eapply heap_wf_maps_nonzero; eauto.
                - inv H2.
              
                - inv Hw; simpl in*; subst; simpl in *.
              
                }
            ** { inv HTy.
                 remember H12 as Backup; clear HeqBackup.
                 inv H12.
                 - exfalso.
                   eapply heap_wf_maps_nonzero; eauto.
                 - inv H2.
              
                 - inv Hw; simpl in*; subst; simpl in *.
                   + inv H0; simpl in *.
                     destruct (H10 0) as [N [T' [HT' [HM' HWT']]]]; [inv H2; simpl; eauto | ].
                     destruct (StructDef.find (elt:=fields) T D) eqn:H.
                     inv H0. rewrite map_length. 
                     assert (StructDef.MapsTo T f D) by (eapply find_implies_mapsto; eauto).
                     assert (f = fs) by (eapply StructDefFacts.MapsTo_fun; eauto). rewrite <- H2 in *.
                     assert (((length (Fields.elements (elt:=type) f)) > 0)%nat) by (eapply fields_implies_length; eauto).
                     omega. inv H. inv H0.
                     inv HT'.
                     rewrite Z.add_0_r in HM'.
                     assert (Hb : b = 0). 
                     {
                       destruct (StructDef.find (elt:=fields) T D);
                        inv H2. reflexivity.
                     } rewrite Hb in *.
                     simpl in H0. 
                     assert (Hts : StructDef.find (elt:=fields) T D = Some fs) by (eapply StructDef.find_1; eauto).
                     rewrite Hts in H2. inv H2.
                     assert (Some TNat = match map snd (Fields.elements (elt := type) fs)
                      with 
                      | nil => None
                      | x:: _ => Some x
                            end) by (eapply element_implies_element; eauto).
                      rewrite <- H in H0. inv H0. 
                      assert (Hyp: (N, TNat) = (n1, t1)). {
                      eapply HeapFacts.MapsTo_fun.
                      exact HM'. exact H9. }
                      inv Hyp; subst; eauto.
                  }
        *   assert (exists t1, w = (TPtr Checked t1)) by (inv HSubType; eauto).
            destruct H. rewrite H in *. clear H.
          { inv HTy.
            clear H8.
            clear H0.
            clear H1.
            remember H7 as Backup; clear HeqBackup.
            inv H7.
            - exfalso. 
              eapply heap_wf_maps_nonzero; eauto.
            - inversion H0.
            - destruct Hw as [? [? ?]]; subst.
              inv H0; simpl in *.
              inv HSubType.
              -- unfold allocate_meta in H4.
                 destruct (H11 l h t). reflexivity.
                 assert (Hpos : exists p, (h - l) = Z.pos p).
                  {
                     destruct h; destruct l; inv H.
                     + exists p. simpl; reflexivity.
                     + exfalso. eapply H0. simpl. reflexivity.
                     + assert (Z.pos p - Z.neg p0 > 0) by (zify; omega).
                       assert (exists p2, Z.pos p - Z.neg p0 = Z.pos p2).
                       {
                        destruct (Z.pos p - Z.neg p0); inv H. exists p1. reflexivity.
                       } destruct H5. exists x. assumption.
                  }
                  destruct Hpos. rewrite H5 in *. simpl in H4. 
                  inv H4; simpl in *. 
                  assert (exists p, h = Z.pos p).
                  {
                    destruct h; inv H. exists p; reflexivity.
                  }
                  destruct H4. destruct l.
                  * assert (Hpos : exists n, Pos.to_nat x = S n) by apply pos_succ.
                    destruct Hpos.
                    destruct (H3 0) as [N [T' [HT' [HM' HWT']]]]; [ simpl; rewrite H7; simpl; zify; omega  | ].
                    rewrite H7 in HT'.  simpl in HT'. inv HT'.  rewrite Z.add_0_r in HM'.
                    maps_to_fun.
                    constructor.
                    assert (Hyp: set_remove_all (n, TPtr Checked (TArray 0 (Z.pos x0) t))
                                          ((n,TPtr Checked (TArray 0 (Z.pos x0) t))::nil) = empty_scope).
                      { 
                        destruct (eq_dec_nt (n, TPtr Checked (TArray 0 (Z.pos x0) t))
                                      (n, TPtr Checked (TArray 0 (Z.pos x0) t))) eqn:EQ; try congruence.
                        unfold set_remove_all.
                        rewrite EQ.
                        auto.
                      }
                    rewrite <- Hyp.
                    apply scope_strengthening; eauto.
                  * exfalso; eapply H0; eauto.
                  * assert (Hpos : exists n, Pos.to_nat x = S n) by apply pos_succ.
                    destruct Hpos. rewrite H4 in *.  clear H4 H0 H.
                    destruct (H3 0) as [N [T' [HT' [HM' HWT']]]]; [ rewrite H7; rewrite replicate_length; zify; omega | ].
                    rewrite H7 in HT'.
                    rewrite Z.add_0_r in HM'.
                    symmetry in HT'.
                     assert (t = T').
                     { 
                       eapply replicate_nth; eauto.
                     } 
                     subst T'.
                    maps_to_fun.
                     econstructor.
                     assert (Hyp: set_remove_all (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))
                                          ((n,TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))::nil) = empty_scope).
                          { 
                            destruct (eq_dec_nt (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))
                                          (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))) eqn:EQ; try congruence.
                            unfold set_remove_all.
                            rewrite EQ.
                            auto.
                          }
  
                        rewrite <- Hyp.
                        apply scope_strengthening; eauto.
              -- unfold allocate_meta in H4.
                 destruct (H11 l0 h0 t). reflexivity.
                 clear H0.
                 assert (Hpos : exists p, (h0 - l0) = Z.pos p).
                  {
                     destruct h0; destruct l0; inv H.
                     + exists p. simpl; reflexivity.
                     + exfalso. eapply H5. simpl. reflexivity.
                     + assert (Z.pos p - Z.neg p0 > 0) by (zify; omega).
                       assert (exists p2, Z.pos p - Z.neg p0 = Z.pos p2).
                       {
                        destruct (Z.pos p - Z.neg p0); inv H. exists p1. reflexivity.
                       } destruct H0. exists x. assumption.
                  }
                  destruct Hpos. rewrite H0 in *. simpl in H4. 
                  inv H4; simpl in *. 
                  assert (exists p, h0 = Z.pos p).
                  {
                    destruct h0; inv H. exists p; reflexivity.
                  }
                  destruct H4. destruct l0.
                  * assert (Hpos : exists n, Pos.to_nat x = S n) by apply pos_succ.
                    destruct Hpos.
                    destruct (H3 0) as [N [T' [HT' [HM' HWT']]]]; [ simpl; rewrite H7; simpl; zify; omega  | ].
                    rewrite H7 in HT'.  simpl in HT'. inv HT'.  rewrite Z.add_0_r in HM'.
                    maps_to_fun.
                    constructor.
                    assert (Hyp: set_remove_all (n, TPtr Checked (TArray 0 (Z.pos x0) t))
                                          ((n,TPtr Checked (TArray 0 (Z.pos x0) t))::nil) = empty_scope).
                      { 
                        destruct (eq_dec_nt (n, TPtr Checked (TArray 0 (Z.pos x0) t))
                                      (n, TPtr Checked (TArray 0 (Z.pos x0) t))) eqn:EQ; try congruence.
                        unfold set_remove_all.
                        rewrite EQ.
                        auto.
                      }
                    rewrite <- Hyp.
                    apply scope_strengthening; eauto.
                  * exfalso; eapply H5; eauto.
                  * assert (Hpos : exists n, Pos.to_nat x = S n) by apply pos_succ.
                    destruct Hpos. rewrite H4 in *.
                    destruct (H3 0) as [N [T' [HT' [HM' HWT']]]]; [ rewrite H7; rewrite replicate_length; zify; omega | ].
                    rewrite H7 in HT'.
                    rewrite Z.add_0_r in HM'.
                    symmetry in HT'.
                     assert (t = T').
                     { 
                       eapply replicate_nth; eauto.
                     } 
                     subst T'.
                    maps_to_fun.
                     econstructor.
                     assert (Hyp: set_remove_all (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))
                                          ((n,TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))::nil) = empty_scope).
                          { 
                            destruct (eq_dec_nt (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))
                                          (n, TPtr Checked (TArray (Z.neg p) (Z.pos x0) t))) eqn:EQ; try congruence.
                            unfold set_remove_all.
                            rewrite EQ.
                            auto.
                          }
  
                        rewrite <- Hyp.
                        apply scope_strengthening; eauto.
            }
  
      + subst.
        destruct (IH (in_hole e'0 c) H') as [HC HWT]; eauto. 
    - inv HHwf.
  
      assert (exists l0 h0, t = (TPtr m' (TArray l0 h0 t'))).
      {
        inv HSubType. exists l. exists h. reflexivity.
        exists l0. exists h0. reflexivity. 
      }
  
      destruct H0 as [l0 [h0 Hb]].
      rewrite Hb in *. clear Hb HSubType.
      (* TODO: Move outside, cleanup *)
      Ltac invert_expr_wf e :=
        match goal with
        | [ H : expr_wf _ e |- _ ] => inv H
        end.
  
      invert_expr_wf (EPlus e1 e2).
      inv Hreduces.
  
      Ltac invert_ctx_and_hole :=
        match goal with
        | [H : in_hole _ ?C = _ |- _] => destruct C; inversion H; simpl in *; subst; clear H
        end.
  
      invert_ctx_and_hole.
  
      + inv H6. (*TODO: auto *)
      + invert_ctx_and_hole.
        * { (* Plus step *)
            match goal with
            | [ H : step _ _ _ _ _ |- _ ] => inv H
            end; split; eauto...
            - inv HTy1.
              eapply TyDeref; eauto.
              constructor.
  
              Ltac cleanup :=
                repeat (match goal with
                        | [H : ?X =  ?X |- _ ] => clear H
                        | [H : ?X -> ?X |- _ ] => clear H
                        end).
              cleanup.
              
              match goal with
              | [ H : well_typed_lit _ _ _ _ _ |- _ ] =>
                remember H as Backup; clear HeqBackup; inv H; eauto; try omega
              end.
  
              unfold allocate_meta in *.
  
              inversion H0; subst b; subst ts; clear H0.
              
              eapply TyLitC; unfold allocate_meta in *; eauto.
  
              intros k Hk.
              
              assert (Hyp: h0 - n2 - (l0 - n2) = h0 - l0) by omega.
              rewrite Hyp in * ; clear Hyp.
              
              destruct (H6 (n2 + k)) as [n' [t'' [HNth [HMap HWT]]]]; [inv H0; omega | ].
  
              exists n'. exists t''.
  
              rewrite Z.add_assoc in HMap.
              inv H0.
              split; [ | split]; auto.
              + destruct (h0 - l0) eqn:HHL; simpl in *.
                * rewrite Z.add_0_r in Hk.
                  destruct (Z.to_nat (n2 + k - l0)); inv HNth.
                * assert (HR: k - (l0 - n2) = n2 + k - l0) by (zify; omega).
                  rewrite HR.
                  auto.
                * destruct (Z.to_nat (n2 + k - l0)); inv HNth.
              + apply scope_weakening_cons.
  
                eapply scope_strengthening in HWT; eauto.
                assert (HAdd : set_add eq_dec_nt (n1, TPtr Checked (TArray l0 h0 t'))
                                       empty_scope =
                               (n1, TPtr Checked (TArray l0 h0 t')) :: nil) by auto.
                rewrite HAdd in HWT.
                clear HAdd.
  
                assert (HEmpty : empty_scope =
                                 set_remove_all (n1, TPtr Checked (TArray l0 h0 t')) 
                                               ((n1, TPtr Checked (TArray l0 h0 t')) :: nil)).
                {
                  unfold set_remove_all.
                  destruct (eq_dec_nt (n1, TPtr Checked (TArray l0 h0 t'))
                                      (n1, TPtr Checked (TArray l0 h0 t'))); auto.
                  congruence.
                }
                rewrite <- HEmpty in HWT.
                auto.
              + eapply SubTyRefl.
            - inv HTy1.
              destruct m'.
              + exfalso; eapply H10; eauto.
              + specialize (HMode eq_refl). inv HMode.
          }
        * clear l h t. 
          specialize (IH1 H3 eq_refl).
          specialize (IH1 (in_hole e'0 E) H').
          destruct IH1 as [HC HWT]; eauto.
          split; eauto. eapply TyIndex; eauto.
          eapply SubTyRefl. eauto...
        * specialize (IH2 H4 eq_refl (in_hole e'0 E) H').
          destruct IH2 as [HC HWT]; eauto.
          split; eauto. eapply TyIndex; eauto...
          eapply SubTyRefl.
    (* T-Assign *)
    - inv Hreduces.
      inv HHwf.
      destruct E; inversion H4; simpl in *; subst.
      + clear H10 H3.
        inv H7.
        inv Hwt2.
        inv Hwt1.
        destruct H1 as [[HW Eq] | Eq]; subst.
        * {
            destruct m'; [| specialize (H2 eq_refl); inv H2].
            inv H0.
            **
              eapply well_typed_heap_in in H11; eauto.
              destruct H11 as [N HMap].
              split.
              - apply HeapUpd with (n := N); eauto...
                eapply PtrUpd; eauto.
              - constructor.
                eapply PtrUpd; eauto. 
            **
              eapply well_typed_heap_in in H11; eauto.
              destruct H11 as [N HMap].
              split.
              - apply HeapUpd with (n := N); eauto...
                eapply PtrUpd; eauto.
              - constructor.
                eapply PtrUpd; eauto. 
              - eapply subtype_well_type;
                eauto. eapply SubTySubsume; eauto.
            **
              eapply well_typed_heap_in in H11. eauto.
              destruct H11 as [N HMap].
              split; eauto.
              - apply HeapUpd with (n := N); eauto...
              - eauto.
              - eauto.
              - eapply subtype_well_type;
                eauto. eapply SubTyStructArrayField; eauto.
          } 
        * destruct Eq as [? [? ?]]; subst.
          inv H0. 
          ** 
            { destruct m'; [| specialize (H2 eq_refl); inv H2].
              eapply (well_typed_heap_in_array n D H l h) in H11; eauto.
              destruct H11 as [N HMap].
              split.
              - apply HeapUpd with (n := N); eauto...
                eapply PtrUpd; eauto.
              - constructor.
                eapply PtrUpd; eauto.
              - eapply (H13 l h). eauto.
              - eapply H13. eauto.
            }
          ** 
            { clear H7. clear l h.
              destruct m'; [| specialize (H2 eq_refl); inv H2].
              eapply (well_typed_heap_in_array n D H l0 h0) in H11; eauto.
              destruct H11 as [N HMap].
              split.
              - apply HeapUpd with (n := N); eauto...
                eapply PtrUpd; eauto.
              - constructor.
                eapply PtrUpd; eauto.
              - eapply (H13 l0 h0). eauto.
              - eapply H13. eauto.
            }
      + destruct (IHHwt1 H6 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
        split; eauto...
      + destruct (IHHwt2 H8 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
        split; eauto... 
    - inv Hreduces.
      inv HHwf.
      inv H7.
      destruct E; inv H5; subst; simpl in*; subst; eauto.
      + inv H8.
      + assert (exists l0 h0, t = (TPtr m' (TArray l0 h0 t'))).
        {
          inv H2. exists l. exists h. reflexivity.
          exists l0. exists h0. reflexivity. 
        }
        destruct H4 as [l0 [h0 H4]].
        rewrite H4 in *. clear H4 H2.
        destruct E; inversion H6; simpl in *; subst.
        * { (* Plus step *)
            inv H8; split; eauto...
            - inv Hwt1.
              eapply TyAssign; eauto.
              constructor.
              cleanup.
              
              match goal with
              | [ H : well_typed_lit _ _ _ _ _ |- _ ] =>
                remember H as Backup; clear HeqBackup; inv H; eauto; try omega
              end.
  
              unfold allocate_meta in *.
  
              inversion H2; subst b; subst ts; clear H0.
              
              eapply TyLitC; unfold allocate_meta in *; eauto.
  
              intros k Hk.
              
              assert (Hyp: h0 - n2 - (l0 - n2) = h0 - l0) by omega.
              rewrite Hyp in * ; clear Hyp.
              inv H2.
              destruct (H5 (n2 + k)) as [n' [t0 [HNth [HMap HWT]]]]; [omega | ].
  
              exists n'. exists t0.
  
              rewrite Z.add_assoc in HMap.
  
              split; [ | split]; eauto.
              + destruct (h0 - l0) eqn:HHL; simpl in *.
                * rewrite Z.add_0_r in Hk.
                  destruct (Z.to_nat (n2 + k - l0)); inv HNth.
                * assert (HR: k - (l0 - n2) = n2 + k - l0) by (zify; omega).
                  rewrite HR.
                  auto.
                * destruct (Z.to_nat (n2 + k - l0)); inv HNth.
              + apply scope_weakening_cons.
  
                eapply scope_strengthening in HWT; eauto.
                assert (HAdd : set_add eq_dec_nt (n1, TPtr Checked (TArray l0 h0 t'))
                                       empty_scope =
                               (n1, TPtr Checked (TArray l0 h0 t')) :: nil) by auto.
                rewrite HAdd in HWT.
                clear HAdd.
  
                assert (HEmpty : empty_scope =
                                 set_remove_all (n1, TPtr Checked (TArray l0 h0 t')) 
                                               ((n1, TPtr Checked (TArray l0 h0 t')) :: nil)).
                {
                  unfold set_remove_all.
                  destruct (eq_dec_nt (n1, TPtr Checked (TArray l0 h0 t'))
                                      (n1, TPtr Checked (TArray l0 h0 t'))); auto.
                  congruence.
                }
                rewrite <- HEmpty in HWT.
                auto.
              + eapply SubTyRefl; eauto.
            - inv Hwt1.
              destruct m'.
              + exfalso; eapply H14; eauto.
              + specialize (H3 eq_refl). exfalso; inv H3.
                
           }
        * destruct (IHHwt1 H10 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
          split. eauto. eapply TyIndexAssign; eauto.
          eapply SubTyRefl. eauto... eauto... 
        * destruct (IHHwt2 H12 eq_refl (in_hole e'0 E) H') as [HC HWT]; eauto.
          split; eauto. eapply TyIndexAssign; eauto... eapply SubTyRefl.
  Qed.


Section Noncrash. 
  Variable D : structdef.
  Variable F : FEnv.
  Hypothesis HDwf : structdef_wf D.

Definition normal (M : mem) (e : expression) : Prop :=
  ~ exists m' M' r, @reduce D F M e m' M' r.

Definition stuck (M : mem) (r : result) : Prop :=
  match r with
  | RBounds => False
  | RNull => False
  | RExpr e => @normal M e /\ ~ value D e
  end.

Inductive eval: mem -> expression -> mode -> mem -> result -> Prop :=
  | eval_refl   : forall M e m, eval M e m M (RExpr e)
  | eval_transC : forall m M M' M'' e e' r,
      eval M e m M' (RExpr e') ->
      @reduce D F M' e' Checked M'' r ->
      eval M e Checked M'' r
  | eval_transU : forall m M M' M'' e e' r,
      eval M e m M' (RExpr e') ->
      @reduce D F M' e' Unchecked M'' r ->
      eval M e Unchecked M'' r.

Theorem noncrash : forall S Q R e t m S' R' r,
    rheap_wf R ->
    @rheap_wt_all D F Q R ->
    @fun_wf D F R ->
    stack_wt D m S ->
    @expr_wf D e ->
    @well_typed D F R empty_env empty_theta Checked e t ->
    @eval (S,R) e m (S',R') r ->
    ~ @stuck (S',R') r.
Proof.
Admitted.

End Noncrash.

  
