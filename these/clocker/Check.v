Require Import Checker.
Require Import String.
Require Import List.


(** * Substitutions  **)

(** auxiliary function that checks if x is in list l **)
Fixpoint mem_S (x:string) (l : list identifier) :=
 match l with
  | nil => false
  | cons y l => if eq_identifier x y then true else mem_S x l
 end.

(** Useful lemmas **)
Lemma in_is_mem : forall x S, In x S <-> mem_S x S = true.
Proof.
  intros.
  split; intros.
  - induction S.
  + simpl. simpl in H. auto.
  + simpl in H. destruct H.
    -- simpl.
    destruct eq_identifier eqn : Hi.
    ++ auto.
    ++ auto.
    -- simpl.
      destruct eq_identifier eqn : Hi.
      ++ auto.
      ++ auto.
  - induction S.
    + simpl in H.
      inversion H.
    + simpl.
      simpl in H.
      destruct eq_identifier eqn : Hi.
      -- left. auto.
      -- right.
         apply IHS.
         auto.
Qed.


Lemma notin_is_memf : forall x S, ~ In x S <-> mem_S x S = false.
Proof.
  intros.
  split; intros.
  - induction S.
    + simpl. auto.
    + simpl in H.
    simpl.
    destruct eq_identifier eqn: Hi.
    -- elim H.
      left.
      auto.
    -- auto.
  - intro.
    apply in_is_mem in H0.
    rewrite H in H0.
    inversion H0.
Qed.

(** ** Substitution functions **)
(** Subst functions for expressions (None means error) **)

Definition e_subst_fun_var (x:identifier) (y:identifier) S :=
  if mem_S x S then Some (cons (x,y) nil)
  else Some nil.

Definition e_subst_fun_exp (x:identifier) e S :=
  match e with
  | Esone_exp (Evar y) => e_subst_fun_var x y S
  | Esone_exp _ => if negb (mem_S x S) then Some nil else None
  | _ => None
  end.

Fixpoint e_subst_fun (p:xs) (e:es) S :=
  match p,e with
  | Patp_nil , Esone_exp (Eunit ck) => Some nil
  | Patp_var x , Esone_exp (Evar y) =>
    if mem_S x S then Some (cons (x,y) nil) else Some nil
  | Patp_var x ,  Esone_exp _ => if negb (mem_S x S) then Some nil else None
  | Patp_tuple x p' , Escons_exps e es' =>
    let s1 := e_subst_fun_exp (x) (Esone_exp e) S in
    let s2 := e_subst_fun p' es' S in
    match s1,s2 with
    | Some l , Some l' => Some (l ++ l')
    | _, _ => None
    end
  | _, _ => None
  end.

(** Subst function for variables list (None means error) **)

Definition p_subst_fun_vars (x:identifier) (y:identifier) S :=
  if mem_S x S then Some (cons (x,y) nil)
  else Some nil.

Fixpoint p_subst_fun p p' S :=
  match p,p' with
    | Patp_nil , Patp_nil => Some nil
  | Patp_var x ,  Patp_var y =>
    if mem_S x S then Some (cons (x,y) nil)
    else Some nil
  | Patp_tuple x p1' , Patp_tuple y p2' =>
    let s1 := p_subst_fun_vars x y S in
    let s2 := p_subst_fun p1' p2' S in
    match s1,s2 with
    | Some l , Some l' => Some (l ++ l')
    | _, _ => None
    end
  | _, _ => None
  end.


(** ** Equivalence of substitutions **)

Lemma eq1 : forall x e S, e_subst_fun_exp x (Esone_exp e) S = e_subst_fun (Patp_var x) (Esone_exp e) S.
  Proof.
    intros.
    unfold e_subst_fun.
    unfold e_subst_fun_exp.
    reflexivity.
  Qed.



(** *** For expressions **)

(* p ~S~ e ▷ s ==> e_subst_fun p e S = Some s *)
Theorem Sub_clk_subst_exp_e_subst_fun : forall p e S sigma, Sub_clk_subst_exp p e S sigma -> e_subst_fun p e S = Some sigma.
Proof.
  intros.
  induction H; auto.
  - simpl.
    apply in_is_mem in H.
    rewrite H.
    auto.
  - simpl.
    destruct (mem_S x S5) eqn : Hm.
    apply notin_is_memf in H.
    rewrite H in Hm.
    inversion Hm.
    simpl.
    destruct e5; auto.
  - simpl.
    rewrite IHSub_clk_subst_exp2.
    rewrite <- eq1 in IHSub_clk_subst_exp1.
    simpl in IHSub_clk_subst_exp1.
    rewrite IHSub_clk_subst_exp1.
    auto.
Qed.



(* e_subst_fun p e S = Some s ==> p ~S~ e ▷ s *)
Theorem e_subst_fun_Sub_clk_subst_exp : forall p e S sigma, e_subst_fun p e S = Some sigma -> Sub_clk_subst_exp p e S sigma.
Proof.
  induction p; intros; simpl.
  - simpl in *.
    destruct e; inversion H.
    + destruct e5; inversion H.
      -- inversion H.
         econstructor.
  - unfold e_subst_fun in H.
    destruct (mem_S y S) eqn : Hm; simpl in *.
    + destruct e; inversion H.
      -- destruct e5; inversion H.
         subst.
         clear H.
         econstructor.
         apply in_is_mem.
         auto.
    + destruct e; inversion H.
      -- destruct e5 ;
           inversion H;
           econstructor;
           apply notin_is_memf;
           auto.
  - unfold e_subst_fun in H.
    destruct e.
    + inversion H.
    + destruct e_subst_fun eqn: Hef.
      destruct e_subst_fun_exp eqn : Hee.
      inversion H.
      econstructor.
      -- destruct e5.
         ++  simpl in *.
            destruct mem_S eqn : Hm.
            ---  simpl in *.
                 inversion Hee.
            --- simpl in *.
                inversion Hee.
                econstructor.
                apply notin_is_memf.
                auto.
         ++  simpl in *.
            destruct mem_S eqn : Hm.
            ---  simpl in *.
                 inversion Hee.
            --- simpl in *.
                inversion Hee.
                econstructor.
                apply notin_is_memf.
                auto.
         ++ simpl in *.
            unfold e_subst_fun_var in Hee.
            destruct mem_S eqn : Hm.
            --- simpl in *.
            inversion Hee.
            econstructor.
            apply in_is_mem.
            auto.
            --- inversion Hee.
            econstructor.
            apply notin_is_memf.
            auto.
         ++ simpl in *.
           destruct mem_S eqn : Hm.
            ---  simpl in *.
                 inversion Hee.
            --- simpl in *.
                inversion Hee.
                econstructor.
                apply notin_is_memf.
                auto.
         ++ simpl in *.
           destruct mem_S eqn : Hm.
            ---  simpl in *.
                 inversion Hee.
            --- simpl in *.
                inversion Hee.
                econstructor.
                apply notin_is_memf.
                auto.
         ++ simpl in *.
           destruct mem_S eqn : Hm.
            ---  simpl in *.
                 inversion Hee.
            --- simpl in *.
                inversion Hee.
                econstructor.
                apply notin_is_memf.
                auto.
         ++ simpl in *.
           destruct mem_S eqn : Hm.
            ---  simpl in *.
                 inversion Hee.
            --- simpl in *.
                inversion Hee.
                econstructor.
                apply notin_is_memf.
                auto.
         ++ simpl in *.
           destruct mem_S eqn : Hm.
            ---  simpl in *.
                 inversion Hee.
            --- simpl in *.
                inversion Hee.
                econstructor.
                apply notin_is_memf.
                auto.
      -- apply IHp.
         auto.
      -- inversion H.
      -- simpl in *.
         destruct mem_S eqn : Hm; simpl in *.
         ++  destruct e5;  inversion H.
             --- destruct e_subst_fun_var; inversion H.
         ++ destruct e5; inversion H.
            --- destruct e_subst_fun_var; inversion H.
Qed.




(* e_subst_fun p e S = Some s <=> p ~S~ e ▷ s *)
Theorem e_subst_fun_Sub_clk_subst_exp_equiv : forall p e S sigma, e_subst_fun p e S = Some sigma <-> Sub_clk_subst_exp p e S sigma.
Proof.
  intros.
  split.
  apply e_subst_fun_Sub_clk_subst_exp.
  apply Sub_clk_subst_exp_e_subst_fun.
Qed.

(** *** For variables **)


Lemma eq2 : forall x y S, p_subst_fun_vars x y S = p_subst_fun (Patp_var x) (Patp_var y) S.
  Proof.
    intros.
    unfold p_subst_fun.
    unfold p_subst_fun_vars.
    reflexivity.
  Qed.


(* p ~S~ p' ▷ s ==> p_subst_fun p p' S = Some s *)
Theorem Sub_clk_subst_pat_p_subst_fun : forall p p' S sigma, Sub_clk_subst_pat p p' S sigma -> p_subst_fun p p' S = Some sigma.
Proof.
  intros.
  induction H; auto.
  - simpl.
    apply in_is_mem in H.
    rewrite H.
    auto.
  - unfold p_subst_fun.
    apply notin_is_memf in H.
    rewrite H.
    auto.
  - simpl.
    rewrite IHSub_clk_subst_pat2.
    rewrite <- eq2 in IHSub_clk_subst_pat1.

    rewrite IHSub_clk_subst_pat1.


    auto.
Qed.



(* p_subst_fun p p' S = Some s ==> p ~S~ p' ▷ s *)
Theorem p_subst_fun_Sub_clk_subst_pat : forall p p' S sigma, p_subst_fun p p' S = Some sigma -> Sub_clk_subst_pat p p' S sigma.
Proof.
  induction p; intros.
  - simpl in *.
    destruct p'; inversion H.
    + subst.
      clear H.
      econstructor.
  - simpl in H.
    destruct p'; inversion H.
    + destruct mem_S eqn : Hm.
      -- simpl in H.
      inversion H.
      simpl in H.
      clear H1.
      inversion H.
      econstructor.
      apply in_is_mem.
      auto.
      -- inversion H; subst.
         clear H.
         econstructor.
         apply notin_is_memf.
         auto.
  - simpl in *.
    destruct p'; inversion H.
    + clear H1.
      unfold p_subst_fun_vars in H.
      destruct mem_S eqn : Hm; simpl in *.
      -- destruct p_subst_fun eqn : Hp.
         ++ inversion H.
            subst.
            clear H.
            assert ((y,y0) :: l = ((y,y0)::nil)++l).
            auto.
            rewrite H.
            econstructor.
            --- econstructor.
                apply in_is_mem; auto.
            --- apply IHp.
                auto.
         ++ inversion H.
      -- destruct p_subst_fun eqn : Hp.
         ++ inversion H; subst.
            clear H.
            assert (sigma = nil ++ sigma).
            auto.
            rewrite H.
            econstructor.
            --- econstructor.
                apply notin_is_memf.
                auto.
            --- apply IHp.
                auto.
         ++ inversion H.
Qed.





(* p_subst_fun p p' S = Some s <=> p ~S~ p' ▷ s *)
Theorem p_subst_fun_Sub_clk_subst_pat_equiv : forall p p' S sigma, p_subst_fun p p' S = Some sigma <-> Sub_clk_subst_pat p p' S sigma.
Proof.
  intros.
  split.
  apply p_subst_fun_Sub_clk_subst_pat.
  apply Sub_clk_subst_pat_p_subst_fun.
Qed.

(** * Clocking functions *)


(** ** Expressions **)
Fixpoint clockof_exp (C : C) (exp:e) :=
  match exp with
  | Eunit ck => Some ck
  | Econst _ ck => Some ck
  | Econstructor _ ck => Some ck
  | Evar x => assoc x C
  | Ebinop e1 op e2 =>
    let c1 := clockof_exp C e1 in
    let c2 := clockof_exp C e2 in
    match c1, c2 with
      | Some ck1, Some ck2 =>
        if eq_ck ck1 ck2 then Some ck1
        else None
      | _,_ => None
    end
  | Eunop op e => clockof_exp C e
  | Ewhen e x =>
    let c1 := clockof_exp C e in
    let c2 := assoc x C in
    match c1, c2 with
      | Some ck1, Some ck2 =>
        if eq_ck ck1 ck2 then Some (Ckon ck1 x)
        else None
      | _, _ => None
    end
  | Ewhennot e x =>
    let c1 := clockof_exp C e in
    let c2 := assoc x C in
    match c1, c2 with
      | Some ck1, Some ck2 =>
        if eq_ck ck1 ck2 then Some (Ckonnot ck1 x)
        else None
      | _, _ => None
    end
  end.

(* C |- e : ck => clockof_exp C e = Some ck *)
Theorem clk_exp_clockof_exp : forall e C ck, clk_lexp C e ck -> clockof_exp C e = Some ck.
  Proof.
    intros.
    induction H; auto.
    + simpl.
      rewrite IHclk_lexp1.
      rewrite IHclk_lexp2.
      destruct eq_ck.
      auto.
      destruct n.
      auto.
    + simpl.
      rewrite IHclk_lexp1.
      inversion H0.
      subst.
      rewrite H3.
      destruct eq_ck.
      subst. auto.
      destruct n.
      auto.
    + simpl.
      rewrite IHclk_lexp1.
      inversion H0.
      subst.
      rewrite H3.
      destruct eq_ck.
      subst. auto.
      destruct n.
      auto.
Qed.


(* clockof_exp C e = Some ck => C |- e : ck *)
Theorem clockof_lexp_clk_lexp : forall e C ck, clockof_exp C e = Some ck -> clk_lexp C e ck.
  Proof.
    induction e; intros; inversion H; subst; auto.
    - econstructor.
    - econstructor.
    - econstructor. auto.
    - econstructor.
    - econstructor.
      + destruct (clockof_exp C e1) eqn : He1.
        -- destruct (clockof_exp C e2) eqn : He2.
           ++  apply IHe1.
               destruct eq_ck.
               inversion H1; subst.
               auto.
               inversion H1.
           ++ inversion H1.
        -- inversion H1.
      + destruct (clockof_exp C e1) eqn : He1.
        -- destruct (clockof_exp C e2) eqn : He2.
           ++  apply IHe2.
               destruct eq_ck.
               inversion H1; subst.
               auto.
               inversion H1.
           ++ inversion H1.
        -- inversion H1.
    - econstructor.
      apply IHe.
      auto.
    - destruct (clockof_exp C e) eqn : He1.
      destruct assoc eqn  : Ha .
      destruct eq_ck.
      subst.
      inversion H1.
      subst.
      econstructor.
      apply IHe.
      auto.
      econstructor.
      auto.
      inversion H1.
      inversion H1.
      inversion H1.
    - destruct (clockof_exp C e) eqn : He1.
      destruct assoc eqn  : Ha .
      destruct eq_ck.
      subst.
      inversion H1.
      subst.
      econstructor.
      apply IHe.
      auto.
      econstructor.
      auto.
      inversion H1.
      inversion H1.
      inversion H1.
Qed.



(* clockof_exp C e = Some ck <=> C |- e : ck *)
Theorem clockof_lexp_clk_lexp_equiv : forall e C ck, clockof_exp C e = Some ck <-> clk_lexp C e ck.
  Proof.
    intros.
    split.
    - apply clockof_lexp_clk_lexp.
    - apply clk_exp_clockof_exp.
Qed.

(** ** List of expressions **)

Fixpoint clockof_exps (C : C) (es:es) :=
  match es with
  | Esone_exp e => clockof_exp C e
  | Escons_exps e es =>
    match (clockof_exp C e), (clockof_exps C es) with
      | Some ck , Some cks => Some (Cktuple ck cks)
      | _,_ => None
    end
  end.

Theorem clk_es_clockof_exps : forall es C ck, clk_es C es ck -> clockof_exps C es = Some ck.
Proof.
  induction es. intros; inversion H; subst.
  - simpl. apply clk_exp_clockof_exp.
    auto.
  - intros.
    simpl in *.
    inversion H; subst.
    apply clk_exp_clockof_exp in H3.
    rewrite H3.
    apply IHes in H5.
    rewrite H5.
    auto.
Qed.

Theorem clockof_exps_clk_es : forall es C ck, clockof_exps C es = Some ck -> clk_es C es ck.
  Proof.
    induction es; intros; inversion H; subst.
    - econstructor.
      apply clockof_lexp_clk_lexp in H1.
      auto.
    - destruct clockof_exp eqn : He.
      + destruct (clockof_exps C es) eqn : Hes.
        -- inversion H1.
           econstructor.
           ++ apply clockof_lexp_clk_lexp.
              auto.
           ++ apply IHes.
              auto.
        -- inversion H1.
      + inversion H1.
Qed.

(** ** Control Expressions **)

Open Scope bool_scope.

Definition eq_ident x y := if eq_identifier x y then true else false.

Definition eq_clock x y := if eq_ck x y then true else false.

Fixpoint clockof_cexp (C:C) (cexp: cexp) :=
  match cexp with
  | Cemerge x e1 e2 =>
    let cx := assoc x C in
    let c1 := clockof_cexp C e1 in
    let c2 := clockof_cexp C e2 in
    match cx,c1,c2 with
     | Some ck, Some (Ckon ck' x'), Some (Ckonnot ck'' x'') =>
       if (eq_ident x x') && (eq_ident x' x'') &&  (eq_clock ck ck') && (eq_clock ck' ck'') then Some ck else None
     | _, _, _ => None
    end
  | Ceif e t f =>
    let ce := clockof_exp C e in
    let ct := clockof_cexp C t in
    let cf := clockof_cexp C f in
    match ce,ct,cf with
      Some a, Some b, Some c =>
      if andb (eq_clock a b) (eq_clock b c) then Some c
      else None
    | _, _, _ => None
    end
  | Ceexp e => clockof_exp C e
  end.


(** useful lemmas for equalities **)

Lemma eq_ident_refl : forall x, eq_ident x x = true.
  Proof.
    intros.
    unfold eq_ident.
    destruct eq_identifier.
    auto.
    destruct n.
    auto.
  Qed.

Lemma eq_ck_refl : forall x, eq_clock x x = true.
  Proof.
    intros.
    unfold eq_clock.
    destruct eq_ck.
    auto.
    destruct n.
    auto.
  Qed.

  Lemma eq_ck_is_eq : forall ck1 ck2,  eq_clock ck1 ck2 = true -> ck1 = ck2.
  Proof.
    intros.
    unfold eq_clock in H.
    destruct eq_ck in H.
    subst. auto.
    inversion H.
  Qed.


  Lemma eq_ident_is_eq : forall x1 x2,  eq_ident x1 x2 = true -> x1 = x2.
  Proof.
    intros.
    unfold eq_ident in H.
    destruct eq_identifier in H.
    subst. auto.
    inversion H.
  Qed.

(* C |- ce : ck => clockof_cexp C ce = Some ck *)
Theorem clk_cexp_clockof_cexp : forall ce C ck, clk_cexp C ce ck -> clockof_cexp C ce = Some ck.
  Proof.
    intros.
    induction H.
    - simpl.
      apply clk_exp_clockof_exp.
      auto.
    - simpl.
      inversion H; subst.
      destruct clockof_cexp eqn : Hce.
      rewrite H4.
      destruct c.
      + inversion IHclk_cexp1.
      + destruct (clockof_cexp C5 ce') eqn : Hce'.
        destruct c0; inversion IHclk_cexp2.
        -- inversion IHclk_cexp1.
           subst.
           rewrite eq_ident_refl.
           rewrite eq_ck_refl.
           simpl.
           auto.
        -- inversion IHclk_cexp2.
      + inversion IHclk_cexp1.
      + inversion IHclk_cexp1.
      + inversion IHclk_cexp1.
      + inversion IHclk_cexp1.
    - simpl.
      rewrite IHclk_cexp1.
      rewrite IHclk_cexp2.
      apply clk_exp_clockof_exp in H.
      rewrite H.
      rewrite eq_ck_refl.
      simpl.
      auto.
Qed.

(* clockof_cexp C ce = Some ck =>  C |- ce : ck *)
Theorem clockof_cexp_clk_cexp : forall ce C ck, clockof_cexp C ce = Some ck -> clk_cexp C ce ck.
  Proof.
    induction ce; intros.
    - econstructor.
      apply clockof_lexp_clk_lexp.
      simpl in H.
      auto.
    - simpl in H.
      destruct assoc eqn : Ha; inversion H.
      + destruct clockof_cexp eqn : Hce1; inversion H.
        destruct c0; inversion H.
        -- destruct (clockof_cexp C ce2) eqn : Hce2; inversion H.
           destruct c1; inversion H.
           ++ destruct eq_ident eqn : Hi1; inversion H.
              destruct (eq_ident x0 x1) eqn : Hi2; inversion H.
              destruct eq_clock eqn : Hc1; inversion H.
              destruct (eq_clock c0 c1) eqn : Hc2; inversion H.
              subst.
              clear H H1 H2 H3 H4 H5 H6 H7 H8.
              apply eq_ident_is_eq in Hi1.
              apply eq_ident_is_eq in Hi2.
              apply eq_ck_is_eq in Hc1.
              apply eq_ck_is_eq in Hc2.
              subst.
              econstructor.
              --- econstructor.
                  auto.
              --- apply IHce1.
                  auto.
              --- apply IHce2.
                  auto.
    - simpl in H.
      destruct clockof_exp eqn : He; inversion H.
      destruct clockof_cexp eqn : Hce1; inversion H.
      destruct (clockof_cexp C ce2) eqn : Hce2; inversion H.
      destruct eq_clock eqn : Hck1; inversion H.
      destruct (eq_clock c0 c1) eqn : Hck2; inversion H.
      apply eq_ck_is_eq in Hck2.
      apply eq_ck_is_eq in Hck1.
      subst.
      econstructor.
      + apply clockof_lexp_clk_lexp.
        auto.
      + apply IHce1.
        auto.
      + apply IHce2.
        auto.
Qed.


(* clockof_cexp C ce = Some ck <=>  C |- ce : ck *)
Theorem clockof_cexp_clk_cexp_equiv : forall ce C ck, clockof_cexp C ce = Some ck <-> clk_cexp C ce ck.
  Proof.
    split.
    - apply clockof_cexp_clk_cexp.
    - apply clk_cexp_clockof_cexp.
  Qed.


(** ** Variable patterns **)

Fixpoint clockof_pat C p :=
  match p with
    | Patp_nil => Some (Ckbase)
    | Patp_var x => assoc x C
    | Patp_tuple x p2 =>
      let c1 := assoc x C in
      let c2 := clockof_pat C p2 in
      match c1, c2 with
        | Some ck1, Some ck2 => Some (Cktuple ck1 ck2)
        | _,_ => None
      end
  end.


(* C |- p : ck => clockof_pat C p = Some ck *)
Theorem Clk_pat_clockof_pat : forall p C ck, Clk_pat C p ck -> clockof_pat C p = Some ck.
  Proof.
    intros.
    induction H; auto.
    - simpl.
      rewrite IHClk_pat.
      inversion H.
      subst.
      rewrite H3.
      auto.
  Qed.


(* clockof_pat C p = Some ck => C |- p : ck *)
Theorem clockof_pat_Clk_pat : forall p C ck, clockof_pat C p = Some ck -> Clk_pat C p ck .
  Proof.
    induction p; intros.
    - simpl in H.
      inversion H; subst.
      econstructor.
    - simpl in H.
      inversion H.
      subst.
      econstructor.
      auto.
    - inversion H.
      destruct (clockof_pat C p)  eqn : Hp.
      + simpl in *.
        destruct assoc eqn : Ha.
        -- inversion H1.
           econstructor.
           ++ econstructor.
              auto.
           ++ apply IHp.
              auto.
        -- inversion H.
      + simpl in H.
        destruct assoc eqn : Ha.
        inversion H1.
        inversion H1.
 Qed.


(* clockof_pat C p = Some ck <=> C |- p : ck *)
Theorem clockof_pat_Clk_pat_equiv : forall p C ck, clockof_pat C p = Some ck <-> Clk_pat C p ck .
  Proof.
    intros.
    split.
    - apply clockof_pat_Clk_pat.
    - apply Clk_pat_clockof_pat.
Qed.

  (** ** Equations **)


Fixpoint clockof_params (C : C) e0 (l:list e) :=
  match l with
  | nil => clockof_exp C e0
  | cons e l =>
    match (clockof_exp C e), (clockof_params C e0 l) with
      | Some ck , Some ck' => if eq_clock ck ck' then Some ck else None
      | _,_ => None
    end
  end.

  Definition well_clocked_equation eqn (H : H) C  :=
    match eqn with
    | EqDef y ck ce =>
      let c1 := clockof_pat C (Patp_var y) in
      let c2 := clockof_cexp C ce in
      match c1,c2 with
      | Some ck1 , Some ck2 => eq_clock ck1 ck2 && eq_clock ck2 ck
      | _,_  => false
      end
    | EqFby y ck k e =>
      let c1 := clockof_pat C (Patp_var y) in
      let c2 := clockof_exp C e in
      match c1,c2 with
      | Some ck1 , Some ck2 =>
         eq_clock ck1 ck2 && eq_clock ck2 ck
      | _, _ => false
      end
    | EqEval y ck h e l =>
      let c1 := clockof_pat C (Patp_var y) in
      let cparams := clockof_params C e l in
      match c1, cparams, ck with
      | Some ck, Some ck', ck'' => eq_clock ck ck' && eq_clock ck' ck''
      | _,_,_ => false
      end
    | EqApp p ck f es =>
      let sigf := assoc_global f H in
      match sigf with
      | Some (Signcons p1 ck1 p2 ck2) =>
        let ckp := clockof_pat C p in
        let ckes := clockof_exps C es in
        match ckp,ckes with
        | Some ckp, Some ckes =>
          let S := carriers ck1 ++ carriers ck2 in
          let sigma := e_subst_fun p1 es S in
          let sigma' := p_subst_fun p2 p S in
          match sigma,sigma' with
              | Some sigma, Some sigma' =>
                let cke_subst := apply_substs sigma (subst_ck ck1 ck) in
                let ckp_subst := apply_substs (sigma' ++ sigma) (subst_ck ck2 ck) in
                eq_clock ckes cke_subst && eq_clock ckp ckp_subst
              | _,_ => false
          end
        | _,_ => false
        end
      | _ => false
      end
    end.


  Lemma HJ:
    forall e l,
    (map (fun e_ : e => e_) l) = l.
  Proof.
    induction l.
    - simpl. auto.
    - simpl.
      rewrite IHl.
      auto.
  Qed.

  Lemma WCcons :
    forall H C y ck5 h5 e_5 a e_list,
      Well_clocked_eq H C (EqEval y ck5 h5 e_5 (a :: e_list)) ->
      Well_clocked_eq H C (EqEval y ck5 h5 e_5 (e_list)).
  Proof.
    intros.
    induction e_list.
    - inversion H0; subst.
      econstructor.
      + simpl in H11.
        auto.
      + auto.
      + simpl in H11.
        simpl.
        auto.
    - inversion H0; subst.
      simpl in *.
      rewrite HJ in H11.
      econstructor.
      + auto.
      + auto.
      + simpl.
        rewrite HJ.
        auto.
Qed.




  (* H, C |- eqn => well_clocked_equation H C eqn = true *)
  Theorem Well_clocked_eq_well_clocked_equation : forall eqn C H, Well_clocked_eq H C eqn -> well_clocked_equation eqn H C = true.
  Proof.
    intros.
    inversion H0; subst.
    - simpl.
      inversion H1.
      subst.
      rewrite H6.
      inversion H4.
      + subst.
      apply Clk_pat_clockof_pat in H4.
      rewrite H4.
      apply clk_es_clockof_exps in H3.
      rewrite H3.
      inversion H2; subst.
      simpl in *.
      apply e_subst_fun_Sub_clk_subst_exp_equiv  in H5.
      rewrite H5.
      apply p_subst_fun_Sub_clk_subst_pat_equiv in H8.
      rewrite H8.
      rewrite Bool.andb_true_iff.
      split.
      rewrite eq_ck_refl.
      auto.
      rewrite H9.
      rewrite eq_ck_refl.
      auto.
      + subst.
        apply Clk_pat_clockof_pat in H4.
        rewrite H4.
        apply clk_es_clockof_exps in H3.
        rewrite H3.
        inversion H2; subst.
        apply e_subst_fun_Sub_clk_subst_exp_equiv  in H7.
        rewrite H7.
        apply p_subst_fun_Sub_clk_subst_pat_equiv in H9.
        rewrite H9.
        rewrite Bool.andb_true_iff.
        split.
        rewrite eq_ck_refl.
        auto.
        rewrite eq_ck_refl.
        auto.
      + subst.
        apply Clk_pat_clockof_pat in H4.
        rewrite H4.
        apply clk_es_clockof_exps in H3.
        rewrite H3.
        inversion H2; subst.
        apply e_subst_fun_Sub_clk_subst_exp_equiv  in H8.
        rewrite H8.
        apply p_subst_fun_Sub_clk_subst_pat_equiv in H10.
        rewrite H10.
        rewrite Bool.andb_true_iff.
        split.
        rewrite eq_ck_refl.
        auto.
        rewrite H11.
        rewrite eq_ck_refl.
        auto.
    -
      unfold well_clocked_equation.
      apply Clk_pat_clockof_pat in H1.
      rewrite H1.
      apply clk_cexp_clockof_cexp in H2.
      rewrite H2.
      inversion H0; subst.
      apply Bool.andb_true_iff.
      split.
      + apply eq_ck_refl.
      + apply eq_ck_refl.
    - simpl.
      apply Clk_pat_clockof_pat in H1.
      simpl in H1.
      rewrite H1.
      apply clk_exp_clockof_exp in H2.
      rewrite H2.
      rewrite eq_ck_refl.
      simpl. auto.
    - induction e_list.
      + simpl in *.
        apply Clk_pat_clockof_pat in H1.
        simpl in H1.
        rewrite H1.
        apply clk_exp_clockof_exp in H2.
        rewrite H2.
        apply Bool.andb_true_iff.
        split; apply eq_ck_refl.
      + rewrite HJ in *.
        apply Clk_pat_clockof_pat in H1.
        simpl in H1.
        assert (H2' := H2).
        apply clk_exp_clockof_exp in H2.
        unfold well_clocked_equation.
        simpl.
        rewrite H1.
        simpl in H3.
        destruct (clockof_exp C a) eqn : Ha.
        -- assert (Well_clocked_eq H C (EqEval y ck5 h5 e_5 e_list)).
           eapply WCcons.
           eauto.
           apply IHe_list in H4.
           simpl in H4.
           rewrite H1 in H4.
           destruct clockof_params eqn : Hp.
           ++ destruct (eq_clock c c0) eqn : Hc.
              --- apply eq_ck_is_eq in Hc.
                  subst.
                  auto.
              --- assert (a = a \/ In a e_list).
                  auto.
                  apply H3 in H5.
                  apply clk_exp_clockof_exp in H5.
                  rewrite Ha in H5.
                  apply Bool.andb_true_iff in H4.
                  inversion H4.
                  apply eq_ck_is_eq in H6.
                  apply eq_ck_is_eq in H7.
                  subst.
                  inversion H5.
                  subst.
                  inversion Hc.
                  apply eq_ck_refl.
           ++ auto.
           ++ auto.
        -- assert (a = a \/ In a e_list).
           auto.
           apply H3 in H4.
           apply clk_exp_clockof_exp in H4.
           rewrite Ha in H4.
           inversion H4.
  Qed.



Lemma H : forall C ck e0 e l,
  clockof_params C e0 l = Some ck ->
  In e l ->
  clockof_exp C e = Some ck.
Proof.
  induction l; intros.
  - simpl in *. inversion H0.
  - simpl in *.
    inversion H0; clear H0.
    + destruct (clockof_exp C a) eqn : Ha.
      destruct clockof_params eqn : Hp.
      destruct eq_clock eqn : Hc.
      apply eq_ck_is_eq in Hc.
      subst.
      inversion H; subst.
      auto.
      inversion H.
      inversion H.
      inversion H.
    +
      apply IHl.
      -- destruct (clockof_exp C a) eqn : He.
         ++ destruct clockof_params eqn : Hp.
            destruct eq_clock eqn : Hc.
            apply eq_ck_is_eq in Hc.
            subst.
            auto.
            inversion H.
            auto.
         ++ inversion H.
      --auto.
Qed.

Lemma Hparamcons :
  forall C e0 a l ck5,
    clockof_params C e0 (a :: l) = Some ck5 ->
    clockof_params C e0 l = Some ck5.
Proof.
  intros.
  induction l.
  - simpl in *.
    destruct clockof_exp eqn : Ha.
    + destruct (clockof_exp C e0) eqn : He.
      -- destruct eq_clock eqn : Hc.
         ++ apply eq_ck_is_eq in Hc.
            inversion Hc.
            subst.
            auto.
         ++ inversion H0.
      -- inversion H0.
    + inversion H0.
  - simpl in *.
     destruct clockof_exp eqn : Ha.
    + destruct (clockof_exp C a0) eqn : He.
      -- destruct clockof_params eqn : Hp.
         ++ destruct eq_clock eqn : Hc.
            --- destruct (eq_clock c c0) eqn : Hc'.
                +++ destruct (eq_clock c c1) eqn : Hc''.
                    ---- apply eq_ck_is_eq in Hc.
                         apply eq_ck_is_eq in Hc'.
                         apply eq_ck_is_eq in Hc''.
                         inversion H0.
                         subst.
                         auto.
                    ---- apply eq_ck_is_eq in Hc.
                         apply eq_ck_is_eq in Hc'.
                         subst.
                         apply IHl.
                         rewrite eq_ck_refl in Hc''.
                         inversion Hc''.
                +++ inversion H0.
            --- inversion H0.
         ++ inversion H0.
      -- inversion H0.
    + inversion H0.
Qed.

Lemma Hparam0 :
  forall C e0 l ck5, clockof_params C e0 l = Some ck5 ->
                     clockof_exp C e0 = Some ck5.
Proof.
  intros.
  induction l.
  - simpl in *.
    auto.
  - apply IHl.
    eapply Hparamcons.
    eauto.
Qed.


  (*  well_clocked_equation H C eqn = true => H, C |- eqn  *)
  Theorem well_clocked_equation_Well_clocked_eq : forall eqn C H,  well_clocked_equation eqn H C = true -> Well_clocked_eq H C eqn.
  Proof.
    intros.
    induction eqn.
    - econstructor.
      + simpl in H1.
        destruct clockof_cexp eqn : Hce.
        destruct assoc eqn : Ha.
      apply Bool.andb_true_iff in H1.
      destruct H1.
      apply eq_ck_is_eq in H1.
      apply eq_ck_is_eq in H2.
      subst.
      econstructor.
      auto.
      inversion H1.
      destruct assoc; inversion H1.
      + simpl in H1.
        destruct assoc eqn : Ha.
        destruct clockof_cexp eqn : Hce.
        apply Bool.andb_true_iff in H1.
        destruct H1.
        apply eq_ck_is_eq in H1.
        apply eq_ck_is_eq in H2.
        subst.
        apply clockof_cexp_clk_cexp.
        auto.
        inversion H1.
        inversion H1.
    - simpl in H1.
      destruct assoc eqn : Ha.
      destruct clockof_exp eqn : He.
      apply Bool.andb_true_iff in H1.
      destruct H1.
      apply eq_ck_is_eq in H1.
      apply eq_ck_is_eq in H2.
      subst.
      econstructor.
      + apply clockof_pat_Clk_pat.
        auto.
      + apply clockof_lexp_clk_lexp.
        auto.
      + inversion H1.
      + inversion H1.
    - simpl in H1.
      destruct assoc_global eqn : Hf.
      destruct s.
      destruct clockof_pat eqn : Hp.
      destruct clockof_exps eqn : He.
      destruct e_subst_fun eqn : Hs.
      destruct p_subst_fun eqn : Hs'.
      econstructor.
      econstructor.
      eauto.
      eauto.
      econstructor.
      auto.
      apply e_subst_fun_Sub_clk_subst_exp.
      eauto.
      auto.
      apply p_subst_fun_Sub_clk_subst_pat.
      eauto.
      auto.
      apply clockof_exps_clk_es.
      apply Bool.andb_true_iff in H1.
      destruct H1.
      apply eq_ck_is_eq in H1.
      apply eq_ck_is_eq in H2.
      subst.
      auto.
      apply clockof_pat_Clk_pat.
      apply Bool.andb_true_iff in H1.
      destruct H1.
      apply eq_ck_is_eq in H1.
      apply eq_ck_is_eq in H2.
      subst.
      auto.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1.
    - simpl in H1.
      destruct assoc eqn : Hy.
      + destruct clockof_params eqn : Hp.
        -- apply Bool.andb_true_iff in H1.
           inversion H1.
           apply eq_ck_is_eq in H2.
           apply eq_ck_is_eq in H3.
           subst.
           econstructor.
           ++ apply clockof_pat_Clk_pat.
              simpl.
              auto.
           ++ apply clockof_lexp_clk_lexp.
              eapply Hparam0.
              eauto.
           ++ rewrite HJ.
              intros.
              apply clockof_lexp_clk_lexp.
              eapply H.
              --- eauto.
              --- eauto.
        -- inversion H1.
      + inversion H1.

  Qed.


  (*  well_clocked_equation eqn H C = true <=> H, C |- eqn  *)
  Theorem well_clocked_equation_Well_clocked_eq_equiv : forall eqn C H,  well_clocked_equation eqn H C = true <-> Well_clocked_eq H C eqn.
  Proof.
    intros.
    split.
    - apply well_clocked_equation_Well_clocked_eq.
    - apply Well_clocked_eq_well_clocked_equation.
  Qed.

  (** ** List of equations ***)


(** Function definition **)
  Fixpoint well_clocked_eqns eqns H C :=
    match eqns with
    | Eqseqs_one eq  => well_clocked_equation eq H C
    | Eqseqs_cons eq eqs => well_clocked_equation eq H C && well_clocked_eqns eqs H C
    end.


  (* H, C |- eqns => well_clocked_eqns eqns H C *)
  Theorem Well_clocked_eqns_well_clocked_eqns : forall eqns H C, Well_clocked_eqns H C eqns -> well_clocked_eqns eqns H C = true.
  Proof.
    intros.
    induction H1; subst.
    - apply Well_clocked_eq_well_clocked_equation.
      auto.
    - simpl.
      apply Bool.andb_true_iff.
      split.
      + apply Well_clocked_eq_well_clocked_equation.
        auto.
      + auto.
  Qed.


  (* well_clocked_eqns eqns H C => H, C |- eqns *)
  Theorem well_clocked_eqns_Well_clocked_eqns : forall eqns H C, well_clocked_eqns eqns H C = true -> Well_clocked_eqns H C eqns.
  Proof.
    induction eqns; intros.
    - simpl in H0.
      econstructor.
      apply well_clocked_equation_Well_clocked_eq.
      auto.
    - simpl in H1.
      apply Bool.andb_true_iff in H1.
      destruct H1.
      econstructor.
      + apply well_clocked_equation_Well_clocked_eq.
        auto.
      + apply IHeqns.
        auto.
  Qed.


  (** ** Node **)


  (** Function **)

  Definition clockof_node node H C :=
    match node with
    | Nodemk_node f p p' eqns =>
      let c := clockof_pat C p in
      let c' := clockof_pat C p' in
      match c,c' with
      | Some ckp, Some ckp' =>
        if well_clocked_eqns eqns H C then
          Some (Signcons p ckp p' ckp')
        else
          None
      | _,_ => None
      end
    end.

  (* H , C |- node : sign => clockof_node H C = Some sign  *)
  Theorem Well_clocked_node_clockof_node : forall node sign H C ,
      Well_clocked_node H C node sign -> clockof_node node H C = Some sign.
    Proof.
      intros.
      destruct node.
      induction H1.
      - simpl.
        apply Clk_pat_clockof_pat in H1.
        apply Clk_pat_clockof_pat in H2.
        apply Well_clocked_eqns_well_clocked_eqns in H0.
        rewrite H0.
        rewrite H1.
        rewrite H2.
        auto.
    Qed.

    (* clockof_node H C = Some sign => H , C |- node : sign *)
    Theorem well_clocked_node_Well_clocked_node : forall node H C sign,
        clockof_node node H C = Some sign -> Well_clocked_node H C node sign.
    Proof.
      intros.
      destruct node.
      simpl in H1.
      destruct clockof_pat eqn : Hp; inversion H1.
      - destruct (clockof_pat C ys) eqn : Hys ; inversion H1.
        + destruct well_clocked_eqns eqn : Heqns; inversion H1.
          -- subst. clear H1.
             econstructor.
             apply well_clocked_eqns_Well_clocked_eqns.
             eauto.
             apply clockof_pat_Clk_pat.
             auto.
             apply clockof_pat_Clk_pat.
             auto.
    Qed.



    (** **  Program **)

    (** Function **)
    Fixpoint well_clocked_prog prog H :=
      match prog with
      | nil => true
      | (C , Nodemk_node f p p' eqns)::nodes =>
        let sign := clockof_node (Nodemk_node f p p' eqns) H C in
        match sign with
        | Some s => well_clocked_prog nodes ((f,s)::H)
        | None => false
        end
      end.


    (* H |- prog => well_clocked_prog prog H = true *)
    Theorem Well_clocked_nodes_clockof_prog : forall prog H,
      Well_clocked_nodes H prog -> well_clocked_prog prog H = true.
    Proof.
      intros.
      induction H1.
      - simpl. auto.
      - destruct IHWell_clocked_nodes.
        simpl.
        inversion H0.
        subst.
        apply Clk_pat_clockof_pat in H12.
        apply Clk_pat_clockof_pat in H13.
        rewrite H12.
        rewrite H13.
        apply Well_clocked_eqns_well_clocked_eqns in H11.
        rewrite H11.
        auto.
    Qed.

    (* well_clocked_prog H = true => H |- prog *)
    Theorem clockof_prog_Well_clocked_nodes : forall prog H,
      well_clocked_prog prog H = true -> Well_clocked_nodes H prog.
    Proof.
      induction prog; intros.
      - simpl in H1.
        econstructor.
      - destruct a.
        simpl in H1.
        destruct n.
        destruct clockof_pat eqn : Hp.
        destruct (clockof_pat c ys) eqn : Hys.
        destruct well_clocked_eqns eqn: Heqns.
        econstructor.
        + econstructor.
          apply well_clocked_eqns_Well_clocked_eqns.
          eauto.
          apply clockof_pat_Clk_pat.
          eauto.
          apply clockof_pat_Clk_pat.
          eauto.
        + eapply IHprog.
          eauto.
        + inversion H1.
        + inversion H1.
        + inversion H1.
    Qed.

    (* well_clocked_prog H = true <=> H |- prog *)
    Theorem clockof_prog_Well_clocked_nodes_equiv : forall prog H,
      well_clocked_prog prog H = true <-> Well_clocked_nodes H prog.
    Proof.
      intros.
      split.
      - apply clockof_prog_Well_clocked_nodes.
      - apply Well_clocked_nodes_clockof_prog.
    Qed.

(** * Extraction **)
Require Extraction.
Extraction Language OCaml.

Extract Inductive bool => bool [true false].
Extract Inductive list => list [ "[]" "(::)" ].
Require Import ExtrOcamlString.
Require Import ExtrOcamlZInt.
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => option [ "Some" "None"].

Extraction "clocks_checked.ml" well_clocked_prog.
