
(*==============================================================================*)
(* Utility                                                                      *)
(*==============================================================================*)

Definition app {A : Type} {B : A -> Type} (f : forall x : A, B x) (a : A) := f a.

Notation "f @ a" := (app f a) (at level 101, left associativity).
Notation "f $ a" := (app f a) (at level 102, right associativity).



Definition exT_implies_ex {A : Type} {P : A -> Prop}

  : {x : A & P x} -> exists x : A, P x

:=
  fun e =>
    match e with
    | existT _ x p => ex_intro _ x p
    end.





(*==============================================================================*)
(* Equivalence Relation Definition                                              *)
(*==============================================================================*)

Class Equiv {A : Type} (R : A -> A -> Prop) :=
{
  refl  : forall (a : A), R a a;
  sym   : forall {x y : A}, R x y -> R y x;
  trans : forall {x y z : A}, R x y -> R y z -> R x z;

  rtrans := fun {x y z : A} (p : R y z) (q : R x y) => trans q p;
}.





(*==============================================================================*)
(* Group Definition                                                             *)
(*==============================================================================*)

Class Group G (R : G -> G -> Prop) `{Equiv G R} :=
{
  (* elements/functions *)

  id   : G;
  mult : G -> G -> G;
  inv  : G -> G;


  (* derived notions *)

  eqv  : G -> G -> Prop := R;

  conj : G -> G -> G := fun g a => mult a (mult g (inv a));
  comm : G -> G -> G := fun a b => mult a (mult b (mult (inv a) (inv b)));

  actL : G -> G -> G := mult;
  actR : G -> G -> G := fun g a => mult a g;


  (* laws *)

  assoc : forall {a b c : G}, R (mult a (mult b c)) (mult (mult a b) c);
  
  left_id  : forall (g : G), R (mult id g) g;
  right_id : forall (g : G), R (mult g id) g;

  left_inv : forall (g : G), R (mult (inv g) g) id;


  (* coherence *)

  inv_well_def  : forall {g g' : G}, R g g' -> R (inv g) (inv g');
  mult_well_def : forall {a a' b b' : G}, R a a' -> R b b' -> R (mult a b) (mult a' b');
}.

Notation "x # y" := (mult x y) (at level 41, right associativity).
Notation "g *"   := (inv g) (at level 39).
Notation "x ~ y" := (eqv x y) (at level 71, no associativity).





(*==============================================================================*)
(* Basic Group Properties                                                       *)
(*==============================================================================*)

Lemma inv_id {G : Type} {R : G -> G -> Prop} `{Group G R}

  : id* ~ id.

Proof.
  apply (trans $ sym $ right_id $ id*).
  apply (trans $ left_inv id).
  exact (refl id).
Qed.



Lemma idempot_inv {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : (g*)* ~ g.

Proof.
  apply (trans $ sym $ right_id $ (g*)*).
  apply (trans $ sym $ mult_well_def (refl $ (g*)*) @ left_inv g).
  apply (trans assoc).
  apply (trans $ mult_well_def (left_inv $ g*) @ refl g).
  exact (left_id g).
Qed.



Lemma right_inv {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : g # g* ~ id.

Proof.
  apply (rtrans $ left_inv $ g*).
  apply mult_well_def.
  - exact (sym $ idempot_inv g).
  - exact (refl $ g*).
Qed.



Lemma left_cancel {G : Type} {R : G -> G -> Prop} `{Group G R} (g a b : G)

  : g # a ~ g # b -> a ~ b.

Proof.
  intro e.
  apply (trans $ sym $ left_id a).
  apply (rtrans $ left_id b).
  apply (trans $ mult_well_def @ sym (left_inv g) @ refl a).
  apply (rtrans $ mult_well_def @ left_inv g @ refl b).
  apply (trans $ sym assoc).
  apply (rtrans assoc).
  apply mult_well_def.
  - exact (refl @ g*).
  - exact e.
Qed.



Lemma right_cancel {G : Type} {R : G -> G -> Prop} `{Group G R} (g a b : G)

  : a # g ~ b # g -> a ~ b.

Proof.
  intro e.
  apply (trans $ sym $ right_id a).
  apply (rtrans $ right_id b).
  apply (trans $ sym $ mult_well_def @ refl a @ right_inv g).
  apply (rtrans $ mult_well_def @ refl b @ right_inv g).
  apply (trans assoc).
  apply (rtrans $ sym assoc).
  apply mult_well_def.
  - exact e.
  - exact (refl (g*)).
Qed.



Lemma left_mult {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G) {a b : G}

  : a ~ b -> g # a ~ g # b.

Proof.
  intro p.
  apply (left_cancel @ g*).
  apply (trans assoc).
  apply (trans $ mult_well_def @ left_inv g @ refl a).
  apply (trans $ left_id a).
  apply (rtrans $ sym assoc).
  apply (rtrans $ sym $ mult_well_def @ left_inv g @ refl b).
  apply (rtrans $ sym $ left_id b).
  exact p.
Qed.



Lemma right_mult {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G) {a b : G}

  : a ~ b -> a # g ~ b # g.

Proof.
  intro p.
  apply (right_cancel @ g*).
  apply (trans $ sym assoc).
  apply (trans $ mult_well_def @ refl a @ right_inv g).
  apply (trans $ right_id a).
  apply (rtrans assoc).
  apply (rtrans $ sym $ mult_well_def @ refl b @ right_inv g).
  apply (rtrans $ sym $ right_id b).
  exact p.
Qed.



Lemma shift_left {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : g # a ~ b -> a ~ g* # b.

Proof.
  intro p.
  apply (left_cancel g).
  apply (rtrans $ sym assoc).
  apply (rtrans $ sym $ mult_well_def @ right_inv g @ refl b).
  apply (rtrans $ sym $ left_id b).
  exact p.
Qed.



Lemma shift_left_inv {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : g* # a ~ b -> a ~ g # b.

Proof.
  intro p.
  apply (rtrans $ mult_well_def @ idempot_inv g @ refl b).
  apply shift_left.
  exact p.
Qed.



Lemma shift_right {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : a # g ~ b -> a ~ b # g*.

Proof.
  intro p.
  apply (right_cancel g).
  apply (rtrans assoc).
  apply (rtrans $ sym $ mult_well_def @ refl b @ left_inv g).
  apply (rtrans $ sym $ right_id b).
  exact p.
Qed.



Lemma shift_right_inv {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : a # g* ~ b -> a ~ b # g.

Proof.
  intro p.
  apply (rtrans $ mult_well_def @ refl b @ idempot_inv g).
  apply shift_right.
  exact p.
Qed.



Lemma simpl_left_inv_left {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : g* # g # a ~ b -> a ~ b.

Proof.
  intro p.
  apply (left_cancel g).
  apply shift_left_inv.
  exact p.
Qed.



Lemma simpl_left_inv_right {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : a # g* # g ~ b -> a ~ b.

Proof.
  intro p.
  apply (right_cancel @ g*).
  apply shift_right_inv.
  apply (trans $ mult_well_def @ refl _ @ idempot_inv g).
  apply (trans $ sym assoc).
  exact p.
Qed.



Lemma simpl_right_inv_left {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : g # g* # a ~ b -> a ~ b.

Proof.
  intro p.
  apply (left_cancel @ g*).
  apply shift_left.
  exact p.
Qed.



Lemma simpl_right_inv_right {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : a # g # g* ~ b -> a ~ b.

Proof.
  intro p.
  apply (right_cancel g).
  apply shift_right_inv.
  apply (trans $ sym assoc).
  exact p.
Qed.



Lemma injective_inv {G : Type} {R : G -> G -> Prop} `{Group G R}

  : forall (a b : G), a* ~ b* -> a ~ b.

Proof.
  intros a b e.
  apply (trans $ sym $ idempot_inv a).
  apply (rtrans $ idempot_inv b).
  apply inv_well_def.
  exact e.
Qed.



Lemma inv_mult {G : Type} {R : G -> G -> Prop} `{Group G R} (g h : G)

  : (g # h)* ~ h* # g*.

Proof.
  apply (right_cancel @ g # h).
  apply (trans $ left_inv $ g # h).
  apply (rtrans assoc).
  apply shift_left.
  apply (trans $ right_id h).
  apply (trans $ sym $ left_id h).
  apply (rtrans $ sym $ assoc).
  apply mult_well_def.
  exact (sym $ left_inv g).
  exact (refl h).
Qed.



Lemma unique_left_id {G : Type} {R : G -> G -> Prop} `{Group G R} (e : G)

  : (forall (g : G), e # g ~ g) -> id ~ e.

Proof.
  intro l_id_cond.
  apply (trans $ sym $ l_id_cond id).
  exact (right_id e).
Qed.



Lemma unique_right_id {G : Type} {R : G -> G -> Prop} `{Group G R} (e : G)

  : (forall (g : G), e # g ~ g) -> id ~ e.

Proof.
  intro r_id_cond.
  apply (trans $ sym $ r_id_cond id).
  exact (right_id e).
Qed.



Lemma unique_left_inv {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : forall (i : G), i # g ~ id -> i ~ g*.

Proof.
  intros i l_inv_cond.
  apply (right_cancel g).
  apply (rtrans $ sym $ left_inv g).
  exact l_inv_cond.
Qed.



Lemma unique_right_inv {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : forall (i : G), g # i ~ id -> i ~ g*.

Proof.
  intros i r_inv_cond.
  apply (left_cancel g).
  apply (rtrans $ sym $ right_inv g).
  exact r_inv_cond.
Qed.



Lemma conj_id {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : conj g id ~ g.

Proof.
  unfold conj.
  apply (trans $ left_id _).
  apply sym.
  apply shift_right.
  exact (right_id g).
Qed.



Lemma double_conj {G : Type} {R : G -> G -> Prop} `{Group G R}

  : forall a b g : G, conj (conj g b) a ~ conj g (a # b).

Proof.
  intros.
  unfold conj.
  apply (trans assoc).
  apply (trans $ mult_well_def @ assoc @ refl _).
  apply (trans $ sym assoc).
  apply (trans $ mult_well_def @ refl _ @ sym assoc).
  apply (trans $ sym $ mult_well_def @ refl _ $ mult_well_def @ refl _ @ inv_mult a b).
  exact (refl _).
Qed.



Lemma conj_well_def {G : Type} {R : G -> G -> Prop} `{Group G R}

  : forall {g a g' a' : G}, g ~ g' -> a ~ a' -> conj g a ~ conj g' a'.

Proof.
  intros g a g' a' e1 e2.
  unfold conj.
  apply (mult_well_def e2).
  apply (fun e => mult_well_def e @ inv_well_def e2).
  exact e1.
Qed.



Lemma conj_inv {G : Type} {R : G -> G -> Prop} `{Group G R}

  : forall a b : G, conj (conj a b) (b*) ~ a.

Proof.
  intros.
  apply (trans $ double_conj (b*) b a).
  apply (trans $ conj_well_def @ refl a @ left_inv b).
  exact (conj_id a).
Qed.





(*==============================================================================*)
(* Subroups                                                                     *)
(*==============================================================================*)

Definition Sub (G : Type) (P : G -> Prop) := {x : G & P x}.



Class Subgroup (G : Type) (R : G -> G -> Prop) (P : G -> Prop) `{Group G R} :=
{
  contains_id : P id;

  closed_under_equiv : forall (a b : G), (a ~ b) -> P a -> P b;

  closed_under_mult : forall (a b : G), P a -> P b -> P (a # b);

  closed_under_inv : forall (a : G), P a -> P (a*);
}.



Definition subgroup_equiv {G : Type} (R : G -> G -> Prop) (P : G -> Prop) `{Subgroup G R P}

  : Sub G P -> Sub G P -> Prop

:= 
  fun a b => 
    match a with
    | existT _ u _ => 
      match b with
      | existT _ v _ => R u v
      end
    end.



Lemma subgroup_equiv_refl {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (s : Sub G P), subgroup_equiv R P s s.

Proof.
  intro.
  destruct s.
  unfold subgroup_equiv.
  exact (refl x).
Qed.



Lemma subgroup_equiv_sym {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (s s' : Sub G P), subgroup_equiv R P s s' -> subgroup_equiv R P s' s.

Proof.
  intros s s' e.
  destruct s, s'.
  unfold subgroup_equiv in e.
  unfold subgroup_equiv.
  exact (sym e).
Qed.



Lemma subgroup_equiv_trans {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (s t u : Sub G P), subgroup_equiv R P s t -> subgroup_equiv R P t u -> subgroup_equiv R P s u.

Proof.
  intros s t u e1 e2.
  destruct s, t, u.
  unfold subgroup_equiv in e1, e2.
  unfold subgroup_equiv.
  exact (trans e1 e2).
Qed.



Instance subgroup_equiv_is_equiv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Equiv (subgroup_equiv R P)

:=
{
  refl  := subgroup_equiv_refl;
  sym   := subgroup_equiv_sym;
  trans := subgroup_equiv_trans;
}.



Definition subgroup_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Sub G P

:= existT _ @ id @ contains_id.



Definition subgroup_mult {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Sub G P -> Sub G P -> Sub G P

:= 
  fun a b => 
    match a with
    | existT _ u p =>
      match b with
      | existT _ v q =>
          existT _ 
            @ u # v 
            $ closed_under_mult u v p q
      end
    end.



Lemma subgroup_mult_well_def {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (a a' b b' : Sub G P), let R' := subgroup_equiv R P in

      R' a a' -> R' b b' -> R' (subgroup_mult a b) (subgroup_mult a' b').

Proof.
  intros a a' b b' R' e1 e2.
  destruct a, a', b, b'.
  unfold subgroup_mult, R', subgroup_equiv.
  simpl.
  unfold R', subgroup_equiv in e1, e2.
  exact (mult_well_def e1 e2).
Qed.



Lemma subgroup_mult_assoc {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (a b c : Sub G P), 
      let m  := subgroup_mult  in
      let R' := subgroup_equiv R P in

      R' (m a (m b c)) (m (m a b) c).

Proof.
  intros a b c m R'.
  destruct a, b, c.
  unfold subgroup_mult, m, R', subgroup_equiv.
  simpl.
  exact assoc.
Qed.



Lemma subgroup_left_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P), subgroup_equiv R P (subgroup_mult subgroup_id g) g.

Proof.
  intro.
  destruct g.
  unfold subgroup_equiv, subgroup_mult, subgroup_id.
  simpl.
  exact (left_id x).
Qed.



Lemma subgroup_right_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P), subgroup_equiv R P (subgroup_mult g subgroup_id) g.

Proof.
  intro.
  destruct g.
  unfold subgroup_equiv, subgroup_mult, subgroup_id.
  simpl.
  exact (right_id x).
Qed.



Definition subgroup_inv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Sub G P -> Sub G P

:=
  fun a =>
    match a with
    | existT _ u p =>
        existT _
          @ u*
          @ closed_under_inv u p
    end.



Lemma subgroup_inv_well_def {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (a a' : Sub G P), subgroup_equiv R P a a' -> subgroup_equiv R P (subgroup_inv a) (subgroup_inv a').

Proof.
  intros a a' e.
  destruct a, a'.
  unfold subgroup_equiv, subgroup_inv.
  simpl.
  unfold subgroup_equiv, subgroup_inv in e.
  exact (inv_well_def e).
Qed.



Lemma subgroup_left_inv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P), subgroup_equiv R P (subgroup_mult (subgroup_inv g) g) subgroup_id.

Proof.
  intro.
  destruct g.
  unfold subgroup_equiv, subgroup_mult, subgroup_inv, subgroup_id.
  simpl.
  exact (left_inv x).
Qed.



Instance subgroup_is_group {G : Type} (R : G -> G -> Prop) (P : G -> Prop) `{Subgroup G R P}

  : Group (Sub G P) (subgroup_equiv R P)

:=
{
  id   := subgroup_id;
  mult := subgroup_mult;
  inv  := subgroup_inv;

  assoc := subgroup_mult_assoc;

  left_id  := subgroup_left_id;
  right_id := subgroup_right_id;

  left_inv := subgroup_left_inv;

  mult_well_def := subgroup_mult_well_def;
  inv_well_def  := subgroup_inv_well_def;
}.



Definition inc {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Sub G P -> G

:= 
  fun p =>
    match p with
    | existT _ u _ => u
    end.

Notation "[ g ]" := (inc g).



Lemma subgroup_inc_preserves_inv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P),  [g*] ~ [g]*.

Proof.
  intro.
  destruct g.
  simpl.
  exact (refl _).
Qed.



Lemma subgroup_inc_preserves_mult {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (a b : Sub G P), [a # b] ~ [a] # [b].

Proof.
  intros.
  destruct a, b.
  simpl.
  exact (refl _).
Qed.



Lemma subgroup_closed_under_inv_inc {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P), P [g*] <-> P ([g]*).

Proof.
  intro g.
  destruct g.
  simpl.
  split.
  - trivial.
  - trivial.
Qed.



Class Normal (G : Type) (R : G -> G -> Prop) (P : G -> Prop) `{Subgroup G R P} :=
{
  closed_under_conj : forall (n : G), P n -> forall (g : G), P (conj n g);
}.





(*==============================================================================*)
(* Quotient Groups                                                              *)
(*==============================================================================*)

Definition normal_equiv {G : Type} (R : G -> G -> Prop) (P : G -> Prop) `{Normal G R P}

  : G -> G -> Prop

:= 
  fun g g' => 
    exists (n n' : Sub G P), g # [n] ~ g' # [n'].



Lemma normal_equiv_refl {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (g : G), normal_equiv R P g g.

Proof.
  intro.
  exists id.
  exists id.
  exact (refl _).
Qed.



Lemma normal_equiv_sym {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a b : G), let N := normal_equiv R P in

      N a b -> N b a.

Proof.
  intros a b N.
  unfold normal_equiv in N.
  unfold N.
  simpl.
  intro e.
  destruct e, H3.
  exists x0, x.
  exact (sym H3).
Qed.



Lemma normal_equiv_trans {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a b c : G), let N := normal_equiv R P in 

      N a b -> N b c -> N a c.

Proof.
  intros a b c.
  simpl.
  intros e1 e2.
  destruct e1, e2.
  destruct H3, H4.
  unfold normal_equiv.
  exists (x # x1*).
  exists (x2 # x0*).
  destruct x, x0, x1, x2.
  simpl.
  simpl in H3, H4.
  apply (trans assoc).
  apply (rtrans $ sym $ assoc).
  apply (trans $ mult_well_def H3 $ refl $ x1*).
  apply (rtrans $ mult_well_def H4 $ refl $ x0*).
  apply (trans $ sym $ assoc).
  apply (rtrans assoc).
  apply mult_well_def.
  - exact (refl b).
  - exact (trans @ right_inv x1 @ sym (right_inv x0)).
Qed.



Instance normal_equiv_is_equiv {G : Type} (R : G -> G -> Prop) (P : G -> Prop) `{Normal G R P}

  : Equiv (normal_equiv R P)

:=
{
  refl  := normal_equiv_refl;
  sym   := normal_equiv_sym;
  trans := normal_equiv_trans;
}.



Lemma normal_equiv_assoc {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a b c : G), let N := normal_equiv R P in

      N (a # (b # c)) ((a # b) # c).

Proof.
  intros.
  unfold N, normal_equiv.
  exists subgroup_id, subgroup_id.
  simpl.
  apply mult_well_def.
  exact assoc.
  exact (refl id).
Qed.



Lemma normal_equiv_left_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a : G), normal_equiv R P (id # a) a.

Proof.
  intro a.
  unfold normal_equiv.
  exists subgroup_id, subgroup_id.
  simpl.
  apply mult_well_def.
  - exact (left_id a).
  - exact (refl id).
Qed.



Lemma normal_equiv_right_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a : G), normal_equiv R P (a # id) a.

Proof.
  intro a.
  unfold normal_equiv.
  exists subgroup_id, subgroup_id.
  simpl.
  apply mult_well_def.
  - exact (right_id a).
  - exact (refl id).
Qed.



Lemma normal_equiv_left_inv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a : G), normal_equiv R P (a* # a) id.

Proof.
  intro a.
  unfold normal_equiv.
  exists subgroup_id, subgroup_id.
  simpl.
  apply mult_well_def.
  - exact (left_inv a).
  - exact (refl id).
Qed.



Lemma normal_equiv_mult_well_def {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a a' b b' : G), let N := normal_equiv R P in

      N a a' -> N b b' -> N (a # b) (a' # b').

Proof.
  intros a a' b b'.
  simpl.
  intros e1 e2.
  destruct e1, e2, H3, H4.
  unfold normal_equiv.
  set (u  := [x0] # [x2]*).
  set (u' := conj ([x1] # [x]*) (b' *)).
  destruct x, x0, x1, x2.
  simpl in H3, H4, u, u'.
  set (q := closed_under_mult x0 (x2*) p0 (closed_under_inv x2 p2)).
  exists (existT _ u q).
  set (q' := closed_under_conj (x1 # x*) (closed_under_mult x1 (x*) p1 (closed_under_inv x p)) (b' *)).
  exists (existT _ u' q').
  simpl.
  unfold u, u', conj.

  apply (trans $ sym assoc).
  apply (trans $ mult_well_def @ refl a @ assoc).
  apply (trans $ mult_well_def @ refl a $ mult_well_def @ H4 @ refl (x2*)).
  apply (trans $ sym $ mult_well_def @ refl a @ assoc).
  apply (trans assoc).
  apply (trans $ mult_well_def @ refl _ @ right_inv x2).
  apply (trans $ right_id _).
  apply (rtrans $ sym $ assoc).
  apply (rtrans $ sym $ assoc).
  apply shift_right.
  apply (trans $ sym assoc).
  apply (trans $ mult_well_def @ refl a @ right_inv b').
  apply (trans $ right_id a).
  apply (rtrans $ sym assoc).
  apply shift_right.
  apply (trans H3).
  apply mult_well_def.
  - apply (rtrans assoc).
    apply (rtrans $ sym $ mult_well_def @ refl a' @ right_inv b').
    exact (sym $ right_id a').
  - exact (refl x1).
Qed.



Lemma normal_equiv_inv_well_def {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a a' : G), let N := normal_equiv R P in

      N a a' -> N (a*) (a'*).

Proof.
  intros a a'.
  simpl.
  intro e.
  destruct e, H3.
  unfold normal_equiv.
  set (u  := a # [x]* # a*).
  set (u' := a' # [x0]* # a'*).
  destruct x, x0.
  simpl in H3, u, u'.
  set (q  := closed_under_conj (x*) (closed_under_inv x p) a).
  set (q' := closed_under_conj (x0*) (closed_under_inv x0 p0) a').
  exists (existT _ u q).
  exists (existT _ u' q').
  unfold u, u', q, q'; simpl.
  apply (trans assoc).
  apply (rtrans $ sym assoc).
  apply mult_well_def.
  - exact (trans @ left_inv a @ (sym @ left_inv a')).
  - apply (trans $ sym $ inv_mult _ _).
    apply (rtrans $ inv_mult _ _).
    apply inv_well_def.
    exact H3.
Qed.



Definition Quotient (G : Type) (R : G -> G -> Prop) (P : G -> Prop) `{Normal G R P}

  := G.



Instance quotient_group {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : @Group (Quotient G R P) (normal_equiv R P) (normal_equiv_is_equiv R P)

:=
{
  id  := id;
  inv := inv;
  mult := mult;

  assoc := normal_equiv_assoc;

  left_id  := normal_equiv_left_id;
  right_id := normal_equiv_right_id;

  left_inv := normal_equiv_left_inv;

  inv_well_def := normal_equiv_inv_well_def;
  mult_well_def := normal_equiv_mult_well_def;
}.



(*==============================================================================*)
(* Group Homomorphisms                                                          *)
(*==============================================================================*)

Class GrpHom {G G' : Type} (R : G -> G -> Prop) (R' : G' -> G' -> Prop) (h : G -> G') `{Group G R, Group G' R'}
:=
{
  (* conditions *)

  hom_well_def : forall {a b : G}, a ~ b -> h a ~ h b;

  preserves_id : h id ~ id;

  break : forall {a b : G}, h (a # b) ~ h a # h b;
}.



Definition dom {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}
  := G.



Definition cod {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h} 
  := G'.



Lemma hom_preserves_inv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (x : G), h (x*) ~ (h x)*.

Proof.
  intro.
  apply (right_cancel @ h x).
  apply (rtrans $ sym $ left_inv _).
  apply (trans $ sym $ break).
  apply (rtrans $ preserves_id).
  apply hom_well_def.
  exact (left_inv x).
Qed.



Definition is_in_image {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : G' -> Prop

:= fun g' => exists g : G, h g ~ g'.



Definition image {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  := Sub G' (is_in_image h).



Lemma image_contains_images {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall g : G, is_in_image h (h g).

Proof.
  intro g.
  exists g.
  exact (refl @ h g).
Qed.



Lemma image_contains_id {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : is_in_image h id.

Proof.
  unfold is_in_image.
  exists id.
  exact preserves_id.
Qed.



Lemma image_closed_under_equiv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (a b : G'), a ~ b -> is_in_image h a -> is_in_image h b.

Proof.
  intros a b p.
  unfold is_in_image.
  intro i.
  destruct i.
  exists x.
  apply (rtrans p).
  exact H4.
Qed.



Lemma image_closed_under_mult {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (a b : G'), is_in_image h a -> is_in_image h b -> is_in_image h (a # b).

Proof.
  intros a b.
  unfold is_in_image.
  intros ia ib.
  destruct ia, ib.
  exists (x # x0).
  apply (trans break).
  apply mult_well_def.
  - exact H4.
  - exact H5.
Qed.



Lemma image_closed_under_inv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (a : G'), is_in_image h a -> is_in_image h (a*).

Proof.
  intro a.
  unfold is_in_image.
  intros i.
  destruct i.
  exists (x*).
  apply (trans $ hom_preserves_inv h x).
  apply inv_well_def.
  exact H4.
Qed.



Instance image_is_subgroup {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : Subgroup G' R' (is_in_image h)

:=
{
  contains_id        := image_contains_id h;

  closed_under_equiv := image_closed_under_equiv h;
  closed_under_mult  := image_closed_under_mult h;
  closed_under_inv   := image_closed_under_inv h;
}.



Definition restrict_cod {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : G -> image h

:= 
  fun g : G => 
    existT (fun x => is_in_image h x)
      @ h g 
      @ image_contains_images h g.



Lemma restrict_cod_preserves_id {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : subgroup_equiv R' (is_in_image h) (restrict_cod h id) subgroup_id.

Proof.
  unfold subgroup_equiv, is_in_image, restrict_cod, subgroup_id.
  simpl.
  exact preserves_id.
Qed.



Lemma restrict_cod_break {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let S  := subgroup_equiv R' (is_in_image h) in
    let h' := restrict_cod h in

    forall (x y : G), S (h' (x # y)) (subgroup_mult (h' x) (h' y)).

Proof.
  intros.
  unfold S, h', subgroup_equiv, is_in_image, restrict_cod, subgroup_mult; simpl.
  exact break.
Qed.



Lemma restrict_cod_well_def {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let S  := subgroup_equiv R' (is_in_image h) in
    let h' := restrict_cod h in

    forall (x y : G), x ~ y -> S (h' x) (h' y).

Proof.
  intros S h' x y p.
  unfold S, h', subgroup_equiv, is_in_image, restrict_cod, subgroup_mult; simpl.
  exact (hom_well_def p).
Qed.



Instance restrict_cod_is_hom {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : @GrpHom G (image h) R (subgroup_equiv R' (is_in_image h)) (restrict_cod h) 
      H 
      H0 
      subgroup_equiv_is_equiv 
      (subgroup_is_group R' (is_in_image h))

:= 
{
  hom_well_def := @restrict_cod_well_def G G' R R' h H H0 H1 H2 H3;
  preserves_id  := @restrict_cod_preserves_id G G' R R' h H H0 H1 H2 H3;
  break        := @restrict_cod_break G G' R R' h H H0 H1 H2 H3;
}.



Definition is_in_kernel {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : G -> Prop

:= fun g => h g ~ id.



Definition kernel {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  := Sub G (is_in_kernel h).



Lemma kernel_contains_id {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : is_in_kernel h id.

Proof.
  unfold is_in_kernel.
  exact preserves_id.
Qed.



Lemma kernel_closed_under_equiv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall {a b : G}, a ~ b -> is_in_kernel h a -> is_in_kernel h b.

Proof.
  intros a b p.
  unfold is_in_kernel.
  intro e.
  apply sym.
  apply (trans $ sym e).
  apply hom_well_def.
  exact p.
Qed.



Lemma kernel_closed_under_mult {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall {a b : G}, is_in_kernel h a -> is_in_kernel h b -> is_in_kernel h (a # b).

Proof.
  intros a b.
  unfold is_in_kernel.
  intros e1 e2.
  apply (rtrans $ left_id id).
  apply (rtrans $ mult_well_def e1 e2).
  exact break.
Qed.



Lemma kernel_closed_under_inv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall {a : G}, is_in_kernel h a -> is_in_kernel h (a*).

Proof.
  intro a.
  unfold is_in_kernel.
  intro e.
  apply (trans $ hom_preserves_inv h a).
  apply (rtrans inv_id).
  apply inv_well_def.
  exact e.
Qed.



Instance kernel_is_subgroup {G G' : Type} (R : G -> G -> Prop) (R' : G' -> G' -> Prop) (h : G -> G') `{GrpHom G G' R R' h}

  : Subgroup G R (is_in_kernel h)

:=
{
  contains_id := kernel_contains_id h;

  closed_under_equiv := @kernel_closed_under_equiv G G' R R' h H H0 H1 H2 H3;
  closed_under_mult  := @kernel_closed_under_mult G G' R R' h H H0 H1 H2 H3;
  closed_under_inv   := @kernel_closed_under_inv G G' R R' h H H0 H1 H2 H3;
}.



Lemma kernel_closed_under_conj {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (a : G), is_in_kernel h a -> forall (g : G), is_in_kernel h (conj a g).

Proof.
  unfold is_in_kernel.
  intros a p g.
  unfold conj.
  apply (trans break).
  apply (trans $ mult_well_def @ refl (h g) @ break).
  apply (trans $ mult_well_def @ refl (h g) $ mult_well_def @ p @ refl _).
  apply (trans $ mult_well_def @ refl (h g) $ left_id _).
  apply (trans $ mult_well_def @ refl (h g) @ hom_preserves_inv h g).
  exact (right_inv _).
Qed.



Instance kernel_is_normal {G G' : Type} (R : G -> G -> Prop) (R' : G' -> G' -> Prop) (h : G -> G') `{GrpHom G G' R R' h}

  : Normal G R (is_in_kernel h)

:=
{
  closed_under_conj := kernel_closed_under_conj h;
}.



Definition hom_equiv {G G' : Type} (R : G -> G -> Prop) {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  := normal_equiv R (is_in_kernel h).



Instance hom_equiv_is_equiv {G G' : Type} (R : G -> G -> Prop) {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : Equiv (hom_equiv R h)

:= normal_equiv_is_equiv R (is_in_kernel h).



Definition HomQuotient {G G' : Type} (R : G -> G -> Prop) {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  := @Quotient G R (is_in_kernel h) 
        H 
        H0 
        (kernel_is_subgroup R R' h) 
        (kernel_is_normal R R' h).





(*==============================================================================*)
(* First Isomorphism Theorem                                                    *)
(*==============================================================================*)

Class GrpAut (G G' : Type) (R : G -> G -> Prop) (R' : G' -> G' -> Prop) (h : G -> G') `{GrpHom G G' R R' h} :=
{
  injective : forall {x y : G}, h x ~ h y -> x ~ y;

  surjective : forall z : G', exists x : G, h x ~ z;
}.



Lemma group_aut_kernel_is_unitary {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpAut G G' R R' h}

  : forall x : G, is_in_kernel h x -> x ~ id.

Proof.
  unfold is_in_kernel.
  intros x p.
  apply injective.
  apply (rtrans $ sym $ preserves_id).
  exact p.
Qed.



Definition isomorphic (G : Type) (R : G -> G -> Prop) (G' : Type) (R' : G' -> G' -> Prop) `{Group G R, Group G' R'}

  := {h : G -> G' & {e : GrpHom R R' h & GrpAut G G' R R' h}}.



Lemma quotient_to_image_well_def {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let K  := hom_equiv R h  in
    let S  := subgroup_equiv R' (is_in_image h) in

    forall (x y : G), K x y -> S (h' x) (h' y).

Proof.
  intros h' K S x y p.
  unfold S, subgroup_equiv.
  simpl.
  apply (right_cancel id).
  unfold K, hom_equiv, normal_equiv, is_in_kernel, Sub in p.
  destruct p, x0, H4, x1.
  simpl in H4.
  apply (trans $ sym $ mult_well_def @ refl (h x) @ e).
  apply (rtrans $ mult_well_def @ refl (h y) @ e0).
  apply (trans $ sym break).
  apply (rtrans break).
  exact (hom_well_def H4).
Qed.



Lemma quotient_to_image_preserves_id {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let S := subgroup_equiv R' (is_in_image h) in

    S (h' id) subgroup_id.

Proof.
  intros h' S.
  unfold S, subgroup_equiv, subgroup_id, restrict_cod; simpl.
  exact preserves_id.
Qed.



Lemma quotient_to_image_break {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let S  := subgroup_equiv R' (is_in_image h) in
    let m  := subgroup_mult in

    forall (x y : G), S (h' (x # y)) (m (h' x) (h' y)).

Proof.
  intros h' S m x y.
  unfold S, h', m, subgroup_equiv, subgroup_mult, restrict_cod; simpl.
  exact break.
Qed.



Instance quotient_to_image_is_hom {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : GrpHom (hom_equiv R h) (subgroup_equiv R' (is_in_image h)) (restrict_cod h)

:=
{
  hom_well_def := @quotient_to_image_well_def G G' R R' h H H0 H1 H2 H3;
  preserves_id := @quotient_to_image_preserves_id G G' R R' h H H0 H1 H2 H3;
  break        := @quotient_to_image_break G G' R R' h H H0 H1 H2 H3;
}.



Lemma quotient_to_image_injective {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let K  := hom_equiv R h  in
    let S  := subgroup_equiv R' (is_in_image h) in

    forall (x y : G), S (h' x) (h' y) -> K x y.

Proof.
  intros h' K p x y.
  unfold h', K, hom_equiv, subgroup_equiv; simpl.
  intro q.
  unfold normal_equiv, is_in_kernel, Sub.
  assert (is_in_kernel h (x* # y)).
  - unfold is_in_kernel.
    apply (trans break).
    apply (trans $ mult_well_def @ hom_preserves_inv h x @ refl (h y)).
    apply (trans $ mult_well_def @ (inv_well_def q) @ refl (h y)).
    exact (left_inv _).
  - exists (existT _ (x* # y) H4).
    exists (existT _ id (kernel_contains_id h)).
    simpl.
    apply (rtrans $ sym $ right_id y).
    apply (trans assoc).
    apply (trans $ mult_well_def @ right_inv x @ refl y).
    exact (left_id y).
Qed.



Lemma quotient_to_image_surjective {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let K  := hom_equiv R h  in
    let S  := subgroup_equiv R' (is_in_image h) in

    forall (z : image h), exists x : G, S (h' x) z.

Proof.
  intros h' K S z.
  destruct z, i; simpl.
  exists x0.
  exact e.
Qed.



Instance quotient_to_image_is_aut {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : GrpAut G (image h) (hom_equiv R h) (subgroup_equiv R' (is_in_image h)) 
      (restrict_cod h)

:=
{
  injective  := quotient_to_image_injective h;
  surjective := quotient_to_image_surjective h;
}.



Theorem first_iso_theorem {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let K  := hom_equiv R h  in
    let S  := subgroup_equiv R' (is_in_image h) in

    isomorphic 
      (HomQuotient R h) K 
      (image h) S.

Proof.
  intros h' K S.
  unfold isomorphic.
  unfold HomQuotient.
  unfold Quotient.
  exists h'.
  exists (quotient_to_image_is_hom h).
  exact (quotient_to_image_is_aut h).
Qed.





(*==============================================================================*)
(* Free Groups                                                                  *)
(*==============================================================================*)




























