Definition id {A: Type} (a: A) : A := a.

Lemma id_step :
  forall {A: Type} (a: A), id a = a.
Proof.
reflexivity.
Qed.

Definition equiv {A B: Type} (f g: A -> B) : Prop :=
  forall (a: A), f a = g a.

Notation "f ~~ g" := (equiv f g)
                     (at level 100, right associativity).

Definition compose {A B C: Type} (f: A -> B) (g: B -> C) : A -> C :=
  fun (a: A) => g (f a).

Lemma compose_step :
  forall {A B C: Type} (f: A -> B) (g: B -> C) (a: A),
    (compose f g) a = g (f a).
Proof.
reflexivity.
Qed.

Notation "f ;; g" := (compose f g)
                    (at level 80, right associativity).

Lemma compose_id_l :
  forall {A B: Type} (f: A -> B),
    (@id A);; f ~~ f.
Proof.
intros A B f a.
rewrite -> compose_step.
rewrite -> id_step.
reflexivity.
Qed.

Lemma compose_id_r :
  forall {A B: Type} (f: A -> B),
    f;; (@id B) ~~ f.
Proof.
intros A B F a.
rewrite -> compose_step.
rewrite -> id_step.
reflexivity.
Qed.

Lemma compose_assoc :
  forall {A B C D: Type} (f: A -> B) (g: B -> C) (h: C -> D),
    (f;; g);; h ~~ f;; (g;; h).
Proof.
intros A B C D f g h a.
repeat rewrite -> compose_step.
reflexivity.
Qed.

Record Functor : Type := mkFunctor {
  FObj : Type -> Type;
  FMorph : forall {A B: Type} (f: A -> B), FObj A -> FObj B;
  FId : forall (A: Type), FMorph (@id A) ~~ @id (FObj A);
  FCompose : forall (A B C: Type) (f: A -> B) (g: B -> C),
               FMorph (f;; g) ~~ (FMorph f);; (FMorph g)
}.

Inductive list (A: Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A}.

Fixpoint map {A B: Type} (f: A -> B) (l: list A) : list B :=
  match l with
  | nil => nil
  | cons a t => cons (f a) (map f t)
  end.

Lemma map_id :
  forall (A: Type), map (@id A) ~~ @id (list A).
Proof.
intros A a.
induction a as [| first rest IH].
 + rewrite -> id_step.
   reflexivity.
 + rewrite -> id_step.
   simpl.
   rewrite -> IH.
   repeat rewrite -> id_step.
   reflexivity.
Qed.

Lemma map_compose :
  forall {A B C: Type} (f: A -> B) (g: B -> C),
    map (f;; g) ~~ (map f);; (map g).
Proof.
intros.
intros a.
induction a as [| first rest IH].
+ reflexivity.
+ simpl.
  repeat rewrite -> IH.
  reflexivity.
Qed.

Definition ListF : Functor := {|
  FObj := list;
  FMorph := @map;
  FId := map_id;
  FCompose := @map_compose
|}.

Record Monad: Type :=
mkMonad
  {
    M: Functor;
    Eta(A: Type): A -> M.(FObj)(A);
    Mu(A: Type): M.(FObj)(M.(FObj)(A)) -> M.(FObj)(A);
    MuNatural : forall {A: Type}, 
      (M.(FMorph)(Mu A)) ;; (Mu A) ~~ (Mu (M.(FObj)(A))) ;; (Mu A);
    EtaNatural1 : forall {A: Type}, Eta(M.(FObj) A) ;; (Mu A) ~~ @id(M.(FObj) A);
    EtaNatural2 : forall {A: Type}, M.(FMorph)(Eta A) ;; (Mu A) ~~ @id(M.(FObj) A)
  }.

Fixpoint concat {A: Type} (xs ys: list A): list A := 
  match xs with
  | nil => ys
  | cons xs_first xs_rest => cons xs_first (concat xs_rest ys)
  end.

Lemma nil_right_concat_ident :
  forall (A: Type) (xs: list A),
    concat xs nil = xs.
Proof. 
intros.
induction xs as [|first rest IH].
+ reflexivity.
+ simpl.
  rewrite -> IH.
  reflexivity.
Qed.

Lemma nil_left_concat_ident :
  forall (A: Type) (xs: list A),
    concat nil xs = xs.
Proof. reflexivity. Qed.

Lemma concat_assoc :
  forall (A: Type) (xs ys zs: list A),
    concat (concat xs ys) zs = concat xs (concat ys zs).
Proof. induction xs as [|first_x rest_x IH].
  + reflexivity.
  + simpl. rewrite <- IH.
Qed.


Fixpoint flatten {A: Type} (xs: list (list A)): list A := 
  match xs with
  | nil => nil
  | cons xs_first xs_rest => concat xs_first (flatten xs_rest)
  end.

Lemma flatten_natural :
  forall {A: Type} (xs: list (list (list A))),
    (map flatten ;; flatten) xs = (flatten ;; flatten) xs.
Proof.
intros. 
repeat rewrite -> compose_step.
induction xs as [|first_xs rest_xs IH].
+ reflexivity.
+ simpl.
  rewrite -> IH.
  induction first_xs as [|first_x rest_x IH2].
  - reflexivity.
  - simpl.
    induction first_x as [| first_first_x rest_first_x IH3].
    * simpl. 
      rewrite <- IH2.
      reflexivity.
    * simpl.
      rewrite <- IH2.
      rewrite <- IH.
      induction rest_x as [| first_rest_x rest_rest_x IH4].
      ++ simpl.
         rewrite -> nil_right_concat_ident. 
         reflexivity.
      ++ simpl.
         rewrite -> IH.
         induction rest_rest_x as [| f_r_r_x r_r_r_x IH5].
         +++ simpl. rewrite -> nil_right_concat_ident. simpl.

Definition cons_simp {A: Type} (x: A) := cons x nil.

Lemma cons_natural_1 :
  forall {A: Type} (xs: list A),
    (cons_simp ;; flatten) xs = xs.
Proof. 
intros.
rewrite -> compose_step.
simpl.
induction xs as [| first rest IH].
+ reflexivity.
+ simpl.
  rewrite -> nil_right_concat_ident.
  reflexivity. 
Qed.

Lemma cons_natural_2 :
  forall {A: Type} (xs: list A),
    ((map cons_simp) ;; flatten) xs = xs.
Proof.
intros.
rewrite -> compose_step.
induction xs as [| first rest IH].
+ reflexivity.
+ simpl.
  rewrite -> IH.
  reflexivity.
Qed.

Definition ListM: Monad := {|
  M := ListF;
  Eta(A: Type):= cons_simp;
  Mu(A: Type)(xs: list(list(A))) := flatten xs;
  MuNatural := @flatten_natural;
  EtaNatural1 := @cons_natural_1;
  EtaNatural2 := @cons_natural_2
|}.

Print ListM.