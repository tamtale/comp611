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

Axiom func_extensionality: forall (A B:Type) (f g: A -> B),
  (f ~~ g) -> f = g.

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

Lemma compose_assoc_ext :
  forall {A B C D: Type} (f: A -> B) (g: B -> C) (h: C -> D),
    ((f;; g);; h) = (f;; (g;; h)).
Proof.
intros.
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
  forall {A: Type}, map (@id A) ~~ @id (list A).
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
  FId := @map_id;
  FCompose := @map_compose
|}.

Record Monad: Type :=
mkMonad
  {
    M: Functor;
    Eta{A: Type}: A -> FObj M A;
    Mu: forall {A: Type}, FObj M (FObj M A) -> FObj M A;
    MuNatural : forall {A: Type}, 
      FMorph M (@Mu A) ;; Mu ~~ Mu ;; Mu;
    EtaNatural1 : forall {A: Type}, @Eta(FObj M A) ;; Mu ~~ @id(FObj M A);
    EtaNatural2 : forall {A: Type}, FMorph M (@Eta A) ;; (Mu) ~~ @id(FObj M A)
  }.

Fixpoint concat {A: Type} (xs ys: list A): list A := 
  match xs with
  | nil => ys
  | cons xs_first xs_rest => cons xs_first (concat xs_rest ys)
  end.

Lemma nil_right_concat_ident :
  forall {A: Type} (xs: list A),
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
  forall {A: Type} (xs: list A),
    concat nil xs = xs.
Proof. reflexivity. Qed.


Fixpoint flatten {A: Type} (xs: list (list A)): list A := 
  match xs with
  | nil => nil
  | cons xs_first xs_rest => concat xs_first (flatten xs_rest)
  end.

Lemma concat_assoc:
  forall {A: Type} (xs ys zs: list A),
  concat xs (concat ys zs) = concat (concat xs ys) zs.
Proof. induction xs as [| first_xs rest_xs IH].
  + reflexivity.
  + simpl. destruct ys as [| first_ys rest_ys].
    - simpl. rewrite -> nil_right_concat_ident. reflexivity.
    - simpl. destruct zs as [| first_zs rest_zs].
      * simpl. repeat rewrite -> nil_right_concat_ident. reflexivity.
      * rewrite <- IH. reflexivity.
Qed.

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
    destruct first_x as [| first_first_x rest_first_x].
    * simpl. 
      rewrite <- IH2.
      reflexivity.
    * simpl.
      rewrite <- IH2.
      rewrite <- IH.
      destruct rest_x as [| first_rest_x rest_rest_x].
      ++ simpl.
         rewrite -> nil_right_concat_ident. 
         reflexivity.
      ++ simpl.
         rewrite -> IH.
         destruct rest_rest_x as [| f_r_r_x r_r_r_x].
         +++ simpl. 
             rewrite -> nil_right_concat_ident.
             rewrite -> concat_assoc.
             reflexivity.
        +++ simpl. repeat rewrite -> concat_assoc. reflexivity. 
Qed.

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

Record KleisliTriple: Type :=
mkTriple {
  T: Type -> Type;
  Unit(A: Type): A -> T(A);
  Bind: forall {A B: Type}(f: A -> T(B)), T(A) -> T(B);
  UnitReturn(A: Type): (Bind (Unit A)) ~~ @id(T A);
  UnitComposeReturn(A B: Type): forall (f: A -> T(B)), 
    Unit A ;; Bind f ~~ f;
  BindProp(A B C: Type): forall (f: A -> T(B)) (g: B -> T(C)),
    Bind (f ;; (Bind g)) ~~ (Bind f) ;; (Bind g);
  Mult{A: Type}: T(T(A)) -> T(A) := Bind (@id (T A))
}.

Definition fmorph_from_triple (kt: KleisliTriple) {A B: Type} (f: A -> B): (T kt A -> T kt B) :=
(Bind kt) (f ;; @Unit kt B).


Lemma fid_from_triple(kt: KleisliTriple): forall {A: Type}, @fmorph_from_triple kt A A id ~~ id.
Proof. 
intros. 
unfold fmorph_from_triple. 
unfold equiv.
intros a.
rewrite id_step.
cut (Bind kt (id ;; Unit kt A) ~~ Bind kt (Unit kt A)).
- unfold equiv.
  intros.
  rewrite -> H.
  rewrite -> UnitReturn.
  reflexivity.
- unfold equiv.
  intros.
  repeat rewrite -> UnitReturn.
  reflexivity.
Qed.


Lemma fcompose_from_triple(kt: KleisliTriple): forall (A B C: Type) (f: A -> B) (g: B -> C),
  fmorph_from_triple kt (f ;;g) ~~ fmorph_from_triple kt f ;; fmorph_from_triple kt g.
Proof. 
intros. 
unfold fmorph_from_triple. 
unfold equiv.
intros.
rewrite <- BindProp.
cut (((f;; Unit kt B);; Bind kt (g;; Unit kt C)) = (f;; (Unit kt B;; Bind kt (g;; Unit kt C)))).
+ intros. 
  rewrite H.
  cut ((Unit kt B;;Bind kt (g;; Unit kt C)) = (g;;Unit kt C)).
  - intros.
    rewrite H0.
    reflexivity.
  - cut ((Unit kt B;; Bind kt (g;; Unit kt C)) ~~ (g;; Unit kt C)).
    * intros. apply func_extensionality. apply H0.
    * apply UnitComposeReturn.
+ cut (((f;; Unit kt B);; Bind kt (g;; Unit kt C)) ~~ (f;; Unit kt B;; Bind kt (g;; Unit kt C))).
  - apply func_extensionality.
  - apply compose_assoc.  
Qed.


Definition mu_from_triple (kt: KleisliTriple) {A: Type}: (T kt (T kt A)) -> T kt A :=
Bind kt (@id (T kt A)).

Lemma mu_natural_from_triple (kt: KleisliTriple): forall (A: Type),
  (fmorph_from_triple kt) (@mu_from_triple kt A) ;; mu_from_triple kt ~~ 
  mu_from_triple kt ;; mu_from_triple kt.
Proof. 
  intros.
  unfold fmorph_from_triple.
  unfold mu_from_triple.
  unfold equiv.
  intros.
  rewrite <- BindProp.
  cut (((Bind kt id;; Unit kt (T kt A));; Bind kt id) = (Bind kt id;; (Unit kt (T kt A);; Bind kt id))).
  + intros.
    rewrite -> H.
    repeat rewrite -> compose_step.
    cut ((Unit kt (T kt A);; Bind kt id) = id).
    - intros H0.
    rewrite H0. 
    cut ((@Bind kt (T kt (T kt A)) A (Bind kt id;; id)) ~~ (Bind kt id ;; Bind kt id)).
    * intros.
      cut ((Bind kt id (Bind kt id a)) = (Bind kt id ;; Bind kt id) a).
      ++ intros. rewrite H2. 
         cut (forall (b: T kt (T kt (T kt A))), Bind kt (Bind kt id;; id) b = (Bind kt id;; Bind kt id) b).
         -- intros. apply H3.
         -- apply BindProp.
      ++ cut (forall (b: T kt (T kt (T kt A))), Bind kt id (Bind kt id b) = (Bind kt id;; Bind kt id) b).
         -- intros.  apply H2.
         -- cut (forall c: (T kt (T kt (T kt A))), Bind kt id (Bind kt id c) = (Bind kt id;; Bind kt id) c) .
            ** intros. apply H2.
            ** intros. rewrite compose_step. reflexivity.
    * apply BindProp.
  - cut ((@id (T kt A) = Bind kt (Unit kt A))).
     * intros. 
       cut ((Unit kt (T kt A);; Bind kt id) ~~ id).
       ++ intros. apply func_extensionality. apply H1.
       ++ apply UnitComposeReturn.
     * cut (id ~~ Bind kt (Unit kt A)) .
       ++ apply func_extensionality.
       ++ unfold equiv. symmetry.
          cut (forall b: T kt A, Bind kt (Unit kt A) b = id b).
          -- intros. apply H0.
          -- intros. apply UnitReturn.
  + cut (((Bind kt id;; Unit kt (T kt A));; Bind kt id) ~~(Bind kt id;; Unit kt (T kt A);; Bind kt id)).
  - intros. apply func_extensionality. apply H.
  - apply compose_assoc.
Qed.

Lemma eta_natural_from_triple_1 (kt: KleisliTriple): forall (A: Type),
(@Unit kt (T kt A)) ;; mu_from_triple kt ~~ @id (T kt A).
Proof. intros. unfold mu_from_triple. apply UnitComposeReturn.
Qed.

Lemma eta_natural_from_triple_2 (kt: KleisliTriple): forall (A: Type),
(fmorph_from_triple kt) (Unit kt A) ;; mu_from_triple kt ~~ id.
Proof. unfold fmorph_from_triple. unfold mu_from_triple.
  unfold equiv.
  intros.
  cut ((Bind kt (Unit kt A;; Unit kt (T kt A));; Bind kt id) = Bind kt ((Unit kt A;; Unit kt (T kt A));; Bind kt id)).
  + intros. rewrite H. 
    cut (((Unit kt A;; Unit kt (T kt A));; Bind kt id) = (Unit kt A;; (Unit kt (T kt A);; Bind kt id))).
    - intros. 
      rewrite H0.  
      cut ((Unit kt (T kt A);; Bind kt id) = id).
      * intros. 
        rewrite H1. 
        cut ((Unit kt A;; id) = Unit kt A).
        ++ intros. rewrite H2. rewrite UnitReturn. reflexivity.
        ++ cut ((Unit kt A;; id) ~~ Unit kt A) .
           -- intros. apply func_extensionality. apply H2.
           -- apply compose_id_r.
      * cut ((Unit kt (T kt A);; Bind kt id) ~~ id).
        ++ intros. apply func_extensionality. apply H1.
        ++ apply UnitComposeReturn.
    - apply compose_assoc_ext.
  + cut ((Bind kt (Unit kt A;; Unit kt (T kt A));; Bind kt id) ~~ Bind kt ((Unit kt A;; Unit kt (T kt A));; Bind kt id)).
    - intros. apply func_extensionality. apply H.
    - remember (Unit kt A;; Unit kt (T kt A)) as f.
      remember id as g.
      unfold equiv. symmetry. apply BindProp.
Qed.

(*Definitions for Ringads.*)

Class MZero `(m: Monad) : Type := {
  Zero{A: Type}: FObj (M m) A;
  MuDistributesZero: forall {A: Type}, Mu m (@Zero (FObj (M m) A)) = Zero
}.
Class MPlus `(m: Monad): Type := {
  Plus{A: Type}: FObj (M m) A -> FObj (M m) A -> FObj (M m) A; 
  MuDistributesPlus: forall {A: Type} (x y: FObj (M m) (FObj (M m) A)), Mu m (Plus x y) = Plus (Mu m x) (Mu m y)
}.

Class Ringad `(m: Monad, mzero: MZero(m), mplus: MPlus(m)): Type := {
  MZeroUnit: forall {A: Type} (xs: FObj (M m) A), 
    (Plus xs Zero = xs) /\ (Plus Zero xs = xs)
}.

Lemma flatten_nil: forall (A: Type), Mu ListM (@nil (list A)) = @nil A.
Proof. intuition. Qed.

Instance listZero: MZero(ListM):= {
  Zero{A: Type} := @nil A;
  MuDistributesZero := flatten_nil
}.


Lemma flatten_distributes_concat: forall (A : Type) (xs ys : FObj (M ListM) (FObj (M ListM) A)),
Mu ListM (concat xs ys) = concat (Mu ListM xs) (Mu ListM ys).
Proof. 
intros. simpl. 
induction xs as [| first_xs rest_xs IH].
  + reflexivity.
  + induction ys as [| first_ys rest_ys IH2].
    - simpl. 
      repeat rewrite -> nil_right_concat_ident.
      reflexivity.
    - simpl. 
      rewrite -> concat_assoc. 
      induction first_xs as [|first_first_xs rest_first_xs IH3].
        * repeat rewrite -> nil_left_concat_ident. 
          rewrite <- concat_assoc.
          induction rest_xs as [|first_rest_xs rest_rest_xs IH4].
          ++ simpl. reflexivity.
          ++ induction first_ys as [|first_first_ys rest_first_ys IH5].
          Admitted. (* Do this later. *)

Instance listConcat: MPlus ListM := {
  Plus{A: Type} := @concat A;
  MuDistributesPlus := flatten_distributes_concat
}.


Lemma nil_concat_ident : forall (A : Type) (xs : FObj (M ListM) A),
Plus xs Zero = xs /\ Plus Zero xs = xs.
Proof. simpl. split.
+ apply nil_right_concat_ident.
+ apply nil_left_concat_ident.
Qed.

Instance list_ringad: Ringad ListM listZero listConcat := {
  MZeroUnit:= nil_concat_ident
}.

