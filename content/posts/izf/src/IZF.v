Require Import Program.

Create HintDb zf.

Module Type IZF.
  Parameter set : Type.

  Notation "A ≡ B" := (A = B) (at level 70).
  Axiom K : forall {x y: set} (p p0: x ≡ y), p = p0.

  Parameter member : set -> set -> Prop.
  Notation "A ∈ B" := (member A B) (at level 70).
  Parameter equiv_ext :
    forall {x y}, (forall {z}, z ∈ x <-> z ∈ y) -> x ≡ y.
  Notation "A ∉ B" := (A ∈ B -> False) (at level 70).
  Hint Resolve equiv_ext : zf.
  Axiom M : forall {x y} (p p0: x ∈ y), p = p0.

  Definition subset A B := forall x, x ∈ A -> x ∈ B.
  Notation "A ⊆ B" := (subset A B) (at level 70).

  Parameter empty : set.
  Notation "∅" := empty.
  Parameter empty_prop : forall {x}, x ∉ ∅.
  Hint Resolve empty_prop : zf.

  Parameter insert : set -> set -> set.
  Notation "x +> y" := (insert x y) (at level 60).
  Parameter insert_propH :
    forall {x y z}, z ∈ x +> y -> z ∈ y \/ z ≡ x.
  Parameter insert_propG :
    forall {x y z}, z ∈ y \/ z ≡ x -> z ∈ x +> y.
  Hint Resolve insert_propH insert_propG : zf.
  
  Parameter union : set -> set.
  Notation "⋃ X" := (union X) (at level 60).
  Parameter union_propG :
    forall {x z}, (exists y, y ∈ x /\ z ∈ y) -> z ∈ ⋃x.
  Parameter union_propH :
    forall {x z}, z ∈ ⋃x -> exists y, y ∈ x /\ z ∈ y.
  Hint Resolve union_propH union_propG : zf.

  Definition ordered_pair x y :=
    insert (insert x ∅) (insert (insert x (insert y ∅)) ∅).
  Notation "⟨ x , y ⟩" := (ordered_pair x y).

  Definition Suc x := x +> x.
  
  Parameter infinity : set.
  Notation "'ω'" := infinity (at level 60).
  Parameter infinity_propZ : ∅ ∈ ω.
  Parameter infinity_propS :
    forall {x}, x ∈ ω -> Suc x ∈ ω.
  Hint Resolve infinity_propZ infinity_propS : zf.

  Parameter selection : (set -> Prop) -> set -> set.
  Parameter selection_propH : forall {P x y},
      x ∈ selection P y -> x ∈ y /\ P x.
  Parameter selection_propG : forall {P x y},
      x ∈ y /\ P x -> x ∈ selection P y.
  Hint Resolve selection_propH selection_propG : zf.
  
  Definition formula {D} := {P: set -> set -> Prop | forall x, x ∈ D -> exists y, P x y}.
  
  Parameter collection : forall {D}, @formula D -> set.
  Parameter collection_propH : forall {D P x},
      x ∈ @collection D P -> exists i, i ∈ D /\ proj1_sig P i x.
  Parameter collection_propG : forall {D P x},
      (exists i, i ∈ D /\ proj1_sig P i x) -> x ∈ @collection D P.
  Hint Resolve collection_propH collection_propG : zf.

  Parameter ϵ_induction :
    forall {P}, (forall x, (forall y, y ∈ x -> P y) -> P x) ->
           forall x, P x.
  
  Parameter ω_induction :
    forall {P}, (forall x, x ∈ ω -> P x -> P (Suc x)) ->
           P ∅ ->
           forall x, x ∈ ω -> P x.
  
  Parameter ϵ_rec : (forall x, (forall y, y ∈ x -> set) -> set) -> set -> set.  
  Axiom ϵ_rec_prop : forall {H x}, ϵ_rec H x = H x (fun y _ => ϵ_rec H y).
End IZF.
