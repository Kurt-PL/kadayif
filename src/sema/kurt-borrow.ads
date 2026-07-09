--  Kurt.Borrow — the reference derivation tree and permission states
--  (§8.2, §8.3). This is the data-structure foundation of the ownership
--  model; later milestones (lifetimes, copy/transfer, destructors) read
--  from it. Kurt.Sema drives it during the body-analysis pass.
--
--  Bootstrap scope: references are tracked per simple named place (the
--  binding they are taken of). `%` references are NOT tracked (§8.2.2:
--  they carry no position in the tree). The tree models re-derivation via
--  parent links; the first milestone creates roots only.

with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;

package Kurt.Borrow is

   package SU renames Ada.Strings.Unbounded;

   --  §8.3 permission state of a landside reference.
   type Perm_State is
     (Idle,         --  $T before its first store
      Assert_Excl,  --  $T after a store (programmer-asserted exclusivity)
      Proven_Excl,  --  reached only by an implementation proof (unused here)
      Shared_RO,    --  &T
      Shared_RW,    --  &mut T
      Atomic_Ref);  --  &atomic T / &guard T

   --  An exclusive state is one of the `$T` family.
   function Is_Exclusive (S : Perm_State) return Boolean is
     (S in Idle | Assert_Excl | Proven_Excl);

   type Node_Id is new Natural;
   No_Node : constant Node_Id := 0;

   type Tree is limited private;

   --  Discard all tracked references (called per subroutine body).
   procedure Clear (T : in out Tree);

   --  Create a reference node to the place named Referent, held by the
   --  binding Bound_To, with the given initial permission State. Parent is
   --  the node it re-derives from (No_Node for a root). Scope_Len is the
   --  enclosing lexical depth, recorded for liveness (see Kill_Above).
   function Create
     (T         : in out Tree;
      Referent  : String;
      Bound_To  : String;
      State     : Perm_State;
      Parent    : Node_Id := No_Node;
      Scope_Len : Natural := 0) return Node_Id;

   --  The live node currently bound to Name (its reference value), or
   --  No_Node. The most recently created match wins (shadowing).
   function Of_Binding (T : Tree; Name : String) return Node_Id;

   --  Record a store through node N: an exclusive Idle node asserts
   --  exclusivity (-> Assert_Excl). Other states are unchanged.
   procedure Record_Store (T : in out Tree; N : Node_Id);

   --  §8.3 apply the foreign-store transition of the permission-state machine
   --  to every live node that overlaps By's referent and lies outside By's
   --  derivation subtree (the foreign nodes). Idle and Assert_Excl lapse to
   --  Shared_RW; Shared_RO / Shared_RW lapse in place; Atomic_Ref lapses only
   --  under a non-atomic store (§8.2.1). The lapse is a state fact, not a
   --  diagnostic: a non-optimizing implementation derives no transformation
   --  premise from permission states, so a lapse drives no error (§8.3.1).
   --  The mandatory alias translation failure is detected separately, before
   --  this transition runs, by Has_Live_Alias / Has_Asserted_Excl.
   procedure Apply_Foreign_Store
     (T : in out Tree; By : Node_Id; Atomic : Boolean);

   --  Mark not-live every node born in a scope deeper than Keep_Len. Called
   --  by Kurt.Sema when it unwinds a block's bindings.
   procedure Kill_Above (T : in out Tree; Keep_Len : Natural);

   --  §8.3 Constraint support: is there another live reference to the same
   --  referent as N, outside N's derivation subtree? Such a reference is a
   --  statically provable alias of N.
   function Has_Live_Alias (T : Tree; N : Node_Id) return Boolean;

   --  Is there a live exclusive (`$T`) node to Referent already at
   --  Assert_Excl? Creating another reference to that place is a foreign
   --  access that provably aliases the asserted-exclusive reference.
   function Has_Asserted_Excl (T : Tree; Referent : String) return Boolean;

   function State_Of (T : Tree; N : Node_Id) return Perm_State;
   function Referent_Of (T : Tree; N : Node_Id) return String;

private

   type Node_Rec is record
      Referent  : SU.Unbounded_String;
      Bound_To  : SU.Unbounded_String;
      State     : Perm_State := Shared_RO;
      Parent    : Node_Id    := No_Node;
      Live      : Boolean    := True;
      Scope_Len : Natural    := 0;
   end record;

   package Node_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Node_Rec);

   type Tree is limited record
      Nodes : Node_Vectors.Vector;
   end record;

end Kurt.Borrow;
