---------------------------- MODULE stack ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

(* Define items *)
ItemType == {1, 2, 3, 4, 5}
EmptyTop == 0
Item(e) == e \in ItemType

(* Stack Record *)
StackType ==
    [ Top : ItemType \cup {EmptyTop},
      elems : SUBSET ItemType,
      deleted : SUBSET ItemType
    ]

VARIABLES Stack

(* Variables *)
vars == <<Stack>>

Init ==
    /\ Stack \in StackType
    /\ Stack.elems = {1, 2, 3}
    /\ Stack.deleted = {4, 5}
    /\ Stack.Top = EmptyTop

Push(e) ==
    /\ Item(e)
    /\ e \in Stack.deleted
    /\ Stack' = [ Stack EXCEPT
                    !.deleted = @ \ {e},
                    !.elems = @ \cup {e},
                    !.Top = e
                ]

Pop ==
    /\ Stack.Top # EmptyTop
    /\ LET top == Stack.Top IN
       /\ Stack' = [ Stack EXCEPT
                      !.deleted = @ \cup {top},
                      !.elems = @ \ {top},
                      !.Top = IF Stack.elems \ {top} = {} THEN EmptyTop ELSE CHOOSE x \in Stack.elems \ {top} : TRUE
                   ]

Clear ==
    /\ Stack' = [ Stack EXCEPT
                    !.deleted = @ \cup Stack.elems,
                    !.elems = {},
                    !.Top = EmptyTop 
                ]

NoChange ==
    Stack' = Stack

Next ==
    \/ \E e \in Stack.deleted : Push(e)
    \/ Pop
    \/ Clear
    \/ NoChange

(* Invariants *)
StackIsValid == 
    /\ \A i \in ItemType: (i \in Stack.elems) \/ (i \in Stack.deleted) \/ (i = EmptyTop)
    /\ (Stack.Top = EmptyTop) \/ (Stack.Top \in Stack.elems)

Inv == StackIsValid

Spec == Init /\ [][Next]_vars /\ Inv

(* Properties *)
Prop1 ==
    \E d \in Stack.deleted : TRUE

Prop2 == 
    Stack.elems = {}

Prop3 ==
    \E e \in ItemType : e \in Stack.deleted /\ e \in Stack.elems

Prop4 == 
    \E e \in ItemType : e \in Stack.elems /\ e \in Stack.deleted

TestPush ==
    \E e \in ItemType : e \in Stack.deleted /\ e \in Stack.elems

========================================================================
