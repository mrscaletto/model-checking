--------------------------------- MODULE elevator ---------------------------------
EXTENDS Integers, TLC, Sequences

(*--algorithm ElevatorLTS 
variables
  NumberOfUsers = 3,
  floors = 5,  \* Total number of floors
  currentFloor = 1,  \* The current floor of the elevator
  requestedFloors = {},  \* A set of floors requested by users
  moving = FALSE,  \* Elevator's is moving status
  direction = "up",  \* Elevator's current direction, could be "up" or "down"
  doorOpen = FALSE;  \* Elevator's door open status

define
  \* Safety properties
  Safety1 == \* No moving while the doors are open
    /\ doorOpen => ~moving
    
  Safety2 == \* Cannot move beyond highest floor or below ground
    /\ currentFloor <= floors
    /\ currentFloor > 0

  Safety3 == \* Cannot have a floor requested not in the building
    /\ requestedFloors \subseteq 1..floors

  Safety4 == \* Doors cannot open while elevator is moving
    /\ moving => ~doorOpen

  Safety5 == \* Elevator must stop at a requested floor
    /\ currentFloor \in requestedFloors => ~moving

  \* Liveness properties
  Liveness1 == \* Elevator will eventually respond to a request
    <> ([]<>(requestedFloors /= {} => ~moving))

  Liveness2 == \* The doors will eventually open at a requested floor
    <> ([]<>(currentFloor \in requestedFloors => doorOpen))

end define;

macro Move()
begin
  \* The elevator moves to the next floor based on the current direction
  if (direction = "up") then
    \* Move up one floor, if not at the top already
    if (currentFloor < floors) then
      currentFloor := currentFloor + 1;
    else
      \* Change direction if at top floor
    \*  direction := "down";
    end if;
  else
    \* Move down one floor, if not at the bottom already
    if (currentFloor > 1) then
      currentFloor := currentFloor - 1;
    else
      \* Change direction if at bottom floor
      \* direction := "up";
    end if;
  end if;
  moving := TRUE;
end macro;

macro OpenDoors()
begin
  \* Open the doors if the elevator is not moving
  if (~moving) then
    doorOpen := TRUE;
    \* Removing served floor from request set
    requestedFloors := requestedFloors \ {currentFloor};
  end if;
end macro;

procedure CloseDoors()
begin
  t1: doorOpen := FALSE;
end procedure;

\* Process representing the main behavior of the Elevator
process Elevator = "elevator"
begin
  E1: while (TRUE) do
    await ~moving;
    either
      \* Respond to a floor request
      with fl \in requestedFloors do
        if (fl > currentFloor) then
          direction := "up";
        elsif (fl < currentFloor) then
          direction := "down";
        end if;
        Move();
      end with;
    or
      \* Simply move in the current direction if no specific floor is requested
      Move();
    or
        
      if (currentFloor \in requestedFloors) then
        OpenDoors();
        \* await @+1;
        call CloseDoors();
      end if;
    end either;
  end while;
end process;

\* Process to simulate floor button presses
process User = "User" 
\* \in 1..3
variables
  userFloor = 1;  \* The floor where the user currently is
begin
  U1: while (TRUE) do
    either
      \* User requests the elevator
      with newFloor \in 1..floors do
        requestedFloors := requestedFloors \cup {newFloor};
        await (doorOpen /\ currentFloor = newFloor);
      end with;
    or
      \* User does nothing
      skip;
    end either;
  end while;

end process; 

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "beaf5e7f" /\ chksum(tla) = "bcf56048")
VARIABLES NumberOfUsers, floors, currentFloor, requestedFloors, moving, 
          direction, doorOpen, pc, stack

(* define statement *)
Safety1 ==
  /\ doorOpen => ~moving

Safety2 ==
  /\ currentFloor <= floors
  /\ currentFloor > 0

Safety3 ==
  /\ requestedFloors \subseteq 1..floors

Safety4 ==
  /\ moving => ~doorOpen

Safety5 ==
  /\ currentFloor \in requestedFloors => ~moving


Liveness1 ==
  <> ([]<>(requestedFloors /= {} => ~moving))

Liveness2 ==
  <> ([]<>(currentFloor \in requestedFloors => doorOpen))

VARIABLE userFloor

vars == << NumberOfUsers, floors, currentFloor, requestedFloors, moving, 
           direction, doorOpen, pc, stack, userFloor >>

ProcSet == {"elevator"} \cup {"User"}

Init == (* Global variables *)
        /\ NumberOfUsers = 3
        /\ floors = 5
        /\ currentFloor = 1
        /\ requestedFloors = {}
        /\ moving = FALSE
        /\ direction = "up"
        /\ doorOpen = FALSE
        (* Process User *)
        /\ userFloor = 1
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "elevator" -> "E1"
                                        [] self = "User" -> "U1"]

t1(self) == /\ pc[self] = "t1"
            /\ doorOpen' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << NumberOfUsers, floors, currentFloor, 
                            requestedFloors, moving, direction, stack, 
                            userFloor >>

CloseDoors(self) == t1(self)

E1 == /\ pc["elevator"] = "E1"
      /\ ~moving
      /\ \/ /\ \E fl \in requestedFloors:
                 /\ IF (fl > currentFloor)
                       THEN /\ direction' = "up"
                       ELSE /\ IF (fl < currentFloor)
                                  THEN /\ direction' = "down"
                                  ELSE /\ TRUE
                                       /\ UNCHANGED direction
                 /\ IF (direction' = "up")
                       THEN /\ IF (currentFloor < floors)
                                  THEN /\ currentFloor' = currentFloor + 1
                                  ELSE /\ TRUE
                                       /\ UNCHANGED currentFloor
                       ELSE /\ IF (currentFloor > 1)
                                  THEN /\ currentFloor' = currentFloor - 1
                                  ELSE /\ TRUE
                                       /\ UNCHANGED currentFloor
                 /\ moving' = TRUE
            /\ pc' = [pc EXCEPT !["elevator"] = "E1"]
            /\ UNCHANGED <<requestedFloors, doorOpen, stack>>
         \/ /\ IF (direction = "up")
                  THEN /\ IF (currentFloor < floors)
                             THEN /\ currentFloor' = currentFloor + 1
                             ELSE /\ TRUE
                                  /\ UNCHANGED currentFloor
                  ELSE /\ IF (currentFloor > 1)
                             THEN /\ currentFloor' = currentFloor - 1
                             ELSE /\ TRUE
                                  /\ UNCHANGED currentFloor
            /\ moving' = TRUE
            /\ pc' = [pc EXCEPT !["elevator"] = "E1"]
            /\ UNCHANGED <<requestedFloors, direction, doorOpen, stack>>
         \/ /\ IF (currentFloor \in requestedFloors)
                  THEN /\ IF (~moving)
                             THEN /\ doorOpen' = TRUE
                                  /\ requestedFloors' = requestedFloors \ {currentFloor}
                             ELSE /\ TRUE
                                  /\ UNCHANGED << requestedFloors, doorOpen >>
                       /\ stack' = [stack EXCEPT !["elevator"] = << [ procedure |->  "CloseDoors",
                                                                      pc        |->  "E1" ] >>
                                                                  \o stack["elevator"]]
                       /\ pc' = [pc EXCEPT !["elevator"] = "t1"]
                  ELSE /\ pc' = [pc EXCEPT !["elevator"] = "E1"]
                       /\ UNCHANGED << requestedFloors, doorOpen, stack >>
            /\ UNCHANGED <<currentFloor, moving, direction>>
      /\ UNCHANGED << NumberOfUsers, floors, userFloor >>

Elevator == E1

U1 == /\ pc["User"] = "U1"
      /\ \/ /\ \E newFloor \in 1..floors:
                 /\ requestedFloors' = (requestedFloors \cup {newFloor})
                 /\ (doorOpen /\ currentFloor = newFloor)
         \/ /\ TRUE
            /\ UNCHANGED requestedFloors
      /\ pc' = [pc EXCEPT !["User"] = "U1"]
      /\ UNCHANGED << NumberOfUsers, floors, currentFloor, moving, direction, 
                      doorOpen, stack, userFloor >>

User == U1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Elevator \/ User
           \/ (\E self \in ProcSet: CloseDoors(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
===================================================================================
