-------------------------- MODULE Elevator  --------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS 
    OFF, ON, CLOSED, OPEN, MINFLOOR, MAXFLOOR

VARIABLES 
    running,
    currentFloor,
    requestQueue,
    queueSize,
    cabinDoor,
    floor1Door,
    floor2Door,
    floor3Door,
    floor4Door,
    timeRemaining
     
    \*opTime,                 \* operation time

vars == <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

TypeOK == cabinDoor \in { CLOSED, OPEN } /\ running \in { OFF, ON } /\ timeRemaining \in Nat

\*MaxTime == 10
MaxQueue == 10


Init ==
    /\ running = OFF
    /\ currentFloor = 1
    /\ requestQueue = << >>
    /\ queueSize = 0 
    /\ cabinDoor = CLOSED
    /\ floor1Door = CLOSED
    /\ floor2Door = CLOSED
    /\ floor3Door = CLOSED
    /\ floor4Door = CLOSED
    /\ timeRemaining = 10

\* increment remaining time by one second
(*
IncTime ==
    \*/\ running = OFF
    /\ timeRemaining' = timeRemaining + 1
    /\ timeRemaining' <= MaxTime
    /\  <<running, currentFloor, requestQueue, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door >>

Start ==
    /\ timeRemaining > 0
    /\ running' = ON
    /\ UNCHANGED << door, running, currentFloor >>

Cancel ==
    /\ running' = OFF
    /\ timeRemaining' = 0
    /\ UNCHANGED << door, currentFloor >>
*)

Test(x) == x # currentFloor
CheckFloorInQueue(floornum,queue) ==
    IF Len(queue) = 0 THEN FALSE
        ELSE IF Len(queue) = 1
            /\ queue[1] # floornum
        THEN FALSE 
        ELSE IF Len(queue) = 2
            /\ queue[1] # floornum
            /\ queue[2] # floornum
        THEN FALSE 
        ELSE IF Len(queue) = 3
            /\ queue[1] # floornum
            /\ queue[2] # floornum
            /\ queue[3] # floornum
        THEN FALSE
    ELSE TRUE
        
Tick ==
    \*/\ running = ON
    /\ timeRemaining' = timeRemaining - 1
    /\ timeRemaining' >= 0
    \*/\ IF timeRemaining' = 0 THEN running' = OFF ELSE UNCHANGED << running >>
    /\ UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door >>

floor1Request ==
    /\ ~CheckFloorInQueue(1,requestQueue)
    /\ requestQueue' = Append(requestQueue,1)
    /\ queueSize' = queueSize + 1 
    /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

floor2Request ==
    /\ ~CheckFloorInQueue(2,requestQueue)
    /\ requestQueue' = Append(requestQueue,2)
    /\ queueSize' = queueSize + 1 
    /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

floor3Request ==
    /\ ~CheckFloorInQueue(3,requestQueue)
    /\ requestQueue' = Append(requestQueue,3)
    /\ queueSize' = queueSize + 1 
    /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

floor4Request ==
    /\ ~CheckFloorInQueue(4,requestQueue)
    /\ requestQueue' = Append(requestQueue,4)
    /\ queueSize' = queueSize + 1 
    /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

checkQueue ==
    IF CheckFloorInQueue(currentFloor,requestQueue) THEN
        /\ requestQueue' = SelectSeq(requestQueue,Test)
        /\ cabinDoor' = OPEN
        /\ running' = OFF
        /\ UNCHANGED <<currentFloor, queueSize, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

moveUp ==
    /\ requestQueue # << >>
    /\ Head(requestQueue) > currentFloor 
    /\ currentFloor < MAXFLOOR  
    /\ currentFloor' = currentFloor + 1
    /\ cabinDoor' = CLOSED
    /\ running' = ON
    /\ UNCHANGED << requestQueue, queueSize, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

moveDown ==
    /\ requestQueue # << >>
    /\ Head(requestQueue) < currentFloor 
    /\ currentFloor > MINFLOOR  
    /\ currentFloor' = currentFloor - 1
    /\ cabinDoor' = CLOSED
    /\ running' = ON
    /\ UNCHANGED << requestQueue, queueSize, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

\*TickProgress == TRUE

TickProgress == WF_timeRemaining(Tick)

Next ==
    \/ floor1Request
    \/ floor2Request
    \/ floor3Request
    \/ floor4Request
    \/ moveUp 
    \/ moveDown 
    \/ checkQueue
    \/ Tick

Spec == Init /\ [][Next]_vars /\ TickProgress

\*DoorSafety == TRUE
\*DoorSafety == queueSize < MaxQueue

DoorSafety == timeRemaining > 0

\* DoorSafety == door = OPEN => running = OFF
\* DoorSafety == running = ON => door = CLOSED

LivenessConditions == TRUE

\* HeatLiveness == running = ON ~> running = OFF

RunsUntilDoneOrInterrupted == TRUE

\* RunsUntilDoneOrInterrupted == 
\*     [][running = ON => running' = ON \/ timeRemaining' = 0 \/ door' = OPEN]_vars

====

(*OpenDoor ==
    /\ cabinDoor' = OPEN
    /\ UNCHANGED <<running, currentFloor, requestQueue, queueSize, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

CloseDoor ==
    /\ cabinDoor' = CLOSED
    /\ UNCHANGED <<running, currentFloor, requestQueue, queueSize, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
*)


(*
moveDown ==
    IF requestQueue # << >> THEN
        IF Head(requestQueue) > currentFloor THEN 
        \/  /\ currentFloor' = currentFloor + 1     \*move up 1
            /\ currentFloor' < MAXFLOOR    \* until reach max
            /\ UNCHANGED <<running, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
        \/  /\ currentFloor >= MAXFLOOR  
            /\ UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
        ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
*)
(*
moveDown ==
    IF requestQueue # << >> THEN
        IF Head(requestQueue) < currentFloor THEN 
        \/  /\ currentFloor' = currentFloor - 1     \*move up 1
            /\ currentFloor' > MINFLOOR    \* until reach max
            /\ UNCHANGED <<running, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
        \/  /\ currentFloor <= MINFLOOR  
            /\ UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
        ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

moveDown ==
    IF requestQueue # << >> THEN
        IF Head(requestQueue) < currentFloor THEN 
        \/  /\ currentFloor' = currentFloor - 1     \*move up 1
            /\ currentFloor' > MINFLOOR    \* until reach max
            /\ UNCHANGED <<running, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
        \/  /\ currentFloor <= MINFLOOR  
            /\ UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
        ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

*)
(*
checkQueue ==
    IF requestQueue # << >> THEN
        /\ requestQueue' = SelectSeq(requestQueue,Test)
        /\ timeRemaining' = 10
        /\ UNCHANGED <<running, currentFloor, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door >>    
    ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
*)
