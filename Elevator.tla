-------------------------- MODULE Elevator  --------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS 
    OFF, ON, CLOSED, OPEN, MINFLOOR, MAXFLOOR

VARIABLES 
    running,
    cabinDoor,
    currentFloor,
    requestQueue,
    timePassed
     
vars == <<running, currentFloor, requestQueue, cabinDoor, timePassed>>

TypeOK == cabinDoor \in { CLOSED, OPEN } /\ running \in { OFF, ON } /\ timePassed \in Nat

MaxTime == 20

Init ==
    /\ running = OFF
    /\ currentFloor = 1
    /\ requestQueue = << >>
    /\ cabinDoor = CLOSED
    /\ timePassed = 0

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
    /\ timePassed' = timePassed + 1
    /\ timePassed' <= MaxTime
    /\ UNCHANGED <<running, currentFloor, requestQueue, cabinDoor>>

floor1Request ==
    /\ ~CheckFloorInQueue(1,requestQueue)
    /\ requestQueue' = Append(requestQueue,1)
    /\ UNCHANGED <<running, currentFloor, cabinDoor, timePassed>>

floor2Request ==
    /\ ~CheckFloorInQueue(2,requestQueue)
    /\ requestQueue' = Append(requestQueue,2)
    /\ UNCHANGED <<running, currentFloor, cabinDoor, timePassed>>

floor3Request ==
    /\ ~CheckFloorInQueue(3,requestQueue)
    /\ requestQueue' = Append(requestQueue,3)
    /\ UNCHANGED <<running, currentFloor, cabinDoor, timePassed>>

floor4Request ==
    /\ ~CheckFloorInQueue(4,requestQueue)
    /\ requestQueue' = Append(requestQueue,4)
    /\ UNCHANGED <<running, currentFloor, cabinDoor, timePassed>>

checkQueue ==
    IF CheckFloorInQueue(currentFloor,requestQueue) THEN
        /\ requestQueue' = SelectSeq(requestQueue,Test)
        /\ cabinDoor' = OPEN
        /\ running' = OFF
        /\ UNCHANGED <<currentFloor, timePassed >>
    ELSE UNCHANGED <<running, currentFloor, requestQueue, cabinDoor, timePassed>>

moveUp ==
    /\ requestQueue # << >>
    /\ Head(requestQueue) > currentFloor 
    /\ currentFloor < MAXFLOOR  
    /\ currentFloor' = currentFloor + 1
    /\ cabinDoor' = CLOSED
    /\ running' = ON
    /\ UNCHANGED << requestQueue, timePassed>>

moveDown ==
    /\ requestQueue # << >>
    /\ Head(requestQueue) < currentFloor 
    /\ currentFloor > MINFLOOR  
    /\ currentFloor' = currentFloor - 1
    /\ cabinDoor' = CLOSED
    /\ running' = ON
    /\ UNCHANGED << requestQueue, timePassed>>

TickProgress == WF_timePassed(Tick)

Next ==
    \/ Tick
    \/ floor1Request
    \/ floor2Request
    \/ floor3Request
    \/ floor4Request
    \/ checkQueue
    \/ moveUp 
    \/ moveDown 

Spec == Init /\ [][Next]_vars /\ TickProgress


TimeInvariant == TRUE
\* Use with -simulate
\*TimeInvariant == timePassed < MaxTime

\*DoorSafety == TRUE
DoorSafety == cabinDoor = OPEN => running = OFF
RunSafety == running = ON => cabinDoor = CLOSED

LivenessConditions == TRUE
\*LivenessConditions == running = ON ~> running = OFF

RunsUntilDoneOrInterrupted == TRUE
\* RunsUntilDoneOrInterrupted == 
\*     [][running = ON => running' = ON \/ timePassed' = 0 \/ door' = OPEN]_vars

====