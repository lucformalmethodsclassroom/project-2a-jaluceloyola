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

Tick ==
    \*/\ running = ON
    /\ timeRemaining' = timeRemaining - 1
    /\ timeRemaining' >= 0
    \*/\ IF timeRemaining' = 0 THEN running' = OFF ELSE UNCHANGED << running >>
    /\ UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door >>
OpenDoor ==
    /\ cabinDoor' = OPEN
    /\ UNCHANGED <<running, currentFloor, requestQueue, queueSize, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

CloseDoor ==
    /\ cabinDoor' = CLOSED
    /\ UNCHANGED <<running, currentFloor, requestQueue, queueSize, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

(*
floor1Request == \* add floor to Q FIFO
    IF Len(requestQueue) = 0 THEN 
        /\ requestQueue' = Append(requestQueue,1)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    ELSE IF Len(requestQueue) = 1 THEN 
        IF requestQueue[1] # 1 THEN 
        /\ requestQueue' = Append(requestQueue,1)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
        ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    ELSE IF Len(requestQueue) = 2 THEN 
        IF requestQueue[1] # 1 /\ requestQueue[2] # 1 THEN 
        /\ requestQueue' = Append(requestQueue,1)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>
        ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    ELSE IF Len(requestQueue) = 3 THEN 
        IF requestQueue[1] # 1  /\ requestQueue[2] # 1 /\ requestQueue[3] # 1 THEN 
        /\ requestQueue' = Append(requestQueue,1)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
        ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>
    ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>
*)

floor1Request == \* add floor to Q FIFO
    \/  Len(requestQueue) = 0
        /\ requestQueue' = Append(requestQueue,1)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ Len(requestQueue) = 1 
        /\ requestQueue[1] # 1 
        /\ requestQueue' = Append(requestQueue,1)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ Len(requestQueue) = 2 
        /\ requestQueue[1] # 1 /\ requestQueue[2] # 1 
        /\ requestQueue' = Append(requestQueue,1)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>
    \/ Len(requestQueue) = 3 
        /\ requestQueue[1] # 1  /\ requestQueue[2] # 1 /\ requestQueue[3] # 1 
        /\ requestQueue' = Append(requestQueue,1)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>

floor2Request == \* add floor to Q FIFO
    \/  Len(requestQueue) = 0
        /\ requestQueue' = Append(requestQueue,2)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ Len(requestQueue) = 1 
        /\ requestQueue[1] # 2
        /\ requestQueue' = Append(requestQueue,2)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ Len(requestQueue) = 2 
        /\ requestQueue[1] # 2 /\ requestQueue[2] # 2 
        /\ requestQueue' = Append(requestQueue,1)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>
    \/ Len(requestQueue) = 3 
        /\ requestQueue[1] # 2  /\ requestQueue[2] # 2 /\ requestQueue[3] # 2 
        /\ requestQueue' = Append(requestQueue,2)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>

floor3Request == \* add floor to Q FIFO
    \/  Len(requestQueue) = 0
        /\ requestQueue' = Append(requestQueue,3)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ Len(requestQueue) = 1 
        /\ requestQueue[1] # 3
        /\ requestQueue' = Append(requestQueue,3)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ Len(requestQueue) = 2 
        /\ requestQueue[1] # 3 /\ requestQueue[2] # 3 
        /\ requestQueue' = Append(requestQueue,3)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>
    \/ Len(requestQueue) = 3 
        /\ requestQueue[1] # 3  /\ requestQueue[2] # 3 /\ requestQueue[3] # 2
        /\ requestQueue' = Append(requestQueue,3)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>

floor4Request == \* add floor to Q FIFO
    \/  Len(requestQueue) = 0
        /\ requestQueue' = Append(requestQueue,4)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ Len(requestQueue) = 1 
        /\ requestQueue[1] # 4
        /\ requestQueue' = Append(requestQueue,4)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ Len(requestQueue) = 2 
        /\ requestQueue[1] # 4 /\ requestQueue[2] # 4 
        /\ requestQueue' = Append(requestQueue,4)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>
    \/ Len(requestQueue) = 3 
        /\ requestQueue[1] # 4  /\ requestQueue[2] # 4 /\ requestQueue[3] # 4
        /\ requestQueue' = Append(requestQueue,4)
        /\ queueSize' = queueSize + 1 
        /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    \/ UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining>>

(*
floor2Request == \* add floor to Q FIFO
    /\ requestQueue' = Append(requestQueue,2)
    /\ queueSize' = queueSize + 1 
    /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

floor3Request == \* add floor to Q FIFO
    /\ requestQueue' = Append(requestQueue,3)
    /\ queueSize' = queueSize + 1 
    /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

floor4Request == \* add floor to Q FIFO
    /\ requestQueue' = Append(requestQueue,4)
    /\ queueSize' = queueSize + 1
    /\ UNCHANGED <<running, currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
*)

moveUp ==
    IF requestQueue # << >> THEN
        IF Head(requestQueue) > currentFloor THEN 
        \/  /\ currentFloor' = currentFloor + 1     \*move up 1
            /\ currentFloor' < MAXFLOOR    \* until reach max
            /\ UNCHANGED <<running, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
        \/  /\ currentFloor >= MAXFLOOR  
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

checkQueue ==
    IF requestQueue # << >> THEN
        IF currentFloor = Head(requestQueue) THEN 
            /\ requestQueue' = Tail(requestQueue)
            /\ timeRemaining' = 5
            /\ UNCHANGED <<running, currentFloor, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door >>
        ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
    ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>

(*
checkQueue ==
    IF requestQueue # << >> THEN
        /\ requestQueue' = SelectSeq(requestQueue,Test)
        /\ timeRemaining' = 10
        /\ UNCHANGED <<running, currentFloor, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door >>    
    ELSE UNCHANGED <<running, currentFloor, requestQueue, queueSize, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door, timeRemaining >>
*)
\*TickProgress == TRUE

TickProgress == WF_timeRemaining(Tick)

Next ==
    \*\/ IncTime
    \*\/ Start
    \*\/ Cancel
    \/ OpenDoor
    \/ CloseDoor
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

(* other possible events
      action := "10min"
      action := "1min"
      action := "10sec"
      action := "power"
      action := "timer"
*)


(*

EXTENDS Integers, Sequences

CONSTANTS OPEN, CLOSED, minFloor, maxFloor

VARIABLES 
    currentFloor,
    requestQueue,
    \*opTime,                 \* operation time
    cabinDoor,
    floor1Door,
    floor2Door,
    floor3Door,
    floor4Door
    \*v

    \*MOVING,
    \*NOTMOVING,
    \*minFloor
    \*maxFloor

Max == 1000

Init == \*v = 0
    /\ currentFloor = 1
    /\ cabinDoor = CLOSED
    /\ floor1Door = CLOSED
    /\ floor2Door = CLOSED
    /\ floor3Door = CLOSED
    /\ floor4Door = CLOSED
    /\ requestQueue = << >>            \* start w/ blank queue -- 
    \*/\ opTime = 0

\*Tick == 
    \*/\ running = ON
    \*/\ timeRemaining' = timeRemaining - 1
    \*/\ timeRemaining' >= 0
    \*/\ IF timeRemaining' = 0 THEN running' = OFF ELSE UNCHANGED << running >>
    \*/\ UNCHANGED << door >>
    \*  \/  /\ v' = v + 1     \*move up 1
    \*      /\ v' <= Max      \* until reach max
    \*  \/  /\ v >= Max    
    \*      /\ UNCHANGED <<v>>

\*OpenDoor ==
\*    /\cabinDoor' = OPEN
\*    /\ UNCHANGED << running, timeRemaining >>

\*CloseDoor ==
\*    cabinDoor' = CLOSED
    \*/\ UNCHANGED << running, timeRemaining >>

floor1Request == \* add floor to Q FIFO
    \*/\ requestQueue' = << 1 >> \o requestQueue
    /\ requestQueue' = Append(1, requestQueue)
    /\ currentFloor' = currentFloor
    /\ cabinDoor' = cabinDoor
    /\ floor1Door' = floor1Door
    /\ floor2Door' = floor2Door
    /\ floor3Door' = floor3Door
    /\ floor4Door' = floor4Door

    \*/\ UNCHANGED << currentFloor, cabinDoor, floor1Door, floor2Door, floor3Door, floor4Door>>

floor2Request == \* add floor to Q
    /\ requestQueue' = << 2 >> \o requestQueue

floor3Request == \* add floor to Q
    /\ requestQueue' = << 3 >> \o requestQueue

floor4Request == \* add floor to Q
    /\ requestQueue' = << 4 >> \o requestQueue

\*checkQueue ==
\*    IF currentFloor = Head(requestQueue) THEN requestQueue' = Tail(requestQueue)

moveUp ==
    currentFloor' = currentFloor + 1
    \*\/  IF Head(requestQueue) <= currentFloor THEN UNCHANGED currentFloor ELSE  
    \*\/  /\ currentFloor' = currentFloor + 1     \*move up 1
    \*    /\ currentFloor' < maxFloor      \* until reach max
    \*\/  /\ currentFloor >= MaxFloor   
    \*    /\ UNCHANGED <<currentFloor>> 


moveDown ==
    \*IF Head(requestQueue) >= currentFloor THEN UNCHANGED currentFloor ELSE  
    \/  /\ currentFloor' = currentFloor - 1     \*move down 1
        /\ currentFloor' > minFloor      \* until reach max
    \/  /\ currentFloor <= minFloor
        /\ UNCHANGED <<currentFloor>>

TypeOK == TRUE\*v \in 0..Max
    \*/\ elevatorPosition \* need to have a variable like doorstate to reference \in DoorState 
    \*/\ cabin  
    \*/\ requestQueue \* TODO
    \*/\ operation

Next == 
    \/ moveUp \*/\ Tick
    \/ moveDown \*/\ Tick
    \/ floor1Request \*/\ Tick
    \/ floor2Request \*/\ Tick
    \/ floor3Request \*/\ Tick
    \/ floor4Request \*/\ Tick
    \*\/ checkQueue \*/\ Tick

\*  \/  /\ v' = v + 1     \*move up 1
\*      /\ v' <= Max      \* until reach max
\*  \/  /\ v >= Max    
\*      /\ UNCHANGED <<v>>

\*Spec == Init /\ [][Next]_v
Spec == Init /\ Next

Safety == TRUE 
    \*v % 2 = 0

LivenessConditions == TRUE

RunsUntilDoneOrInterrupted == TRUE

====

*)