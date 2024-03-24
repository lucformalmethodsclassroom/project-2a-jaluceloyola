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

\* Function used to test if a given floor is in the requestQueue
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

\*used with SelectSeq to clear the current floor from the queue
Test(x) == x # currentFloor

Init ==
    /\ running = OFF
    /\ cabinDoor = CLOSED
    /\ currentFloor = 1
    /\ requestQueue = <<1,2,3,4>>
    /\ timePassed = 0

\*Increment passing of time as elevator moves between floors   
Tick ==
    /\ timePassed' = timePassed + 1
    /\ UNCHANGED <<running, currentFloor, requestQueue, cabinDoor>>

\*All 4 Floor Requests all check to see if requested floor is in the Queue, 
\* and if not, adds it to the end of the queue 
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

\* checkQueue checks if currentFloor exists in request Queue. If TRUE,
\* then stop running, open the doors to let passengers out and remove 
\* the current floor from the queue. Also, if current floor is the same 
\* as the oldest floor request (i.e. the head of the sequence), it resets 
\* the amount of time that has passed since the oldest queue request
\* has been served
checkQueue ==
    IF CheckFloorInQueue(currentFloor,requestQueue) THEN
        /\ requestQueue' = SelectSeq(requestQueue,Test)
        /\ running' = OFF
        /\ cabinDoor' = OPEN
        /\ IF Head(requestQueue) = currentFloor 
            THEN /\ timePassed' = 0
                 /\ UNCHANGED <<currentFloor>>
            ELSE /\ UNCHANGED <<currentFloor, timePassed>>
    ELSE UNCHANGED <<running, currentFloor, requestQueue, cabinDoor, timePassed>>

\* moveUp will check to see if there is a request in the queue, and if the oldest request is above
\* the current floor. If so, it then closes the elevator door and moves up, checking first to see if the 
\* elevator isn't already at the top floor
moveUp ==
    /\ requestQueue # << >>
    /\ Head(requestQueue) > currentFloor 
    /\ currentFloor < MAXFLOOR  
    /\ currentFloor' = currentFloor + 1
    /\ cabinDoor' = CLOSED
    /\ running' = ON
    /\ UNCHANGED << requestQueue, timePassed>>

\* same as moveUp, but in the other direction
moveDown ==
    /\ requestQueue # << >>
    /\ Head(requestQueue) < currentFloor 
    /\ currentFloor > MINFLOOR  
    /\ currentFloor' = currentFloor - 1
    /\ cabinDoor' = CLOSED
    /\ running' = ON
    /\ UNCHANGED << requestQueue, timePassed>>

Next ==
    \/ floor1Request
    \/ floor2Request
    \/ floor3Request
    \/ floor4Request
    \/ checkQueue
    \/  /\ moveUp
        /\ Tick 
    \/  /\ moveDown 
        /\ Tick

\* Ensures Tick is called with weak fairness
TickProgress == WF_timePassed(Tick)

Spec == Init /\ [][Next]_vars /\ TickProgress

TypeOK == running \in { OFF, ON } /\ cabinDoor \in { CLOSED, OPEN } /\ currentFloor \in {1,2,3,4} /\ timePassed \in Nat

DoorSafety == cabinDoor = OPEN => running = OFF
RunSafety == running = ON => cabinDoor = CLOSED

EventualService == <>(requestQueue = <<>>) \* Eventually all floors get serviced
TimelyService == timePassed = 1 ~> timePassed = 0 \* Eventually the oldest request in the queue gets serviced

RunsUntilDoneOrInterrupted == 
    [][running = ON => running' = ON \/ cabinDoor' = OPEN]_vars

LivenessConditions == running = ON ~> running = OFF

====