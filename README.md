# Elevator TLA+

This code models the floor-request queue for a single elevator, subject to the following requirements:  

- There is one elevator, which serves four floors.  
- Each floor has one button to call the elevator.  
- The elevator cabin has one button for each floor.  
- Users on floors or aboard the elevator can request the elevator to visit floors; requests are queued, and duplicate requests are ignored.  
- When the elevator cabin visits a floor, users can get on and/or off the elevator, and pending requests for that floor are cleared.  
- Each floor has one door for safely entering/exiting the elevator, which opens simultaneously with a corresponding door on the elevator cabin.  

This code uses a sequence to named 'requestQueue' to collect all floor requests for the elevator. There is no distinction made between requests made from inside the elevator or requests made from individual floors with respect to the priorty of the request in the queue.  

The variable 'timePassed' is used to track how long the oldest request has been at the front of the queue.  

The actions 'moveUp' and 'moveDown' moves the elevator in the respective direction, but contains logic restricting the elevator from moving away from the oldest request in the queue (i.e. the request at the head of the sequence). This ensures
all floor requests will be met in a timely manner. It also closes the door, and sets the elevator into operation (i.e. running = ON). Each movement of the elevator also cause the value of 'timePassed' to increase by one.  

The actions 'Floor1Request', 'Floor2Request', etc... simply check to see if the current floor request is already in the queue, and if not adds the request to the end of the queue, ensuring older requests will have a higher priorty for being served. 
   
The action 'checkQueue' checks to see if the current floor is in the queue, and if so stops the elevator and opens the doors to allow passengers to enter/exit ,and removes the current floor from 'requestQueue'. If the current floor is also the same as the request at the head of 'requestQueue', then timePassed is set to 0.  

The opening of the 'outer' elevator doors on each floor are not explicitly modeled. It is assumed that these outer doors can only open when the elevator cabin is on their respective floor, i.e. the outer door on each floor is functionally part of the 'door' of the elevator when the cabin shares a floor with them, and that it is not mechanically possible to open these 'floor doors' when the elevator cabin is on another floor (not quite sure how to model someone taking a crowbar and forcing them open).  

Safety conditions were chosen to ensure:  
- The doors can only be open when the elevator is not running.
- The elevator can only run when the doors are closed.  

Liveliness conditions were chosen to check if:  
- The request queue is eventually empty at some point (i.e. all floor requests will eventualy be served).  
- One timeRemaining has started to increase, it will eventually be reset to zero (i.e. the oldest request in the queue will be served in a relatively timely manner).

W.r.t. the extra credit:   
- This code does not have the capability to restric access to certain floors.  
- This code does not have the capability to parametrically model the number of floors or elevators.
- Most elevators have a maximum weight capacity, so there would be value in tracking the number of concurrent passengers in the elevator cabin if this was a safety condition that needed to be tracked by the model.

  




