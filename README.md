# Elevator TLA+

This code models the floor-request queue for a single elevator, subject to the following requirements:  

- There is one elevator, which serves four floors.  
- Each floor has one button to call the elevator.  
- The elevator cabin has one button for each floor.  
- Users on floors or aboard the elevator can request the elevator to visit floors; requests are queued, and duplicate requests are ignored.  
- When the elevator cabin visits a floor, users can get on and/or off the elevator, and pending requests for that floor are cleared.  
- Each floor has one door for safely entering/exiting the elevator, which opens simultaneously with a corresponding door on the elevator cabin.  

This code uses a sequence to collect all floor requests for 
