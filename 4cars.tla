------------- MODULE 4cars -------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NumRoads, NumCars, NULL
ASSUME NumRoads >= NumCars

NR == NumRoads
NC == NumCars

(* --algorithm four_cars

variables cars = [car \in 1..NC |-> 1], roads = [road \in 1..NR |-> 0] 

define


RightCar(c) == (c % NR) + 1   
RightCarStopped(c) == roads[RightCar(c)] 




end define;



fair process approachStop \in 1..NC
variables stopped = TRUE;
begin s:
    while stopped do
    roads[self] := 1;
      Drive:
      await(RightCarStopped(self)) = NULL;
        stopped := FALSE;
        roads[self] := NULL

  end while;

end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "feef3aa6" /\ chksum(tla) = "dc109a7c")
VARIABLES cars, roads, pc

(* define statement *)
RightCar(c) == (c % NR) + 1
RightCarStopped(c) == roads[RightCar(c)]

VARIABLE stopped

vars == << cars, roads, pc, stopped >>

ProcSet == (1..NC)

Init == (* Global variables *)
        /\ cars = [car \in 1..NC |-> 1]
        /\ roads = [road \in 1..NR |-> 0]
        (* Process approachStop *)
        /\ stopped = [self \in 1..NC |-> TRUE]
        /\ pc = [self \in ProcSet |-> "s"]

s(self) == /\ pc[self] = "s"
           /\ IF stopped[self]
                 THEN /\ roads' = [roads EXCEPT ![self] = 1]
                      /\ pc' = [pc EXCEPT ![self] = "Drive"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ roads' = roads
           /\ UNCHANGED << cars, stopped >>

Drive(self) == /\ pc[self] = "Drive"
               /\ (RightCarStopped(self)) = NULL
               /\ stopped' = [stopped EXCEPT ![self] = FALSE]
               /\ roads' = [roads EXCEPT ![self] = NULL]
               /\ pc' = [pc EXCEPT ![self] = "s"]
               /\ cars' = cars

approachStop(self) == s(self) \/ Drive(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NC: approachStop(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NC : WF_vars(approachStop(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=======
