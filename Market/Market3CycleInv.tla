---------------------------- MODULE Market3CycleInv ---------------------------
(*
  This is an extension of Market3 that monitors the main invariant.
  It does so by non-deterministically saving a snapshot of drops and pools,
  for a non-deterministically chosen pair of denominations. The invariant MonInv
  checks that once the drops have reached the previously saved state of drops,
  the pools should not go below the previously saved state of pools.
  Since TLC explores all reachable states and we allow the monitor to take
  snapshot in any state, it is sufficient to take a snapshot
  once per system execution. 
 *)

EXTENDS Market3

\* additional variable to save the snapshot into
VARIABLE snapshot
  
\* initialize the system and the monitor
MonInit ==
  \* initialize the system
  /\ INIT
  \* no snapshot taken yet
  /\ snapshot = [ active |-> FALSE ]
  
\* make a step: either by the system, or by the monitor
MonNext ==
  \* the system makes a step
  \/ NEXT /\ UNCHANGED snapshot
  \* the monitor saves a snapshot
  \/ /\ ~snapshot.active
     /\ \E ab \in PairType:
        LET ba == <<ab[2], ab[1]>> IN
        snapshot' = [
          active |-> TRUE,
          pair   |-> ab,
          poolsAB |-> pools[ab],
          poolsBA |-> pools[ba],
          drops  |-> drops
        ]  
     /\ UNCHANGED vars

\* check the invariant of the monitored system
MonInv ==
    LET ab == snapshot.pair
        ba == <<ab[2], ab[1]>>
        NoPoolDrain ==
      /\ pools[ab] * snapshot.poolsBA = pools[ba] * snapshot.poolsAB
      /\ pools[ab] >= snapshot.poolsAB
      /\ pools[ba] >= snapshot.poolsBA
    IN  
    (snapshot.active /\ drops = snapshot.drops) => NoPoolDrain

===============================================================================
