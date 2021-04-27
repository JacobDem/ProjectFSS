------------------------------ MODULE project2 ------------------------------
EXTENDS Integers, Sequences
CONSTANTS rowLen, train
VARIABLES sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains
-----------------------------------------------------------------------------
vars == <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>

rowW1Constraint == Len(rowW1) \leq rowLen
rowW2Constraint == Len(rowW2) \leq rowLen
rowO1Constraint == Len(rowO1) \leq rowLen
rowO2Constraint == Len(rowO2) \leq rowLen

(* Trein = tuple met betekenis <<treinnummer,richting>>: richting = 1 voor W -> O en 0 voor O -> W
   De 5 treinsporen zijn de lijst "sporen": positie 1 is spoor W1, positie 2 is spoor W2, ... *)

Init == /\ sporen =[n \in 1..5 |-> <<>>]
        /\ (/\ bestemmingW1 = -1 /\ bestemmingW2 = -1 /\ bestemmingC = -1 /\ bestemmingO1 = -1 /\ bestemmingO2 = -1 /\ newW1 = -1 /\ newW2 = -1 /\ newC = -1 /\ newO1 = -1 /\ newO2 = -1)
        /\ rowW1 = <<>>
        /\ rowW2 = <<>>
        /\ rowO1 = <<>>
        /\ rowO2 = <<>>
        /\ trains = 0
                 
TypeInvariant == /\ sporen[1][2] \in (0..1)
                 /\ sporen[2][2] \in (0..1)
                 /\ sporen[3][2] \in (0..1)
                 /\ sporen[4][2] \in (0..1)
                 /\ sporen[5][2] \in (0..1)
                 /\ bestemmingW1 \in (-1..6)
                 /\ bestemmingW2 \in (-1..6)
                 /\ bestemmingC \in (-1..6)
                 /\ bestemmingO1 \in (-1..6)
                 /\ bestemmingO2 \in (-1..6)
                 /\ rowW1 \in Seq(train)
                 /\ rowW2 \in Seq(train)
                 /\ rowO1 \in Seq(train)
                 /\ rowO2 \in Seq(train)
                 
 RowO1Rcv == /\ rowO1' = Append(rowO1, <<trains, 0>>)
             /\ trains' = trains + 1
             /\ UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO2>>

 RowO2Rcv == /\ rowO2' = Append(rowO2, <<trains, 0>>)
             /\ trains' = trains + 1
             /\ UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1>>

 RowW1Rcv == /\ rowW1' = Append(rowW1, <<trains, 1>>)
             /\ trains' = trains + 1
             /\ UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowO1, rowW2, rowO2>>
 
 RowW2Rcv == /\ rowW2' = Append(rowW2, <<trains, 1>>)
              /\ trains' = trains + 1
              /\ UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowO1, rowO2>>
 
 RowO1Send == /\ rowO1 # <<>>
              /\ IF sporen[4] = <<>>
                 THEN newO1' = Head(rowO1) /\ rowO1' = Tail(rowO1) /\ sporen' = [sporen EXCEPT ![4] = newO1'] /\ UNCHANGED <<bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO2, rowW1, rowW2, rowO2, trains>>
                 ELSE UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>
 RowO2Send == /\ rowO2 # <<>>
              /\ IF sporen[5] = <<>>
                 THEN newO2' = Head(rowO2) /\ rowO2' = Tail(rowO2) /\ sporen' = [sporen EXCEPT ![5] = newO2'] /\ UNCHANGED << bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1,  rowW1, rowW2, rowO1, trains>>
                 ELSE UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>
 RowW1Send == /\ rowW1 # <<>>
              /\ IF sporen[1] = <<>>
                 THEN newW1' = Head(rowW1) /\ rowW1' = Tail(rowW1) /\ sporen' = [sporen EXCEPT ![1] = newW1'] /\ UNCHANGED <<bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW2, newC, newO1, newO2, rowW2, rowO1, rowO2, trains>>
                 ELSE  UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>
 RowW2Send == /\ rowW2 # <<>>
              /\ IF sporen[2] = <<>>
                 THEN newW2' = Head(rowW2) /\ rowW2' = Tail(rowW2) /\ sporen' = [sporen EXCEPT ![2] = newW2 '] /\ UNCHANGED <<bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newC, newO1, newO2, rowW1, rowO1, rowO2, trains>>
                 ELSE UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>
(*Bereken de volgende bestemming van (mogelijke) trein op spoor C*)
SpoorC == /\ IF sporen[3] # <<>>
             THEN CASE sporen[3][2] = 1 -> CASE \/ sporen[4] = <<>> \/ sporen[4][2] = 1 -> /\ bestemmingC' = 4
                                          [] \/ sporen[5] = <<>> \/ sporen[5][2] = 1 -> /\ bestemmingC' = 5
                                          [] OTHER -> bestemmingC' = 3
                 [] sporen[3][2] = 0 -> CASE \/ sporen[1] = <<>> \/ sporen[1][2] = 0 -> /\ bestemmingC' = 1
                                          [] \/ sporen[2] = <<>> \/ sporen[2][2] = 0 -> /\ bestemmingC' = 2
                                          [] OTHER -> bestemmingC' = 3
                 (*[] OTHER -> bestemmingC' = -1*)
             ELSE bestemmingC' = -1 
          /\ UNCHANGED  <<sporen, bestemmingW1, bestemmingW2, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>    

(*Bereken de volgende bestemming van (mogelijke) trein op spoor W1*)
SpoorW1 == /\ IF sporen[1] # <<>>
              THEN CASE sporen[1][2] = 0 -> bestemmingW1' = 0
                  [] sporen[1][2] = 1 -> CASE (bestemmingC' > 3 \/ bestemmingC' = -1) -> (bestemmingW1' = 3)
                                         [] OTHER -> bestemmingW1' = 1
                  (*[] OTHER -> bestemmingW1' = -1*)
              ELSE bestemmingW1' = -1
           /\ UNCHANGED <<sporen, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>
           

(*Bereken de volgende bestemming van (mogelijke) trein op spoor W2*)
SpoorW2 == /\ IF sporen[2] # <<>>
              THEN CASE sporen[2][2] = 0 -> bestemmingW2' = 0
                  [] sporen[2][2] = 1 -> IF /\ (bestemmingC' > 3 \/ bestemmingC' = -1) /\ (bestemmingW1' # 3) # TRUE THEN /\ bestemmingW2' = 3 ELSE bestemmingW2' = 2
                  (*[] OTHER -> bestemmingW2' = -1*)
              ELSE bestemmingW2' = -1    
           /\ UNCHANGED <<sporen, bestemmingW1, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>    

(*Bereken de volgende bestemming van (mogelijke) trein op spoor O1*)
SpoorO1 == /\ IF sporen[4] # <<>>
              THEN CASE sporen[4][2] = 1 -> bestemmingO1' = 6
                  [] sporen[4][2] = 0 -> IF (bestemmingC' < 3 ) /\ bestemmingW1' # 3 /\ bestemmingW2 # 3 THEN /\ bestemmingO1' = 3 ELSE bestemmingO1' = 4
                  (*[] OTHER -> bestemmingO1' = -1*)
              ELSE bestemmingO1' = -1
           /\ UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO2, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>
  
(*Bereken de volgende bestemming van (mogelijke) trein op spoor O2*)
SpoorO2 == /\ IF sporen[5] # <<>>
              THEN CASE sporen[5][2] = 1 -> bestemmingO2' = 6
                  [] sporen[5][2] = 0 -> IF /\ bestemmingC' < 3 /\ bestemmingW1' # 3 /\ bestemmingW2 # 3 /\ bestemmingO1 # 3 THEN /\ bestemmingO2' = 3 ELSE bestemmingO2' = 5
                  (*[] OTHER -> bestemmingO2' = -1*)
              ELSE bestemmingO2' = -1
           /\ UNCHANGED <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, newW1, newW2, newC, newO1, newO2, rowW1, rowW2, rowO1, rowO2, trains>>

(*Voer de verplaatsingen door*)
Verplaatsing == /\ CASE bestemmingW1' = 1 -> newW1' = sporen[1]
                     [] bestemmingC' = 1 -> newW1' = sporen[3]
                     [] OTHER -> newW1' = <<>>
                /\ CASE bestemmingW2' = 2 -> newW2' = sporen[2]
                     [] bestemmingC' = 2 -> newW2' = sporen[3]
                     [] OTHER -> newW2' = <<>>
                /\ CASE bestemmingC' = 3 -> newC' = sporen[3]
                     [] bestemmingW1' = 3 -> newC' = sporen[1]
                     [] bestemmingW2' = 3 -> newC' = sporen[2]
                     [] bestemmingO1' = 3 -> newC' = sporen[4]
                     [] bestemmingO2' = 3 -> newC' = sporen[5]
                     [] OTHER -> newC' = <<>>
                /\ CASE bestemmingO1' = 4 -> newO1' = sporen[4]
                     [] bestemmingC' = 4 -> newO1' = sporen[3]
                     [] OTHER -> newO1' = <<>>
                /\ CASE bestemmingO2' = 5 -> newO2' = sporen[5]
                     [] bestemmingC' = 5 -> newO2' = sporen[5]
                     [] OTHER -> newO2' = <<>>
                /\ sporen' = [sporen EXCEPT ![1] = newW1', ![2] = newW2', ![3] = newC', ![4] = newO1', ![5] = newO2']
                /\ UNCHANGED <<bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, rowW1, rowW2, rowO1, rowO2, trains>>
Next == \/(/\ SpoorC /\ SpoorW1 /\ SpoorW2 /\ SpoorO1 /\ SpoorO2 /\ Verplaatsing)
        \/ RowO1Rcv 
        \/ RowO2Rcv 
        \/ RowW1Rcv
        \/ RowW2Rcv
        \/ RowO1Send 
        \/ RowO2Send 
        \/ RowW1Send
        \/ RowW2Send
        
Spec == Init/\[][Next]_vars

NotSolved == sporen # [n \in 1..5 |-> <<>>]
--------------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []NotSolved
=============================================================================

=============================================================================
\* Modification History
\* Last modified Tue Apr 27 10:49:38 CEST 2021 by ysabe
\* Created Fri Apr 23 15:23:31 CEST 2021 by ysabe
