------------------------------ MODULE project ------------------------------
EXTENDS Integers, Sequences

VARIABLES sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, bufferW1, bufferO1, bufferW2, bufferO2, treinCount

CONSTANTS bufferGrootte
-----------------------------------------------------------------------------
vars == <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2, bufferW1, bufferW2, bufferO1, bufferO2, treinCount>>

unchangedVars == <<sporen, bestemmingW1, bestemmingW2, bestemmingC, bestemmingO1, bestemmingO2, newW1, newW2, newC, newO1, newO2>>

(* Trein = tuple met betekenis <<treinnummer,richting>>: richting = 1 voor W -> O en 0 voor O -> W
   De 5 treinsporen zijn de lijst "sporen": positie 1 is spoor W1, positie 2 is spoor W2, ... *)

Init == /\ sporen =[[n \in 1..5 |-> <<>>] EXCEPT ![1] = <<1,1>>, ![3] = <<2,0>>, ![5] = <<3,0>>]
        /\ (/\ bestemmingW1 = -1 /\ bestemmingW2 = -1 /\ bestemmingC = -1 /\ bestemmingO1 = -1 /\ bestemmingO2 = -1 /\ newW1 = -1 /\ newW2 = -1 /\ newC = -1 /\ newO1 = -1 /\ newO2 = -1)
        /\ bufferW1 = <<>>
        /\ bufferO1 = <<>>
        /\ bufferW2 = <<>>
        /\ bufferO2 = <<>>
        /\ treinCount = 3

(*Bereken de volgende bestemming van (mogelijke) trein op spoor C*)
SpoorC == IF sporen[3] # <<>>
          THEN CASE sporen[3][2] = 1 -> CASE \/ sporen[4] = <<>> \/ sporen[4][2] = 1 -> /\ bestemmingC' = 4
                                          [] \/ sporen[5] = <<>> \/ sporen[5][2] = 1 -> /\ bestemmingC' = 5
                                          [] OTHER -> bestemmingC' = 3
                 [] sporen[3][2] = 0 -> CASE \/ sporen[1] = <<>> \/ sporen[1][2] = 0 -> /\ bestemmingC' = 1
                                          [] \/ sporen[2] = <<>> \/ sporen[2][2] = 0 -> /\ bestemmingC' = 2
                                          [] OTHER -> bestemmingC' = 3
                 [] OTHER -> bestemmingC' = -1
          ELSE bestemmingC' = -1       

(*Bereken de volgende bestemming van (mogelijke) trein op spoor W1*)
SpoorW1 == IF sporen[1] # <<>>
           THEN CASE sporen[1][2] = 0 -> bestemmingW1' = 0
                  [] sporen[1][2] = 1 -> CASE (\/ bestemmingC' > 3 \/ bestemmingC' = -1) -> (bestemmingW1' = 3)
                                         [] OTHER -> bestemmingW1' = 1
                  [] OTHER -> bestemmingW1' = -1
           ELSE bestemmingW1' = -1

(*Bereken de volgende bestemming van (mogelijke) trein op spoor W2*)
SpoorW2 == IF sporen[2] # <<>>
           THEN CASE sporen[2][2] = 0 -> bestemmingW2' = 0
                  [] sporen[2][2] = 1 -> IF /\ (bestemmingC' > 3 \/ bestemmingC' = -1) /\ (bestemmingW1' # 3) THEN /\ bestemmingW2' = 3 ELSE bestemmingW2' = 2
                  [] OTHER -> bestemmingW2' = -1
           ELSE bestemmingW2' = -1        

(*Bereken de volgende bestemming van (mogelijke) trein op spoor O1*)
SpoorO1 == IF sporen[4] # <<>>
           THEN CASE sporen[4][2] = 1 -> bestemmingO1' = 6
                  [] sporen[4][2] = 0 -> IF /\ (bestemmingC' < 3) /\ bestemmingW1' # 3 /\ bestemmingW2' # 3 THEN /\ bestemmingO1' = 3 ELSE bestemmingO1' = 4
                  [] OTHER -> bestemmingO1' = -1
           ELSE bestemmingO1' = -1
  
(*Bereken de volgende bestemming van (mogelijke) trein op spoor O2*)
SpoorO2 == IF sporen[5] # <<>>
           THEN CASE sporen[5][2] = 1 -> bestemmingO2' = 6
                  [] sporen[5][2] = 0 -> IF /\ (bestemmingC' < 3) /\ bestemmingW1' # 3 /\ bestemmingW2' # 3 /\ bestemmingO1' # 3 THEN /\ bestemmingO2' = 3 ELSE bestemmingO1' = 5
                  [] OTHER -> bestemmingO2' = -1
           ELSE bestemmingO2' = -1

(*Voer de verplaatsingen door*)
Verplaatsing == /\ (\/ bestemmingW1' # 1 \/ bestemmingW2' # 2 \/ bestemmingC' # 3 \/ bestemmingO1' # 4 \/ bestemmingO2' # 5)
                /\ CASE bestemmingW1' = 1 -> newW1' = sporen[1] /\ UNCHANGED bufferW1
                     [] bestemmingC' = 1 -> newW1' = sporen[3] /\ UNCHANGED bufferW1
                     [] OTHER -> IF (Len(bufferW1) # 0 /\ sporen[1] = <<>>) THEN (newW1' = Head(bufferW1) /\ bufferW1' = Tail(bufferW1)) ELSE (newW1' = <<>> /\ UNCHANGED bufferW1)
                /\ CASE bestemmingW2' = 2 -> newW2' = sporen[2] /\ UNCHANGED bufferW2
                     [] bestemmingC' = 2 -> newW2' = sporen[3] /\ UNCHANGED bufferW2
                     [] OTHER -> IF (Len(bufferW2) # 0 /\ sporen[2] = <<>>) THEN (newW2' = Head(bufferW2) /\ bufferW2' = Tail(bufferW2)) ELSE (newW2' = <<>> /\ UNCHANGED bufferW2)
                /\ CASE bestemmingC' = 3 -> newC' = sporen[3]
                     [] bestemmingW1' = 3 -> newC' = sporen[1]
                     [] bestemmingW2' = 3 -> newC' = sporen[2]
                     [] bestemmingO1' = 3 -> newC' = sporen[4]
                     [] bestemmingO2' = 3 -> newC' = sporen[5]
                     [] OTHER -> newC' = <<>>
                /\ CASE bestemmingO1' = 4 -> newO1' = sporen[4] /\ UNCHANGED bufferO1
                     [] bestemmingC' = 4 -> newO1' = sporen[3] /\ UNCHANGED bufferO1
                     [] OTHER -> IF (Len(bufferO1) # 0 /\ sporen[4] = <<>>) THEN (newO1' = Head(bufferO1) /\ bufferO1' = Tail(bufferO1)) ELSE (newO1' = <<>> /\ UNCHANGED bufferO1)
                /\ CASE bestemmingO2' = 5 -> newO2' = sporen[5] /\ UNCHANGED bufferO2
                     [] bestemmingC' = 5 -> newO2' = sporen[5] /\ UNCHANGED bufferO2
                     [] OTHER -> IF (Len(bufferO2) # 0 /\ sporen[5] = <<>>) THEN (newO2' = Head(bufferO2) /\ bufferO2' = Tail(bufferO2)) ELSE (newO2' = <<>> /\ UNCHANGED bufferO2)
                /\ sporen' = [sporen EXCEPT ![1] = newW1', ![2] = newW2', ![3] = newC', ![4] = newO1', ![5] = newO2']
                /\ UNCHANGED treinCount
                
aankomstW1 == /\ Len(bufferW1) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ bufferW1' = bufferW1 \o <<<<treinCount',1>>>>
              /\ UNCHANGED unchangedVars
              /\ UNCHANGED bufferO1
              /\ UNCHANGED bufferO2
              /\ UNCHANGED bufferW2
              
aankomstW2 == /\ Len(bufferW2) < bufferGrootte
              /\ treinCount' = treinCount + 1
              /\ bufferW2' = bufferW2 \o <<<<treinCount',1>>>>
              /\ UNCHANGED unchangedVars
              /\ UNCHANGED bufferO1
              /\ UNCHANGED bufferO2
              /\ UNCHANGED bufferW1
              
aankomstO1 == /\ Len(bufferO1) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ bufferO1' = bufferO1 \o <<<<treinCount',0>>>>
              /\ UNCHANGED unchangedVars
              /\ UNCHANGED bufferW2
              /\ UNCHANGED bufferO2
              /\ UNCHANGED bufferW1
              
aankomstO2 == /\ Len(bufferO2) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ bufferO2' = bufferO2 \o <<<<treinCount',0>>>>
              /\ UNCHANGED unchangedVars
              /\ UNCHANGED bufferW2
              /\ UNCHANGED bufferO1
              /\ UNCHANGED bufferW1
             
aankomstW == \/ aankomstW1 \/ aankomstW2
aankomstO == \/ aankomstO1 \/ aankomstO2

nieuweTrein == \/ aankomstW 
               \/ aankomstO

doorrijden == /\ SpoorC /\ SpoorW1 /\ SpoorW2 /\ SpoorO1 /\ SpoorO2 /\ Verplaatsing

Next == \/ doorrijden \/ nieuweTrein 
        
Spec == Init/\[][Next]_vars

NotSolved == \/ treinCount < 10 \/ sporen # [n \in 1..5 |-> <<>>] \/ bufferW1 # <<>> \/ bufferW2 # <<>> \/ bufferO1 # <<>> \/ bufferO2 # <<>>
--------------------------------------------------------------------------------
=============================================================================


\* Modification History
\* Last modified Fri Apr 23 19:21:06 CEST 2021 by jacob
\* Created Thu Apr 22 11:45:14 CEST 2021 by jacob
