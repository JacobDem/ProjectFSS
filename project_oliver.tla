------------------------------ MODULE project ------------------------------
EXTENDS Integers, Sequences

VARIABLES sporen,             (*Lijst van elementen die de treinen bevat. Volgorde: spoor W1, W2, C, O1, O2.
                              Treinen worden weergegeven als <<treinnumer, richting>>. Waarbij richting = 1 W->O is 
                              en 0 O->W is. *)
                              
          bestemmingen,       (*Lijst van volgende station-perron. Per station staat hier een getal dat voorstelt naar waar
                              de volgende trein KAN gaan. 1 is W1, 2 is W2, 3 is C, 4 is O1, 5 is O2. -1 is de waarde
                              die zegt dat er geen trein aanwezig is op dit perron. 0 is de waarde die wordt gebruikt om naar 
                              westen te rijden, 6 om naar het oosten te rijden (buiten ons netwerk) *) 
                                        
          new,                (*Lijst van elementen die de treinen bevat. Wordt gebruikt om de nieuwe situatie in op te 
                              slaan alvorens de situatie uit te voeren*)
                              
          buffers,            (*Lijst van buffers voor inkomende treinen, die wachten om perron W1, W2, O1 en O2 op te rijden*) 
          treinCount          (*Aantal treinen op het netwerk. Wordt gebruikt om treinen een treinnumer te geven.*)

CONSTANTS bufferGrootte       (*aantal treinen in buffers*)
-----------------------------------------------------------------------------
vars == <<sporen, bestemmingen, new, buffers, treinCount>>

unchangedVars == <<sporen, bestemmingen, new>>

(* Initalisatie *)
Init == /\ sporen =[[n \in 1..5 |-> << >>] EXCEPT ![1] = <<1,1>>, ![3] = <<2,0>>, ![5] = <<3,0>>]
        /\ bestemmingen = [n \in 1..5 |-> -1]
        /\ new = [n \in 1..5 |-> -1]
        /\ buffers = [n \in 1..5 |-> << >>]
        /\ treinCount = 3 \* Want al 3 treinen hierboven. Enkel voor test! Ook test runnen met problemen zoals in tekst.*\

(*Bereken de volgende bestemming van (mogelijke) trein op spoor C. 
Als naar oosten, en O1 of O2 is vrij, bestemming is een van deze (prioriteit O1). Anders blijf staan.
Als naar westen, en W1 of W2 is vrij, bestemming is een van deze. Anders blijf staan.
Indien geen trein, geen bestemming opgeven.*)
SpoorC == IF sporen[3] # <<>>
          THEN CASE sporen[3][2] = 1 -> CASE \/ sporen[4] = <<>> \/ sporen[4][2] = 1 -> /\ bestemmingen[3]' = 4
                                          [] \/ sporen[5] = <<>> \/ sporen[5][2] = 1 -> /\ bestemmingen[3]' = 5
                                          [] OTHER -> bestemmingen[3]' = 3
                 [] sporen[3][2] = 0 -> CASE \/ sporen[1] = <<>> \/ sporen[1][2] = 0 -> /\ bestemmingen[3]' = 1
                                          [] \/ sporen[2] = <<>> \/ sporen[2][2] = 0 -> /\ bestemmingen[3]' = 2
                                          [] OTHER -> bestemmingen[3]' = 3
                 [] OTHER ->  bestemmingen[3]' = -1
          ELSE  bestemmingen[3]' = -1       

(*Bereken de volgende bestemming van (mogelijke) trein op spoor W1. 
Als naar westen, rijdt naar westen. 
Als naar oosten, kijk of er al een trein naar C rijd, indien niet rijdt naar C.*)
SpoorW1 == IF sporen[1] # <<>>
           THEN CASE sporen[1][2] = 0 -> bestemmingen[1]' = 0
                  [] sporen[1][2] = 1 -> CASE (\/ bestemmingen[3]' > 3 \/ bestemmingen[3]' = -1) -> (bestemmingen[1]' = 3)
                                         [] OTHER -> bestemmingen[1]' = 1
                  [] OTHER -> bestemmingen[1]' = -1
           ELSE bestemmingen[1]' = -1

(*Bereken de volgende bestemming van (mogelijke) trein op spoor W2*)
SpoorW2 == IF sporen[2] # <<>>
           THEN CASE sporen[2][2] = 0 -> bestemmingen[2]' = 0
                  [] sporen[2][2] = 1 -> IF /\ (bestemmingen[3]' > 3 \/ bestemmingen[3]' = -1) /\ (bestemmingen[1]' # 3) THEN /\ bestemmingen[2]' = 3 ELSE bestemmingen[2]' = 2
                  [] OTHER -> bestemmingen[2]' = -1
           ELSE bestemmingen[2]' = -1        

(*Bereken de volgende bestemming van (mogelijke) trein op spoor O1*)
SpoorO1 == IF sporen[4] # <<>>
           THEN CASE sporen[4][2] = 1 -> bestemmingen[4]' = 6
                  [] sporen[4][2] = 0 -> IF /\ (bestemmingen[3]' < 3) /\ bestemmingen[1]' # 3 /\ bestemmingen[2]' # 3 THEN /\ bestemmingen[4]' = 3 ELSE bestemmingen[4]' = 4
                  [] OTHER -> bestemmingen[4]' = -1
           ELSE bestemmingen[4]' = -1
  
(*Bereken de volgende bestemming van (mogelijke) trein op spoor O2*)
SpoorO2 == IF sporen[5] # <<>>
           THEN CASE sporen[5][2] = 1 -> bestemmingen[5]' = 6
                  [] sporen[5][2] = 0 -> IF /\ (bestemmingen[3]' < 3) /\ bestemmingen[1]' # 3 /\ bestemmingen[2]' # 3 /\ bestemmingen[4]' # 3 THEN /\ bestemmingen[5]' = 3 ELSE bestemmingen[5]' = 5
                  [] OTHER -> bestemmingen[5]' = -1
           ELSE bestemmingen[5]' = -1

(*Voer de verplaatsingen door*)
Verplaatsing == /\ (\/ bestemmingen[1]' # 1 \/ bestemmingen[2]' # 2 \/ bestemmingen[3]' # 3 \/ bestemmingen[4]' # 4 \/ bestemmingen[5]' # 5)
                /\ CASE bestemmingen[1]' = 1 -> new[1]' = sporen[1] /\ UNCHANGED buffers[1]
                     [] bestemmingen[3]' = 1 -> new[1]' = sporen[3] /\ UNCHANGED buffers[1]
                     [] OTHER -> IF (Len(buffers[1]) # 0 /\ sporen[1] = <<>>) THEN (new[1]' = Head(buffers[1]) /\ buffers[1]' = Tail(buffers[1])) ELSE (new[1]' = <<>> /\ UNCHANGED buffers[1])
                /\ CASE bestemmingen[2]' = 2 -> new[2]' = sporen[2] /\ UNCHANGED buffers[2]
                     [] bestemmingen[3]' = 2 -> new[2]' = sporen[3] /\ UNCHANGED buffers[2]
                     [] OTHER -> IF (Len(buffers[2]) # 0 /\ sporen[2] = <<>>) THEN (new[2]' = Head(buffers[2]) /\ buffers[2]' = Tail(buffers[2])) ELSE (new[2]' = <<>> /\ UNCHANGED buffers[2])
                /\ CASE bestemmingen[1]' = 3 -> new[3]' = sporen[3]
                     [] bestemmingen[3]' = 3 -> new[3]' = sporen[1]
                     [] bestemmingen[2]' = 3 -> new[3]' = sporen[2]
                     [] bestemmingen[4]' = 3 -> new[3]' = sporen[4]
                     [] bestemmingen[5]' = 3 -> new[3]' = sporen[5]
                     [] OTHER -> new[3]' = <<>>
                /\ CASE bestemmingen[4]' = 4 -> new[4]' = sporen[4] /\ UNCHANGED buffers[4]
                     [] bestemmingen[3]' = 4 -> new[4]' = sporen[3] /\ UNCHANGED buffers[4]
                     [] OTHER -> IF (Len(buffers[4]) # 0 /\ sporen[4] = <<>>) THEN (new[4]' = Head(buffers[4]) /\ buffers[4]' = Tail(buffers[4])) ELSE (new[4]' = <<>> /\ UNCHANGED buffers[4])
                /\ CASE bestemmingen[5]' = 5 -> new[5]' = sporen[5] /\ UNCHANGED buffers[5]
                     [] bestemmingen[3]' = 5 -> new[5]' = sporen[5] /\ UNCHANGED buffers[5]
                     [] OTHER -> IF (Len(buffers[5]) # 0 /\ sporen[5] = <<>>) THEN (new[5]' = Head(buffers[5]) /\ buffers[5]' = Tail(buffers[5])) ELSE (new[5]' = <<>> /\ UNCHANGED buffers[5])
                /\ sporen' = [sporen EXCEPT ![1] = new[1]', ![2] = new[2]', ![3] = new[3]', ![4] = new[4]', ![5] = new[5]']
                /\ UNCHANGED treinCount
                
aankomstW1 == /\ Len(buffers[1]) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ buffers[1]' = buffers[1] \o <<<<treinCount',1>>>>
              /\ UNCHANGED unchangedVars
              /\ UNCHANGED buffers[4]
              /\ UNCHANGED buffers[5]
              /\ UNCHANGED buffers[2]
              
aankomstW2 == /\ Len(buffers[2]) < bufferGrootte
              /\ treinCount' = treinCount + 1
              /\ buffers[2]' = buffers[2] \o <<<<treinCount',1>>>>
              /\ UNCHANGED unchangedVars
              /\ UNCHANGED buffers[4]
              /\ UNCHANGED buffers[5]
              /\ UNCHANGED buffers[1]
              
aankomstO1 == /\ Len(buffers[4]) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ buffers[4]' = buffers[4] \o <<<<treinCount',0>>>>
              /\ UNCHANGED unchangedVars
              /\ UNCHANGED buffers[2]
              /\ UNCHANGED buffers[5]
              /\ UNCHANGED buffers[1]
              
aankomstO2 == /\ Len(buffers[5]) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ buffers[5]' = buffers[5] \o <<<<treinCount',0>>>>
              /\ UNCHANGED unchangedVars
              /\ UNCHANGED buffers[2]
              /\ UNCHANGED buffers[4]
              /\ UNCHANGED buffers[1]
             
aankomstW == \/ aankomstW1 \/ aankomstW2
aankomstO == \/ aankomstO1 \/ aankomstO2

nieuweTrein == \/ aankomstW 
               \/ aankomstO

doorrijden == /\ SpoorC /\ SpoorW1 /\ SpoorW2 /\ SpoorO1 /\ SpoorO2 /\ Verplaatsing

Next == \/ doorrijden \/ nieuweTrein 
        
Spec == Init/\[][Next]_vars

NotSolved == \/ treinCount < 10 \/ sporen # [n \in 1..5 |-> <<>>] \/ buffers[1] # <<>> \/ buffers[2] # <<>> \/ buffers[4] # <<>> \/ buffers[5] # <<>>
--------------------------------------------------------------------------------
=============================================================================


\* Modification History
\* Last modified Sun Apr 25 11:30:37 CEST 2021 by Oliver De Vijt
\* Last modified Fri Apr 23 19:33:18 CEST 2021 by jacob
\* Created Thu Apr 22 11:45:14 CEST 2021 by jacob
