 ------------------------------ MODULE Project_oliver_fair ------------------------------
EXTENDS Integers, Sequences

VARIABLES sporen,             (*Lijst die de sporen voorsteld en treinen kan bevatten. Volgorde: spoor W1, W2, C, O1, O2.
                              Treinen worden weergegeven als <<richting>>. Waarbij richting = 1 W->O is 
                              en 0 O->W is. -1 is nog geen bestemming.*)
                              
          bestemmingen,       (*Lijst met lengte = aantal sporen. Per spoor staat hier een getal dat voorstelt naar waar
                              de volgende trein KAN gaan. 1 is W1, 2 is W2, 3 is C, 4 is O1, 5 is O2. -1 is de waarde
                              die zegt dat er geen trein aanwezig is op dit perron. 0 is de waarde die wordt gebruikt om naar 
                              westen te rijden, 6 om naar het oosten te rijden (buiten ons netwerk) *) 
                                        
          newW1, newW2,      (*Elementen die treinen bevatten. Wordt gebruikt om de nieuwe situatie in op te slaan alvorens *)
          newW3, newW4,      (*de situatie uit te voeren*)
          newC1, newC2,
          newO1, newO2, 
          newO3, newO4,          

                   
          bufferW,               (*Buffers voor inkomende treinen, die wachten om perron W1, W2, O1 en O2 op te rijden*) 
          bufferO,
                    
          CWTopBezet,            (*Geeft aan of de verbinding C -> O reeds wordt gebruikt in de huidige cyclus*)
          CWBottomBezet,         (*Geeft aan of de verbinding C -> W reeds wordt gebruikt in de huidige cyclus*)
          COTopBezet,            (*Geeft aan of het perron C al geclaimd is in de huidige cyclus*)
          COBottomBezet,
          
          C1Bezet,
          C2Bezet,
          
          magDoorrijden,      (*Geeft aan of elke trein een nieuwe bestemming is toegewezen*)
          spoorVeranderd,     (*Lijst van getallen die aangeven welk perron reeds een nieuwe bestemming is toegewezen*)
          
          verplaatst,         (*Geeft aan of de verplaatsingen zijn doorgevoerd. Wordt gebruikt om de buffers te laten
                              weten dat er treinen uit de buffers naar de sporen mag gebracht worden*)
                              
          buffersGecontroleerd (*Lijst van getallen die aangeven welke buffers al eventueel een trein op een spoor
                               hebben kunnen zetten*)
 
CONSTANTS bufferGrootte       (*aantal treinen in buffers*)
-----------------------------------------------------------------------------
vars == <<sporen, bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst, buffersGecontroleerd>>

(* Initalisatie *)
Init == /\ sporen =[n \in 1..10 |-> -1 ]
        /\ bestemmingen = [n \in 1..10 |-> -1]
        /\ newW1 = -1 /\ newW2 = -1 /\ newW3 = -1 /\ newW4 = -1 /\ newC1 = -1 /\ newC2 = -1 /\ newO1 = -1 /\ newO2 = -1 /\ newO3 = -1 /\ newO4 = -1
        /\ bufferW = 0 /\ bufferO = 0
        /\ CWTopBezet = FALSE
        /\ CWBottomBezet = FALSE
        /\ COTopBezet = FALSE
        /\ COBottomBezet = FALSE
        /\ C1Bezet = FALSE
        /\ C2Bezet = FALSE
        /\ magDoorrijden = FALSE
        /\ spoorVeranderd = [n \in 1..10 |-> 0]
        /\ verplaatst = FALSE
        /\ buffersGecontroleerd = [n \in 1..8 |-> 0]
        
TypeInvariant == /\ \A n \in 1..10: sporen[n] \in (-1..1)
                 /\ \A n \in 1..4: bestemmingen[n] \in (-1..6)               (*Bestemming van treinen moet mogelijk zijn*)
                 /\ \A n \in 5..6: bestemmingen[n] \in {-1,1,2,3,4,n,7,8,9,10}   
                 /\ \A n \in 7..10: bestemmingen[n] \in {-1,5,6,n,11}
                 /\ newW1 \in (-1..1) /\ newW2 \in (-1..1) /\ newW3 \in (-1..1) /\ newW4 \in (-1..1) /\ newC1 \in (-1..1) /\ newC2 \in (-1..1) /\ newO1 \in (-1..1) /\ newO2 \in (-1..1)/\ newO3 \in (-1..1) /\ newO4 \in (-1..1)
                 /\ bufferW \in (0..bufferGrootte) /\ bufferO \in (0..bufferGrootte)
                 /\ CWTopBezet \in {TRUE, FALSE}
                 /\ CWBottomBezet \in {TRUE, FALSE}
                 /\ COTopBezet \in {TRUE, FALSE}
                 /\ COBottomBezet \in {TRUE, FALSE}
                 /\ C1Bezet \in {TRUE, FALSE}
                 /\ C2Bezet \in {TRUE, FALSE}
                 /\ magDoorrijden \in {TRUE, FALSE}
                 /\ \A n \in 1..10: spoorVeranderd[n] \in (0..1)
                 /\ verplaatst \in {TRUE, FALSE}
                 /\ \A n \in 1..8: buffersGecontroleerd[n] \in (0..1)

(*Constructies die vaker voorkomen*)
spoorW1Safe == IF sporen[1] # -1 THEN sporen[1] = 0 ELSE TRUE
spoorW2Safe == IF sporen[2] # -1 THEN sporen[2] = 0 ELSE TRUE
spoorW3Safe == IF sporen[3] # -1 THEN sporen[3] = 0 ELSE TRUE
spoorW4Safe == IF sporen[4] # -1 THEN sporen[4] = 0 ELSE TRUE
spoorO1Safe == IF sporen[7] # -1 THEN sporen[7] = 1 ELSE TRUE
spoorO2Safe == IF sporen[8] # -1 THEN sporen[8] = 1 ELSE TRUE
spoorO3Safe == IF sporen[9] # -1 THEN sporen[9] = 1 ELSE TRUE
spoorO4Safe == IF sporen[10] # -1 THEN sporen[10] = 1 ELSE TRUE



----------------------(*VERPLAATSING VAN DE TREINEN*)-----------------------------


(*Bereken de volgende bestemming van (mogelijke) trein op spoor C. 
Als naar oosten, en O1 of O2 is vrij, bestemming is een van deze (prioriteit O1). Anders blijf staan.
Als naar westen, en W1 of W2 is vrij, bestemming is een van deze. Anders blijf staan.
Indien geen trein, geen bestemming opgeven.*)
SpoorC1 == /\ spoorVeranderd[5] = 0
           /\ IF sporen[5] # -1
              THEN CASE sporen[5] = 1 -> CASE /\ (\/ sporen[7] = -1 \/ sporen[7] = 1) /\ COTopBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 7] /\ COTopBezet' = TRUE /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet
                                              [] /\ (\/ sporen[8] = -1 \/ sporen[8] = 1) /\ COTopBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 8] /\ COTopBezet' = TRUE /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet
                                              [] /\ (\/ sporen[9] = -1 \/ sporen[9] = 1) /\ COTopBezet = FALSE /\ COBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 9] /\ COTopBezet' = TRUE /\ COBottomBezet' = TRUE /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet
                                              [] /\ (\/ sporen[10] = -1 \/ sporen[10] = 1) /\ COTopBezet = FALSE /\ COBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 10] /\ COTopBezet' = TRUE /\ COBottomBezet' = TRUE /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet
                                              [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 5] /\ C1Bezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet
                     [] sporen[5] = 0 -> CASE /\ (\/ sporen[1] = -1 \/ sporen[1] = 0) /\ CWTopBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 1] /\ CWTopBezet' = TRUE /\ UNCHANGED COBottomBezet /\ UNCHANGED COTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet
                                              [] /\ (\/ sporen[2] = -1 \/ sporen[2] = 0) /\ CWTopBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 2] /\ CWTopBezet' = TRUE /\ UNCHANGED COBottomBezet /\ UNCHANGED COTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet
                                              [] /\ (\/ sporen[3] = -1 \/ sporen[3] = 0) /\ CWTopBezet = FALSE /\ CWBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 3] /\ CWTopBezet' = TRUE /\ CWBottomBezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet
                                              [] /\ (\/ sporen[4] = -1 \/ sporen[4] = 0) /\ CWTopBezet = FALSE /\ CWBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 4] /\ CWTopBezet' = TRUE /\ CWBottomBezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet
                                              [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 5] /\ C1Bezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet
             ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![5] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![5] = 1]
           /\ UNCHANGED <<sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, C2Bezet, magDoorrijden, verplaatst, buffersGecontroleerd>>

SpoorC2 == /\ spoorVeranderd[6] = 0
           /\ IF sporen[6] # -1
              THEN CASE sporen[6] = 1 -> CASE /\ (\/ sporen[9] = -1 \/ sporen[9] = 1) /\ COBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 9] /\ COBottomBezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C2Bezet
                                              [] /\ (\/ sporen[10] = -1 \/ sporen[10] = 1) /\ COBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 10] /\ COBottomBezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C2Bezet
                                              [] /\ (\/ sporen[7] = -1 \/ sporen[7] = 1) /\ COTopBezet = FALSE /\ COBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 7] /\ COTopBezet' = TRUE /\ COBottomBezet' = TRUE /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C2Bezet
                                              [] /\ (\/ sporen[8] = -1 \/ sporen[8] = 1) /\ COTopBezet = FALSE /\ COBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 8] /\ COTopBezet' = TRUE /\ COBottomBezet' = TRUE /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C2Bezet
                                              [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 6] /\ C2Bezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet
                     [] sporen[6] = 0 -> CASE /\ (\/ sporen[3] = -1 \/ sporen[3] = 0) /\ CWBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 3] /\ CWBottomBezet' = TRUE /\ UNCHANGED COBottomBezet /\ UNCHANGED COTopBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED C2Bezet
                                              [] /\ (\/ sporen[4] = -1 \/ sporen[4] = 0) /\ CWBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 4] /\ CWBottomBezet' = TRUE /\ UNCHANGED COBottomBezet /\ UNCHANGED COTopBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED C2Bezet
                                              [] /\ (\/ sporen[1] = -1 \/ sporen[1] = 0) /\ CWTopBezet = FALSE /\ CWBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 1] /\ CWTopBezet' = TRUE /\ CWBottomBezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C2Bezet
                                              [] /\ (\/ sporen[2] = -1 \/ sporen[2] = 0) /\ CWTopBezet = FALSE /\ CWBottomBezet = FALSE -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 2] /\ CWTopBezet' = TRUE /\ CWBottomBezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C2Bezet
                                              [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = 6] /\ C2Bezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![6] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C2Bezet
             ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![6] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C2Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![6] = 1]
           /\ UNCHANGED <<sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, C1Bezet, magDoorrijden, verplaatst, buffersGecontroleerd>>

(*Bereken de volgende bestemming van (mogelijke) trein op spoor W1*)
SpoorW1 == /\ spoorVeranderd[1] = 0
           /\ IF sporen[1] # -1
              THEN CASE sporen[1] = 0 -> /\ bestemmingen' = [bestemmingen EXCEPT ![1] = 0] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
                     [] sporen[1] = 1 -> CASE /\ C1Bezet = FALSE /\ CWTopBezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe \/ C2Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![1] = 5] /\ CWTopBezet' = TRUE /\ C1Bezet' = TRUE /\ UNCHANGED CWBottomBezet /\ UNCHANGED C2Bezet) 
                                              [] /\ C2Bezet = FALSE /\ CWTopBezet = FALSE /\ CWBottomBezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe \/ C1Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![1] = 6] /\ CWTopBezet' = TRUE /\ CWBottomBezet' = TRUE /\ C2Bezet' = TRUE /\ UNCHANGED C1Bezet) 
                                              [] OTHER -> (/\ bestemmingen' = [bestemmingen EXCEPT ![1] = 1] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet)
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![1] = -1] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![1] = -1] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![1] = 1] 
           /\ IF \A n \in 1..10 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, COTopBezet, COBottomBezet>>
                 
(*Bereken de volgende bestemming van (mogelijke) trein op spoor W2*)
SpoorW2 == /\ spoorVeranderd[2] = 0
           /\ IF sporen[2] # -1
              THEN CASE sporen[2] = 0 -> /\ bestemmingen' = [bestemmingen EXCEPT ![2] = 0] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
                     [] sporen[2] = 1 -> CASE /\ C1Bezet = FALSE /\ CWTopBezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe \/ C2Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![2] = 5] /\ CWTopBezet' = TRUE /\ C1Bezet' = TRUE /\ UNCHANGED CWBottomBezet /\ UNCHANGED C2Bezet) 
                                              [] /\ C2Bezet = FALSE /\ CWTopBezet = FALSE /\ CWBottomBezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe \/ C1Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![2] = 6] /\ CWTopBezet' = TRUE /\ CWBottomBezet' = TRUE /\ C2Bezet' = TRUE /\ UNCHANGED C1Bezet) 
                                              [] OTHER -> (/\ bestemmingen' = [bestemmingen EXCEPT ![2] = 2] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet)
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![2] = -1] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![2] = -1] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![2] = 1] 
           /\ IF \A n \in 1..10 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, COTopBezet, COBottomBezet>>

SpoorW3 == /\ spoorVeranderd[3] = 0
           /\ IF sporen[3] # -1
              THEN CASE sporen[3] = 0 -> /\ bestemmingen' = [bestemmingen EXCEPT ![3] = 0] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
                     [] sporen[3] = 1 -> CASE /\ C2Bezet = FALSE /\ CWBottomBezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe \/ C1Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![3] = 6] /\ CWBottomBezet' = TRUE /\ C2Bezet' = TRUE /\ UNCHANGED CWTopBezet /\ UNCHANGED C1Bezet) 
                                              [] /\ C1Bezet = FALSE /\ CWTopBezet = FALSE /\ CWBottomBezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe \/ C2Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![3] = 5] /\ CWTopBezet' = TRUE /\ CWBottomBezet' = TRUE /\ C1Bezet' = TRUE /\ UNCHANGED C2Bezet) 
                                              [] OTHER -> (/\ bestemmingen' = [bestemmingen EXCEPT ![3] = 3] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet)
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![3] = -1] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![3] = -1] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![3] = 1] 
           /\ IF \A n \in 1..10 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, COTopBezet, COBottomBezet>>

SpoorW4 == /\ spoorVeranderd[4] = 0
           /\ IF sporen[4] # -1
              THEN CASE sporen[4] = 0 -> /\ bestemmingen' = [bestemmingen EXCEPT ![4] = 0] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
                     [] sporen[4] = 1 -> CASE /\ C2Bezet = FALSE /\ CWBottomBezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe \/ C1Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![4] = 6] /\ CWBottomBezet' = TRUE /\ C2Bezet' = TRUE /\ UNCHANGED CWTopBezet /\ UNCHANGED C1Bezet) 
                                              [] /\ C1Bezet = FALSE /\ CWTopBezet = FALSE /\ CWBottomBezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe \/ C2Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![4] = 5] /\ CWTopBezet' = TRUE /\ CWBottomBezet' = TRUE /\ C1Bezet' = TRUE /\ UNCHANGED C2Bezet) 
                                              [] OTHER -> (/\ bestemmingen' = [bestemmingen EXCEPT ![4] = 4] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet)
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![4] = -1] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![4] = -1] /\ UNCHANGED CWTopBezet /\ UNCHANGED CWBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![4] = 1] 
           /\ IF \A n \in 1..10 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, COTopBezet, COBottomBezet>>


(*Bereken de volgende bestemming van (mogelijke) trein op spoor O1*)
SpoorO1 == /\ spoorVeranderd[7] = 0
           /\ IF sporen[7] # -1
              THEN CASE sporen[7] = 1 -> /\ bestemmingen' = [bestemmingen EXCEPT ![7] = 11] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
                     [] sporen[7] = 0 -> CASE /\ C1Bezet = FALSE /\ COTopBezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe \/ C2Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![7] = 5] /\ COTopBezet' = TRUE /\ C1Bezet' = TRUE /\ UNCHANGED COBottomBezet /\ UNCHANGED C2Bezet) 
                                              [] /\ C2Bezet = FALSE /\ COTopBezet = FALSE /\ COBottomBezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe \/ C1Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![7] = 6] /\ COTopBezet' = TRUE /\ COBottomBezet' = TRUE /\ C2Bezet' = TRUE /\ UNCHANGED C1Bezet) 
                                              [] OTHER -> (/\ bestemmingen' = [bestemmingen EXCEPT ![7] = 7] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet)
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![7] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![7] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![7] = 1] 
           /\ IF \A n \in 1..10 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, CWTopBezet, CWBottomBezet>>           

SpoorO2 == /\ spoorVeranderd[8] = 0
           /\ IF sporen[8] # -1
              THEN CASE sporen[8] = 1 -> /\ bestemmingen' = [bestemmingen EXCEPT ![8] = 11] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
                     [] sporen[8] = 0 -> CASE /\ C1Bezet = FALSE /\ COTopBezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe \/ C2Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![8] = 5] /\ COTopBezet' = TRUE /\ C1Bezet' = TRUE /\ UNCHANGED COBottomBezet /\ UNCHANGED C2Bezet) 
                                              [] /\ C2Bezet = FALSE /\ COTopBezet = FALSE /\ COBottomBezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe \/ C1Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![8] = 6] /\ COTopBezet' = TRUE /\ COBottomBezet' = TRUE /\ C2Bezet' = TRUE /\ UNCHANGED C1Bezet) 
                                              [] OTHER -> (/\ bestemmingen' = [bestemmingen EXCEPT ![8] = 8] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet)
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![8] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![8] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![8] = 1] 
           /\ IF \A n \in 1..10 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, CWTopBezet, CWBottomBezet>>           

SpoorO3 == /\ spoorVeranderd[9] = 0
           /\ IF sporen[9] # -1
              THEN CASE sporen[9] = 1 -> /\ bestemmingen' = [bestemmingen EXCEPT ![9] = 11] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
                     [] sporen[9] = 0 -> CASE /\ C2Bezet = FALSE /\ COBottomBezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe \/ C1Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![9] = 6] /\ COBottomBezet' = TRUE /\ C2Bezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED C1Bezet) 
                                              [] /\ C1Bezet = FALSE /\ COTopBezet = FALSE /\ COBottomBezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe \/ C2Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![9] = 5] /\ COTopBezet' = TRUE /\ COBottomBezet' = TRUE /\ C1Bezet' = TRUE /\ UNCHANGED C2Bezet) 
                                              [] OTHER -> (/\ bestemmingen' = [bestemmingen EXCEPT ![9] = 9] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet)
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![9] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![9] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![9] = 1] 
           /\ IF \A n \in 1..10 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, CWTopBezet, CWBottomBezet>>           

SpoorO4 == /\ spoorVeranderd[10] = 0
           /\ IF sporen[10] # -1
              THEN CASE sporen[10] = 1 -> /\ bestemmingen' = [bestemmingen EXCEPT ![10] = 11] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
                     [] sporen[10] = 0 -> CASE /\ C2Bezet = FALSE /\ COBottomBezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe \/ C1Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![10] = 6] /\ COBottomBezet' = TRUE /\ C2Bezet' = TRUE /\ UNCHANGED COTopBezet /\ UNCHANGED C1Bezet) 
                                               [] /\ C1Bezet = FALSE /\ COTopBezet = FALSE /\ COBottomBezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe \/ C2Bezet = FALSE) -> (/\ bestemmingen' = [bestemmingen EXCEPT ![10] = 5] /\ COTopBezet' = TRUE /\ COBottomBezet' = TRUE /\ C1Bezet' = TRUE /\ UNCHANGED C2Bezet) 
                                               [] OTHER -> (/\ bestemmingen' = [bestemmingen EXCEPT ![10] = 10] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet)
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![10] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![10] = -1] /\ UNCHANGED COTopBezet /\ UNCHANGED COBottomBezet /\ UNCHANGED C1Bezet /\ UNCHANGED C2Bezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![10] = 1] 
           /\ IF \A n \in 1..10 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, CWTopBezet, CWBottomBezet>>           

(*Voer de verplaatsingen door*)
Verplaatsing == /\ IF \E n \in 1..10 : bestemmingen[n] = 1 THEN \E n \in 1..10 : /\ bestemmingen[n] = 1 /\ newW1' = sporen[n] ELSE newW1' = -1
                /\ IF \E n \in 1..10 : bestemmingen[n] = 2 THEN \E n \in 1..10 : /\ bestemmingen[n] = 2 /\ newW2' = sporen[n] ELSE newW2' = -1
                /\ IF \E n \in 1..10 : bestemmingen[n] = 3 THEN \E n \in 1..10 : /\ bestemmingen[n] = 3 /\ newW3' = sporen[n] ELSE newW3' = -1
                /\ IF \E n \in 1..10 : bestemmingen[n] = 4 THEN \E n \in 1..10 : /\ bestemmingen[n] = 4 /\ newW4' = sporen[n] ELSE newW4' = -1
                /\ IF \E n \in 1..10 : bestemmingen[n] = 5 THEN \E n \in 1..10 : /\ bestemmingen[n] = 5 /\ newC1' = sporen[n] ELSE newC1' = -1
                /\ IF \E n \in 1..10 : bestemmingen[n] = 6 THEN \E n \in 1..10 : /\ bestemmingen[n] = 6 /\ newC2' = sporen[n] ELSE newC2' = -1
                /\ IF \E n \in 1..10 : bestemmingen[n] = 7 THEN \E n \in 1..10 : /\ bestemmingen[n] = 7 /\ newO1' = sporen[n] ELSE newO1' = -1
                /\ IF \E n \in 1..10 : bestemmingen[n] = 8 THEN \E n \in 1..10 : /\ bestemmingen[n] = 8 /\ newO2' = sporen[n] ELSE newO2' = -1
                /\ IF \E n \in 1..10 : bestemmingen[n] = 9 THEN \E n \in 1..10 : /\ bestemmingen[n] = 9 /\ newO3' = sporen[n] ELSE newO3' = -1
                /\ IF \E n \in 1..10 : bestemmingen[n] = 10 THEN \E n \in 1..10 : /\ bestemmingen[n] = 10 /\ newO4' = sporen[n] ELSE newO4' = -1
                /\ sporen' = <<newW1', newW2', newW3', newW4', newC1', newC2', newO1', newO2', newO3', newO4'>>
                /\ spoorVeranderd' = [n \in 1..10 |-> 0]
                /\ (/\ CWTopBezet' = FALSE /\ CWBottomBezet' = FALSE /\ COTopBezet' = FALSE /\ COBottomBezet' = FALSE /\ C1Bezet' = FALSE /\ C2Bezet' = FALSE /\ magDoorrijden' = FALSE)
                /\ verplaatst' = TRUE
                /\ UNCHANGED <<buffersGecontroleerd, bestemmingen, bufferW, bufferO>>
      
      
      
----------------------(*AANKOMST NIEUWE TREINEN*)-----------------------------
      
      
(*Nieuwe trein komt toe in buffer W1 (als de buffer niet vol zit)*)          
aankomstW == /\ bufferW < bufferGrootte
             /\ bufferW' = bufferW + 1
             /\ UNCHANGED <<sporen, bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferO, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst, buffersGecontroleerd>>
            
(*Nieuwe trein komt toe in buffer O1 (als de buffer niet vol zit)*)          
aankomstO == /\ bufferO < bufferGrootte
             /\ bufferO' = bufferO + 1
             /\ UNCHANGED <<sporen, bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst, buffersGecontroleerd>>
          


----------------------(*WERKING VAN DE BUFFERS*)-----------------------------


(*Haal een trein uit buffer W1 indien spoor W1 vrij is en dit geen deadlock kan veroorzaken*)
bufferWNaarSpoorW1 == /\ buffersGecontroleerd[1] # 1
                      /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![1] = 1]
                      /\ IF /\ bufferW # 0 
                            /\ sporen[1] = -1
                            /\ CASE /\ sporen[5] # -1 /\ sporen[6] # -1 -> \/ (\/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe) \/ (/\ sporen[5] = 1 /\ sporen[6] = 1 )
                                 [] /\ sporen[5] # -1 /\ sporen[6] = -1 -> \/ (\/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe) \/ (sporen[5] = 1)
                                 [] /\ sporen[5] = -1 /\ sporen[6] # -1 -> \/ (\/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe) \/ (sporen[6] = 1)
                                 [] OTHER -> (\/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe \/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe)
                         THEN /\ sporen' = [sporen EXCEPT ![1] = 1]
                              /\ bufferW' = bufferW - 1 
                         ELSE UNCHANGED <<sporen, bufferW>>
                      /\ UNCHANGED <<bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferO, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst>>

bufferWNaarSpoorW2 == /\ buffersGecontroleerd[2] # 1
                      /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![2] = 1]
                      /\ IF /\ bufferW # 0 
                            /\ sporen[2] = -1
                            /\ CASE /\ sporen[5] # -1 /\ sporen[6] # -1 -> \/ (\/ spoorW1Safe \/ spoorW3Safe \/ spoorW4Safe) \/ (/\ sporen[5] = 1 /\ sporen[6] = 1 )
                                 [] /\ sporen[5] # -1 /\ sporen[6] = -1 -> \/ (\/ spoorW1Safe \/ spoorW3Safe \/ spoorW4Safe) \/ (sporen[5] = 1)
                                 [] /\ sporen[5] = -1 /\ sporen[6] # -1 -> \/ (\/ spoorW1Safe \/ spoorW3Safe \/ spoorW4Safe) \/ (sporen[6] = 1)
                                 [] OTHER -> (\/ spoorW1Safe \/ spoorW3Safe \/ spoorW4Safe \/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe)
                         THEN /\ sporen' = [sporen EXCEPT ![2] = 1]
                              /\ bufferW' = bufferW - 1
                         ELSE UNCHANGED <<sporen, bufferW>>
                      /\ UNCHANGED <<bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferO, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst>>
   
bufferWNaarSpoorW3 == /\ buffersGecontroleerd[3] # 1
                      /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![3] = 1]
                      /\ IF /\ bufferW # 0 
                            /\ sporen[3] = -1
                            /\ CASE /\ sporen[5] # -1 /\ sporen[6] # -1 -> \/ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW4Safe) \/ (/\ sporen[5] = 1 /\ sporen[6] = 1 )
                                 [] /\ sporen[5] # -1 /\ sporen[6] = -1 -> \/ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW4Safe) \/ (sporen[5] = 1)
                                 [] /\ sporen[5] = -1 /\ sporen[6] # -1 -> \/ (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW4Safe) \/ (sporen[6] = 1)
                                 [] OTHER -> (\/ spoorW1Safe \/ spoorW2Safe \/ spoorW4Safe \/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe)
                         THEN /\ sporen' = [sporen EXCEPT ![3] = 1]
                              /\ bufferW' = bufferW - 1
                         ELSE UNCHANGED <<sporen, bufferW>>
                      /\ UNCHANGED <<bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferO, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst>>
           
bufferWNaarSpoorW4 == /\ buffersGecontroleerd[4] # 1
                      /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![4] = 1]
                      /\ IF /\ bufferW # 0 
                            /\ sporen[4] = -1
                            /\ CASE /\ sporen[5] # -1 /\ sporen[6] # -1 -> \/ (\/ spoorW1Safe \/ spoorW3Safe \/ spoorW2Safe) \/ (/\ sporen[5] = 1 /\ sporen[6] = 1 )
                                 [] /\ sporen[5] # -1 /\ sporen[6] = -1 -> \/ (\/ spoorW1Safe \/ spoorW3Safe \/ spoorW2Safe) \/ (sporen[5] = 1)
                                 [] /\ sporen[5] = -1 /\ sporen[6] # -1 -> \/ (\/ spoorW1Safe \/ spoorW3Safe \/ spoorW2Safe) \/ (sporen[6] = 1)
                                 [] OTHER -> (\/ spoorW1Safe \/ spoorW3Safe \/ spoorW2Safe \/ spoorO1Safe \/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe)
                         THEN /\ sporen' = [sporen EXCEPT ![4] = 1]
                              /\ bufferW' = bufferW - 1
                         ELSE UNCHANGED <<sporen, bufferW>>
                      /\ UNCHANGED <<bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferO, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst>>

bufferONaarSpoorO1 == /\ buffersGecontroleerd[5] # 1
                      /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![5] = 1]
                      /\ IF /\ bufferO # 0 
                            /\ sporen[7] = -1
                            /\ CASE /\ sporen[5] # -1 /\ sporen[6] # -1 -> \/ (\/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe) \/ (/\ sporen[5] = 0 /\ sporen[6] = 0)
                                 [] /\ sporen[5] # -1 /\ sporen[6] = -1 -> \/ (\/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe) \/ (sporen[5] = 0)
                                 [] /\ sporen[5] = -1 /\ sporen[6] # -1 -> \/ (\/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe) \/ (sporen[6] = 0)
                                 [] OTHER -> (\/ spoorO2Safe \/ spoorO3Safe \/ spoorO4Safe \/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe)
                         THEN /\ sporen' = [sporen EXCEPT ![7] = 0]
                              /\ bufferO' = bufferO - 1
                         ELSE UNCHANGED <<sporen, bufferO>>
                      /\ UNCHANGED <<bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst>>

bufferONaarSpoorO2 == /\ buffersGecontroleerd[6] # 1
                      /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![6] = 1]
                      /\ IF /\ bufferO # 0 
                            /\ sporen[8] = -1
                            /\ CASE /\ sporen[5] # -1 /\ sporen[6] # -1 -> \/ (\/ spoorO1Safe \/ spoorO3Safe \/ spoorO4Safe) \/ (/\ sporen[5] = 0 /\ sporen[6] = 0)
                                 [] /\ sporen[5] # -1 /\ sporen[6] = -1 -> \/ (\/ spoorO1Safe \/ spoorO3Safe \/ spoorO4Safe) \/ (sporen[5] = 0)
                                 [] /\ sporen[5] = -1 /\ sporen[6] # -1 -> \/ (\/ spoorO1Safe \/ spoorO3Safe \/ spoorO4Safe) \/ (sporen[6] = 0)
                                 [] OTHER -> (\/ spoorO1Safe \/ spoorO3Safe \/ spoorO4Safe \/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe)
                         THEN /\ sporen' = [sporen EXCEPT ![8] = 0]
                              /\ bufferO' = bufferO - 1
                         ELSE UNCHANGED <<sporen, bufferO>>
                      /\ UNCHANGED <<bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst>>

bufferONaarSpoorO3 == /\ buffersGecontroleerd[7] # 1
                      /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![7] = 1]
                      /\ IF /\ bufferO # 0 
                            /\ sporen[9] = -1
                            /\ CASE /\ sporen[5] # -1 /\ sporen[6] # -1 -> \/ (\/ spoorO2Safe \/ spoorO1Safe \/ spoorO4Safe) \/ (/\ sporen[5] = 0 /\ sporen[6] = 0)
                                 [] /\ sporen[5] # -1 /\ sporen[6] = -1 -> \/ (\/ spoorO2Safe \/ spoorO1Safe \/ spoorO4Safe) \/ (sporen[5] = 0)
                                 [] /\ sporen[5] = -1 /\ sporen[6] # -1 -> \/ (\/ spoorO2Safe \/ spoorO1Safe \/ spoorO4Safe) \/ (sporen[6] = 0)
                                 [] OTHER -> (\/ spoorO2Safe \/ spoorO1Safe \/ spoorO4Safe \/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe)
                         THEN /\ sporen' = [sporen EXCEPT ![9] = 0]
                              /\ bufferO' = bufferO - 1
                         ELSE UNCHANGED <<sporen, bufferO>>
                      /\ UNCHANGED <<bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst>>

bufferONaarSpoorO4 == /\ buffersGecontroleerd[8] # 1
                      /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![8] = 1]
                      /\ IF /\ bufferO # 0 
                            /\ sporen[10] = -1
                            /\ CASE /\ sporen[5] # -1 /\ sporen[6] # -1 -> \/ (\/ spoorO2Safe \/ spoorO3Safe \/ spoorO1Safe) \/ (/\ sporen[5] = 0 /\ sporen[6] = 0)
                                 [] /\ sporen[5] # -1 /\ sporen[6] = -1 -> \/ (\/ spoorO2Safe \/ spoorO3Safe \/ spoorO1Safe) \/ (sporen[5] = 0)
                                 [] /\ sporen[5] = -1 /\ sporen[6] # -1 -> \/ (\/ spoorO2Safe \/ spoorO3Safe \/ spoorO1Safe) \/ (sporen[6] = 0)
                                 [] OTHER -> (\/ spoorO2Safe \/ spoorO3Safe \/ spoorO1Safe \/ spoorW1Safe \/ spoorW2Safe \/ spoorW3Safe \/ spoorW4Safe)
                         THEN /\ sporen' = [sporen EXCEPT ![10] = 0]
                              /\ bufferO' = bufferO - 1
                         ELSE UNCHANGED <<sporen, bufferO>>
                      /\ UNCHANGED <<bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd, verplaatst>> 
                    
----------------------(*HOOFDFUNCTIES*)-----------------------------
                      
                               
bufferNaarSpoor == \/ bufferWNaarSpoorW1
                   \/ bufferWNaarSpoorW2
                   \/ bufferWNaarSpoorW3
                   \/ bufferWNaarSpoorW4
                   \/ bufferONaarSpoorO1
                   \/ bufferONaarSpoorO2
                   \/ bufferONaarSpoorO3
                   \/ bufferONaarSpoorO4
              
nieuweTrein == \/ aankomstW 
               \/ aankomstO

doorrijden == \/ SpoorC1
              \/ SpoorC2 
              \/ (/\ spoorVeranderd[5] = 1 /\ spoorVeranderd[6] = 1 /\ SpoorW1)
              \/ (/\ spoorVeranderd[5] = 1 /\ spoorVeranderd[6] = 1 /\ SpoorW2)
              \/ (/\ spoorVeranderd[5] = 1 /\ spoorVeranderd[6] = 1 /\ SpoorW3)
              \/ (/\ spoorVeranderd[5] = 1 /\ spoorVeranderd[6] = 1 /\ SpoorW4)
              \/ (/\ spoorVeranderd[5] = 1 /\ spoorVeranderd[6] = 1 /\ SpoorO1)
              \/ (/\ spoorVeranderd[5] = 1 /\ spoorVeranderd[6] = 1 /\ SpoorO2)
              \/ (/\ spoorVeranderd[5] = 1 /\ spoorVeranderd[6] = 1 /\ SpoorO3)
              \/ (/\ spoorVeranderd[5] = 1 /\ spoorVeranderd[6] = 1 /\ SpoorO4)
             

(*Eerst wordt voor elk spoor gezorgd dat de trein erop een nieuwe bestemming krijgt, 
daarna komen er eventueel nieuwe treinen in de buffers toe en worden de verplaatsingen doorgevoerd*)
Next == \/ (/\ ~verplaatst /\ ~magDoorrijden /\ doorrijden)
        \/ (/\ magDoorrijden /\ nieuweTrein)
        \/ (/\ magDoorrijden /\ Verplaatsing)
        \/ (/\ verplaatst /\ bufferNaarSpoor)
        \/ (/\ (\A n \in 1..8: buffersGecontroleerd[n] = 1)
            /\ verplaatst' = FALSE
            /\ buffersGecontroleerd' = [n \in 1..8 |-> 0]
            /\ UNCHANGED <<sporen, bestemmingen, newW1, newW2, newW3, newW4, newC1, newC2, newO1, newO2, newO3, newO4, bufferW, bufferO, COTopBezet, COBottomBezet, CWTopBezet, CWBottomBezet, C1Bezet, C2Bezet, magDoorrijden, spoorVeranderd >>)

VeiligheidSpec == IF magDoorrijden = TRUE \*Veiligheid moet enkel gecontroleerd worden wanneer de treinen op het punt staan van te verplaatsen
                  THEN /\ \A i,j \in 1..10: \/ i = j                           \*Geen meerdere treinen naar eenzelfde spoor
                                            \/ bestemmingen[i] = -1
                                            \/ bestemmingen[i] = 0
                                            \/ bestemmingen[i] = 11
                                            \/ bestemmingen[i] # bestemmingen[j]        
                  
                       /\ ~(\A n \in 1..2: bestemmingen[n] \in 5..6)        \*Treinen in W die naar
                       /\ ~(\A n \in 3..4: bestemmingen[n] \in 5..6)        \*C doorrijden mogen elkaar        
                       /\ ~(/\ \E n \in 1..2: bestemmingen[n] = 6              \*niet kunnen kruisen
                            /\ \E m \in 3..4: bestemmingen[m] = 5)           
                       
                       /\ ~(\A n \in 7..8: bestemmingen[n] \in 5..6)        \*Treinen in O die naar
                       /\ ~(\A n \in 9..10: bestemmingen[n] \in 5..6)       \*C doorrijden mogen elkaar 
                       /\ ~(/\ \E n \in 7..8: bestemmingen[n] = 6              \*niet kunnen kruisen
                            /\ \E m \in 9..10: bestemmingen[m] = 5)    
                       
                       /\ ~(/\ bestemmingen[5] \in 3..4                     \*Treinen op sporen C1 en C2
                            /\ bestemmingen[6] \in 1..2)                    \* Mogen elkaar niet kruisen
                            
                       /\ (\/ ~( bestemmingen[5] \in 1..2)                  \*Als trein C1 naar W rijdt,
                           \/ (/\ \A n \in 1..2: bestemmingen[n] < 3           \*Mogen de treinen in W
                               /\ \A m \in 3..4: bestemmingen[m] # 5))         \*Hem niet kunnen kruisen
                       /\ (\/ ~( bestemmingen[5] \in 3..4) 
                           \/ (\A n \in 1..4: bestemmingen[n] < 5))

                       /\ (\/ ~( bestemmingen[6] \in 1..2)                  \*Als trein C2 naar W rijdt,
                           \/ (\A n \in 1..4: bestemmingen[n] < 5))            \*Mogen de treinen in W
                       /\ (\/ ~( bestemmingen[6] \in 3..4)                  \*Hem niet kunnen kruisen
                           \/ (/\ \A n \in 1..2: bestemmingen[n] # 6
                               /\ \A m \in 3..4: bestemmingen[m] < 5))
                               
                       /\ ~(/\ bestemmingen[5] \in 9..10                    \*Treinen op sporen C1 en C2
                            /\ bestemmingen[6] \in 7..8)                    \* Mogen elkaar niet kruisen
                            
                       /\ (\/ ~( bestemmingen[5] \in 7..8)                  \*Als trein C1 naar O rijdt,
                           \/ (/\ \A n \in 7..8: \/ bestemmingen[n] > 6        \*Mogen de treinen in O
                                                 \/ bestemmingen[n] = -1       \*Hem niet kunnen kruisen
                               /\ \A m \in 9..10: bestemmingen[m] # 5))         
                       /\ (\/ ~( bestemmingen[5] \in 9..10) 
                           \/ (\A n \in 7..10: \/ bestemmingen[n] > 6
                                               \/ bestemmingen[n] = -1))

                       /\ (\/ ~( bestemmingen[6] \in 7..8)                  \*Als trein C2 naar O rijdt,
                           \/ (/\ \A n \in 7..10: \/ bestemmingen[n] > 6       \*Mogen de treinen in O
                                                  \/ bestemmingen[n] = -1))    \*Hem niet kunnen kruisen
                       /\ (\/ ~( bestemmingen[6] \in 9..10) 
                           \/ (/\ \A n \in 7..8: \/ bestemmingen[n] # 6
                                              \/ bestemmingen[n] = -1
                               /\ \A m \in 9..10: \/ bestemmingen[m] > 6
                                                  \/ bestemmingen[m] = -1)) 
                                            
                  ELSE TRUE 

                                            
DeadlockSpec == IF magDoorrijden = TRUE THEN \E n \in 1..10 : bestemmingen[n] # n ELSE TRUE (*Vanaf er geen enkele trein meer kan verplaatsen,
                                                                                           zit het systeem in een deadlock*)
FairSpoor1 == sporen[1] = -1
FairSpoor2 == sporen[2] = -1
FairSpoor3 == sporen[3] = -1
FairSpoor4 == sporen[4] = -1
FairSpoor5 == sporen[5] = -1
FairSpoor6 == sporen[6] = -1
FairSpoor7 == sporen[7] = -1
FairSpoor8 == sporen[8] = -1
FairSpoor9 == sporen[9] = -1
FairSpoor10 == sporen[10] = -1


FairnessVereisten == WF_vars(FairSpoor1)
                   /\ WF_vars(FairSpoor2)
                   /\ WF_vars(FairSpoor3)
                   /\ WF_vars(FairSpoor4)
                   /\ WF_vars(FairSpoor5)
                   /\ WF_vars(FairSpoor6)
                   /\ WF_vars(FairSpoor7)
                   /\ WF_vars(FairSpoor8)
                   /\ WF_vars(FairSpoor9)
                   /\ WF_vars(FairSpoor10)                                                                                    
                                                                                           
                                                                                           
                                                                                       
Spec == Init/\[][Next]_vars /\ FairnessVereisten
--------------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
