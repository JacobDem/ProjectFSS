------------------------------ MODULE project ------------------------------
EXTENDS Integers, Sequences

VARIABLES sporen,             (*Lijst die de sporen voorsteld en treinen kan bevatten. Volgorde: spoor W1, W2, C, O1, O2.
                              Treinen worden weergegeven als <<treinnumer, richting>>. Waarbij richting = 1 W->O is 
                              en 0 O->W is. *)
                              
          bestemmingen,       (*Lijst van volgende station-perron. Per station staat hier een getal dat voorstelt naar waar
                              de volgende trein KAN gaan. 1 is W1, 2 is W2, 3 is C, 4 is O1, 5 is O2. -1 is de waarde
                              die zegt dat er geen trein aanwezig is op dit perron. 0 is de waarde die wordt gebruikt om naar 
                              westen te rijden, 6 om naar het oosten te rijden (buiten ons netwerk) *) 
                                        
          newW1, newW2, newC, newO1, newO2,  (*Elementen die treinen bevatten. Wordt gebruikt om de nieuwe situatie in op te 
                                             slaan alvorens de situatie uit te voeren*)
                              
          bufferW1, bufferW2, bufferO1, bufferO2,   (*Buffers voor inkomende treinen, die wachten om perron W1, W2, O1 en O2 op te rijden*) 
          
          treinCount,          (*Aantal treinen op het netwerk. Wordt gebruikt om treinen een treinnumer te geven.*)
          
          CObezet,            (*Geeft aan of de verbinding C -> O reeds wordt gebruikt in de huidige cyclus*)
          CWbezet,            (*Geeft aan of de verbinding C -> W reeds wordt gebruikt in de huidige cyclus*)
          Cbezet,             (*Geeft aan of het perron C al geclaimd is in de huidige cyclus*)
          
          magDoorrijden,      (*Geeft aan of elke trein een nieuwe bestemming is toegewezen*)
          spoorVeranderd,     (*Lijst van getallen die aangeven welk perron reeds een nieuwe bestemming is toegewezen*)
          
          verplaatst,         (*Geeft aan of de verplaatsingen zijn doorgevoerd. Wordt gebruikt om de buffers te laten
                              weten dat er treinen uit de buffers naar de sporen mag gebracht worden*)
                              
          buffersGecontroleerd (*Lijst van getallen die aangeven welke buffers al eventueel een trein op een spoor
                               hebben kunnen zetten*)

CONSTANTS bufferGrootte       (*aantal treinen in buffers*)
-----------------------------------------------------------------------------
vars == <<sporen, bestemmingen, newW1, newW2, newC, newO1, newO2, bufferW1, bufferW2, bufferO1, bufferO2, treinCount, CObezet, CWbezet, Cbezet, magDoorrijden, spoorVeranderd, verplaatst, buffersGecontroleerd>>

(* Initalisatie *)
Init == /\ sporen =[[n \in 1..5 |-> << >>] EXCEPT ![1] = <<1,1>>, ![3] = <<2,0>>, ![5] = <<3,0>>]
        /\ bestemmingen = [n \in 1..5 |-> -1]
        /\ newW1 = -1 /\ newW2 = -1 /\ newC = -1 /\ newO1 = -1 /\ newO2 = -1
        /\ bufferW1 = <<>> /\ bufferW2 = <<>> /\ bufferO1 = <<>> /\ bufferO2 = <<>>
        /\ treinCount = 3 \* Want al 3 treinen hierboven. Enkel voor test! Ook test runnen met problemen zoals in tekst.*\
        /\ CObezet = FALSE
        /\ CWbezet = FALSE
        /\ Cbezet = FALSE
        /\ magDoorrijden = FALSE
        /\ spoorVeranderd = [n \in 1..5 |-> 0]
        /\ verplaatst = FALSE
        /\ buffersGecontroleerd = [n \in 1..4 |-> 0]

(*Constructies die vaker voorkomen*)
spoorW1Safe == IF sporen[1] # <<>> THEN sporen[1][2] = 0 ELSE TRUE
spoorW2Safe == IF sporen[2] # <<>> THEN sporen[2][2] = 0 ELSE TRUE
spoorO1Safe == IF sporen[4] # <<>> THEN sporen[4][2] = 1 ELSE TRUE
spoorO2Safe == IF sporen[5] # <<>> THEN sporen[5][2] = 1 ELSE TRUE



----------------------(*VERPLAATSING VAN DE TREINEN*)-----------------------------


(*Bereken de volgende bestemming van (mogelijke) trein op spoor C. 
Als naar oosten, en O1 of O2 is vrij, bestemming is een van deze (prioriteit O1). Anders blijf staan.
Als naar westen, en W1 of W2 is vrij, bestemming is een van deze. Anders blijf staan.
Indien geen trein, geen bestemming opgeven.*)
SpoorC == /\ spoorVeranderd[3] = 0
          /\ IF sporen[3] # <<>>
             THEN CASE sporen[3][2] = 1 -> CASE \/ sporen[4] = <<>> \/ sporen[4][2] = 1 -> /\ bestemmingen' = [bestemmingen EXCEPT ![3] = 4] /\ CObezet' = TRUE /\ UNCHANGED Cbezet /\ UNCHANGED CWbezet
                                             [] \/ sporen[5] = <<>> \/ sporen[5][2] = 1 -> /\ bestemmingen' = [bestemmingen EXCEPT ![3] = 5] /\ CObezet' = TRUE /\ UNCHANGED Cbezet /\ UNCHANGED CWbezet
                                             [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![3] = 3] /\ Cbezet' = TRUE /\ UNCHANGED CObezet /\ UNCHANGED CWbezet
                    [] sporen[3][2] = 0 -> CASE \/ sporen[1] = <<>> \/ sporen[1][2] = 0 -> /\ bestemmingen' = [bestemmingen EXCEPT ![3] = 1] /\ CWbezet' = TRUE /\ UNCHANGED Cbezet /\ UNCHANGED CObezet
                                             [] \/ sporen[2] = <<>> \/ sporen[2][2] = 0 -> /\ bestemmingen' = [bestemmingen EXCEPT ![3] = 2] /\ CWbezet' = TRUE /\ UNCHANGED Cbezet /\ UNCHANGED CObezet
                                             [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![3] = 3] /\ Cbezet' = TRUE /\ UNCHANGED CObezet /\ UNCHANGED CWbezet
                    [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![3] = -1] /\ UNCHANGED CObezet /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet
             ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![3] = -1] /\ UNCHANGED CObezet /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet
          /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![3] = 1]
          /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newC, newO1, newO2, bufferW1, bufferW2, bufferO1, bufferO2, treinCount, magDoorrijden>>

(*Bereken de volgende bestemming van (mogelijke) trein op spoor W1*)
SpoorW1 == /\ spoorVeranderd[1] = 0
           /\ IF sporen[1] # <<>>
              THEN CASE sporen[1][2] = 0 -> /\ bestemmingen' = [bestemmingen EXCEPT ![1] = 0] /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet
                     [] sporen[1][2] = 1 -> IF (/\ Cbezet = FALSE /\ CWbezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe)) THEN (/\ bestemmingen' = [bestemmingen EXCEPT ![1] = 3] /\ CWbezet' = TRUE /\ Cbezet' = TRUE) ELSE (/\ bestemmingen' = [bestemmingen EXCEPT ![1] = 1] /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet)
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![1] = -1] /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![1] = -1] /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![1] = 1] 
           /\ IF \A n \in 1..5 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newC, newO1, newO2, bufferW1, bufferW2, bufferO1, bufferO2, treinCount, CObezet>>
                 
(*Bereken de volgende bestemming van (mogelijke) trein op spoor W2*)
SpoorW2 == /\ spoorVeranderd[2] = 0
           /\ IF sporen[2] # <<>>
              THEN CASE sporen[2][2] = 0 -> /\ bestemmingen' = [bestemmingen EXCEPT ![2] = 0] /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet
                     [] sporen[2][2] = 1 -> IF /\ Cbezet = FALSE /\ CWbezet = FALSE /\ (\/ spoorO1Safe \/ spoorO2Safe) THEN /\ bestemmingen' = [bestemmingen EXCEPT ![2] = 3] /\ CWbezet' = TRUE /\ Cbezet' = TRUE ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![2] = 2] /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![2] = -1] /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![2] = -1] /\ UNCHANGED CWbezet /\ UNCHANGED Cbezet   
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![2] = 1] 
           /\ IF \A n \in 1..5 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newC, newO1, newO2, bufferW1, bufferW2, bufferO1, bufferO2, treinCount, CObezet>>
           
(*Bereken de volgende bestemming van (mogelijke) trein op spoor O1*)
SpoorO1 == /\ spoorVeranderd[4] = 0
           /\ IF sporen[4] # <<>>
              THEN CASE sporen[4][2] = 1 -> /\ bestemmingen' = [bestemmingen EXCEPT ![4] = 6] /\ UNCHANGED CObezet /\ UNCHANGED Cbezet
                     [] sporen[4][2] = 0 -> IF /\ Cbezet = FALSE /\ CObezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe) THEN /\ bestemmingen' = [bestemmingen EXCEPT ![4] = 3] /\ CObezet' = TRUE /\ Cbezet' = TRUE ELSE bestemmingen' = [bestemmingen EXCEPT ![4] = 4] /\ UNCHANGED CObezet /\ UNCHANGED Cbezet
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![4] = -1] /\ UNCHANGED CObezet /\ UNCHANGED Cbezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![4] = -1] /\ UNCHANGED CObezet /\ UNCHANGED Cbezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![4] = 1] 
           /\ IF \A n \in 1..5 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newC, newO1, newO2, bufferW1, bufferW2, bufferO1, bufferO2, treinCount, CWbezet>>
           
(*Bereken de volgende bestemming van (mogelijke) trein op spoor O2*)
SpoorO2 == /\ spoorVeranderd[5] = 0
           /\ IF sporen[5] # <<>>
              THEN CASE sporen[5][2] = 1 -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 6] /\ UNCHANGED CObezet /\ UNCHANGED Cbezet
                     [] sporen[5][2] = 0 -> IF /\ Cbezet = FALSE /\ CObezet = FALSE /\ (\/ spoorW1Safe \/ spoorW2Safe) THEN /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 3] /\ CObezet' = TRUE /\ Cbezet' = TRUE ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![5] = 5] /\ UNCHANGED CObezet /\ UNCHANGED Cbezet
                     [] OTHER -> /\ bestemmingen' = [bestemmingen EXCEPT ![5] = -1] /\ UNCHANGED CObezet /\ UNCHANGED Cbezet
              ELSE /\ bestemmingen' = [bestemmingen EXCEPT ![5] = -1] /\ UNCHANGED CObezet /\ UNCHANGED Cbezet
           /\ spoorVeranderd' = [spoorVeranderd EXCEPT ![5] = 1] 
           /\ IF \A n \in 1..5 : spoorVeranderd'[n] = 1 THEN magDoorrijden' = TRUE ELSE UNCHANGED magDoorrijden
           /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, newW1, newW2, newC, newO1, newO2, bufferW1, bufferW2, bufferO1, bufferO2, treinCount, CWbezet>>

(*Voer de verplaatsingen door*)
Verplaatsing == /\ (\/ bestemmingen[1] # 1 \/ bestemmingen[2] # 2 \/ bestemmingen[3] # 3 \/ bestemmingen[4] # 4 \/ bestemmingen[5] # 5)
                /\ CASE bestemmingen[1] = 1 -> newW1' = sporen[1]
                     [] bestemmingen[3] = 1 -> newW1' = sporen[3]
                     [] OTHER -> newW1' = <<>>
                /\ CASE bestemmingen[2] = 2 -> newW2' = sporen[2]
                     [] bestemmingen[3] = 2 -> newW2' = sporen[3]
                     [] OTHER -> newW2' = <<>>
                /\ CASE bestemmingen[3] = 3 -> newC' = sporen[3]
                     [] bestemmingen[1] = 3 -> newC' = sporen[1]
                     [] bestemmingen[2] = 3 -> newC' = sporen[2]
                     [] bestemmingen[4] = 3 -> newC' = sporen[4]
                     [] bestemmingen[5] = 3 -> newC' = sporen[5]
                     [] OTHER -> newC' = <<>>
                /\ CASE bestemmingen[4] = 4 -> newO1' = sporen[4]
                     [] bestemmingen[3] = 4 -> newO1' = sporen[3]
                     [] OTHER -> newO1' = <<>>
                /\ CASE bestemmingen[5] = 5 -> newO2' = sporen[5]
                     [] bestemmingen[3] = 5 -> newO2' = sporen[5]
                     [] OTHER -> newO2' = <<>>
                /\ sporen' = [sporen EXCEPT ![1] = newW1', ![2] = newW2', ![3] = newC', ![4] = newO1', ![5] = newO2']
                /\ spoorVeranderd' = [n \in 1..5 |-> 0]
                /\ (/\ CWbezet' = FALSE /\ CObezet' = FALSE /\ Cbezet' = FALSE /\ magDoorrijden' = FALSE)
                /\ verplaatst' = TRUE
                /\ UNCHANGED <<buffersGecontroleerd, bestemmingen, treinCount, bufferW1, bufferW2, bufferO1, bufferO2>>
      
      
      
----------------------(*AANKOMST NIEUWE TREINEN*)-----------------------------
      
      
(*Nieuwe trein komt toe in buffer W1 (als de buffer niet vol zit)*)          
aankomstW1 == /\ Len(bufferW1) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ bufferW1' = bufferW1 \o <<<<treinCount',1>>>>
              /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, bestemmingen, newW1, newW2, newC, newO1, newO2, spoorVeranderd, CWbezet, CObezet, Cbezet, magDoorrijden, bufferW2, bufferO1, bufferO2>>
            
(*Nieuwe trein komt toe in buffer W2 (als de buffer niet vol zit)*)          
aankomstW2 == /\ Len(bufferW2) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ bufferW2' = bufferW2 \o <<<<treinCount',1>>>>
              /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, bestemmingen, newW1, newW2, newC, newO1, newO2, spoorVeranderd, CWbezet, CObezet, Cbezet, magDoorrijden, bufferW1, bufferO1, bufferO2>>
  
(*Nieuwe trein komt toe in buffer O1 (als de buffer niet vol zit)*)          
aankomstO1 == /\ Len(bufferO1) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ bufferO1' = bufferO1 \o <<<<treinCount',0>>>>
              /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, bestemmingen, newW1, newW2, newC, newO1, newO2, spoorVeranderd, CWbezet, CObezet, Cbezet, magDoorrijden, bufferW1, bufferW2, bufferO2>>
              
(*Nieuwe trein komt toe in buffer O2 (als de buffer niet vol zit)*)          
aankomstO2 == /\ Len(bufferO2) < bufferGrootte
              /\ treinCount' = treinCount + 1 
              /\ bufferO2' = bufferO2 \o <<<<treinCount',0>>>>
              /\ UNCHANGED <<buffersGecontroleerd, verplaatst, sporen, bestemmingen, newW1, newW2, newC, newO1, newO2, spoorVeranderd, CWbezet, CObezet, Cbezet, magDoorrijden, bufferW1, bufferW2, bufferO1>>



----------------------(*WERKING VAN DE BUFFERS*)-----------------------------


(*Haal een trein uit buffer W1 indien spoor W1 vrij is en dit geen deadlock kan veroorzaken*)
bufferW1NaarSpoor == /\ buffersGecontroleerd[1] # 1
                     /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![1] = 1]
                     /\ IF /\ Len(bufferW1) # 0 
                           /\ sporen[1] = <<>>
                           /\ IF sporen[3] # <<>> THEN (\/ spoorW2Safe \/ sporen[3][2] = 1)
                                                  ELSE (\/ spoorW2Safe \/ spoorO1Safe \/ spoorO2Safe)
                        THEN /\ sporen' = [sporen EXCEPT ![1] = Head(bufferW1)]
                             /\ bufferW1' = Tail(bufferW1)
                        ELSE UNCHANGED <<sporen, bufferW1>>
                     /\ UNCHANGED <<bestemmingen, newW1, newW2, newC, newO1, newO2, bufferW2, bufferO1, bufferO2, treinCount, CObezet, CWbezet, Cbezet, magDoorrijden, spoorVeranderd, verplaatst>>
           
(*Haal een trein uit buffer W2 indien spoor W2 vrij is en dit geen deadlock kan veroorzaken*)
bufferW2NaarSpoor == /\ buffersGecontroleerd[2] # 1
                     /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![2] = 1]
                     /\ IF /\ Len(bufferW2) # 0 
                           /\ sporen[2] = <<>>
                           /\ IF sporen[3] # <<>> THEN (\/ spoorW1Safe \/ sporen[3][2] = 1)
                                                  ELSE (\/ spoorW1Safe \/ spoorO1Safe \/ spoorO2Safe)
                        THEN /\ sporen' = [sporen EXCEPT ![2] = Head(bufferW2)]
                             /\ bufferW2' = Tail(bufferW2)
                        ELSE UNCHANGED <<sporen, bufferW2>>
                     /\ UNCHANGED <<bestemmingen, newW1, newW2, newC, newO1, newO2, bufferW1, bufferO1, bufferO2, treinCount, CObezet, CWbezet, Cbezet, magDoorrijden, spoorVeranderd, verplaatst>>

(*Haal een trein uit buffer O1 indien spoor O1 vrij is en dit geen deadlock kan veroorzaken*)
bufferO1NaarSpoor == /\ buffersGecontroleerd[3] # 1
                     /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![3] = 1]
                     /\ IF /\ Len(bufferO1) # 0 
                           /\ sporen[4] = <<>>
                           /\ IF sporen[3] # <<>> THEN (\/ spoorO2Safe \/ sporen[3][2] = 0)
                                                  ELSE (\/ spoorW1Safe \/ spoorW2Safe \/ spoorO2Safe)
                        THEN /\ sporen' = [sporen EXCEPT ![4] = Head(bufferO1)]
                             /\ bufferO1' = Tail(bufferO1)
                        ELSE UNCHANGED <<sporen, bufferO1>>
                     /\ UNCHANGED <<bestemmingen, newW1, newW2, newC, newO1, newO2, bufferW2, bufferW1, bufferO2, treinCount, CObezet, CWbezet, Cbezet, magDoorrijden, spoorVeranderd, verplaatst>>
         
(*Haal een trein uit buffer O2 indien spoor O2 vrij is en dit geen deadlock kan veroorzaken*)
bufferO2NaarSpoor == /\ buffersGecontroleerd[4] # 1
                     /\ buffersGecontroleerd' = [buffersGecontroleerd EXCEPT ![4] = 1]
                     /\ IF /\ Len(bufferO2) # 0 
                           /\ sporen[5] = <<>>
                           /\ IF sporen[3] # <<>> THEN (\/ spoorO1Safe \/ sporen[3][2] = 0)
                                            ELSE (\/ spoorW1Safe \/ spoorW2Safe \/ spoorO1Safe)
                        THEN /\ sporen' = [sporen EXCEPT ![5] = Head(bufferO2)]
                             /\ bufferO2' = Tail(bufferO2) 
                        ELSE UNCHANGED <<sporen, bufferO2>>
                     /\ UNCHANGED <<bestemmingen, newW1, newW2, newC, newO1, newO2, bufferW2, bufferW1, bufferO1, treinCount, CObezet, CWbezet, Cbezet, magDoorrijden, spoorVeranderd, verplaatst>>
                    
                    
                    
----------------------(*HOOFDFUNCTIES*)-----------------------------
                      
                               
bufferNaarSpoor == \/ bufferW1NaarSpoor
                   \/ bufferW2NaarSpoor
                   \/ bufferO1NaarSpoor
                   \/ bufferO2NaarSpoor
              
aankomstW == \/ aankomstW1 \/ aankomstW2
aankomstO == \/ aankomstO1 \/ aankomstO2

nieuweTrein == \/ aankomstW 
               \/ aankomstO

doorrijden == \/ SpoorC 
              \/ (/\ spoorVeranderd[3] = 1 /\ SpoorW1)
              \/ (/\ spoorVeranderd[3] = 1 /\ SpoorW2)
              \/ (/\ spoorVeranderd[3] = 1 /\ SpoorO1)
              \/ (/\ spoorVeranderd[3] = 1 /\ SpoorO2)
             

(*Eerst wordt voor elk spoor gezorgd dat de trein erop een nieuwe bestemming krijgt, 
daarna komen er eventueel nieuwe treinen in de buffers toe en worden de verplaatsingen doorgevoerd*)
Next == \/ (/\ ~verplaatst /\ doorrijden)
        \/ (/\ magDoorrijden /\ nieuweTrein )
        \/ (/\ magDoorrijden /\ Verplaatsing)
        \/ (/\ verplaatst /\ bufferNaarSpoor)
        \/ (/\ (\A n \in 1..4: buffersGecontroleerd[n] = 1) 
            /\ verplaatst' = FALSE
            /\ buffersGecontroleerd' = [n \in 1..4 |-> 0]
            /\ UNCHANGED <<sporen, bestemmingen, newW1, newW2, newC, newO1, newO2, bufferW1, bufferW2, bufferO1, bufferO2, treinCount, CObezet, CWbezet, Cbezet, magDoorrijden, spoorVeranderd>>)
        
Spec == Init/\[][Next]_vars

NotSolved == \/ treinCount < 5 \/ sporen # [n \in 1..5 |-> <<>>] \/ bufferW1 # <<>> \/ bufferW2 # <<>> \/ bufferO1 # <<>> \/ bufferO2 # <<>>
--------------------------------------------------------------------------------
=============================================================================


\* Modification History
\* Last modified Sun Apr 25 15:38:06 CEST 2021 by jacob
\* Created Thu Apr 22 11:45:14 CEST 2021 by jacob
