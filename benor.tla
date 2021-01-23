------------------------------- MODULE benor -------------------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, F, MAXROUND,INPUT
\* INPUT= <<0,1,1,1>> e.g. for N=4, binary consensus
 
ASSUME F<N
Procs == 1..N

(*
--algorithm benor
{ variable p1Msg={}, p2Msg={};

 

  fair process (p \in Procs)
  variable r=1, p1v=INPUT[self], p2v=-1, decided={};
  { 
  S: while (r<= MAXROUND){
  
        p1Msg := p1Msg \union {<<self, r, p1v>>};
        
  RM1:  await Cardinality({msg \in p1Msg: msg[2]=r }) >=(N-F); 
        if (Cardinality({msg \in p1Msg: msg[2]=r /\ msg[3]=0})*2>N) p2v:=0;
        else if (Cardinality({msg \in p1Msg: msg[2]=r /\ msg[3]=1})*2>N) p2v:=1;
        else p2v:=-1;
        p2Msg := p2Msg \union {<<self, r, p2v>>};
        
  RM2:  await Cardinality({msg \in p2Msg: msg[2]=r }) >=(N-F);
        if (Cardinality({msg \in p2Msg: msg[2]=r /\ msg[3]=0})>=F+1) {
        decided:=decided \union {0};
        p1v:=0;
        }
        else if (Cardinality({msg \in p2Msg: msg[2]=r /\ msg[3]=1})>=F+1) {
        decided:=decided \union {1};
        p1v:=1;
        }
        else if (Cardinality({msg \in p2Msg: msg[2]=r /\ msg[3]=0})>0) p1v:=0;
        else if (Cardinality({msg \in p2Msg: msg[2]=r /\ msg[3]=1})>0) p1v:=1;
        else with(val \in {0,1}) p1v:=val;
        
        r:=r+1; 
     }\* end while
  }\* end process


} \* end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-06f84ca156b6e34f240c22b3bc602b09
VARIABLES p1Msg, p2Msg, pc, r, p1v, p2v, decided

vars == << p1Msg, p2Msg, pc, r, p1v, p2v, decided >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        (* Process p *)
        /\ r = [self \in Procs |-> 1]
        /\ p1v = [self \in Procs |-> INPUT[self]]
        /\ p2v = [self \in Procs |-> -1]
        /\ decided = [self \in Procs |-> {}]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF r[self]<= MAXROUND
                 THEN /\ p1Msg' = (p1Msg \union {<<self, r[self], p1v[self]>>})
                      /\ pc' = [pc EXCEPT ![self] = "RM1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ p1Msg' = p1Msg
           /\ UNCHANGED << p2Msg, r, p1v, p2v, decided >>

RM1(self) == /\ pc[self] = "RM1"
             /\ Cardinality({msg \in p1Msg: msg[2]=r[self] }) >=(N-F)
             /\ IF Cardinality({msg \in p1Msg: msg[2]=r[self] /\ msg[3]=0})*2>N
                   THEN /\ p2v' = [p2v EXCEPT ![self] = 0]
                   ELSE /\ IF Cardinality({msg \in p1Msg: msg[2]=r[self] /\ msg[3]=1})*2>N
                              THEN /\ p2v' = [p2v EXCEPT ![self] = 1]
                              ELSE /\ p2v' = [p2v EXCEPT ![self] = -1]
             /\ p2Msg' = (p2Msg \union {<<self, r[self], p2v'[self]>>})
             /\ pc' = [pc EXCEPT ![self] = "RM2"]
             /\ UNCHANGED << p1Msg, r, p1v, decided >>

RM2(self) == /\ pc[self] = "RM2"
             /\ Cardinality({msg \in p2Msg: msg[2]=r[self] }) >=(N-F)
             /\ IF Cardinality({msg \in p2Msg: msg[2]=r[self] /\ msg[3]=0})>=F+1
                   THEN /\ decided' = [decided EXCEPT ![self] = decided[self] \union {0}]
                        /\ p1v' = [p1v EXCEPT ![self] = 0]
                   ELSE /\ IF Cardinality({msg \in p2Msg: msg[2]=r[self] /\ msg[3]=1})>=F+1
                              THEN /\ decided' = [decided EXCEPT ![self] = decided[self] \union {1}]
                                   /\ p1v' = [p1v EXCEPT ![self] = 1]
                              ELSE /\ IF Cardinality({msg \in p2Msg: msg[2]=r[self] /\ msg[3]=0})>0
                                         THEN /\ p1v' = [p1v EXCEPT ![self] = 0]
                                         ELSE /\ IF Cardinality({msg \in p2Msg: msg[2]=r[self] /\ msg[3]=1})>0
                                                    THEN /\ p1v' = [p1v EXCEPT ![self] = 1]
                                                    ELSE /\ \E val \in {0,1}:
                                                              p1v' = [p1v EXCEPT ![self] = val]
                                   /\ UNCHANGED decided
             /\ r' = [r EXCEPT ![self] = r[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "S"]
             /\ UNCHANGED << p1Msg, p2Msg, p2v >>

p(self) == S(self) \/ RM1(self) \/ RM2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ee2a9c91942f12f1b63c45ed6f0376b6

\*Agreement == \A p1, p2 \in Procs : (Cardinality(decided[p1])>0 /\ Cardinality(decided[p2])>0) => decided[p1] = decided[p2]
\*
\*MinorityReport == \E p1 \in Procs : 0 \notin decided[p1]
\*
\*Progress  == <> (\A p1 \in Procs :  Cardinality(decided[p1])>0)
Agreement == \A j,k \in Procs: Cardinality(decided[j])=1  /\ Cardinality(decided[k])=1 => decided[j]=decided[k]

MinorityReport == ~ \A j \in Procs: decided[j]={0}

Progress  == <> (\A j \in Procs: Cardinality(decided[j])>0)
\* Exclude failed processes

=========================================================
=============================================================================
\* Modification History
\* Last modified Thu Jul 02 11:55:48 EDT 2020 by asus
\* Last modified Mon Jun 29 14:18:18 EDT 2020 by asus
\* Last modified Wed Jun 24 08:37:04 EDT 2020 by bekir
\* Created Wed Jun 24 07:53:22 EDT 2020 by bekir

\* Reference:
\* https://learntla.com/tla/sets/  : used union to send message and Cardinality
\* https://pdfs.semanticscholar.org/e9a3/f9b2aa79907e3818adc841eb5abc02db2e09.pdf 
