---- MODULE 2pc ----
EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS RM

\* Variables tm: coordinator, rm: participants.
VARIABLES tm_state, rm_state

Init ==
    /\ rm_state = [rm \in RM |-> "execute"] \*execute --> prepare --> commit/abort
    /\ tm_state = "init" \* init --> commit/abort

vars == <<rm_state, tm_state>>
-----------------------------------------
\* Type invariants.
TypeOK ==
    /\ rm_state \in [RM -> {"execute", "prepare", "commit", "abort", "fail"}]
    /\ tm_state \in {"init", "commit", "abort", "hidden"}

-----------------------------------------
\* ACP correctness
\* Commit validity
Committable == (\A x \in RM: rm_state[x] \in {"prepare"})
    \/ (\E y \in RM: rm_state[y] \in {"commit"})
\* Abort validity
Abortable == (\E x \in RM: rm_state[x] \in {"abort", "fail"})
    /\ (\A y \in RM: rm_state[y] # "commit")


\* Agreement: all participants decide commit/abort.
Agreement ==
    /\ ~\E rm1, rm2 \in RM: rm_state[rm1] = "commit" /\ rm_state[rm2] = "abort"
    /\ ~\E rm \in RM: (rm_state[rm] = "commit" \/ rm_state[rm] = "abort") /\ (rm_state[rm] # tm_state /\ tm_state # "init")
\* Termination property
Termination == <>((\A x \in RM: rm_state[x] = "commit" \/ rm_state[x] = "abort"))

-----------------------------------------
\* Prepare on a participant
Prepare(c) ==
    /\ rm_state[c] = "execute"  \* From execute to prepare.
    /\ rm_state' = [rm_state EXCEPT ![c] = "prepare"] \* Prepare c.
\* Decide for a participant
decideCommit(c) ==
    /\ (tm_state = "commit")  \* coordinator first decide commit.
    /\ (rm_state' = [rm_state EXCEPT ![c] = "commit"]) \* Commit c.

decideAbort(c) ==
    /\ (tm_state = "abort" \/ rm_state[c] = "execute")  \* coordinator first decide abort or someone has not voted.
    /\ (rm_state' = [rm_state EXCEPT ![c] = "abort"]) \* Abort c.

Decide(c) == decideCommit(c) \/ decideAbort(c)

Participant(c) ==
    /\ IF rm_state[c] \in {"execute", "prepare"}
        THEN 
            \/ \* the participant vote yes and get prepared
                Prepare(c)
            \/ \* decides according to coordinator.
                Decide(c)
        ELSE     \* the participant has decided.
            UNCHANGED rm_state
    /\ UNCHANGED tm_state


-----------------------------------------
Coordinator ==
    \/
        /\ tm_state = "init"
        /\ Committable
        /\ tm_state' = "commit"
        /\ UNCHANGED rm_state
    \/
        /\ tm_state = "init"
        /\ Abortable
        /\ tm_state' = "abort"
        /\ UNCHANGED rm_state

-----------------------------------------
\* Crash and recovery
\* The participant gets failed.
CrashParticipant(c) ==
    /\ (rm_state' = [rm_state EXCEPT ![c] = "fail"]) \* Abort c.
    /\ UNCHANGED tm_state
\* The participant recovery
RecoveryParticipant(c) ==
    /\ IF rm_state[c] = "fail"
        THEN 
            \/
                decideCommit(c)
            \/
                decideAbort(c)
        ELSE
            UNCHANGED rm_state
    /\ UNCHANGED tm_state
\* The coordinator crashes.
CrashCoordinator ==
    /\ tm_state' = "hidden"
    /\ UNCHANGED rm_state

\* The coordinator recovers.
RecoveryCoordinator ==
    /\  IF tm_state = "hidden"
        THEN 
        \/
            /\ Committable
            /\ tm_state' = "commit"
        \/
            /\ Abortable
            /\ tm_state' = "abort"
        ELSE
            UNCHANGED tm_state
    /\ UNCHANGED rm_state


-----------------------------------------
Next ==
    \/ (\E x \in RM: Participant(x))
    \/ \A c \in RM: CrashParticipant(c)
    \/ \A c \in RM: RecoveryParticipant(c)
    \/ Coordinator
    \/ CrashCoordinator
    \/ RecoveryCoordinator


Spec == /\ Init /\ [][Next]_vars
        /\ \A c \in RM: WF_vars(Participant(c))
        /\ \A c \in RM: WF_vars(CrashParticipant(c))
        /\ \A c \in RM: WF_vars(RecoveryParticipant(c))
        /\ WF_vars(Coordinator)
        /\ WF_vars(CrashCoordinator)
        /\ WF_vars(RecoveryCoordinator)

====================