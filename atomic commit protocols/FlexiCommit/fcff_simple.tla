---- MODULE fcff ----
EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* vote
  undecided, commit, abort, \* decision
  waiting,                  \* coordinator state wrt a participant
  notsent                   \* broadcast state wrt a participant

VARIABLES
  participant, \* participants (N)
  coordinator  \* coordinator  (1)

--------------------------------------------------------------------------------

TypeInvParticipant  == participant \in  [
                         participants -> [
                           vote      : {yes, no}, 
                           alive     : BOOLEAN, 
                           decision  : {undecided, commit, abort},
                           faulty    : BOOLEAN,
                           voteSent  : BOOLEAN
                         ]
                       ]

TypeInvCoordinator == coordinator \in  [
                        request   : [participants -> BOOLEAN],
                        result    : [participants -> {undecided, commit, abort}],
                        broadcast : [participants -> {commit, abort, notsent}],
                        decision  : {commit, abort, undecided},
                        alive     : BOOLEAN,
                        faulty    : BOOLEAN
                      ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

--------------------------------------------------------------------------------

\* Initially:
\* All the participants:
\*  have a yes/no vote
\*  are alive and not faulty
\*  have not sent in their votes yet
\*  are undecided about final decision

\* The coordinator:
\*  has not sent vote requests yet
\*  has not recieved votes from any participant
\*  is alive and not faulty
\*  has not sent broadcast messages to any participant
\*  is undecided about final decision

InitParticipant == participant \in [
                     participants -> [
                       vote     : {yes, no},
                       alive    : {TRUE},
                       decision : {undecided},
                       faulty   : {FALSE},
                       voteSent : {FALSE}
                     ]
                   ]

InitCoordinator == coordinator \in [
                     request   : [participants -> {FALSE}],
                     vote      : [participants -> {waiting}],
                     alive     : {TRUE},
                     broadcast : [participants -> {notsent}],
                     decision  : {undecided},
                     faulty    : {FALSE}
                   ]       

Init == InitParticipant /\ InitCoordinator

--------------------------------------------------------------------------------
\* COORDINATOR STATEMENTS

\* request(i):
\* IF
\*   coordinator is alive
\*   request for vote has not been sent to participant i
\* THEN `~ why isn't THEN left-justified? ~'
\*   request for vote is sent to participant i

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                   [@ EXCEPT ![i] = TRUE]
                 ]
              /\ UNCHANGED<<participant>>


\* getResult(i):
\* IF
\*   coordinator is alive
\*   coordinator is still undecided
\*   coordinator has sent request for votes to all participants
\*   coordinator is waiting to receive a result from participant i
\*   participant i has sent the result message
\* THEN
\*   the coordinator can record the result of participant i

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = 
                   [@ EXCEPT ![i] = participant[i].vote]
                 ]
              /\ UNCHANGED<<participant>>



Init ==
    /\ rm_state = [rm \in RM |-> "execute"] \*execute --> prepare --> commit/abort
    /\ tm_state = "init" \* init --> commit/abort

vars == <<rm_state, tm_state>>
\* Type invariants.
TypeOK ==
    /\ rm_state \in [RM -> {"execute", "undecide", "commit", "abort", "fail"}]
    /\ tm_state \in {"init", "commit", "abort", "hidden"}


-----------------------------------------
\* Propose phase of FC-FF
\* exchange yes votes success on node c.
ExchangeYesVoteSucceed(c) ==
    \/ \A rm \in RM:
        \/ rm_state[rm] = "undecide"
        \/ rm_state[rm] = "commit"
        \/ c = rm
\* exchange vote fails due to network or crash failures.
ExchangeYesVoteFailed(c) == 
    /\ (\A rm \in RM: rm_state[rm] = "fail" \/  rm_state[rm] = "undecide" \/ rm_state[rm] = "execute")
    /\ (\E rm \in RM: rm_state[rm] = "fail" \/ rm_state[rm] = "execute")
\* manager to get some No vote.
ExchangeNoVoteSucceed(c) ==
    (\E rm \in RM: rm_state[rm] = "abort")

Propose(c) ==
    /\  rm_state[c] = "execute"  \* From execute to prepare.
    /\  \* Vote Yes
        \/  /\ ExchangeYesVoteSucceed(c) \* Fast path decide with all Yes votes.
            /\ rm_state' = [rm_state EXCEPT ![c] = "commit"]
        \/  /\ ExchangeYesVoteFailed(c) \*  Slow path due to failures.
            /\ rm_state' = [rm_state EXCEPT ![c] = "undecide"]
        \/  /\ ExchangeNoVoteSucceed(c) \*  Fast path due to no vote.
            /\ rm_state' = [rm_state EXCEPT ![c] = "abort"]
        \/  rm_state' = [rm_state EXCEPT ![c] = "abort"]  \* Vote No.


-----------------------------------------
\* Validate phase of FC-FF
\* Participant decide commit (slow path)
slowDecideCommit(c) ==
    /\
        \/ tm_state = "commit" \* slow path decide commit.
        \/ (\A rm \in RM: rm_state[rm] = "commit" \/  rm_state[rm] = "undecide") \*  Fast path decide with all Yes votes.
    /\ (rm_state' = [rm_state EXCEPT ![c] = "commit"]) \* Commit c.
\* Participant decide abort
slowDecideAbort(c) ==
    /\ 
        \/ tm_state = "abort"   \* slow path decide abort.
        \/ rm_state[c] = "execute" \* get vote return fail.
    /\ (rm_state' = [rm_state EXCEPT ![c] = "abort"]) \* Abort c.

Validate(c) == slowDecideCommit(c) \/ slowDecideAbort(c)


-----------------------------------------
\* Participant and coordinator algorithms of FC-FF
Participant(c) ==
    /\ IF rm_state[c] \in {"execute", "undecide"}
        THEN 
            \/ Propose(c)
            \/ Validate(c)
        ELSE     \* the participant has decided.
            UNCHANGED rm_state
    /\ UNCHANGED tm_state

Coordinator ==
    \/
        /\ tm_state = "init"
        /\  \/ (\A x \in RM: rm_state[x] \in {"undecide"})
            \/ (\E y \in RM: rm_state[y] \in {"commit"})
        /\ tm_state' = "commit"
        /\ UNCHANGED rm_state
    \/
        /\ tm_state = "init"
        /\ (\E x \in RM: rm_state[x] = "abort")
        /\ tm_state' = "abort"
        /\ UNCHANGED rm_state

-----------------------------------------
\* Crash and recovery
\* In FC-FF, a node is committable if 1. all vote Yes. 2. some decide Commit.
Committable == (\A x \in RM: rm_state[x] \in {"undecide"})
    \/ (\E y \in RM: rm_state[y] \in {"commit"})
    \/ tm_state = "commit"
\* In FC-FF. a node is abortable if some did not vote Yes. (In this case, that node must decide abort)
Abortable == (\E x \in RM: rm_state[x] = "abort")
\* The participant gets failed.
CrashParticipant(c) ==
    /\ (rm_state' = [rm_state EXCEPT ![c] = "fail"]) \* Abort c.
    /\ UNCHANGED tm_state
\* The participant recovery
RecoveryParticipant(c) ==
    /\ IF rm_state[c] = "fail"
        THEN 
            \/
                /\ Committable
                /\ rm_state' = [rm_state EXCEPT ![c] = "commit"]
            \/
                /\ Abortable
                /\ rm_state' = [rm_state EXCEPT ![c] = "abort"]
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

-----------------------------------------
\* ACP correctness
\* Agreement: all participants decide commit/abort.
Agreement ==
    /\ ~\E rm1, rm2 \in RM: rm_state[rm1] = "commit" /\ rm_state[rm2] = "abort"
    /\ ~\E rm \in RM: (rm_state[rm] = "commit" \/ rm_state[rm] = "abort") /\ (rm_state[rm] # tm_state /\ tm_state # "init")
\* Termination property
Termination == <>((\A x \in RM: rm_state[x] = "commit" \/ rm_state[x] = "abort"))


====================