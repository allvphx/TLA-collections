---------------------- MODULE 2pc -------------------
CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* vote
  abort, commit,             \* decision
  waiting, init, prepare, notsent

VARIABLES
  participant, \* participants (N)
  coordinator  \* coordinator  (1)

------------------------------------------------------
TypeInvParticipant  == participant \in  [
                         participants -> [
                           vote     : {yes, no}, 
                           alive    : BOOLEAN, 
                           faulty   : BOOLEAN,
                           state    : {init, waiting, prepare, commit, abort},
                           reply_channel        : {notsent, prepare, abort}
                         ]
                       ]

TypeInvCoordinator == coordinator \in  [
                        alive     : BOOLEAN,
                        faulty    : BOOLEAN,
                        state     : {commit, abort, init},
                        results   : [participants -> {waiting, prepare, abort}],
                        request_channel   : [participants -> BOOLEAN],
                        broadcast_channel : [participants -> {commit, abort, notsent}]
                      ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

------------------------------------------------------------------------------
\* Coordinator Normal Processing Statements

\* Initially:
\* All the participants:
\*  have a yes/no vote
\*  are alive and not faulty
\*  have not sent their votes/results yet
\*  is in initial state

\* The coordinator:
\*  has not sent vote requests yet
\*  has not recieved votes from any participant
\*  is alive and not faulty
\*  has not sent broadcast messages to any participant
\*  is in initial state

InitParticipant == participant \in [
                     participants -> [
                        vote     : {yes, no}, 
                        alive    : {TRUE},
                        faulty   : {FALSE},
                        state    : {init},
                        reply_channel        : {notsent},
                        votes_receive_channel: [participants -> {waiting}]
                     ]
                   ]

InitCoordinator == coordinator \in [
                        alive    : {TRUE},
                        faulty   : {FALSE},
                        state     : {init},
                        results   : [participants -> {waiting}],
                        request_channel   : [participants -> {FALSE}],
                        broadcast_channel : [participants -> {notsent}]
                   ]
Init == InitParticipant /\ InitCoordinator

--------------------------------------------------------------------------------
\* COORDINATOR STATEMENTS

\* sendPrepare(i):
\* IF
\*   coordinator is alive and inside init state.
\*   request for vote has not been sent to participant i
\*   request for vote sent to participant i

sendPrepare(i) ==   /\ coordinator.alive
                    /\ coordinator.state = init
                    /\ ~coordinator.request_channel[i]
                    /\ coordinator' = [coordinator EXCEPT !.request_channel =
                        [@ EXCEPT ![i] = TRUE]]
                    /\ UNCHANGED<<participant>>

\* getVote(i):
\* IF
\*   coordinator is alive
\*   coordinator has not decided
\*   coordinator has sent prepare to participant i
\*   coordinator is waiting to receive the vote from participant i
\*   participant i has finished local execution and returned vote OR
\*      participant i has encountered fault and thus misses vote
\* THEN
\*   the coordinator can record the vote of participant i

getVote(i) ==   /\ coordinator.alive
                /\ coordinator.state = init
                /\ \A j \in participants: coordinator.request_channel[j]
                /\ coordinator.results[i] = waiting
                /\
                    \/ participant[i].reply_channel # notsent
                    \/ participant[i].faulty
                /\ coordinator' = [coordinator EXCEPT !.results = 
                   [@ EXCEPT ![i] = participant[i].reply_channel]
                 ]
                /\ UNCHANGED<<participant>>

\* makeDecision:
\* IF
\*   coordinator is alive
\*   coordinator has not decided
\* THEN
\*   IF
\*     coordinator has received yes votes from all participants
\*   THEN
\*     coordinator decides commit
\*   IF
\*     coordinator has received no votes from any participant
\*   THEN
\*     coordinator decides abort
\*   ELSE
\*     coordinator decides abort when timeout due to the crash failure of participants.

makeDecision == /\ coordinator.alive
                /\ coordinator.state = init
                /\ \/ /\ \A j \in participants : coordinator.results[j] = prepare   \* commit with all yes votes.
                      /\ coordinator' = [coordinator EXCEPT !.state = commit]
                   \/ /\ \E k \in participants : coordinator.results[k] = abort \* abort due to a no vote.
                      /\ coordinator' = [coordinator EXCEPT !.state = abort]
                   \/ /\ \E k \in participants :
                        /\ participant[k].faulty
                        /\ coordinator.results[k] = waiting   \* timeout due to the crash failure of some participant. 
                      /\ coordinator' = [coordinator EXCEPT !.state = abort]
                /\ UNCHANGED<<participant>>

\* coordDecide(i):
\* IF 
\*   coordinator is alive
\*   coordinator has made a decision
\*   coordinator has not broadcasted decision to participant i
\* THEN
\*   coordinator sends its decision to participant i 

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.state \in {commit, abort}
                     /\ coordinator.broadcast_channel[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast_channel = 
                          [@ EXCEPT ![i] = coordinator.state]
                        ]
                     /\ UNCHANGED<<participant>>

------------------------------------------------------------------------------
\* Coordinator Crash Recovery Statements


\* coordDie:
\* IF 
\*   coordinator is alive
\* THEN
\*   coordinator dies
\*   coordinator is now faulty
\*   not persisted states are lost

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE,
                !.faulty = TRUE,
                !.results = [i \in participants |-> waiting]]
            /\ UNCHANGED<<participant>>

\* coordMissResponse(i):
\* one of the messages sent to coordinator gets lost

coordMissResponse(i) == 
            /\ participant' = [participant EXCEPT ![i].reply_channel = notsent]
            /\ UNCHANGED<<coordinator>>

\* coordMissMessage:
\* IF 
\*   coordinator is die
\* THEN
\*   one of the messages sent to coordinator gets lost

coordMissMessage == /\ ~coordinator.alive
            /\ \E i \in participants: coordMissResponse(i)
            /\ UNCHANGED<<coordinator>>


\* coordRecover:
\* IF 
\*   coordinator is die
\* THEN
\*   coordinator recovers

coordRecover == /\ ~coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = TRUE]
            /\ UNCHANGED<<participant>>


----------------------------------------------------------------------------------
\* Participant Normal Processing Statements

\* receivePrepare(i):
\* IF 
\*   participant i is alive
\*   participant i has not received the prepare message
\*   coordinator has broadcasted the prepare message for participant i.
\* THEN
\*   participant state changes to undecided.

receivePrepare(i) ==
                /\ participant[i].alive
                /\ participant[i].state = init
                /\ coordinator.request_channel[i]
                /\ participant' = [participant EXCEPT ![i].state = waiting]
                /\ UNCHANGED<<coordinator>>



\* sendResult(i):
\* IF 
\*   participant is alive
\*   participant has finished local execution.
\* THEN
\*   participant sends resulting vote

sendResult(i) ==
                /\ participant[i].alive
                /\ participant[i].state \in {prepare, abort}
                /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.reply_channel = participant[i].state]]
                /\ UNCHANGED<<coordinator>>


\* abortOnNoVote(i):
\* IF
\*   participant is alive
\*   participant is waiting
\*   participant's vote is no
\* THEN
\*   participant decides to abort

abortOnNoVote(i) ==
                /\ participant[i].alive
                /\ participant[i].state = waiting
                /\ participant[i].vote = no
                /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.state = abort]]
                /\ UNCHANGED<<coordinator>>

\* prepareOnNoVote(i):
\* IF
\*   participant is alive
\*   participant is waiting
\*   participant's vote is yes
\* THEN
\*   participant decides to prepare local transaction.

prepareOnCommitVote(i) ==
                /\ participant[i].alive
                /\ participant[i].state = waiting
                /\ participant[i].vote = yes
                /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.state = prepare]]
                /\ UNCHANGED<<coordinator>>


\* decidePath(i):
\* IF
\*   participant is alive
\*   participant is prepare
\*   participant has recieved decision from the coordinator
\* THEN
\*   participant decides according to decision from coordinator
\*

decidePath(i) ==
            /\ participant[i].alive
            /\ participant[i].state = prepare
            /\ coordinator.broadcast_channel[i] # notsent
            /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.state = coordinator.broadcast_channel[i]]
                ]
            /\ UNCHANGED<<coordinator>>

----------------------------------------------------------------------------------
\* Participant Termination


\* terminateOnTimeoutGossipDriven(i, j):
\* IF
\*   participant i, j are alive
\*   participant i is still waiting
\*   participant i has voted yes.
\*   participant j has decided.
\* THEN
\*   participant decides to follow the alive participant.

terminateOnTimeoutGossipDrivenPair(i, j) ==
    /\ participant[i].alive
    /\ participant[i].vote = yes
    /\ participant[j].alive
    /\ participant[i].state = waiting
    /\ participant[j].state \in {commit, abort}
    /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.state = participant[j].state]]
    /\ UNCHANGED<<coordinator>>

terminateOnTimeoutGossipDriven(i) ==
    \E j \in participants: terminateOnTimeoutGossipDrivenPair(i, j)

\* terminateOnTimeoutCoordinatorDriven(i, j):
\* IF
\*   participant i and coordinator are alive
\*   participant i is still waiting
\*   participant i has voted yes.
\*   coordinator has decided.
\* THEN
\*   participant decides to follow the coordinator.

terminateOnTimeoutCoordinatorDriven(i) ==
    /\ participant[i].alive
    /\ participant[i].vote = yes
    /\ participant[i].state = waiting
    /\ coordinator.alive
    /\ coordinator.state \in {commit, abort}
    /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.state = coordinator.state]]
    /\ UNCHANGED<<coordinator>>

----------------------------------------------------------------------------------
\* Participant Crash and Recovery


\* missPrepare(i):
\* IF 
\*   participant i is not alive
\*   coordinator has broadcasted the prepare message for participant i.
\* THEN
\*   participant lost the prepare message.

missPrepare(i) ==
                /\ ~participant[i].alive
                /\ coordinator.request_channel[i]
                /\ coordinator' = [coordinator EXCEPT !.request_channel[i] = FALSE]
                /\ UNCHANGED<<participant>>

\* missCoordDecision(i):
\* IF
\*   participant is not alive
\*   the coordinator has broadcasted a decision
\* THEN
\*   participant lost the decision message
\*

missCoordDecision(i) == /\ ~participant[i].alive
             /\ coordinator.broadcast_channel[i] # notsent
             /\ coordinator' = [coordinator EXCEPT !.broadcast_channel[i] = notsent]
             /\ UNCHANGED<<participant>>

\* parDie(i):
\* IF
\*   participant is alive
\* THEN
\*   participant dies and is now faulty

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]
                ]
             /\ UNCHANGED<<coordinator>>


\* parRecover(i):
\* IF
\*   participant is not alive
\* THEN
\*   participant becomes alive again

parRecover(i) == /\ ~participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.alive = TRUE]
                ]
             /\ UNCHANGED<<coordinator>>


-------------------------------------------------------------------------------

\* FOR N PARTICIPANTS

parProg(i) ==
    \/ receivePrepare(i)
    \/ sendResult(i)
    \/ abortOnNoVote(i)
    \/ prepareOnCommitVote(i)
    \/ decidePath(i)
    \/ terminateOnTimeoutGossipDriven(i)
    \/ terminateOnTimeoutCoordinatorDriven(i)
    \/ missPrepare(i)
    \/ missCoordDecision(i)

parProgN == \E i \in participants : parRecover(i) \/ parDie(i) \/ parProg(i)
\* parProgN == \E i \in participants : parProg(i)


coordProgA(i) ==  sendPrepare(i) \/ getVote(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordRecover \/ coordProgB \/ coordMissMessage
\* coordProgN == coordProgB

notFailureFree ==
        \/ \E j \in participants: participant[j].faulty
        \/ coordinator.faulty

progN == parProgN \/ coordProgN

\* Death transitions are left outside of fairness

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)


Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

--------------------------------------------------------------------------------

\* CORRECTNESS SPECIFICATION

\*******************************************************************************
\* The specification is split between safety and liveness.
\*******************************************************************************

--------------------------------------------------------------------------------

\* SAFETY

\* All participants that decide reach the same decision
Agreement == [] \A i, j \in participants : 
          \/ participant[i].state # commit 
          \/ participant[j].state # abort

\* If any participant decides commit, then all participants must have votes YES
Commit_validity == [] (  (\E i \in participants : participant[i].state = commit) 
          => (\A j \in participants : participant[j].vote = yes))

\* If any participant decides abort, then:
\*   at least one participant voted NO, or
\*   at least one participant is faulty, or
\*   coordinator is faulty
Abort_validity == [] (  (\E i \in participants : participant[i].state = abort) 
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty)

\* Each participant decides at most once
DecideOnce == [][ /\ (\A i \in participants : participant[i].state = commit 
                                => (participant'[i].state = commit))
               /\ (\A j \in participants : participant[j].state = abort  
                                => (participant'[j].state = abort))]_<<participant>>

\* LIVENESS

\* In FC-FF, all participants should decide if no failures happen.
LivenessFF == 
        <>(\A j \in participants: participant[j].state = commit 
            \/ participant[j].state = abort
            \/ notFailureFree)
================================================================================
