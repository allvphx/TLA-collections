--------------------------------- MODULE fccf_async --------------------------------
CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* vote
  undecided, commit, abort, trcommit, trabort, \* decision
  waiting, init,                  \* coordinator state wrt a participant
  notsent                   \* broadcast state wrt a participant

VARIABLES
  participant, \* participants (N)
  coordinator  \* coordinator  (1)

--------------------------------------------------------------------------------

TypeInvParticipant  == participant \in  [
                         participants -> [
                           vote     : {yes, no}, 
                           alive    : BOOLEAN, 
                           faulty   : BOOLEAN,
                           state    : {init, waiting, undecided, trcommit, 
                            trabort, commit, abort},
                           broadcast_channel    : [participants -> {yes, no, notsent, 
                            commit, abort}],
                           reply_channel        : {notsent, commit, abort, undecided},
                           votes_receive_channel: [participants -> {waiting, yes, no}]
                         ]
                       ]

TypeInvCoordinator == coordinator \in  [
                        alive     : BOOLEAN,
                        faulty    : BOOLEAN,
                        state     : {commit, abort, trcommit, trabort, undecided},
                        results   : [participants -> {waiting, undecided, commit, abort}],
                        request_channel   : [participants -> BOOLEAN],
                        broadcast_channel : [participants -> {commit, abort, notsent}]
                      ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

--------------------------------------------------------------------------------

\* Initially:
\* All the participants:
\*  have a yes/no vote
\*  are alive and not faulty
\*  have not sent their votes/results yet
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
                        faulty   : {FALSE},
                        state    : {init},
                        broadcast_channel    : [participants -> {notsent}],
                        reply_channel        : {notsent},
                        votes_receive_channel: [participants -> {waiting}]
                     ]

                   ]

InitCoordinator == coordinator \in [
                        alive    : {TRUE},
                        faulty   : {FALSE},
                        state     : {undecided},
                        results   : [participants -> {waiting}],
                        request_channel   : [participants -> {FALSE}],
                        broadcast_channel : [participants -> {notsent}]
                   ]
Init == InitParticipant /\ InitCoordinator


matchTr(a, tra) ==
    \/ (tra = trabort /\ a = abort)
    \/ (tra = trcommit /\ a = commit)


--------------------------------------------------------------------------------
\* COORDINATOR STATEMENTS

\* sendPropose(i):
\* IF
\*   coordinator is alive
\*   request for vote has not been sent to participant i
\*   request for vote sent to participant i

sendPropose(i) ==/\ coordinator.alive
                /\ ~coordinator.request_channel[i]
                /\ coordinator' = [coordinator EXCEPT !.request_channel =
                   [@ EXCEPT ![i] = TRUE]
                ]
                /\ UNCHANGED<<participant>>


\* getResult(i):
\* IF
\*   coordinator is alive
\*   coordinator has not decided
\*   coordinator has sent propose to all participants
\*   coordinator is waiting to receive the result from participant i
\*   participant i has finished FC-CF local execution and returned result message OR
\*      participant i has encountered fault and thus misses result
\* THEN
\*   the coordinator can record the result of participant i

getResult(i) == /\ coordinator.alive
                /\ coordinator.state = undecided
                /\ \A j \in participants : coordinator.request_channel[j]
                /\ coordinator.results[i] = waiting
                /\
                    \/ participant[i].reply_channel # notsent
                    \/ participant[i].faulty
                /\ coordinator' = [coordinator EXCEPT !.results = 
                   [@ EXCEPT ![i] = participant[i].reply_channel]
                 ]
                /\ UNCHANGED<<participant>>


\* coordTRDFinish:
\* IF
\*   coordinator is alive
\*   coordinator has broadcasted decisions to all nodes
\*   coordinator is in tr decision state
\* THEN
\*   coordinator decides commit/abort

coordTRDFinish ==
            /\ coordinator.alive
            /\  \/
                    /\ \A i \in participants: coordinator.broadcast_channel[i] = commit
                    /\ coordinator.state = trcommit
                    /\ coordinator' = [coordinator EXCEPT !.state = commit]
                \/
                    /\ \A i \in participants: coordinator.broadcast_channel[i] = abort
                    /\ coordinator.state = trabort
                    /\ coordinator' = [coordinator EXCEPT !.state = abort]
            /\ UNCHANGED<<participant>>


\* makeDecision:
\* IF
\*   coordinator is alive
\*   coordinator is undecided
\* THEN
\*   IF
\*     coordinator has received undeicide from all participants
\*   THEN
\*     coordinator decides commit
\*   IF
\*     coordinator has received abort decision from some participant
\*   THEN
\*     coordinator decides accordingly.
\*   ELSE
\*     coordinator stay undecided

makeDecision == /\ coordinator.alive
                /\ coordinator.state = undecided
                /\ IF \A j \in participants : coordinator.results[j] = undecided
                    THEN  coordinator' = [coordinator EXCEPT !.state = trcommit]
                   ELSE IF \E k \in participants : coordinator.results[k] = abort
                    THEN  coordinator' = [coordinator EXCEPT !.state = trabort]
                   ELSE IF \A l \in participants :
                    coordinator.results[l] = waiting => participant[l].faulty
                    THEN  coordinator' = [coordinator EXCEPT !.state = trabort]
                   ELSE UNCHANGED<<coordinator>>
                /\ IF \A j \in participants : coordinator.results[j] = undecided
                      THEN  coordinator' = [coordinator EXCEPT !.state = trcommit]
                   ELSE coordinator' = [coordinator EXCEPT !.state = trabort]
                /\ UNCHANGED<<participant>>


\* coordBroadcast(i) (slow path broadcast):
\* IF 
\*   coordinator is alive
\*   coordinator has made a decision and transit to tr state.
\*   coordinator has not broadcasted decision to participant i
\*   coordinator has not got the decision from participant i
\* THEN
\*   coordinator sends its decision to participant i 

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.state \in {trcommit, trabort}
                     /\ coordinator.broadcast_channel[i] = notsent
                     /\ coordinator.results[i] \in {waiting, undecided}
                     /\ \/  /\ coordinator.state = trcommit
                            /\ coordinator' = [coordinator EXCEPT
                                !.broadcast_channel = [@ EXCEPT ![i] = commit]]
                        \/  /\ coordinator.state = trabort
                            /\ coordinator' = [coordinator EXCEPT
                                !.broadcast_channel = [@ EXCEPT ![i] = abort]]
                     /\ UNCHANGED<<participant>>


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

------------------------------------------------------------------------------

\* PARTICIPANT STATEMENTS 

\* receivePropose(i):
\* IF 
\*   participant i is alive
\*   participant i has not received the propose message
\*   coordinator has broadcasted the propose message for participant i.
\* THEN
\*   participant state changes to undecided.

receivePropose(i) ==
                /\ participant[i].alive
                /\ participant[i].state = init
                /\ coordinator.request_channel[i]
                /\ participant' = [participant EXCEPT ![i].state = waiting]
                /\ UNCHANGED<<coordinator>>

\* missPropose(i):
\* IF 
\*   participant i is not alive
\*   coordinator has broadcasted the propose message for participant i.
\* THEN
\*   participant lost the propose message.

missPropose(i) ==
                /\ ~participant[i].alive
                /\ coordinator.request_channel[i]
                /\ coordinator' = [coordinator EXCEPT !.request_channel[i] = FALSE]
                /\ UNCHANGED<<participant>>


\* sendVote(i, j):
\* IF 
\*   participant i is alive
\*   participant i has received the propose message
\*   participant i has not broadcasted its vote to participant j.
\* THEN
\*   participant sends vote

sendVote(i, j) ==
                /\ participant[i].alive
                /\ participant[i].state # init
                /\ participant[i].broadcast_channel[j] = notsent
                /\ participant' = [participant EXCEPT
                    ![i].broadcast_channel[j] = participant[i].vote]
                /\ UNCHANGED<<coordinator>>

\* receiveVote(i, j):
\* IF 
\*   participant i is alive
\*   participant i is waiting for votes
\*   participant i has not received the vote from j.
\*   participant j has broadcasted its vote to participant i.
\* THEN
\*   participant receives the vote.

receiveVote(i, j) ==
                /\ participant[i].alive
                /\ participant[i].state = waiting
                /\ participant[i].votes_receive_channel[j] = waiting
                /\ participant[j].broadcast_channel[i] \in {yes, no}
                /\ participant' = [participant EXCEPT
                    ![i].votes_receive_channel[j] = participant[j].broadcast_channel[i]]
                /\ UNCHANGED<<coordinator>>


\* missVote(i, j):
\* IF 
\*   participant i is not alive
\*   participant j has broadcasted its vote to participant i.
\* THEN
\*   participant misses the vote.

missVote(i, j) ==
                /\ ~participant[i].alive
                /\ participant[j].broadcast_channel[i] # notsent
                /\ participant' = [participant EXCEPT ![j].broadcast_channel[i] = notsent]
                /\ UNCHANGED<<coordinator>>

\* receiveDecision(i, j):
\* IF 
\*   participant i is alive
\*   participant i has not decided
\*   participant j has broadcasted its decision to participant i.
\* THEN
\*   participant receives the decision and tr decide.

receiveDecision(i, j) ==
                /\ participant[i].alive
                /\ participant[i].state \notin {trcommit, trabort, commit, abort}
                /\  \/  /\ participant[j].broadcast_channel[i] = commit
                        /\ participant' = [participant EXCEPT ![i].state = trcommit]
                    \/  /\ participant[j].broadcast_channel[i] = abort
                        /\ participant' = [participant EXCEPT ![i].state = trabort]
                /\ UNCHANGED<<coordinator>>

\* missDecision(i, j):
\* IF 
\*   participant i is not alive
\*   participant j has broadcasted its decision to participant i.
\* THEN
\*   participant miss the decision message.

missDecision(i, j) ==
                /\ ~participant[i].alive
                /\ participant[j].broadcast_channel[i] \in {commit, abort}
                /\ participant' = [participant EXCEPT ![j].broadcast_channel[i] = notsent]
                /\ UNCHANGED<<coordinator>>


\* parBoardcastPart(i):
\* IF 
\*   participant i is alive
\*   participant i is at the trcommit/trabort state
\*   participant i has not broadcasted its decision to participant j.
\* THEN
\*   participant sends its decision to participant j.

parBoardcastPart(i, j) ==
                /\ participant[i].alive
                /\ participant[i].state \in {trabort, trcommit}
                /\ participant[i].broadcast_channel[j] \in {notsent, yes, no}
                /\  \/  /\ participant[i].state = trabort
                        /\ participant' = [participant EXCEPT ![i].broadcast_channel[j] = abort]
                    \/  /\ participant[i].state = trcommit
                        /\ participant' = [participant EXCEPT ![i].broadcast_channel[j] = commit]
                /\ UNCHANGED<<coordinator>>

\* parBoardcastCoord(i):
\* IF 
\*   participant i is alive
\*   participant i is at the trcommit/trabort state
\*   participant i has not broadcasted its decision to participant j.
\* THEN
\*   participant sends its decision to the coordinator.

parBoardcastCoord(i) == 
                /\ participant[i].alive
                /\ participant[i].state \in {trabort, trcommit}
                /\ participant[i].reply_channel \in {notsent, undecided}
                /\  \/  /\ participant[i].state = trabort
                        /\ participant' = [participant EXCEPT ![i].reply_channel = abort]
                    \/  /\ participant[i].state = trcommit
                        /\ participant' = [participant EXCEPT ![i].reply_channel = commit]
                /\ UNCHANGED<<coordinator>>

parBoardcast(i) ==
            \/ parBoardcastCoord(i)
            \/ \E j \in participants: parBoardcastPart(i, j)



\* parBoardcastEnd(i):
\* IF 
\*   participant i is alive
\*   participant i is at the trcommit/trabort state
\*   participant i has broadcasted its decision to all other nodes.
\* THEN
\*   participant decides.

parBoardcastEnd(i) ==
            /\ participant[i].alive
            /\ participant[i].state \in {trabort, trcommit}
            /\ participant[i].reply_channel \in {commit, abort}
            /\ \A j \in participants: participant[i].broadcast_channel[j] \in {commit, abort}
            /\  \/
                    /\ coordinator.state = trcommit
                    /\ coordinator' = [coordinator EXCEPT !.state = commit]
                \/
                    /\ coordinator.state = trabort
                    /\ coordinator' = [coordinator EXCEPT !.state = abort]
            /\ UNCHANGED<<participant>>


exchangeMsg(i) ==
                \/ \E j \in participants: sendVote(i, j)
                \/ \E k \in participants: receiveVote(i, k)
                \/ \E l \in participants: receiveDecision(i, l)
                \/ \E m \in participants: missDecision(i, m)
                \/ \E n \in participants: missVote(i, n)
                \/ parBoardcast(i)
                \/ parBoardcastEnd(i)


\* sendUndecidedResult(i):
\* IF 
\*   participant is alive
\*   participant has finished local execution in undecided state.
\* THEN
\*   participant sends result

sendUndecidedResult(i) == /\ participant[i].alive
               /\ participant[i].state \in {undecided}
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.reply_channel = participant[i].state]
                  ]
               /\ UNCHANGED<<coordinator>>

\* abortOnVote(i):
\* IF
\*   participant is alive
\*   participant is waiting or undecided
\*   participant's vote is no OR participant has received a no vote
\* THEN
\*   participant decides to abort

abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].state \in {waiting, undecided}
                  /\
                    \/ participant[i].vote = no
                    \/ \E j \in participants: participant[i].votes_receive_channel[j] = no
                  /\ participant' = [participant EXCEPT ![i] = 
                       [@ EXCEPT !.state = trabort]
                     ]
                  /\ UNCHANGED<<coordinator>>

\* undecidedOnVote(i):
\* IF
\*   participant is alive
\*   participant is waiting or undecided
\*   participant'vote is yes and it has received all yes votes from others.
\* THEN
\*   participant decides to block

undecidedOnVote(i) == /\ participant[i].alive
                  /\ participant[i].state \in {waiting, undecided}
                  /\ participant[i].vote = yes
                  /\ \A j \in participants: participant[i].votes_receive_channel[j] = yes
                  /\ participant' = [participant EXCEPT ![i] = 
                       [@ EXCEPT !.state = undecided]
                     ]
                  /\ UNCHANGED<<coordinator>>


\* abortOnTimeout(i):
\* IF
\*   participant is alive
\*   participant is still waiting
\*   participant has voted yes.
\*   participant has only received yes votes.
\*   participant did not receive the vote from some participant due to its failure.
\* THEN
\*   participant decides (unilaterally) to abort

abortOnTimeout(i) == /\ participant[i].alive
                            /\ participant[i].state = waiting
                            /\ participant[i].vote = yes
                            /\ \A j \in participants:
                                participant[i].votes_receive_channel[j] \in {waiting, yes}
                            /\ (\E k \in participants:
                                /\ participant[i].votes_receive_channel[k] = waiting 
                                /\ participant[k].faulty)
                            /\ participant' = [participant EXCEPT ![i] = 
                                 [@ EXCEPT !.state = trabort]
                               ]
                            /\ UNCHANGED<<coordinator>>


\* abortOnWaiting4CoordinatorTimeout(i):
\* IF
\*   participant is alive
\*   participant is still waiting
\*   participant has voted yes.
\*   participant has only received yes votes.
\*   participant did not receive the vote from some participant due to its failure.
\* THEN
\*   participant decides (unilaterally) to abort

abortOnWaiting4CoordinatorTimeout(i) == /\ participant[i].alive
                            /\ participant[i].state = undecided
                            /\ participant[i].vote = yes
                            /\ coordinator.broadcast_channel[i] = notsent
                            /\ ~coordinator.alive
                            /\ participant' = [participant EXCEPT ![i] = 
                                 [@ EXCEPT !.state = trabort]
                               ]
                            /\ UNCHANGED<<coordinator>>

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


\* decideSlowPath(i):
\* IF
\*   participant is alive
\*   participant is undecided
\*   participant has recieved decision from the coordinator
\* THEN
\*   participant decides according to decision from coordinator
\*

decideSlowPath(i) == /\ participant[i].alive
             /\ participant[i].state \in {undecided, waiting}
             /\ coordinator.broadcast_channel[i] # notsent
             /\ \/  /\ coordinator.broadcast_channel[i] = commit
                    /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.state = trcommit]]
                \/  /\ coordinator.broadcast_channel[i] = abort
                    /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.state = trabort]]
             /\ UNCHANGED<<coordinator>>


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
    \/ receivePropose(i)
    \/ exchangeMsg(i)
    \/ missPropose(i)
    \/ abortOnVote(i)
    \/ sendUndecidedResult(i)
    \/ undecidedOnVote(i)
    \/ abortOnTimeout(i)
    \/ decideSlowPath(i)
    \/ missCoordDecision(i)

parProgN == \E i \in participants : parRecover(i) \/ parDie(i) \/ parProg(i)
\* parProgN == \E i \in participants : parProg(i)


coordProgA(i) ==  sendPropose(i) \/ getResult(i)
    \/ coordBroadcast(i) \/ abortOnWaiting4CoordinatorTimeout(i)

coordProgB == coordTRDFinish \/ makeDecision \/ \E i \in participants : coordProgA(i)

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

\* If any participant decides commit, then all participants must have voted YES
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

\* In FC-CF, all alive participants should finally decide.
Liveness == 
        <>(\A j \in participants:
            participant[j].state = commit \/ participant[j].state = abort \/ ~participant[j].alive)
================================================================================