---------------------- MODULE paxos -------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Proposers, Acceptors, Learners, Numbers, Values
ASSUME IsFiniteSet(Proposers) /\ IsFiniteSet(Acceptors) /\ IsFiniteSet(Learners)
ASSUME Numbers \subseteq Nat
AllNodes == UNION {Proposers, Acceptors, Learners}

VARIABLES in_channel, out_channel

\* send message m from node x to a set of nodes y
Send(x, y, m) ==
  /\ in_channel' = [v \in AllNodes |-> in_channel[v] \union IF v \in y THEN {m} ELSE {}]
  /\ out_channel' = [out_channel EXCEPT ![x] = @ \union {m}]

IsMajority(s, full) ==
    Cardinality(s) * 2 > Cardinality(full)

\* proposer select a maximum proposal number n and send PROPOSE request with n to a quorm.
Phase1A ==
  \E n \in Number, p \in Proposers, as \in SUBSET Acceptors:
    /\ IsMajority(as, Acceptors)
    /\ ~\E o \in out_channel[p]: o["t"] = "PREPARE" /\ o["n"] >= n \* no n lower than current one.
    /\ Send(p, as, [t |-> "PREPARE", n |-> n, s |-> p])

\* acceptor receive the PROPOSE message.
\* If the current received number is the highest, send ACCEPT as response.
Phase1B ==
  \E a \in Acceptors:
    \E i \in in_channel[a]:
        /\  i["t"] = "PREPARE"
        /\  ~\E o \in out_channel[a]: o["t"] = "PROMISE" /\ o["n"] >= i["n"]
        \* each time we only promise for the PREPARE with highest n.
        /\  IF ~\E o \in out_channel[a]: o["t"] = "ACCEPTED"
            \* if we have not accepted some value, send back the PROMISE message.
            THEN Send(a, {i["s"]}, [t |-> "PROMISE", n |-> i["n"], s |-> a, m |-> 0, w |-> 0])
            \* if we have accepted some value, send back the PROMISE message with earlier accepted value.
            ELSE \E x \in {o \in out_channel[a]: o["t"] = "ACCEPTED"}:
            \* the optimization indicated in Paxos Made Simple: inform proposer to abandon proposal.
                Send(a, {i["s"]}, [t |-> "PROMISE", n |-> i["n"], s |-> a, m |-> x["m"], w |-> x["w"]])

\* when a proposer's PROPOSE (identified by n) has received PROMISE by major acceptors, the proposer accept it.
Phase2A ==
  \E n \in Numbers, p \in Proposers, as \in SUBSET Acceptors:
    \E m \in in_channel[p]:
        /\ IsMajority(a, Acceptors)
        /\ m["t"] = "PROMISE" /\ m["n"] = n /\ m["s"] \in as
        /\ \A a \in as: \E i \in in_channel[p]: i["t"] = "PROMISE" /\ i["n"] = n /\ i["s"] = a
        \* the proposer has received PROMISE for n from majority.
        /\ ~\E i \in in_channel[p]: i["t"] = "PROMISE" /\ i["n"] = n /\ i["m"] > m["m"]
        \* if acceptor has accepted higher n (m), abandon those with lower n.
        /\ ~\E o \in out_channel[p]: o["t"] = "ACCEPT" /\ o["n"] >= n
        \* each time we accept the highest quorum-promised PROPOSE.
        /\  IF m["w"] = 0 
            \* if no value has been ACCEPT yet in "m" round, propose a value.
            THEN \E v \in Values: Send(p, as, [t |-> "ACCEPT", n |-> n, v |-> v, s |-> p])
            \* otherwise, accept the value accepted in this "m" round.
            ELSE Send(p, as, [t |-> "ACCEPT", n |-> n, v |-> m["w"], s |-> p])

\* if a acceptor receives a ACCEPT message with n, it accepts the proposal 
\* unless it has already responded to a PREPARE request having a higher n.
Phase2B ==
  \E a \in Acceptors:
    \E i \in in_channel[a]:
        /\ i["t"] = "ACCEPT"
        /\
            \/ \E o \in out_channel[a] : o["t"] = "PROMISE" /\ o["n"] > i["n"]
            \* the accepter has PROMISED one with higher n.
            \/ \E o \in out_channel[a] : o["t"] = "ACCEPTED" /\ o["m"] >= i["n"]
            \* or the accepter has ACCEPTED one with higher n. ("m" is the highest n encountered)
        /\ Send(a, UNION {Learners, Proposers}, [t |-> "ACCEPTED", m |-> i["n"], w |-> i["v"], s |-> a])
        \* the optimization indicated in Paxos Made Simple: inform proposer to abandon proposal.

Learned ==
  \E n \in Numbers, l \in Learners, v \in Values, as \in SUBSET Acceptors:
    /\ IsMajority(as, Acceptors)
    /\ \A a \in as: \E i \in in_channel[l]: i["t"] = "ACCEPTED" /\ i["m"] = n /\ i["w"] = v /\ i["s"] = a
    /\ Send(l, {l}, [t |-> "LEARNED", v |-> v])

Init ==
  /\ in_channel = [v \in AllNodes |-> {}]
  /\ out_channel = [v \in AllNodes |-> {}]

Next ==
  \/ Phase1A
  \/ Phase1B
  \/ Phase2A
  \/ Phase2B
  \/ Learned

Spec == Init /\ [][Next]_<<in_channel,out_channel>>
LivenessSpec == Spec /\ WF_<<in_channel,out_channel>>(Next)


Safety == [](Cardinality(UNION {{i \in in_channel[l] : i["t"] = "LEARNED"} : l \in Learners}) < 2)
ConditionLiveness == <>(\E l \in Learners: \E i \in in_channel[l]: i["t"] = "LEARNED")

THEOREM Spec => Safety