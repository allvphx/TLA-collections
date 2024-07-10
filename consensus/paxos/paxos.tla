---------------------- MODULE paxos -------------------

\* The failure model: aynchronous, non-byzantine fault tolerance.
\* In this script, we adopt 2f+1 as quorum.
\* Althrough the network model is aynch, we did not implement the channels.
\* This is because paxos does not differentiate slow and crashed nodes though timeout.
\* It enforces at most f nodes to have network or crash failures, while the rest nodes to be totally failure-free.
CONSTANTS
    proposers, acceptors, learners
    init, waiting

VARIABLES proposer, acceptor, leaners

TypeInvProposer  == proposer \in  [
                         proposers -> [
                           alive    : BOOLEAN,
                           proposal_num: (x \in Int: n >= 0),
                           value: {0, 1},
                           state    : {"init", "ft_agree", "deciding", "finish"},
                         ]
                       ]

TypeInvAcceptor  == acceptor \in  [
                         acceptors -> [
                           alive    : BOOLEAN,
                           proposal_max: (x \in Int: n >= 0),
                           value: {0, 1},
                           state    : {"init", "ft_agree", "deciding", "abort"},
                         ]]
                               
UniqueProposalNum ==
    \A p1, p2 \in proposers: proposer[p1].proposal_num # proposer[p2].proposal_num

TypeInv == TypeInvProposer /\ TypeInvAcceptor /\ UniqueProposalNum


----------------------------------------------
\* Safety requirements

\* Rule 1: only a value that has been proposed may be chosen.
Validity == \A i \in acceptors: acceptors[i].value 

\* Rule 2: only a single value is chosen.

\* Rule 3: a processor learns a value has been chosen only when it has actually been.


