---------------------- MODULE simple -------------------

\* The failure model: aynchronous, non-byzantine fault tolerance.
\* In this script, we adopt 2f+1 as quorum.
\* Althrough the network model is aynch, we did not implement the channels.
\* This is because paxos does not differentiate slow and crashed nodes though timeout.
\* It enforces at most f nodes to have network/crash failures, while the rest nodes to be failure-free.
CONSTANTS
    proposers, acceptors
    init, yes, no, waiting

VARIABLES proposer, acceptor


\* init --(user request value v)--> election --()
TypeInvProposer  == proposer \in  [
                         proposers -> [
                           alive    : BOOLEAN,
                           proposal_num: (x \in Int: n >= 0)
                           state    : {init, election, abort},
                         ]
                       ]


----------------------------------------------
\* Safety requirements

\* Rule 1: only a value that has been proposed may be chosen.
Validity == \A i \in acceptors: