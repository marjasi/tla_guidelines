---- MODULE BenOrAbstSync ----
(* This is an abstract specification of the BenOr consensus algorithm (not the Byzantine version).
   The specification omits message sending entirely by allowing nodes to see each other's estimate
    values directly.
   Round numbers are also omitted from the specification. Nodes can only go to the next phase of a round
    when all nodes have completed the previous phase. This means that there is no need to differentiate
    estimate values with round numbers as was done in the detailed BenOr consensus algorithm TLA+ spec.
   With less states, it's possible to check for temporal properties using TLC, and to more easily
    investigate how random estimate values can be picked to guarantee consensus.
   However, a sequential version of a distributed algorithm doesn't allow for nodes to be in different
    phases or rounds. This makes BenOrAbstSync limited in terms of verifying temporal properties as too
    many important behaviors are omitted.*)
EXTENDS TLC, Integers, FiniteSets

\* Use the BenOr.cfg file.
CONSTANTS NODES, FAULTY_NODES, ESTIMATE_ZERO, ESTIMATE_ONE, CHECK_ALL_INITIAL_VALUES

VARIABLE estimates         \* Function that returns a given node's current estimated value.
VARIABLE decisions         \* Function that returns a given node's current decision value.
VARIABLE proposalMessageValue \* Function that returns a proposal message value for a given node.
VARIABLE phaseFlags        \* Function that returns a value that denotes what phase of a round the node has completed.
VARIABLE currentPhase      \* A variable that returns the current phase of the round for all nodes. 
vars == <<estimates, decisions, proposalMessageValue, phaseFlags, currentPhase>>

\* F must be greater than 0, otherwise the N - F check for proposal messages won't work.
ASSUME /\ (Cardinality(NODES) >= 2 * Cardinality(FAULTY_NODES) + 1) 
       /\ (Cardinality(FAULTY_NODES) >= 1)

\* Nodes and their decisions must be specified.
ASSUME /\ NODES # {}
       /\ ESTIMATE_ONE # {}
       /\ ESTIMATE_ZERO # {}

\* Decision values must be specified for all nodes.
ASSUME Cardinality(ESTIMATE_ONE) + Cardinality(ESTIMATE_ZERO) = Cardinality(NODES) 

\* Numbers of nodes and faulty nodes.
NumberOfNodes == Cardinality(NODES)
NumberOfFaultyNodes == Cardinality(FAULTY_NODES)

\* Decision values of binary consensus.
DecisionValues == {"0", "1"}

\* Set of all possible node decision values including the "-1" used for the initial state.
NodeDecisionValues == DecisionValues \cup {"-1"}

(* Set of all possible proposal message values including the "-1" used to indicate a
    proposal was not yet sent. *)
ProposalMessageValues == {"?", "0", "1"} \cup {"-1"}

\* Set of all functions that map nodes to their estimate values.
NodeEstimateFunctions == [NODES -> DecisionValues]

(* "0" is when the node is able to enter the next round.
   "1" is when the node finishes the first phase and can move on to the second phase.
   "2" is when the node finishes the current round and wants to enter the next round. *)
RoundPhases == {"0", "1", "2"}

\* "-1" is used for the final state of the system.
CurrentRoundPhaseValues == RoundPhases \cup {"-1"}

(* Set of all possible node estimate values. The "-1" is not necessary since all nodes
    estimate a value of "0" or "1" in the initial state. *)
NodeEstimateValues == DecisionValues

(* Used to print variable values.
   Must be used with /\ and in states which are reached by TLC. *)
PrintVal(message, expression)  ==  Print(<<message, expression>>, TRUE)

\* A set of all nodes other than the specified node.
AllOtherNodes(node) ==
    NODES \ {node}

\* The number of node estimates of a given estimated value made by nodes other than the checking node.
HowManyEstimates(checkingNode, estimatedValue) ==
    Cardinality({node \in NODES:
                    /\ node # checkingNode
                    /\ estimates[node] = estimatedValue})

\* Sends a proposal message with a value that is in more than N / 2 estimates.
SendProposalMessage(node) ==
    \E estimateValue \in DecisionValues:
        /\ HowManyEstimates(node, estimateValue) * 2 > NumberOfNodes
        /\ proposalMessageValue' = [proposalMessageValue EXCEPT ![node] = estimateValue]

\* Check if there are more than N / 2 estimates of the same value.
CheckPhase1a(node) ==
    \E estimateValue \in DecisionValues:
        HowManyEstimates(node, estimateValue) * 2 > NumberOfNodes

(* The first phase of the algorithm.
   All nodes check whether there are more than N / 2 estimates with the same value v.
   If such a value exists, then v is sent to all other nodes in a proposal message.
   v is not necessarily the same as the node's current estimate value. A node can send
    a value different from its own estimate value to other nodes in a proposal message.
   If such a value doesn't exist, the node sends a proposal message with a "?" value. *)
Phase1(node) ==
    /\ node \in NODES
    /\ currentPhase = "0"      
    /\ phaseFlags[node] = "0" 
    /\ IF CheckPhase1a(node)
       THEN SendProposalMessage(node)
       ELSE proposalMessageValue' = [proposalMessageValue EXCEPT ![node] = "?"]
    /\ phaseFlags' = [phaseFlags EXCEPT ![node] = "1"]  \* First phase has been completed by the node.
    /\ UNCHANGED <<estimates, decisions, currentPhase>>

\* If all nodes have finished the first phase, the second phase of the round can begin.
StartPhase2 ==
    /\ currentPhase = "0"
    /\ IF \A node \in NODES: phaseFlags[node] = "1"
       THEN /\ currentPhase' = "1"
            /\ UNCHANGED <<estimates, decisions, proposalMessageValue, phaseFlags>>
       ELSE UNCHANGED <<estimates, decisions, proposalMessageValue, phaseFlags, currentPhase>>

\* The number of node proposals of a given proposal value made by nodes other than the checking node.
HowManyProposals(checkingNode, proposalValue) ==
    Cardinality({node \in NODES:
                    /\ node # checkingNode
                    /\ proposalMessageValue[node] = proposalValue})

\* Returns a set of proposal values "0" or "1" that are proposed by at least F + 1 nodes. 
AtLeastNF1Proposals(node) ==
    {estimateValue \in DecisionValues:
        HowManyProposals(node, estimateValue) >= NumberOfFaultyNodes + 1}

\* Check for F + 1 or more proposal messages with the same value.
CheckPhase2a(node) == 
    AtLeastNF1Proposals(node) # {}

\* Returns a set of proposal values "0" or "1" that have been proposed by at least one node.
AtLeast1Proposal(node) ==
    {estimateValue \in DecisionValues:
        HowManyProposals(node, estimateValue) >= 1}

\* Check for at least one proposal of a node without the "?" value.
CheckPhase2b(node) == 
    AtLeast1Proposal(node) # {}

(* Decide an estimate value that has been proposed by at least F + 1 nodes.
   If there are multiple such values, TLC will check all possible choices separately. *)
DecidePhase2a(node) == 
    \E estimateValue \in AtLeastNF1Proposals(node):
        decisions' = [decisions EXCEPT ![node] = estimateValue] 

(* Estimate a proposal value that has been proposed by at least one node.
   If there are multiple such values, TLC will check all possible choices separately. *)
EstimatePhase2b(node) == 
    \E estimateValue \in AtLeast1Proposal(node):
        estimates' = [estimates EXCEPT ![node] = estimateValue]

(* Pick a random estimate value from "0" or "1" for a node.
   TLC will check all possible choices separately. *)
EstimatePhase2c(node) ==
    \E newEstimate \in NodeEstimateValues:
        /\ estimates' = [estimates EXCEPT ![node] = newEstimate]

(* Second phase of the BenOr consensus algorithm.
   All nodes check whether there has been at least F + 1 proposal messages with the same value "0" or "1".
   If there were that many messages, each node updates their decision and estimate values to match the
    value in the proposal messages.
   Otherwise, if there is at least 1 received proposal message with a value "0" or "1", the value is set
    as the new estimate for the receiving node.
   In all other cases, nodes estimate a random value of "0" or "1" for the next round. *)
Phase2(node) ==
    /\ node \in NODES
    /\ currentPhase = "1"     
    /\ phaseFlags[node] = "1"  
    /\ IF CheckPhase2a(node) /\ CheckPhase2b(node)
       THEN DecidePhase2a(node) /\ EstimatePhase2b(node)  \* If there are at least F + 1 valid proposals.
       ELSE IF ~CheckPhase2a(node) /\ CheckPhase2b(node)
            THEN EstimatePhase2b(node) /\ UNCHANGED <<decisions>>  \* If there is at least 1 valid proposal.
            ELSE IF ~CheckPhase2a(node) /\ ~CheckPhase2b(node)
                 THEN EstimatePhase2c(node) /\ UNCHANGED <<decisions>>  \* Estimates are randomized.
                 ELSE FALSE  \* No other cases possible.
    /\ phaseFlags' = [phaseFlags EXCEPT ![node] = "2"]
    /\ UNCHANGED <<proposalMessageValue, currentPhase>>

(* If all nodes have finished the second phase, the next round can begin.
   Sets all node phase and proposal message values to "0" and "-1" accordingly. *)
NextRound ==
    /\ currentPhase = "1"
    /\ IF \A node \in NODES: phaseFlags[node] = "2"
       THEN /\ currentPhase' = "0"
            /\ phaseFlags' = [node \in NODES |-> "0"]
            /\ proposalMessageValue' = [node \in NODES |-> "-1"]
            /\ UNCHANGED <<estimates, decisions>>
       ELSE UNCHANGED <<estimates, decisions, proposalMessageValue, phaseFlags, currentPhase>>

\* Consensus property for TLC to check.
ConsensusReached ==
    /\ \A node \in NODES: decisions[node] \in DecisionValues          \* All decision values must be "0" or "1".
    /\ \A node1, node2 \in NODES: decisions[node1] = decisions[node2] \* All nodes must decide on the same value.

\* The last state of the algorithm when consensus is reached and the current phase is set to "-1".
LastState ==
    /\ ConsensusReached
    /\ currentPhase # "-1"  
    /\ currentPhase'= "-1"  \* Set the round phase to "-1" to stop the algorithm.
    /\ UNCHANGED <<estimates, decisions, proposalMessageValue, phaseFlags>>

TypeOK ==
    /\ \A node \in NODES: estimates[node] \in NodeEstimateValues
    /\ \A node \in NODES: decisions[node] \in NodeDecisionValues
    /\ \A node \in NODES: proposalMessageValue[node] \in ProposalMessageValues
    /\ \A node \in NODES: phaseFlags[node] \in RoundPhases
    /\ currentPhase \in CurrentRoundPhaseValues

(* If CHECK_ALL_INITIAL_VALUES is set to TRUE, TLC will check all possible estimate value
     combinations. Otherwise, initial estimates are defined by configuring what nodes
     estimate a "0" or a "1" value with the sets ESTIMATE_ZERO and ESTIMATE_ONE.
   Initial decisions are set to "-1" at the start to ensure ConsensusReached is not true
    in the initial state. *)
Init ==   
    /\ IF CHECK_ALL_INITIAL_VALUES                                                         
       THEN \E estimateFunction \in NodeEstimateFunctions: estimates = estimateFunction    
       ELSE estimates = [node \in NODES |-> IF node \in ESTIMATE_ZERO THEN "0" ELSE "1"]           
    /\ decisions = [node \in NODES |-> "-1"]                                              
    /\ proposalMessageValue = [node \in NODES |-> "-1"]                                    
    /\ phaseFlags = [node \in NODES |-> "0"]                                               
    /\ currentPhase = "0"                                                                  

Next == 
    \/ \E node \in NODES: 
        \/ Phase1(node)
        \/ Phase2(node)
    \/ StartPhase2
    \/ NextRound
    \/ LastState \* Stops TLC when used with deadlock check enabled.
    
Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ \A node \in NODES: WF_vars(Phase1(node) \/ Phase2(node))
    /\ WF_vars(StartPhase2 \/ NextRound \/ LastState) 

ConsensusProperty == <>[][ConsensusReached]_vars \* Eventually, consensus will always be reached.
------------------------------
THEOREM Spec => []TypeOK \* Checked by TLC.
PROOF OMITTED
------------------------------
THEOREM Spec => ConsensusProperty \* Checked by TLC.
PROOF OMITTED  
==============================