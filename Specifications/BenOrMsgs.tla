---- MODULE BenOrMsgs ----
(* This is a specification of the BenOr consensus algorithm (not the Byzantine version).
   In the specification, messages are added to the msgs set and message records contain
    all necessary values for communication between nodes.
   Compared to the abstract specification, this is a more detailed specification with a lot bigger
    state space size. As the number of rounds NodeRounds is an infinite set, new states are always
    reachable until consensus is achieved.*)
EXTENDS TLC, Integers, FiniteSets

\* Use the BenOr.cfg file.
CONSTANTS NODES, FAULTY_NODES, ESTIMATE_ZERO, ESTIMATE_ONE, CHECK_ALL_INITIAL_VALUES

VARIABLE rounds     \* Function that returns a given node's current round.
VARIABLE estimates  \* Function that returns a given node's current estimated value.
VARIABLE decisions  \* Function that returns a given node's current decision value.
VARIABLE msgs       \* Set of all sent messages.
vars == <<rounds, estimates, decisions, msgs>>

\* F must be greater than 0, otherwise the N - F check for proposal messages won't work.
ASSUME /\ (Cardinality(NODES) >= 2 * Cardinality(FAULTY_NODES) + 1) 
       /\ (Cardinality(FAULTY_NODES) >= 1)

\* Nodes and their decisions must be specified.
ASSUME /\ NODES # {}
       /\ ESTIMATE_ONE # {}
       /\ ESTIMATE_ZERO # {}

\* Decision values must be specified for all nodes.
ASSUME Cardinality(ESTIMATE_ZERO) + Cardinality(ESTIMATE_ONE) = Cardinality(NODES) 

\* Numbers of nodes and faulty nodes.
NumberOfNodes == Cardinality(NODES)
NumberOfFaultyNodes == Cardinality(FAULTY_NODES)

\* Set of node round numbers.
NodeRounds == Nat

\* Decision values of binary consensus.
DecisionValues == {"0", "1"}

\* Set of all possible node decision values including the "-1" used for the initial state.
NodeDecisionValues == DecisionValues \cup {"-1"}

\* Set of all functions that map nodes to their estimate values.
NodeEstimateFunctions == [NODES -> DecisionValues]

(* Set of all possible node estimate values. The "-1" is not necessary since all nodes
    estimate a value of "0" or "1" in the initial state. *)
NodeEstimateValues == DecisionValues

\* Possible values and types of messages in the BenOr consensus algorithm.
MessageType == {"report", "proposal"}
MessageValues == {"0", "1", "?"}

\* Each message record also has a round number.
MessageRecordSet == [Sender: NODES, Round: Nat, Type: MessageType, Value: MessageValues]

(* Used to print variable values.
   Must be used with /\ and in states which are reached by TLC. *)
PrintVal(message, expression)  ==  Print(<<message, expression>>, TRUE)

\* A set of all nodes other than the specified node.
AllOtherNodes(node) ==
    NODES \ {node}

\* Returns TRUE if a node sent the specified message during the specified round.
DidNodeSendMessage(sendingNode, nodeRound, messageType, messageValue) ==
    LET messageRecord == [Sender |-> sendingNode, Round |-> nodeRound, Type |-> messageType, Value |-> messageValue]
    IN  messageRecord \in msgs

\* Returns TRUE if a node sent a message of the specified type with any value ("0", "1", or "?") during the specified round.
DidNodeSendMessageOfType(sendingNode, nodeRound, messageType) ==
    \E msgValue \in MessageValues:
        LET messageRecord == [Sender |-> sendingNode, Round |-> nodeRound, Type |-> messageType, Value |-> msgValue]
        IN  messageRecord \in msgs

(* Adds a specific message to the set msgs with the sending node and the node's round.
   If the a message with the same value was already sent during the specified round, it is not added to
    the msgs set. *)
SendBroadcastMessage(sendingNode, nodeRound, messageType, messageValue) ==
    /\ ~DidNodeSendMessage(sendingNode, nodeRound, messageType, messageValue)
    /\ msgs' = msgs \cup {[Sender |-> sendingNode, Round |-> nodeRound, Type |-> messageType, Value |-> messageValue]}

\* Returns the number of messages with the specified value that were sent by nodes other than sendingNode.
HowManyMessages(sendingNode, nodeRound, messageType, messageValue) == 
    Cardinality({msg \in msgs:
                    /\ msg.Sender # sendingNode
                    /\ msg.Round = nodeRound
                    /\ msg.Type = messageType
                    /\ msg.Value = messageValue})

\* Returns the number of messages sent by nodes other than checkingNode of the specified message type.
HowManyMessagesOfType(checkingNode, nodeRound, messageType) ==
    Cardinality({node \in AllOtherNodes(checkingNode):
        DidNodeSendMessageOfType(node, nodeRound, messageType)})

(* Returns a set of estimate values that are present in more than N / 2 report messages.
   Only one same value can be present in more than N / 2 messages. *)
MajorityOfReports(node, nodeRound) ==
    {estimateValue \in NodeEstimateValues:
        HowManyMessages(node, nodeRound, "report", estimateValue) * 2 > NumberOfNodes}

\* Check if there are more than N / 2 report messages with the same value.
CheckPhase1(node, nodeRound) ==
    MajorityOfReports(node, nodeRound) # {}

(* After each node sends a report message during the first phase, it waits for N - F report 
    messages and then counts how many messages contain the same estimate value v.
   If there are more than N / 2 of such messages, the node sends a proposal message with the
    value that was in more than N / 2 report messages.
   Otherwise, the node sends a proposal message with the "?" value. *)
WaitForReports(node) ==
    /\ node \in NODES
    /\ DidNodeSendMessage(node, rounds[node], "report", estimates[node])
    /\ HowManyMessagesOfType(node, rounds[node], "report") >= NumberOfNodes - NumberOfFaultyNodes
    /\ IF CheckPhase1(node, rounds[node])
       THEN \E majorityValue \in MajorityOfReports(node, rounds[node]):
                SendBroadcastMessage(node, rounds[node], "proposal", majorityValue)
       ELSE SendBroadcastMessage(node, rounds[node], "proposal", "?")
    /\ UNCHANGED <<rounds, estimates, decisions>>

(* The first phase of the BenOr consensus algorithm.
   All nodes send report messages with their estimate value v to all other nodes.
   Each node then checks what kind of values they have received from other nodes.
   The value v that is sent as a proposal message if it is in the majority of report message
    is not necessarily the same as the node's current estimate value. A node can send
    a value different from its own estimate value to other nodes in a proposal message. *)
Phase1(node) ==
    /\ node \in NODES
    /\ \/ SendBroadcastMessage(node, rounds[node], "report", estimates[node])
       \/ WaitForReports(node)
    /\ UNCHANGED <<rounds, estimates, decisions>>

\* Returns a set of proposal values "0" or "1" that are proposed by at least F + 1 nodes. 
AtLeastNF1Proposals(node) ==
    {estimateValue \in NodeEstimateValues:
        HowManyMessages(node, rounds[node], "proposal", estimateValue) >= NumberOfFaultyNodes + 1}

\* Check for F + 1 or more proposal messages with the same value.
CheckPhase2a(node) == 
    AtLeastNF1Proposals(node) # {}

\* Returns a set of proposal values "0" or "1" that have been proposed by at least one node.
AtLeast1Proposal(node) ==
    {estimateValue \in NodeEstimateValues:
        HowManyMessages(node, rounds[node], "proposal", estimateValue) >= 1}

\* Check for at least one proposal of a node without the "?" value.
CheckPhase2b(node) == 
    AtLeast1Proposal(node) # {}

(* Decide an estimate value that has been proposed by at least F + 1 nodes.
   If there are multiple such values, TLC will check all possible choices separately. *)
DecidePhase2a(node) ==
    \E decisionValue \in AtLeastNF1Proposals(node):
        decisions' = [decisions EXCEPT ![node] = decisionValue] 

(* Estimate a proposal value that has been proposed by at least one node.
   If there are multiple such values, TLC will check all possible choices separately. *)
EstimatePhase2b(node) == 
    \E estimateValue \in AtLeast1Proposal(node):
        estimates' = [estimates EXCEPT ![node] = estimateValue]

(* Pick a random estimate value from "0" or "1" for a node.
   TLC will check all possible choices separately. *)
EstimatePhase2c(node) ==
    \E randomEstimate \in NodeEstimateValues:
        /\ estimates' = [estimates EXCEPT ![node] = randomEstimate]

(* The second phase of the BenOr consensus algorithm.
   All nodes that have sent a proposal message wait for N - F of such messages from other nodes.
   If the node receives at least F + 1 proposal messages with the same value v ("0" or "1"), then
    the node sets its decision value to v. Furthermore, if the node receives at least one proposal
    message with the value v, it sets its estimate value to v. Otherwise, the node changes its
    estimate value to "0" or "1" randomly. *)
Phase2(node) ==
    /\ node \in NODES
    /\ DidNodeSendMessageOfType(node, rounds[node], "proposal")
    /\ HowManyMessagesOfType(node, rounds[node], "proposal") >= NumberOfNodes - NumberOfFaultyNodes
    /\ IF CheckPhase2a(node) /\ CheckPhase2b(node)
       THEN DecidePhase2a(node) /\ EstimatePhase2b(node)    
       ELSE IF ~CheckPhase2a(node) /\ CheckPhase2b(node)
            THEN EstimatePhase2b(node) /\ UNCHANGED <<decisions>> 
            ELSE IF ~CheckPhase2a(node) /\ ~CheckPhase2b(node)
                 THEN EstimatePhase2c(node) /\ UNCHANGED <<decisions>> 
                 ELSE FALSE  \* No other cases possible.   
    /\ rounds' = [rounds EXCEPT![node] = @ + 1] \* Node goes to the next round.
    /\ UNCHANGED <<msgs>>

\* Consensus property for TLC to check.
ConsensusReached ==
    /\ \A node \in NODES: decisions[node] \in DecisionValues          \* All decision values must be "0" or "1".
    /\ \A node1, node2 \in NODES: decisions[node1] = decisions[node2] \* All nodes must decide on the same value.

\* The last state of the algorithm when consensus is reached.
LastState ==
    ConsensusReached

TypeOK ==
    /\ \A node \in NODES: rounds[node] \in NodeRounds
    /\ \A node \in NODES: estimates[node] \in NodeEstimateValues
    /\ \A node \in NODES: decisions[node] \in NodeDecisionValues
    /\ msgs \subseteq MessageRecordSet

(* If CHECK_ALL_INITIAL_VALUES is set to TRUE, TLC will check all possible estimate value
     combinations. Otherwise, initial estimates are defined by configuring what nodes
     estimate a "0" or a "1" value with the sets ESTIMATE_ZERO and ESTIMATE_ONE.
   Initial decisions are set to "-1" at the start to ensure ConsensusReached is not true
    in the initial state.
   There are no sent messages in the initial state. *)
Init ==
    /\ rounds = [node \in NODES |-> 1]   
    /\ IF CHECK_ALL_INITIAL_VALUES                                                         
       THEN \E estimateFunction \in NodeEstimateFunctions: estimates = estimateFunction    
       ELSE estimates = [node \in NODES |-> IF node \in ESTIMATE_ZERO THEN "0" ELSE "1"]           
    /\ decisions = [node \in NODES |-> "-1"]
    /\ msgs = {}                                                                                                               

Next == 
    \E node \in NODES: 
        /\ ~LastState \* Stops TLC when used with deadlock check enabled.
        /\ \/ Phase1(node)
           \/ Phase2(node)

Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ WF_vars(Next) 

ConsensusProperty == <>[][ConsensusReached]_vars \* Eventually, consensus will always be reached.
------------------------------
THEOREM Spec => []TypeOK \* Checked by TLC.
PROOF OMITTED
------------------------------
THEOREM Spec => ConsensusProperty \* Checked by TLC.
PROOF OMITTED  
==============================