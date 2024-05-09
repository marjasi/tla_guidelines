---- MODULE BenOrAbstByzCCH ----
(* This is a refinement of BenOrMsgsByzCC, BenOrAbstByzCC, and BenOrMsgsByzCCH with additional refinement history variables.
   Several modifications were required for TLC to successfully verify the refinement mappings RefMsgs:
     - Added the msgsHistory and estimateHistory variables that correspond to the msgs and estimates variables
        from BenOrMsgsByzCC.
     - Modified the specification so that proposal messages are added to the msgsHistory variable when they are sent. Also,
        faulty node proposals with "?" values are added to msgsHistory too. Likewise, report messages with estimate values
        are added in the action formula SetNextRoundEstimate.
     - Made it so that whenever a node estimates a new value, then estimateHistory is also changed.
     - Modified the Init formula to also set the estimateHistory values based on the initial estimates similarly to BenOrMsgsByzCC.
     - Added actions for checking whether certain messages are present in the msgsHistory variable. Added corresponding checks for
        whether specific messages were sent by a node in phase 1, phase 2, and the TossCommonCoin action. This does not alter the
        state space in a way to make the mapping RefAbstCC incorrect, and is required for TLC to verify the mapping RefMsgs.
     - Made it so that during the first phase of the first round, at least N - F initial estimates are sent as report messages before continuing to the second phase.
   The refinement mappings RefMsgsH and RefAbstCC are also provided and can be checked with TLC if put inside the RefinementProperty
    definition before '!Spec'. *)
EXTENDS TLC, Integers, FiniteSets

\* Use the BenOrByzCC.cfg file.
CONSTANTS NODES, FAULTY_NODES, ESTIMATE_ZERO, ESTIMATE_ONE, CHECK_ALL_INITIAL_VALUES

VARIABLE estimatesAtRound  \* Function that returns a function of all the node's estimates at the specified round.
VARIABLE proposalsAtRound  \* Function that returns a function of all the node's proposal values at the specified round.
VARIABLE decisions         \* Function that returns a given node's current decision value.
VARIABLE rounds            \* Function that returns a given node's current round.
VARIABLE commonCoin        \* Models the Common Coin.
VARIABLE msgsHistory       \* History variables for refinement.
VARIABLE estimateHistory

vars == <<estimatesAtRound, proposalsAtRound, decisions, rounds, commonCoin, msgsHistory, estimateHistory>>

(* For the BenOr Byzantine consensus protocol version, N > 5 * F must be true.
   Also, F must be greater than 0, otherwise the N - F check for proposal messages won't work. *)
ASSUME /\ (Cardinality(NODES) > 5 * Cardinality(FAULTY_NODES)) 
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

\* Only a limited number of rounds is modeled.
NodeRounds == 1..3

\* Decision values of binary consensus.
DecisionValues == {"0", "1"}

\* Set of all possible node decision values including the "-1" used for the initial state.
NodeDecisionValues == DecisionValues \cup {"-1"}

\* Set of possible proposal values.
ProposalValues == {"?", "0", "1"}

(* Set of all possible proposal message values including the "-1" used to indicate a
    proposal was not yet sent. *)
ProposalMessageValues == ProposalValues \cup {"-1"}

(* Set of all possible node estimate values. The "-1" is used to track whether a node has
    sent a report message or not. *)
NodeEstimateValues == DecisionValues \cup {"-1"}

\* Set of all functions that map nodes to their estimate values and "-1".
AllNodeEstimateFunctions == [NODES -> NodeEstimateValues]

\* Set of all functions that map nodes to their estimate values "0" or "1".
ValidNodeEstimateFunctions == [NODES -> DecisionValues]

\* Set of all functions that map nodes to their proposal message values.
NodeProposalFunctions == [NODES -> ProposalMessageValues]

(* Set of all possible Common Coin values. "-1" means that the common coin
    was not tossed yet for that round.*)
CommonCoinValues == {"-1", "0", "1"}

\* Possible values and types of messages in the BenOr consensus algorithm.
MessageType == {"report", "proposal"}
MessageValues == {"0", "1", "?"}

\* Each message record also has a round number.
MessageRecordSet == [Sender: NODES, Round: Nat, Type: MessageType, Value: MessageValues]

(* Used to print variable values.
   Must be used with /\ and in states which are reached by TLC. *)
PrintVal(message, expression)  ==  Print(<<message, expression>>, TRUE)

\* Used to print the values of all variables.
PrintAllVariableValues ==
    /\ PrintVal("Estimates at round: ", estimatesAtRound)
    /\ PrintVal("Proposals at round: ", proposalsAtRound)
    /\ PrintVal("Decisions: ", decisions)
    /\ PrintVal("Rounds: ", rounds)
    /\ PrintVal("Common Coin:", commonCoin)

\* A set of all nodes other than the specified node.
AllOtherNodes(node) ==
    NODES \ {node}

\* Returns TRUE if a node sent the specified message during the specified round.
DidNodeSendMessage(sendingNode, nodeRound, messageType, messageValue) ==
    LET messageRecord == [Sender |-> sendingNode, Round |-> nodeRound, Type |-> messageType, Value |-> messageValue]
    IN  messageRecord \in msgsHistory

\* Returns TRUE if a node sent a message of the specified type with any value ("0", "1", or "?") during the specified round.
DidNodeSendMessageOfType(sendingNode, nodeRound, messageType) ==
    \E msgValue \in MessageValues:
        LET messageRecord == [Sender |-> sendingNode, Round |-> nodeRound, Type |-> messageType, Value |-> msgValue]
        IN  messageRecord \in msgsHistory

\* Returns the number of messages sent by nodes other than checkingNode of the specified message type.
HowManyMessagesOfType(checkingNode, nodeRound, messageType) ==
    Cardinality({node \in AllOtherNodes(checkingNode):
        DidNodeSendMessageOfType(node, nodeRound, messageType)})

\* Adds a new message to the msgsHistory variable.
AddToMessageHistory(sendingNode, nodeRound, messageType, messageValue) ==
    /\ ~DidNodeSendMessage(sendingNode, nodeRound, messageType, messageValue)
    /\ msgsHistory' = msgsHistory \cup {[Sender |-> sendingNode, Round |-> nodeRound, Type |-> messageType, Value |-> messageValue]}

(* The number of node estimates of a given estimated value made by nodes other than the checking node
    in the same round. *)
HowManyEstimates(checkingNode, estimatedValue) ==
    Cardinality({node \in NODES:
        /\ node # checkingNode
        /\ estimatesAtRound[rounds[checkingNode]][node] = estimatedValue})

\* Sends a proposal message with a value that is in more than (N + F) / 2 estimates.
SendProposalMessage(node) ==
    \E estimateValue \in DecisionValues:
        /\ HowManyEstimates(node, estimateValue) * 2 > NumberOfNodes + NumberOfFaultyNodes
        /\ proposalsAtRound' = [proposalsAtRound EXCEPT ![rounds[node]][node] = estimateValue]
        /\ AddToMessageHistory(node, rounds[node], "proposal", estimateValue)

\* Check if there are more than (N + F) / 2 estimates of the same value.
CheckPhase1a(node) ==
    \E estimateValue \in DecisionValues:
        HowManyEstimates(node, estimateValue) * 2 > NumberOfNodes + NumberOfFaultyNodes

\* Wait for N - F nodes with estimate values other than "-1" in the same round.
WaitForReports(waitingNode) ==
    Cardinality({node \in NODES:
        /\ node # waitingNode
        /\ estimatesAtRound[rounds[waitingNode]][node] \in DecisionValues}) >= NumberOfNodes - NumberOfFaultyNodes

\* Wait for N - F nodes to send report messages with their estimate values.
WaitForReportMessages(node) ==
    HowManyMessagesOfType(node, rounds[node], "report") >= NumberOfNodes - NumberOfFaultyNodes

(* The first phase of the algorithm.
   All nodes check whether there are more than (N + F) / 2  estimates with the same value v.
   If such a value exists, then v is sent to all other nodes in a proposal message.
   v is not necessarily the same as the node's current estimate value. A node can send
    a value different from its own estimate value to other nodes in a proposal message.
   If such a value doesn't exist, the node sends a proposal message with a "?" value.
   A faulty node always sends a proposal message with the "?" value. *)
Phase1(node) ==
    /\ node \in NODES
    /\ proposalsAtRound[rounds[node]][node] \notin ProposalValues
    /\ WaitForReports(node)
    /\ IF rounds[node] = 1 \* Send initial estimate values within report messages.
       THEN WaitForReportMessages(node)
       ELSE TRUE
    /\ DidNodeSendMessageOfType(node, rounds[node], "report")
    /\ IF /\ CheckPhase1a(node)
          /\ node \notin FAULTY_NODES
       THEN SendProposalMessage(node)
       ELSE /\ proposalsAtRound' = [proposalsAtRound EXCEPT ![rounds[node]][node] = "?"]
            /\ AddToMessageHistory(node, rounds[node], "proposal", "?")
    /\ UNCHANGED <<estimatesAtRound, decisions, rounds, commonCoin, estimateHistory>>

(* The number of node proposals of a given proposal value made by nodes other than the checking node
    in the same round. *)
HowManyProposals(checkingNode, proposalValue) ==
    Cardinality({node \in NODES:
        /\ node # checkingNode
        /\ proposalsAtRound[rounds[checkingNode]][node] = proposalValue})

\* Returns a set of proposal values "0" or "1" that are proposed by more than (N + F) / 2 nodes. 
AtLeastMajorityProposals(node) ==
    {estimateValue \in DecisionValues:
        HowManyProposals(node, estimateValue) * 2 > NumberOfNodes + NumberOfFaultyNodes}

\* Returns a set of proposal values "0" or "1" that are proposed by at least F + 1 nodes. 
AtLeastNF1Proposals(node) ==
    {estimateValue \in DecisionValues:
        HowManyProposals(node, estimateValue) >= NumberOfFaultyNodes + 1}

\* Check for F + 1 or more proposal messages with the same value.
CheckPhase2a(node) == 
    AtLeastMajorityProposals(node) # {}

\* Check for F + 1 or more proposal messages with the same value.
CheckPhase2b(node) == 
    AtLeastNF1Proposals(node) # {}

(* Decide an estimate value that has been proposed by more than (N + F) / 2 nodes.
   If there are multiple such values, TLC will check all possible choices separately. *)
DecidePhase2a(node) == 
    \E estimateValue \in AtLeastMajorityProposals(node):
        decisions' = [decisions EXCEPT ![node] = estimateValue] 

(* Estimate a proposal value that has been proposed by at least F + 1 nodes.
   If there are multiple such values, TLC will check all possible choices separately. *)
EstimatePhase2b(node) == 
    \E estimateValue \in AtLeastNF1Proposals(node):
        /\ estimatesAtRound' = [estimatesAtRound EXCEPT ![rounds[node]][node] = estimateValue]
        /\ estimateHistory' = [estimateHistory EXCEPT ![node] = estimateValue]

(* Pick am estimate value from "0" or "1" for a node based on the common coin of the
    current round. *)
EstimatePhase2c(node) ==
    /\ commonCoin[rounds[node]] # "-1"
    /\ estimatesAtRound' = [estimatesAtRound EXCEPT ![rounds[node]][node] = commonCoin[rounds[node]]]
    /\ estimateHistory' = [estimateHistory EXCEPT ![node] = commonCoin[rounds[node]]]

\* Wait for N - F proposal messages with values other than "-1" in the same round.
WaitForProposals(waitingNode) ==
    Cardinality({node \in NODES:
        /\ node # waitingNode
        /\ proposalsAtRound[rounds[waitingNode]][node] \in ProposalValues}) >= NumberOfNodes - NumberOfFaultyNodes 

(* Second phase of the BenOr consensus algorithm.
   All nodes check whether there have been more than (N + F) / 2 proposal messages with the same value "0" or "1".
   If there were that many messages, each node updates their decision and estimate values to match the
    value in the proposal messages.
   Otherwise, if there are at least F + 1 received proposal messages with the same value value "0" or "1",
    the value is set as the new estimate for the receiving node.
   In all other cases, nodes estimate a random value of "0" or "1" for the next round. *)
Phase2(node) ==
    /\ node \in NODES
    /\ WaitForProposals(node)
    /\ DidNodeSendMessageOfType(node, rounds[node], "proposal")
    /\ IF CheckPhase2a(node) /\ CheckPhase2b(node)
       THEN DecidePhase2a(node) /\ EstimatePhase2b(node) \* If there are more than (N + F) / 2 valid proposals..
       ELSE IF ~CheckPhase2a(node) /\ CheckPhase2b(node)
            THEN EstimatePhase2b(node) /\ UNCHANGED <<decisions>>  \* If there are at least F + 1 valid proposals.
            ELSE IF ~CheckPhase2a(node) /\ ~CheckPhase2b(node)
                 THEN EstimatePhase2c(node) /\ UNCHANGED <<decisions>>  \* Estimates are randomized.
                 ELSE FALSE  \* No other cases possible.
    /\ rounds' = [rounds EXCEPT ![node] = @ + 1]
    /\ UNCHANGED <<proposalsAtRound, commonCoin, msgsHistory>>

(* Set the node's next round's estimate to the previous round's estimate value so that other nodes are aware
    that the node has entered the next round. In the previous round the estimate will be some valid value other
    than "-1".*)
SetNextRoundEstimate(node) ==
    /\ node \in NODES
    /\ IF rounds[node] = 1 /\ estimatesAtRound[rounds[node]][node] # "-1"
       THEN /\ AddToMessageHistory(node, rounds[node], "report", estimatesAtRound[rounds[node]][node])
            /\ UNCHANGED <<estimatesAtRound>>
       ELSE /\ estimatesAtRound[rounds[node]][node] = "-1"
            /\ estimatesAtRound' = [estimatesAtRound EXCEPT ![rounds[node]][node] = estimatesAtRound[rounds[node] - 1][node]]
            /\ AddToMessageHistory(node, rounds[node], "report", estimatesAtRound[rounds[node] - 1][node])
    /\ UNCHANGED <<proposalsAtRound, decisions, rounds, commonCoin, estimateHistory>>

(* Set the Common Coin value for the current round.
   If in the round at least 1 node has already estimated some value non-randomly, then that round's common coin
    value will be set to the node's estimate value (the Common Coin was lucky).
   Otherwise, the Common Coin value is set to "0" or "1" and TLC will check behaviors when all nodes randomly
    estimate "0" or "1" together. *)
TossCommonCoin ==
    /\ \E round \in NodeRounds:
        /\ commonCoin[round] = "-1"
        /\ \/ \E node \in NODES \ FAULTY_NODES: \* If at least 1 node already estimated some value in phase 2b.
                 /\ estimatesAtRound[round][node] # "-1"
                 /\ WaitForProposals(node)
                 /\ DidNodeSendMessageOfType(node, rounds[node], "proposal")
                 /\ \/ CheckPhase2a(node) /\ CheckPhase2b(node)
                    \/ ~CheckPhase2a(node) /\ CheckPhase2b(node)
                 /\ commonCoin' = [commonCoin EXCEPT ![round] = estimatesAtRound[round][node]]
           \/ /\ \A node \in NODES \ FAULTY_NODES:
                    /\ WaitForProposals(node)
                    /\ DidNodeSendMessageOfType(node, rounds[node], "proposal")
                    /\ ~CheckPhase2a(node)
                    /\ ~CheckPhase2b(node)
              /\ \E coinValue \in DecisionValues: \* All nodes estimate both values based on the Common Coin.
                    commonCoin' = [commonCoin EXCEPT ![round] = coinValue]
    /\ UNCHANGED <<estimatesAtRound, proposalsAtRound, decisions, rounds, msgsHistory, estimateHistory>>

(* Consensus property for TLC to check.
   Consensus is guaranteed only between non-faulty nodes.
   All decision values must be "0" or "1" and all non-faulty nodes must decide
    on the same value.*)
ConsensusReachedByzantine ==
    /\ \A node \in NODES \ FAULTY_NODES: decisions[node] \in DecisionValues 
    /\ \A node1, node2 \in NODES \ FAULTY_NODES: decisions[node1] = decisions[node2]

(* Common Coin validity property for TLC to check.
   The CC is valid, if its actually set during every round.*)
CommonCoinValid ==
    /\ \A round \in NodeRounds: commonCoin[round] \in DecisionValues

(* The last state of the algorithm when consensus is reached.
   Used to stop the algorithm by omitting behaviors after consensus is reached.*)
LastState ==
    /\ ConsensusReachedByzantine

TypeOK ==
    /\ \A round \in NodeRounds: estimatesAtRound[round] \in AllNodeEstimateFunctions
    /\ \A round \in NodeRounds: proposalsAtRound[round] \in NodeProposalFunctions
    /\ \A node \in NODES: decisions[node] \in NodeDecisionValues
    /\ \A node \in NODES: rounds[node] \in NodeRounds
    /\ \A round \in NodeRounds: commonCoin[round] \in CommonCoinValues
    /\ msgsHistory \subseteq MessageRecordSet


(* If CHECK_ALL_INITIAL_VALUES is set to TRUE, TLC will check all possible estimate value
     combinations. Otherwise, initial estimates are defined by configuring what nodes
     estimate a "0" or a "1" value with the sets ESTIMATE_ZERO and ESTIMATE_ONE.
   Estimates for all other rounds are set to "-1".
   Proposal message values for all rounds are set to "-1".
   Initial decisions are set to "-1" at the start to ensure ConsensusReached is not true
    in the initial state.
   Initially no Common Coins were tossed at any round yet. *)
Init ==   
    /\ IF CHECK_ALL_INITIAL_VALUES
       THEN \E estimateFunction \in ValidNodeEstimateFunctions:
            /\ estimatesAtRound = [round \in NodeRounds |-> IF round = 1
                                                         THEN estimateFunction
                                                         ELSE [node \in NODES |-> "-1"]]
            /\ estimateHistory = estimateFunction
       ELSE /\ estimatesAtRound = [round \in NodeRounds |-> IF round = 1
                                                         THEN [node \in NODES |->
                                                             IF node \in ESTIMATE_ZERO
                                                             THEN "0"
                                                             ELSE "1"]
                                                         ELSE [node \in NODES |-> "-1"]]
            /\ estimateHistory = [node \in NODES |-> IF node \in ESTIMATE_ZERO THEN "0" ELSE "1"]
    /\ proposalsAtRound = [round \in NodeRounds |-> [node \in NODES |-> "-1"]]               
    /\ decisions = [node \in NODES |-> "-1"]                                                                                               
    /\ rounds = [node \in NODES |-> 1]
    /\ commonCoin = [round \in NodeRounds |-> "-1"]
    /\ msgsHistory = {}                                                           

Next == 
    /\ ~LastState \* Stops TLC when used with deadlock check enabled.
    /\ \/ \E node \in NODES:
            \/ Phase1(node)
            \/ Phase2(node)
            \/ SetNextRoundEstimate(node)
       \/ TossCommonCoin

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A node \in NODES:
        WF_vars(Phase1(node) \/ Phase2(node) \/ SetNextRoundEstimate(node))
    /\ WF_vars(TossCommonCoin)

(* VERY IMPORTANT: when checking the RefinementProperty, all INSTANCE statements in the other refined 
    history variable specification .tla file must be commented out to avoid circular dependencies.
   Also, the RefinementProperty definition must be commented out as well since the INSTANCE statements
    would not be defined in such a case.*)
RefMsgsH ==
    INSTANCE BenOrMsgsByzCCH
    WITH msgs <- msgsHistory,
         estimates <- estimateHistory,
         estimateHistory <- estimatesAtRound,
         proposalHistory <- proposalsAtRound

RefMsgs ==
    INSTANCE BenOrMsgsByzCC
    WITH msgs <- msgsHistory,
         estimates <- estimateHistory

RefAbstCC ==
    INSTANCE BenOrAbstByzCC

RefinementProperty ==  \* Can be uncommented here and in the BenOrByzCC.cfg file to check refinement.
    /\ RefMsgs!Spec
    /\ RefMsgsH!Spec
    /\ RefAbstCC!Spec 
ConsensusProperty == <>[][ConsensusReachedByzantine]_vars \* Eventually, consensus will always be reached.
CommonCoinProperty == <>[][CommonCoinValid]_vars \* Eventually, the CC will be set for all rounds.
------------------------------
THEOREM Spec => []TypeOK \* Checked by TLC.
PROOF OMITTED
------------------------------
THEOREM Spec => ConsensusProperty \* Checked by TLC.
PROOF OMITTED
------------------------------
THEOREM Spec => CommonCoinProperty \* Checked by TLC.
PROOF OMITTED  
==============================