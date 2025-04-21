
------------------------------- MODULE OutOfBand ------------------------------

(* This code provides formal verification of the ATIS-1000105 Out-Of-Band solution 
for handling SHAKEN PASSporTs over TDM interconnects. 

Flow:
    1. A call originating in SIP signaling reaches a service provider 
        that converts the call to TDM signaling with valid SHAKEN PASSporT.
    2. Interworking function (IWF) triggers STI-OOBS to publish PASSporT(s) to STI-CPS.
    3. If no PASSporT is published, the STI-AS generates a PASSporT for STI-OOBS to publish to STI-CPS.
        Calls are sent downstream only after confirmation of the PASSporT on STI-CPS.
    4. SIP call signal gets converted to TDM signaling with no PASSporT.
    5. TDM Call signal traverses service providers over TDM NNI (Network to Network Interface).
    6. STI-OOBS retrieves the PASSporT from the current STI-CPS and publishes it to the next STI-CPS.
    7. Once the call reaches a service provider or interconnect back to SIP signaling, 
        the IWF retrieves all relevant PASSporT(s) from the STI-CPS and reinserts them into the SIP signaling identity headers.
    8. The TSP sends the SIP identity headers to the STI-VS (Verification Service). 
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    MaxTDMLatency, \* Adding non-deterministic latency values to mimic real-world randomness
    JWT_TTL,    \*  Used to define the JWT time until expiry, would be defined by servie provider's routing and network protection timers
    MaxTokenTTL \*  Used to see if PASSporTs expired before call was successfully transmitted

VARIABLES 
    stiCPS, \* Used to track PASSporT handling through STI-CPS
    stiOOBS, \* Used to keep track of intermediary STI-OOBS which send request to STI-CPS to publish/retrieve PASSporTs
    currTime, \* A way to track time
    callState,  \* Tracks the state of the call as it progresses through the actions
    nonceRegistry \* Tracks the nonces of used JWTs, meant to prevent replay attacks on the STI-CPS with previoulsy used JWTs

vars == << stiCPS, stiOOBS, currTime, callState, nonceRegistry >>

callIds == 1..3

NoPassport == [
    iat |-> 0,
    signature |-> ""
]

NoJWT == [
    iat |-> 0,
    exp |-> 0,
    passports |-> "",
    nonce |-> 0
]


IsValidJWT(jwt) ==
    /\ jwt.iat <= currTime
    /\ jwt.exp > currTime
    /\ jwt.nonce \notin nonceRegistry

IsValidPassport(ppt) ==
    /\ ppt.iat <= currTime
    /\ ppt.signature = "valid"

Init ==  
    /\ currTime = 0
    /\ callState = [id \in callIds |->
        [stage |-> "SIP_Origination",   \* Location of call signal
         pport |-> [iat |-> currTime, signature |-> "valid"], \* PASSporT for call attestation
         jwt |-> NoJWT]]  \* JSON Web Token for PASSporT transmission to STI-CPS
    /\ stiCPS = [id \in callIds |-> NoPassport]
    /\ stiOOBS = [id \in callIds |-> "idle"]
    /\ nonceRegistry = {}

PublishPassport(id) ==
    /\ callState[id].stage = "SIP_Origination"
    /\ stiOOBS[id] = "idle"
    /\ IsValidPassport(callState[id].pport)
    /\ stiOOBS' = [stiOOBS EXCEPT ![id] = "publishing"]
    /\ stiCPS' = [stiCPS EXCEPT ![id] = callState[id].pport]
    /\ callState' = [callState EXCEPT
                        ![id].stage = "TDM_NNI",
                        ![id].pport = NoPassport,
                        ![id].jwt = [
                            iat |-> currTime,
                            exp |-> currTime + JWT_TTL,
                            nonce |-> currTime * 10 + id
                        ]]
    /\ nonceRegistry' = nonceRegistry \cup {callState'[id].jwt.nonce}
    /\ currTime' = currTime + 1

TDMNNIRetrievePassport(id) ==
    /\ callState[id].stage = "TDM_NNI"
    /\ stiOOBS[id] = "publishing"
    /\ stiCPS[id] /= NoPassport
    /\ IsValidPassport(stiCPS[id])
    /\ stiOOBS' = [stiOOBS EXCEPT ![id] = "retrieving"]
    /\ callState' = [callState EXCEPT 
                        ![id].stage = "TDM_Interconnect",
                        ![id].pport = stiCPS[id],
                        ![id].jwt = [
                            iat |-> currTime,
                            exp |-> currTime + JWT_TTL,
                            nonce |-> currTime * 10 + id
                        ]]
    /\ stiCPS' = [stiCPS EXCEPT ![id] = NoPassport]
    /\ currTime' = currTime + 1
    /\ nonceRegistry' = nonceRegistry \cup {callState'[id].jwt.nonce}

TDMNNIPublishPassport(id) ==
    /\ callState[id].stage = "TDM_Interconnect"
    /\ callState[id].pport /= NoPassport
    /\ stiOOBS' = [stiOOBS EXCEPT ![id] = "publishing"]
    /\ stiCPS' = [stiCPS EXCEPT ![id] = callState[id].pport]
    /\ callState' = [callState EXCEPT  
                        ![id].pport = NoPassport,
                        ![id].jwt = [
                            iat |-> currTime,
                            exp |-> currTime + JWT_TTL,
                            nonce |-> currTime * 10 + id
                        ]]
    /\ \E latency \in 5..MaxTDMLatency: 
            currTime' = currTime + latency
    /\ nonceRegistry' = nonceRegistry \cup {callState'[id].jwt.nonce}

ReintegratePassport(id) ==
    /\ callState[id].stage = "TDM_Interconnect"
    /\ stiCPS[id] /= NoPassport
    /\ IsValidPassport(stiCPS[id])
    /\ stiOOBS' = [stiOOBS EXCEPT ![id] = "retrieving"]
    /\ callState' = [callState EXCEPT  
                        ![id].stage = "SIP_Termination",
                        ![id].pport = stiCPS[id],
                        ![id].jwt = [
                            iat |-> currTime,
                            exp |-> currTime + JWT_TTL,
                            nonce |-> currTime * 1000 + id
                        ]]
    /\ currTime' = currTime + 1
    /\ nonceRegistry' = nonceRegistry \cup {callState'[id].jwt.nonce}
    /\ UNCHANGED stiCPS

\* This action will ensure calls retan attestation
CompleteCall(id) ==
    /\ callState[id].stage = "SIP_Termination"
    /\ IsValidPassport(callState[id].pport)
    /\ stiOOBS' = [stiOOBS EXCEPT ![id] = "idle"]
    /\ UNCHANGED <<currTime, stiCPS, callState, nonceRegistry>>

ReplayJWT(id) ==
    /\ callState[id].stage = "SIP_Termination"
    /\ callState[id].jwt /= NoJWT
    /\ ~IsValidJWT(callState[id].jwt)
    /\ UNCHANGED <<currTime, stiCPS, stiOOBS, callState, nonceRegistry>>

Next ==
    \/ \E id \in callIds: PublishPassport(id)
    \/ \E id \in callIds: TDMNNIRetrievePassport(id)
    \/ \E id \in callIds: TDMNNIPublishPassport(id)
    \/ \E id \in callIds: ReintegratePassport(id)
    \/ \E id \in callIds: CompleteCall(id)
    \/ \E id \in callIds: ReplayJWT(id)

Liveness ==
    \* Ensures all calls will eventually terminate
   /\ \A id \in callIds:
        <>[](callState[id].stage = "SIP_Termination")
    \* Ensure stiOOBS nodes will eventually all be idle when call finishes
    /\ \A id2 \in callIds:
        <>[](stiOOBS[id2] = "idle")

Invariants ==
    \* Attestation preserved by CompleteCall action
    \* PASSporT is validated before call is completed.

    \* STI-CPS holds PASSporT through TDM traversal
    /\ \A id2 \in callIds:
        [](callState[id2].stage = "TDM_Interconnect" =>
            stiCPS[id2] /= NoPassport)

    \* PASSporTs remain valid
    /\ \A id3 \in callIds:
        [](callState[id3].pport.payload.iat + MaxTokenTTL >= currTime)


Spec == 
    Init 
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ Liveness
============================================================================