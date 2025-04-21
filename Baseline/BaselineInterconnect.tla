---------------------------- MODULE BaselineInterconnect ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES currentNetwork, passportStatus


Init ==
    \* Call from IP-based network with SHAKEN compliant passport attached
    /\ currentNetwork = "IP1"
    /\ passportStatus = "attached"

(* 
    We separate out the steps as calls are passed through to IP2
    and attestation is lost.
    1: IP1 passes call to TDM interconnect
    2: PASSporT is lost
    3: Transition to IP2
*)
Next ==
    \/ \* Call goes from IP1 -> TDM 
        /\ currentNetwork = "IP1"
        /\ currentNetwork' = "TDM1"
        /\ passportStatus' = "dropped" (* Passport lost *)
    \/
        /\ currentNetwork = "TDM1"
        /\ currentNetwork'= "TDM2"
        /\ UNCHANGED <<passportStatus>>
    \/  
        /\ currentNetwork = "TDM2"
        /\ currentNetwork' = "IP2"
        /\ UNCHANGED <<passportStatus>>
    \/  
        /\ currentNetwork = "IP2"
        /\ UNCHANGED <<passportStatus, currentNetwork>>

Invariants ==
       [](currentNetwork \in  {"TDM1", "TDM2"} => passportStatus = "dropped")
    /\ [](currentNetwork = "IP2" => passportStatus = "dropped")

Spec == Init /\ [][Next]_<<currentNetwork, passportStatus>>
=============================================================================