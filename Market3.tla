------------------------------- MODULE Market3 -------------------------------
EXTENDS     FiniteSets, FiniteSetsExt, Naturals, Sequences, SequencesExt

CONSTANT    ExchAccount,    \* Set of all accounts
            MaxAmount       \* Max amount of coins in circulation

VARIABLE    accounts,
\* Ask coin
            ask,
            \* Bid coin
            bid,
            \* Limit Books
            limits,
            \* The reserve holds the initial amounts
            reserve,
            \* Stop Books
            stops

-----------------------------------------------------------------------------
\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
GT(a, b) ==     IF a[1]*b[2] > a[2]*b[1] THEN TRUE ELSE FALSE

GTE(a, b) ==    IF a[1]*b[2] >= a[2]*b[1] THEN TRUE ELSE FALSE 

LT(a, b) ==     IF a[1]*b[2] < a[2]*b[1] THEN TRUE ELSE FALSE

LTE(a, b) ==    IF a[1]*b[2] <= a[2]*b[1] THEN TRUE ELSE FALSE

\* Sequence Helpers
IGT(limitSeq, pos) ==   {i \in DOMAIN limitSeq: 
                            GT(
                                limitSeq[i].exchrate,
                                pos.exchrate
                            )}
ILT(stopSeq, pos) ==    {i \in DOMAIN stopSeq: 
                            LT(
                                stopSeq[i].exchrate,
                                pos.exchrate
                            )}


\* Three Coin Types. Two Denoms and NOM
CoinType == {"Denom_A", "Denom_B", "NOM"}


Amounts == 0..MaxAmount

\* amounts are pairs <<type, amount>>
AmountType(b) == b[1]  
AmountAmount(b) == b[2]

PairTypePre == {{a, b} : a \in CoinType, b \in CoinType}
PairType == { ptp \in PairTypePre : Cardinality(ptp) > 1 }
PairPlusCoin == { <<pair, coin>> \in PairType \X CoinType : coin \in pair }

ExchRateType == {<<a, b>> : a \in Amounts, b \in Amounts}

PositionType == 
[
    acct: ExchAccount,
    \* Exchange Rate is defined as
    \* Cardinality(exchrate[0]) / Cardinality(exchrate[1])
    exchrate: ExchRateType,
    \* cardinality of amount is the amount
    amount: Amounts
]

CoinRecords(ct) == [
                \* Holds a amount (set) of coins
                \* Balances are represented by Cardinality of amount
                \* So, in implementation, consider this balance
                amount: Amounts,
                positions: [CoinType -> Seq(Seq(PositionType) \X Seq(PositionType))]
                    
              ]

CoinRecord == CoinRecords("Denom_A") \union CoinRecords("Denom_B") \union CoinRecords("NOM") 

TypeInvariant ==     
/\  accounts \in [
        ExchAccount -> {
          f \in [CoinType -> CoinRecord]:
          \A ct \in CoinType: f[ct] \in CoinRecords(ct)
        }
      ]
/\  ask \in CoinType
    \* Bid Coin
/\  bid \in CoinType
/\  limits \in [Seq(PairType \X CoinType) -> Seq(PositionType)]
/\  reserve \in [CoinType -> Amounts]
/\  stops \in [Seq(PairType \X CoinType) -> Seq(PositionType)]

INIT ==     
/\  accounts = [
        ea \in ExchAccount |-> [ 
            ct \in CoinType |-> [
                amount |-> 0, 
                positions |-> [c \in CoinType \ {ct} |-> << <<>>, <<>> >>]
            ]
        ]
    ]
/\  ask = "NOM"
/\  bid = "Coin_A"
/\  limits = [ppc \in PairPlusCoin |-> <<>>]
/\  reserve = [type \in CoinType |->
        CASE    type = "Denom_A" -> MaxAmount        
        []      type = "Denom_B" -> MaxAmount
        []      type = "NOM" -> MaxAmount
    ]
/\  stops =[ppc \in PairPlusCoin |-> <<>>] 


(***************************************************************************)
(* Deposit(acct, amount, type)                                             *)
(*                                                                         *)
(* The Deposit function takes a SUBSET of coins from a single type and     *)
(* the reserve and places it into an exchange account.                     *)
(***************************************************************************)
Deposit(acct, amount, type) ==
/\  amount <= reserve[type]
    /\  accounts' = [accounts EXCEPT ![acct][type] = 
            [
                amount |-> @.amount + amount,
                positions |-> @.positions
            ]
        ]
    /\  reserve' = [reserve EXCEPT ![type] = @ - amount]
    /\  UNCHANGED << ask, bid, limits, stops >>

Withdraw(acct, amount, type) ==
    /\  amount <= accounts[acct][type].amount
    /\  accounts' = [accounts EXCEPT ![acct][type] = 
            [
                amount |-> @.amount - amount,
                positions |-> @.positions
            ]
        ]
    /\  reserve' = [reserve EXCEPT ![type] = @ + amount]
    /\  UNCHANGED << ask, bid, limits, stops >>

Open(acct, askCoin, bidCoin, type, pos) == 
    LET positions == accounts[acct][bidCoin].positions[askCoin] IN
    \* Exchange Account Balance of Bid Coin must not be less then than the
    \* total amounts in all positions for any particular pair with the Bid 
    \* Coin.
    IF  accounts[acct][bidCoin].amount < 
        pos.amount + 
        IF Len(positions[1]) > 0 THEN
            IF Len(positions[2]) > 0
            THEN Sum(positions[1]) + Sum(positions[2])
            ELSE Sum(positions[1])
        ELSE
            IF Len(positions[2]) > 0
            THEN Sum(positions[2])
            ELSE 0
        

    THEN UNCHANGED << accounts, ask, bid, limits, stops >>
    ELSE
    LET 
        t == IF type = "limit" THEN 1 ELSE 2
        amount == accounts[acct][bidCoin].amount
        posSeqs == accounts[acct][bidCoin].positions[askCoin]
    IN 
    /\  IF  Sum(posSeqs[t]) + pos.amount <= amount
        THEN
        /\  ask' = askCoin
        /\  bid' = bidCoin   
            \* IF type is limit?  
        /\  IF  t = 1
            THEN
            /\  LET igt == IGT(posSeqs[1], pos) IN
                IF igt = {} 
                THEN 
                    accounts' = 
                        [accounts EXCEPT ![acct][bidCoin].positions[askCoin] =
                        <<Append(@[1], pos),@[2]>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![acct][bidCoin].positions[askCoin] =
                        <<InsertAt(@[1], Min(igt), pos),@[2]>>]
            /\  LET igt == IGT(limits[<<{askCoin, bidCoin}, bidCoin>>], pos) IN
                IF igt = {}
                THEN    limits' =
                    [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Append(@, pos)]
                ELSE    limits' =
                    [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    InsertAt(@, Min(igt), pos)]
            /\  UNCHANGED << stops >>
            \* ELSE type is stops
            ELSE
            /\  LET ilt == ILT(posSeqs[2], pos) IN
                IF ilt = {}
                THEN 
                    accounts' = 
                        [accounts EXCEPT ![acct][bidCoin].positions[askCoin] =
                        <<@[1], Append(@[2], pos)>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![acct][bidCoin].positions[askCoin] =
                        <<@[1], InsertAt(@[2], Max(ilt), pos)>>]
            /\  LET ilt == ILT(stops[<<{askCoin, bidCoin}, bidCoin>>], pos) IN
                IF ilt = {}
                THEN    
                    stops' =
                        [stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                        Append(@, pos)]
                ELSE
                    stops' =
                        [stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                        InsertAt(@, Max(ilt), pos)]
            /\  UNCHANGED << limits >>
        \* ELSE Balance is too low
        ELSE    UNCHANGED << accounts, ask, bid, limits, stops >>

Close(acct, askCoin, bidCoin, type, i) ==
    LET 
        t == IF type = "limit" THEN 1 ELSE 2
        amount == accounts[acct][bidCoin].amount
        posSeqs == accounts[acct][bidCoin].positions[askCoin]
        pos == posSeqs[t][i]
    IN  IF t = 1
        THEN       
            /\  limits' =
                    [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Remove(@, pos)]
            /\  accounts' = [ 
                    accounts EXCEPT ![acct][bidCoin].positions[askCoin][1] = 
                    Remove(@, pos)
                ]
            /\  UNCHANGED << stops >> 
        ELSE    
            /\  stops' = [
                    stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Remove(@, pos)
                ]
            /\  accounts' = [ 
                    accounts EXCEPT ![acct][bidCoin].positions[askCoin][2] = 
                    Remove(@, pos)
                ]
            /\  UNCHANGED << limits >>

NEXT == \/  \E acct \in ExchAccount :
            \E type \in CoinType :
            \E amount \in Amounts :
                \/  IF amount > 0 THEN
                        Deposit(acct, amount, type)
                    ELSE UNCHANGED <<
                            accounts, 
                            ask,
                            bid,
                            limits, 
                            reserve,
                            stops
                        >>
                \/  IF amount > 0 THEN
                        Withdraw(acct, amount, type)
                    ELSE UNCHANGED <<
                            accounts, 
                            ask,
                            bid,
                            limits, 
                            reserve,
                            stops
                        >>
        \/  \E  acct \in ExchAccount :
            \E  type \in {"limit", "stop"} :
            \E  askCoin \in CoinType :
            \E  bidCoin \in CoinType \ {askCoin} :
            \E  exchrate \in { <<a, b>> : 
                    a \in Amounts, 
                    b \in Amounts 
                } : 
            \E  bidAmount \in Amounts :
                \* select a non-empty bag of coins
             /\ bidAmount > 0
             /\ \* Open
                \/  /\ Open(acct, askCoin, bidCoin, type, [
                        \* Position owner 
                        acct |-> acct,
                        \* Exchange Rate is defined as
                        \* Cardinality(exchrate[1]) / Cardinality(exchrate[2])
                        exchrate |-> exchrate,
                        \* cardinality of bag is the amount
                        amount |-> bidAmount
                      ])
                    /\ UNCHANGED reserve
                \*  Close
                \/  IF type = "limit" 
                    THEN 
                    \* get the first sequence
                    LET seq == accounts[acct][bidCoin].positions[askCoin][1] IN
                    /\  Len(seq) > 0
                    /\  \E  i \in DOMAIN seq :
                        /\  Close(
                                acct,
                                askCoin,
                                bidCoin,
                                type,
                                i
                            )
                        /\ UNCHANGED <<reserve, ask, bid>>
                    ELSE 
                    \* get the second sequence
                    LET seq == accounts[acct][bidCoin].positions[askCoin][2] IN
                    /\  Len(seq) > 0
                    /\  \E  i \in DOMAIN seq :   
                        /\  Close(
                                acct,
                                askCoin,
                                bidCoin,
                                type,
                                i
                            )
                        /\ UNCHANGED <<reserve, ask, bid>>
         
Spec == INIT /\ 
        [][NEXT]_<<
            accounts,
            ask,
            bid,
            limits, 
            reserve,
            stops
          >>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
