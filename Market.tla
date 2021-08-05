------------------------------- MODULE Market -------------------------------
EXTENDS     FiniteSets, FiniteSetsExt, Naturals, Sequences, SequencesExt

CONSTANT    ExchAccount,    \* Set of all accounts
            NOM,           \* Set of all coins
            Denom_A,
            Denom_B

VARIABLE    accounts,
            \* Ask coin
            ask,
            \* Bid coin
            bid,
            \* Limit Books
            limits,
            \* The reserve holds the initial bags
            reserve,
            \* Stop Books
            stops

-----------------------------------------------------------------------------
SumSeq(s) ==    LET F[i \in 0..Len(s)] ==
                    IF i = 0 THEN 0
                    ELSE UNION { s[i].bag + F[i-1].bag }
                IN  Cardinality(F[Len(s)])

\* Sequence Helpers
IGT(limitSeq, pos) ==   {i \in 0..Len(limitSeq): 
                        limitSeq[i].exchrate > pos.exchrate}
ILT(stopSeq, pos) ==    {i \in 0..Len(stopSeq): 
                        stopSeq[i].exchrate < pos.exchrate}
-----------------------------------------------------------------------------
\* Three Coin Types. Two Denoms and NOM
CoinType == {"Denom_A", "Denom_B", "NOM"}

\* Coins are held in bags of which whose Cardinality
\* represents a balance or amount of coins
CoinBag == SUBSET Denom_A \/ SUBSET Denom_B \/ SUBSET NOM

ExchRateType == Seq(CoinBag \X CoinBag)

PositionType == 
[
    \* Position owner 
    acct: ExchAccount,
    \* Exchange Rate is defined as
    \* Cardinality(exchrate[0]) / Cardinality(exchrate[1])
    exchrate: ExchRateType,
    \* cardinality of bag is the amount
    bag: CoinBag
]

CoinRecords(ct) == 
[
    \* Holds a bag (set) of coins
    \* Balances are represented by Cardinality of bag
    \* So, in implementation, consider this balance
    bag: CoinBag,
    positions: [CoinType \ {ct} -> Seq(Seq(PositionType) \X Seq(PositionType))]                    
]

CoinRecord == CoinRecords(Denom_A) \/ CoinRecords(Denom_B) \/ CoinRecords(NOM)

-----------------------------------------------------------------------------

TypeInvariant ==     
/\  accounts \in [
        ExchAccount -> {
            f \in [CoinType -> CoinRecord]:
            \A ct \in CoinType: f[ct] \in CoinRecords(ct)
        }
    ]
    \* Ask Coin
/\  ask \in CoinType
    \* Bid Coin
/\  bid \in CoinType
    \* [Bid -> [Ask -> Limits]]
/\  limits \in [CoinType -> [CoinType -> Seq(PositionType)]]
/\  reserve \in [CoinType -> CoinBag]
    \* [Bid -> [Ask -> Stops]]
/\  stops \in [CoinType -> [CoinType -> Seq(PositionType)]]

INIT ==     
/\  accounts = [
        ea \in ExchAccount |-> [ 
            ct \in CoinType |-> [
                bag |-> {}, 
                positions |-> [c \in CoinType \ {ct} |-> << <<>>, <<>> >>]
            ]
        ]
    ]
/\  ask = "NOM"
/\  bid = "Coin_A"
/\  limits \in [
        bidCoin \in CoinType |-> 
        [askCoin \in CoinType |-> << >>]
    ]
/\  reserve = [type \in CoinType |-> 
        CASE    type = "Denom_A" -> Denom_A        
        []      type = "Denom_B" -> Denom_B
        []      type = "NOM" -> NOM
    ]
/\  stops \in [
        bidCoin \in CoinType |-> 
        [askCoin \in CoinType |-> << >>]
    ]

(***************************************************************************)
(* Deposit(acct, bag, type)                                                *)
(*                                                                         *)
(* The Deposit function takes a SUBSET of coins from a single type and     *)
(* the reserve and places it into an exchange account.                     *)
(***************************************************************************)
Deposit(acct, bag, type) ==
/\  bag \in SUBSET reserve[type]
/\  accounts' = [accounts EXCEPT ![acct][type] = 
        [
            bag |-> bag \union @.bag,
            positions |-> @.positions
        ]
    ]
/\  reserve' = [reserve EXCEPT ![type] = @ \ bag]

Withdraw(acct, bag, type) ==
/\  bag \in SUBSET accounts[acct][type].bag
/\  accounts' = [accounts EXCEPT ![acct][type] = 
        [
            bag |-> @.bag \ bag,
            positions |-> @.positions
        ]
    ]
/\  reserve' = [reserve EXCEPT ![type] = @ \union bag]

(***************************************************************************)
(* Open(acct, askCoin, bidCoin, pos)                                       *)
(*                                                                         *)
(* Open a position on the exchange.  The position is placed in the         *)
(* corresponding user exchange account bid coin sequence and the exchange  *)
(* order book defined by the type, bid coin and ask coin.                  *)
(*                                                                         *) 
(* Parameters                                                              *)
(* acct<AccountType>: Exchange Account                                     *)
(* askCoin<Coin>: Ask Coin                                                 *)
(* bidCoin<Coin>: Bid Coin                                                 *)
(* pos<PositionType>: Position                                             *)
(***************************************************************************)
Open(acct, askCoin, bidCoin, type, pos) == 
    IF Cardinality(pos.bag) > Cardinality(accounts[acct][bidCoin].balance)
    THEN UNCHANGED << accounts, ask, bid, limits, stops >>
    ELSE
    LET 
        t == IF type = "limit" THEN 1 ELSE 2
        balance == accounts[acct][bidCoin].balance
        posSeqs == accounts[acct][bidCoin].positions[askCoin]
    IN 
    /\  IF  SumSeq(posSeqs[t]) + Cardinality(pos.amt) <= Cardinality(balance)
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
                        <<Append(pos, @[1]),@[2]>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![acct][bidCoin].positions[askCoin] =
                        <<InsertAt(@[1], Min(igt), pos),@[2]>>]
            /\  LET igt == IGT(limits[bidCoin][askCoin], pos) IN
                IF igt = {}
                THEN    limits' =
                    [limits EXCEPT ![bidCoin][askCoin] =
                    Append(pos, @)]
                ELSE    limits' =
                    [limits EXCEPT ![askCoin][bidCoin] =
                    InsertAt(@, Min(igt), pos)]
            /\  UNCHANGED << stops >>
            \* ELSE type is stops
            ELSE
            /\  LET ilt == ILT(posSeqs[2], pos) IN
                IF ilt = {}
                THEN 
                    accounts' = 
                        [accounts EXCEPT ![<<acct, bidCoin>>].positions[askCoin] =
                        <<@[1], Append(pos, @[2])>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![acct][bidCoin].positions[askCoin] =
                        <<@[1], InsertAt(@[2], Max(ilt), pos)>>]
            /\  LET ilt == ILT(stops[askCoin][bidCoin], pos) IN
                IF ilt = {}
                THEN    
                    stops' =
                        [stops EXCEPT ![bidCoin][askCoin] =
                        Append(pos, @)]
                ELSE
                    stops' =
                        [stops EXCEPT ![bidCoin][askCoin] =
                        InsertAt(@, Max(ilt), pos)]
            /\  UNCHANGED << limits >>
        \* ELSE Balance is too low
        ELSE    UNCHANGED << accounts, ask, bid, limits, stops >>

Close(acct, askCoin, bidCoin, type, i) ==
    LET 
        t == IF type = "limit" THEN 1 ELSE 2
        balance == accounts[acct][bidCoin].balance
        posSeqs == accounts[acct][bidCoin].positions[askCoin]
        pos == posSeqs[i]
    IN  IF t = 1
        THEN       
            /\  limits' =
                    [limits EXCEPT ![bidCoin][askCoin] =
                    Remove(@[1], pos)]
            /\  accounts' = [ 
                    accounts EXCEPT ![acct][bidCoin].positions[askCoin] = 
                    <<Remove(@[1], pos),@[2]>>
                ]
            /\  UNCHANGED << stops >> 
        ELSE    
            /\  stops' = [
                    stops EXCEPT ![bidCoin][askCoin] =
                    Remove(@[2], pos)
                ]
            /\  accounts' = [ 
                    accounts EXCEPT ![acct][bidCoin].positions[askCoin] = 
                    <<@[1], Remove(@[2], pos)>>
                ]
            /\  UNCHANGED << limits >>

NEXT == \/  \E acct \in ExchAccount :
            \E denom \in CoinType :
                \/  \E bag \in SUBSET reserve[denom] :
                    IF Cardinality(bag) > 0 THEN
                        Deposit(acct, bag, denom)
                    ELSE UNCHANGED <<accounts, reserve>>
                \/  \E bag \in SUBSET accounts[acct][denom].bag :
                    IF Cardinality(bag) > 0 THEN
                        Withdraw(acct, bag, denom)
                    ELSE UNCHANGED <<accounts, reserve>>
        \/  \E  acct \in ExchAccount :
            \E  askCoin \in CoinType :
            \E  bidCoin \in CoinType \ {askCoin} :
            \E  pos \in PositionType :
            \E  type \in {"limit", "stop"} :
            \/  Open(acct, askCoin, bidCoin, type, pos)
            \/  IF type = "limit" 
                THEN 
                    \E seq \in acct[bidCoin].positions[askCoin][1] :
                    /\  Len(seq) > 0
                    /\  \E  i \in Len(seq) :    
                        /\  Close(
                                acct,
                                askCoin,
                                bidCoin,
                                type,
                                i
                            )
                        
                                 
                ELSE 
                    \E seq \in acct[bidCoin].positions[askCoin][2] :
                    /\  Len(seq) > 0
                    /\  \E  i \in Len(seq) :   
                        /\  Close(
                                acct,
                                askCoin,
                                bidCoin,
                                type,
                                i
                            )
         
Spec == INIT /\ [][NEXT]_<<accounts, ask, bid, limits, reserve, stops>>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Thu Aug 05 13:33:34 CDT 2021 by Charles Dusek
\* Created Sat Jul 31 19:33:47 CDT 2021 by Charles Dusek
