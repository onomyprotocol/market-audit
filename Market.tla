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
                    ELSE Cardinality(s[i].bag) + F[i - 1]
                IN  F[Len(s)]

\* Sequence Helpers
IGT(limitSeq, pos) ==   {i \in DOMAIN limitSeq: 
                        limitSeq[i].exchrate > pos.exchrate}
ILT(stopSeq, pos) ==    {i \in DOMAIN stopSeq: 
                        stopSeq[i].exchrate < pos.exchrate}
-----------------------------------------------------------------------------
\* Three Coin Types. Two Denoms and NOM
CoinType == {"Denom_A", "Denom_B", "NOM"}

PairTypePre == {{a, b} : a \in CoinType, b \in CoinType}
PairType == { ptp \in PairTypePre : Cardinality(ptp) > 1 }
PairPlusCoin == { <<pair, coin>> \in PairType \X CoinType : coin \in pair }

\* Coins are held in bags of which whose Cardinality
\* represents a balance or amount of coins
CoinBag ==  SUBSET Denom_A 
            \union  SUBSET Denom_B 
            \union  SUBSET NOM

ExchRateType == {<<a, b>> : a \in CoinBag, b \in CoinBag}

CoinBagger(bidCoinType) ==  CASE    bidCoinType = "Denom_A" -> Denom_A
                            []      bidCoinType = "Denom_B" -> Denom_B
                            []      bidCoinType = "NOM" -> NOM 

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

CoinRecord ==
  CoinRecords("Denom_A") \union CoinRecords("Denom_B") \union CoinRecords("NOM")

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
    \* [<< -> Limits]]
/\  limits \in [<<PairType, CoinType>> -> Seq(PositionType)]
/\  reserve \in [CoinType -> CoinBag]
    \* [Bid -> [Ask -> Stops]]
/\  stops \in [<<PairType, CoinType>> -> Seq(PositionType)]

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
/\  limits = [ppc \in PairPlusCoin |-> <<>>]
/\  reserve = [type \in CoinType |-> 
        CASE    type = "Denom_A" -> Denom_A        
        []      type = "Denom_B" -> Denom_B
        []      type = "NOM" -> NOM
    ]
/\  stops =[ppc \in PairPlusCoin |-> <<>>] 

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
/\  UNCHANGED << ask, bid, limits, stops >>

Withdraw(acct, bag, type) ==
/\  bag \in SUBSET accounts[acct][type].bag
/\  accounts' = [accounts EXCEPT ![acct][type] = 
        [
            bag |-> @.bag \ bag,
            positions |-> @.positions
        ]
    ]
/\  reserve' = [reserve EXCEPT ![type] = @ \union bag]
/\  UNCHANGED << ask, bid, limits, stops >>

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
    IF Cardinality(pos.bag) > Cardinality(accounts[acct][bidCoin].bag)
    THEN UNCHANGED << accounts, ask, bid, limits, stops >>
    ELSE
    LET 
        t == IF type = "limit" THEN 1 ELSE 2
        bag == accounts[acct][bidCoin].bag
        posSeqs == accounts[acct][bidCoin].positions[askCoin]
    IN 
    /\  IF  SumSeq(posSeqs[t]) + Cardinality(pos.bag) <= Cardinality(bag)
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
        bag == accounts[acct][bidCoin].bag
        posSeqs == accounts[acct][bidCoin].positions[askCoin]
        pos == posSeqs[i]
    IN  IF t = 1
        THEN       
            /\  limits' =
                    [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Remove(@, pos[1])]
            /\  accounts' = [ 
                    accounts EXCEPT ![acct][bidCoin].positions[askCoin] = 
                    <<Remove(@, pos[1]),@[2]>>
                ]
            /\  UNCHANGED << stops >> 
        ELSE    
            /\  stops' = [
                    stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Remove(@, pos[2])
                ]
            /\  accounts' = [ 
                    accounts EXCEPT ![acct][bidCoin].positions[askCoin] = 
                    <<@[1], Remove(@, pos[2])>>
                ]
            /\  UNCHANGED << limits >>

NEXT == \/  \E acct \in ExchAccount :
            \E denom \in CoinType :
                \/  \E bag \in SUBSET reserve[denom] :
                    IF Cardinality(bag) > 0 THEN
                        Deposit(acct, bag, denom)
                    ELSE UNCHANGED <<accounts, ask, bid, limits, stops, reserve>>
                \/  \E bag \in SUBSET accounts[acct][denom].bag :
                    IF Cardinality(bag) > 0 THEN
                        Withdraw(acct, bag, denom)
                    ELSE UNCHANGED <<accounts, ask, bid, limits, stops, reserve>>
        \/  \E  acct \in ExchAccount :
            \E  type \in {"limit", "stop"} :
            \E  askCoin \in CoinType :
            \E  bidCoin \in CoinType \ {askCoin} :
            \E  askRateBag \in CoinBagger(askCoin) :
            \E  bidRateBag \in CoinBagger(bidCoin) :
            \E  exchrate \in { <<a, b>> : a \in SUBSET {askRateBag}, b \in SUBSET {bidRateBag} } : 
            \E  bag \in SUBSET CoinBagger(bidCoin) :
                \* select a non-empty bag of coins
             /\ bag # {}
             /\ \/  /\ Open(acct, askCoin, bidCoin, type, [
                        \* Position owner 
                        acct |-> acct,
                        \* Exchange Rate is defined as
                        \* Cardinality(exchrate[1]) / Cardinality(exchrate[2])
                        exchrate |-> exchrate,
                        \* cardinality of bag is the amount
                        bag |-> bag
                      ])
                    /\ UNCHANGED reserve
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
         
Spec == INIT /\ [][NEXT]_<<accounts, ask, bid, limits, reserve, stops>>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Thu Aug 05 22:34:04 CDT 2021 by Charles Dusek
\* Created Sat Jul 31 19:33:47 CDT 2021 by Charles Dusek
