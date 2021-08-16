------------------------------- MODULE Market4 -------------------------------
EXTENDS     FiniteSets, FiniteSetsExt, Naturals, Sequences, SequencesExt

CONSTANT    ExchAccount,    \* Set of all accounts
            MaxAmount       \* Max amount of coins in circulation

VARIABLE    accounts,
            \* Drops are proportional entitlements to the AMM liquidity pools
            drops,
            \* Limit Books
            limits,
            \* Pools hold the AMM liquidity
            pools,
            \* The reserve holds the initial amounts
            reserve,
            \* Stop Books
            stops

vars == <<accounts, limits, reserve, stops>>

-----------------------------------------------------------------------------
\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
GT(a, b) == a[1]*b[2] > a[2]*b[1]

GTE(a, b) == a[1]*b[2] >= a[2]*b[1] 

LT(a, b) == a[1]*b[2] < a[2]*b[1]

LTE(a, b) == a[1]*b[2] <= a[2]*b[1]

\* Given a sequence of positions `seq \in Seq(PositionType)`, sum up
\* all of the position amounts. Returns 0 if seq is empty.
SumSeqPos(seq) == FoldLeft( LAMBDA p,q: p + q.amount, 0, seq )

\* Asserts that balance covers the sum of all position amounts in limitsSeq and stopsSeq
PositionInv( limitsSeq, stopsSeq, balance ) ==
    SumSeqPos( limitsSeq ) + SumSeqPos(stopsSeq) <= balance

TruncatePositions( limitsSeq, stopsSeq, balance ) == 
    \* we use CHOOSE to get one pair, but the cutoff pair is not necessarily unique:
    \* consider: balance = 1, limtsSeq (amounts) = << 1,1 >>, stopsSeq (amounts) = << 1, 1 >>
    \* Truncation returns either << <<>>, <<1>> >> or << <<1>>, <<>> >>
    \* It is up to the implementation to define a deterministic way of resolving 
    \* cases with multiple solutions. 
    \* For example, the implementation could prefer to truncate limits over stops whenever possible
    LET cutoffs == CHOOSE pair \in (DOMAIN limitsSeq \union {0}) \X (DOMAIN stopsSeq \union {0}):
        LET i == pair[1]
            j == pair[2] 
        IN 
        /\ PositionInv( SubSeq(limitsSeq, 1, i) , SubSeq(stopsSeq, 1, j), balance )
        /\ i < Len(limitsSeq) => 
            ~PositionInv( SubSeq(limitsSeq, 1, i+1) , SubSeq(stopsSeq, 1, j), balance ) 
        /\ j < Len(stopsSeq) =>
            ~PositionInv( SubSeq(limitsSeq, 1, i) , SubSeq(stopsSeq, 1, j +1 ), balance ) 
    IN << 
        SubSeq(limitsSeq, 1, cutoffs[1]), 
        SubSeq(stopsSeq, 1, cutoffs[2])
        >>

\* Three Coin Types. Two Denoms and NOM
CoinType == {"Denom_A", "Denom_B", "NOM"}


Amounts == 0..MaxAmount
PositiveAmounts == 1..MaxAmount

PairTypePre == {<<a, b>> : a \in CoinType, b \in CoinType}
PairType == { ptp \in PairTypePre : ptp[1] # ptp[2] }

PairSetTypePre == {<<a, b>> : a \in CoinType, b \in CoinType}
PairSetType == { pst \in PairSetTypePre : Cardinality(pst) > 1 }

ExchRateType == {<<a, b>> : a \in Amounts, b \in Amounts}

PositionType == 
[
    acct: ExchAccount,
    \* Exchange Rate is defined as
    \* Cardinality(exchrate[0]) / Cardinality(exchrate[1])
    exchrate: ExchRateType,
    \* cardinality of amount is the amount
    amount: PositiveAmounts
]

TypeInvariant ==  
\*  accounts[ <<acct, coin>> ] is the balance of `coin` in account `acct`
/\  accounts \in [ExchAccount \X CoinType -> Amounts]
\*  drops[ acct \X {coin, coin} ] is a balance of liquidity drop token
/\  drops \in [ExchAccount \X PairSetType -> Amounts] 
\*  limits[ <<acct, <<pair, coin>> >> ] is a sequence of positions tied to `acct` and the pair+coin `<<pair, coin>>`
/\  limits \in [ ExchAccount \X PairType -> Seq(PositionType)]
\*  pools[ pair ] is a balance of liquidity within a pool tied to a pair <<a, b>> where balance is b coin
/\  pools \in [ PairType -> Amounts ]
\*  stops[ <<acct, <<pair, coin>> >> ] is a sequence of positions tied to `acct` and the pair+coin `<<pair, coin>>`
/\  stops \in [ ExchAccount \X PairType -> Seq(PositionType)]
\*  reserve[ coin ] is the amount of coins of type `coin` currently held in reserve
/\  reserve \in [CoinType -> Amounts]

INIT ==     
\* initially, all ballances are 0 as all the coins are held by the reserve
/\  accounts = [eaAndCt \in ExchAccount \X CoinType |-> 0]
\* initially, there are no open positions    
/\  limits = [accTAndPpc \in ExchAccount \X PairType |-> <<>>]
/\  stops = [accTAndPpc \in ExchAccount \X PairType |-> <<>>] 
\* initially, all the coins are in the reserve
/\  reserve = [type \in CoinType |-> MaxAmount]

(***************************************************************************)
(* Deposit(acct, amount, type)                                             *)
(*                                                                         *)
(* The Deposit function takes an amount of coins from a single type and    *)
(* the reserve and places it into an exchange account.                     *)
(***************************************************************************)
Deposit(acct, amount, coinType) ==
    /\  amount <= reserve[coinType]
    /\  accounts' = [accounts EXCEPT ![acct, coinType] = @ + amount]
    /\  reserve' = [reserve EXCEPT ![coinType] = @ - amount]
    /\  UNCHANGED << limits, stops >>

\* Does not automatically update positions. It requires problematic positions
\* to already be closed (externally), before balances are changed
ConditionalWithdraw(acct, amount, coinType) ==
    LET newBalance == accounts[acct,coinType] - amount
    IN
    /\  amount <= accounts[acct, coinType]
    \* Precondition: the post-withdrawal balance still covers open positions
    \* It is up to the user to select and close positions before withdrawal
    /\  \A askCoin \in CoinType \ {coinType}:
        PositionInv( 
            limits[acct, <<{askCoin, coinType}, coinType>>],
            stops[acct, <<{askCoin, coinType}, coinType>>],
            newBalance
            )
    /\  accounts' = [accounts EXCEPT ![acct, coinType] = @ - amount]
    /\  reserve' = [reserve EXCEPT ![coinType] = @ + amount]
    /\  UNCHANGED << limits, stops >>

\* Automatically updates positions if the balance goes below the amounts required by open positions
Withdraw(acct, amount, coinType) ==
    /\  amount <= accounts[acct, coinType]
    /\  LET newBalance == accounts[acct, coinType] - amount 
        IN 
        /\ accounts' = [accounts EXCEPT ![acct, coinType] = newBalance]
        \* We need to prune limits and stops, such that we keep the 
        \* longest possible prefix, for which the sum of positions is covered by newBalance
        /\ limits' = [ acctAndPPC \in ExchAccount \X PairType |->
            LET acctArg == acctAndPPC[1]
                pair == acctAndPPC[2]
            IN  IF acctArg # acct \/ pair[2] # coinType
                THEN limits[acctArg, pair]
                ELSE 
                    LET newPosSeqPair == 
                        TruncatePositions( limits[acct, pair], stops[acct, pair], newBalance )
                    IN newPosSeqPair[1]
            ]
        /\ stops' = [ acctAndPPC \in ExchAccount \X PairType |->
            LET acctArg == acctAndPPC[1]
                pair == acctAndPPC[2]
            IN  IF acctArg # acct \/ pair[2] # coinType
                THEN stops[acctArg, pair]
                ELSE 
                    LET newPosSeqPair == 
                        TruncatePositions( limits[acct, pair], stops[acct, pair], newBalance )
                    IN newPosSeqPair[2]
            ]
    /\  reserve' = [reserve EXCEPT ![coinType] = @ + amount]

(***************************************************************************)
(* Max amount that pool may sell of ask coin without                       *)
(* executing the most adjacent order                                       *)
(*                                                                         *)
(* Differential Invariant:                                                 *)
(* d(poolAsk) / d(poolBid) = d(erate)                                      *)
(* d(poolAsk) = d(poolBid) * d(erate)                                      *)
(*                                                                         *)
(* Integrate over poolAsk on lhs and poolBid & erate on rhs then           *)
(* substitute and simplify                                                 *)
(***************************************************************************)
MaxPoolBid(erateFinal, erateInitial) ==
erateInitial[2] * 
(
    (erateFinal[1] \ erateFinal[2]) *
    (
        2 - 
        (erateFinal[1] * erateInitial[2]) \
        (erateFinal[2] * erateInitial[1])
    )
) - erateInitial[1]

Execute(askCoin, bidCoin, limitsUpd, stopsUpd) ==
(***************************************************************************)
(* CASE 1: The Pool Exchange Rate (Ask Coin Bal / Bid Coin Bal) greater    *)
(*         than or equal Ask Stop Book Inverse Exchange Rate               *)
(***************************************************************************)
CASE    GTE(poolExchRate, askStopInverseExchrate) ->
    (***********************************************************************)
    (* CASE 1.1: Inverse Exchange Rate of the head of the Ask Stop Book    *)
    (*           is equal to exchange rate of the head of the Bid Limit    *)
    (*           book                                                      *)
    (*                                                                     *)
    (*   Action: Execute no loss trade                                     *)
    (***********************************************************************)
    CASE    EQ(bidLimitExchrate, askStopInverseExchRate) ->
    (***********************************************************************)
    (* CASE 1.2: Inverse Exchange Rate of the head of the Ask Stop Book    *)
    (*           is less than the exchange rate of the head of the Bid     *)
    (*           Limit book                                                *)
    (*                                                                     *)
    (*   Action: Execute Ask Stop Order                                    *)
    (***********************************************************************)
    []      LT(askStopInverseExchRate, bidLimitExchrate) ->
            
(***************************************************************************)
(* CASE 2: The Pool Exchange Rate (Ask Coin Bal / Bid Coin Bal) greater    *)
(*         than Bid Limit Book Exchange Rate                               *)
(*                                                                         *)
(* Action: Execute Bid Limit Order                                         *)
(***************************************************************************)      
[]      GT(bidLimitExchrate, poolExchRate) ->
        IF askStopInverseExchRate <= limitBook[2]
            THEN 
                LET strikeExchRate == askStopInverseExchRate
                    maxBid == MaxPoolBid(poolExchRate, strikeExchRate)
                IN  IF maxBid > bidLimit
                    THEN


Open(acct, askCoin, bidCoin, limitOrStop, pos) ==
    LET acctLimits == limits[acct,<<askCoin, bidCoin>>]
        acctStops == stops[acct,<<askCoin, bidCoin>>]
        balance == accounts[acct, bidCoin] IN 
    \* precondition: Exchange Account Balance of Bid Coin must be at least the
    \* total amounts in all positions for any particular pair with the Bid 
    \* Coin. 
    /\ balance >= pos.amount + SumSeqPos(acctLimits) + SumSeqPos(acctStops)
    /\  LET seqOfPos == IF limitOrStop = "limit" THEN acctLimits ELSE acctStops IN
        \* precondition:  redundant. The condition above asserts that a >= b + c + d, which implies
        \* that a >= b + c and a >= b + d, for nonnegative b,c,d
        \* consider removing either this or the previous precondition.
        /\ SumSeqPos(seqOfPos) + pos.amount <= balance
        /\  IF limitOrStop = "limit"
            THEN
                \* igte is the index of pos in the extended sequence such that:
                \* 1. pos has a greater or equal to exchange rate than all elements to the left of it (if any)
                \* 2. pos has a lesser exchange rate than all elements to the right of it (if any) 
                /\ \E igte \in DOMAIN seqOfPos \union { Len(seqOfPos) + 1 }:
                    /\ \A i \in DOMAIN seqOfPos:
                        IF i < igte
                        THEN LTE(seqOfPos[i].exchrate, pos.exchrate)
                        ELSE LT(pos.exchrate, seqOfPos[i].exchrate)
                    /\  LET limitsUpd == [ limits EXCEPT ![acct, <<askCoin, bidCoin>>] =
                                \* InsertAt: Inserts element pos at the position igte moving the original element to igte+1
                                InsertAt(@, igte, pos)
                            ]
                            stopsUpd == stops
                        IN  LET booksUpd == Execute(limitUpd, stops)
                            IN  /\  limits' = booksUpd.limits
                                /\  stops'  = booksUpd.stops
                /\ UNCHANGED << stops >>
            \* ELSE type is stops
            ELSE
                \* ilte is the index of pos in the extended sequence such that:
                \* 1. pos has a less or equal to exchange rate than all elements to the left of it (if any)
                \* 2. pos has a greater exchange rate than all elements to the right of it (if any) 
                /\ \E ilte \in DOMAIN seqOfPos \union { Len(seqOfPos) + 1 }:
                    /\ \A i \in DOMAIN seqOfPos:
                        IF i < ilte
                        THEN GTE(seqOfPos[i].exchrate, pos.exchrate)
                        ELSE GT(pos.exchrate, seqOfPos[i].exchrate)
                    /\  LET stopsUpd == [ stops EXCEPT ![acct, <<askCoin, bidCoin>>] =
                                \* InsertAt: Inserts element pos at the position ilte moving the original element to ilte+1
                                InsertAt(@, ilte, pos)
                            ]
                            limitsUpd == limits
                        IN  LET booksUpd == Execute(limitsUpd, stopsUpd)
                            IN  /\  limits' = booksUpd.limits
                                /\  stops' = booksUpd.stops
                /\  UNCHANGED << limits >>
    /\ UNCHANGED << accounts, reserve >>

Close(acct, askCoin, bidCoin, limitOrStop, i) ==
    LET seqOfPos == IF limitOrStop = "limit" 
                    THEN limits[acct,<<askCoin, bidCoin>>] 
                    ELSE stops[acct,<<askCoin, bidCoin>>] 
    IN 
    /\  LET pos == seqOfPos[i] IN 
        IF limitOrStop = "limit"
        THEN
            \* Remove removes all copies, what if there are multiple equivalent positions?
            /\ limits' = [limits EXCEPT ![acct, <<askCoin, bidCoin>>] = Remove(@, pos)]
            /\ UNCHANGED << stops >>
        ELSE
            /\ stops' = [stops EXCEPT ![acct, <<askCoin, bidCoin>>] = Remove(@, pos)]
            /\ UNCHANGED << limits >>
    /\ UNCHANGED << accounts, reserve >>

Provision(acct, pair, amt) ==
LET \* This is a hack below need to find out how to do this without making a set of 1 element
    strong == CHOOSE strong \in pair : 
        pools[<<strong, pair \ {strong}>>] >= pools[<<pair \ {strong}, strong>>]
    weak == CHOOSE weak \in pair \ {strong} : TRUE
    poolExchrate == << pools[<<weak, strong>>], pools[<<strong, weak>>] >>
    balStrong == accounts[<<acct, strong>>].balance
    balWeak == accounts[<<acct, weak>>].balance
    bidStrong == amt
    bidWeak == 
    IF  pools[<<pair, strong>>] > 0
    THEN
        (bidStrong * pools[<<pair, weak>>]) \div pools[<<pair, strong>>]
    ELSE
        IF amt <= balWeak
            THEN    balWeak
            ELSE    amt      
IN  \* Enabling Condition: balance of strong coin greater than amt 
    /\  balStrong >= amt
    /\  pools' = [ pools EXCEPT
            ![<<pair>>] = @ + bidStrong,
            ![<<pair[2], pair[1]>>] = @ + bidWeak
        ]
    /\  drops' = [ drops EXCEPT 
            ![<<acct, pair>>] = @ + bidStrong 
        ]
    /\  accounts' = [ accounts EXCEPT
            ![<<acct, weak>>].balance = @ - bidWeak,
            ![<<acct, strong>>].balance = @ - bidStrong
        ]
    /\ UNCHANGED << limits, stops >>

Liquidate(acct, pair, amt) ==
\* Qualifying condition
/\  LET 
        strong == CHOOSE strong \in pair : 
            pools[<<strong, pair \ {strong}>>] >= pools[<<pair \ {strong}, strong>>]
        weak == CHOOSE weak \in pair \ {strong} : TRUE
        amtStrong == amt
        amtWeak == 
        IF pools[<<pair, strong>>] > 0
        THEN (amt * pools[<<pair, weak>>]) \div pools[<<pair, strong>>]
        ELSE amt
    IN
        \* Enabling Condition: 
        /\  amtStrong <= drops[<<acct, pair>>]
        /\  accounts' = [ accounts EXCEPT
                ![<<acct, weak>>].balance = @ + amtWeak,
                ![<<acct, strong>>].balance = @ + amtStrong
            ]
        /\  pools' = [ pools EXCEPT 
                ![<<pair, strong>>] = @ - @ * (amt \div pools[<<weak, strong>>]),
                ![<<pair, weak>>] = @ - amt
            ]
        
        /\ drops' = [ drops EXCEPT 
            ![<<acct, pair>>] = @ - amt ]
        /\ UNCHANGED << limits, stops >>

NEXT == 
    \E acct \in ExchAccount :
        \/  \E coinType \in CoinType :
            \E amount \in PositiveAmounts :
                \/  Deposit(acct, amount, coinType)
                \/  Withdraw(acct, amount, coinType)
        \/  \E  limitOrStop \in {"limit", "stop"} :
            \E  askCoin \in CoinType :
            \E  bidCoin \in CoinType \ {askCoin} :
            \/  \E  exchrate \in Amounts \X PositiveAmounts: \* what is exchrate 0 / x ?
                \E  bidAmount \in PositiveAmounts :
                    /\  Open(acct, askCoin, bidCoin, limitOrStop, [
                            \* Exchange Rate is defined as
                            \* exchrate[1] / exchrate[2]
                            exchrate |-> exchrate,
                            amount |-> bidAmount
                        ])
                \*  Close
            \/  LET seq == IF limitOrStop = "limit"
                           THEN limits[acct, <<askCoin, bidCoin>>]
                           ELSE stops[acct, <<askCoin, bidCoin>>]
                IN 
                \E i \in DOMAIN seq:
                    Close(acct, askCoin, bidCoin, limitOrStop, i)
    
Spec == INIT /\ [][NEXT]_vars

\* For each coin, the amount in the system is constant
CoinAmountInv == 
    \A coinType \in CoinType:
        LET Plus(acct, p) == p + accounts[acct, coinType]
        IN FoldSet( Plus, reserve[coinType], ExchAccount ) = MaxAmount

\* If exchrate is a fraction <<a,b>>, then b != 0
NoDivBy0Inv == 
    \A acct \in ExchAccount:
    \A pair \in PairType:
        LET SeqHasNoDivByZero(seq) == 
           \A i \in DOMAIN seq: seq[i].exchrate[2] # 0
        IN 
        /\ SeqHasNoDivByZero( limits[acct, pair] )
        /\ SeqHasNoDivByZero( stops[acct, pair] ) 

\* each seq in limits is nondecreasing w.r.t. exchrate, i.e. 
\* each exchange rate is greater or equal than the previous one in the sequence, and
\* each seq in stops is nonincreasing w.r.t. exchrate
PosOrderInv ==
    \A acct \in ExchAccount:
    \A pair \in PairType:
        LET lim == limits[acct, pair]
            sto == stops[acct, pair] 
        IN
        /\ \A i \in (DOMAIN lim) \ {1}:
            LTE(lim[i-1].exchrate,lim[i].exchrate)
        /\ \A i \in (DOMAIN sto) \ {1}:
            GTE(sto[i-1].exchrate,sto[i].exchrate)

\* limits/stops[acct, pair] has its length bounded by MaxAmounts
PosSeqLengthBoundInv ==
    \A acct \in ExchAccount:
    \A pair \in PairType:
        LET BoundedLen(seq) == Len(seq) <= MaxAmount
        IN 
        /\ BoundedLen( limits[acct, pair] )
        /\ BoundedLen( stops[acct, pair] )
        
\* One of the critical system invariants: For every account `acct` and pair of coins `pair`,
\* the account balance for the bidCoin covers all open positions for `F[acct, pair]`  
PositionsAreProvisionedInv == 
    \A acct \in ExchAccount:
    \A pair \in PairType:
        PositionInv( limits[acct, pair], stops[acct, pair], accounts[acct, pair[2]] )

Inv ==
    /\ TypeInvariant
    /\ CoinAmountInv
    /\ NoDivBy0Inv
    /\ PosOrderInv
    /\ PosSeqLengthBoundInv
    /\ PositionsAreProvisionedInv

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
