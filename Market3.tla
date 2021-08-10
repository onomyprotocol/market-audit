------------------------------- MODULE Market3 -------------------------------
EXTENDS     FiniteSets, FiniteSetsExt, Naturals, Sequences, SequencesExt

CONSTANT    ExchAccount,    \* Set of all accounts
            MaxAmount       \* Max amount of coins in circulation

VARIABLE    accounts,
            \* Limit Books
            limits,
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

\* Given a sequence of positions `seq \in Seq(PositionType)`, sum up
\* all of the position amounts. Returns 0 if seq is empty.
SumSeqPos(seq) == FoldLeft( LAMBDA p,q: p + q.amount, 0, seq )


\* Three Coin Types. Two Denoms and NOM
CoinType == {"Denom_A", "Denom_B", "NOM"}


Amounts == 0..MaxAmount
PositiveAmounts == 1..MaxAmount

PairTypePre == {{a, b} : a \in CoinType, b \in CoinType}
PairType == { ptp \in PairTypePre : Cardinality(ptp) > 1 }

\* The set {<<{x,y},z>>: x,y \in S /\ x != y /\ ( z = x \/ z = y )} is 
\* isomorphic to { <<s,t>>: s,t \in S /\ s != t }, 
\* consider using <<a,b>> instead of <<{a,b},b>>
PairPlusCoin == { <<pair, coin>> \in PairType \X CoinType : coin \in pair }

ExchRateType == {<<a, b>> : a \in Amounts, b \in Amounts}

PositionType == 
[
    \* Exchange Rate is defined as
    \* Cardinality(exchrate[0]) / Cardinality(exchrate[1])
    exchrate: ExchRateType,
    \* cardinality of amount is the amount
    amount: PositiveAmounts
]

TypeInvariant ==  
\* accounts[ <<acct, coin>> ] is the balance of `coin` in account `acct`
/\  accounts \in [ExchAccount \X CoinType -> Amounts]
\* limits[ <<acct, <<pair, coin>> >> ] is a sequence of positions tied to `acct` and the pair+coin `<<pair, coin>>`
/\  limits \in [ ExchAccount \X PairPlusCoin -> Seq(PositionType)]
\* stops[ <<acct, <<pair, coin>> >> ] is a sequence of positions tied to `acct` and the pair+coin `<<pair, coin>>`
/\  stops \in [ ExchAccount \X PairPlusCoin -> Seq(PositionType)]
\* reserve[ coin ] is the amount of coins of type `coin` currently held in reserve
/\  reserve \in [CoinType -> Amounts]

INIT ==     
\* initially, all ballances are 0 as all the coins are held by the reserve
/\  accounts = [eaAndCt \in ExchAccount \X CoinType |-> 0]
\* initially, there are no open positions    
/\  limits = [accTAndPpc \in ExchAccount \X PairPlusCoin |-> <<>>]
/\  stops = [accTAndPpc \in ExchAccount \X PairPlusCoin |-> <<>>] 
\* initially, all the coins are in the reserve
/\  reserve = [type \in CoinType |-> MaxAmount]

(***************************************************************************)
(* Deposit(acct, amount, type)                                             *)
(*                                                                         *)
(* The Deposit function takes a SUBSET of coins from a single type and     *)
(* the reserve and places it into an exchange account.                     *)
(***************************************************************************)
Deposit(acct, amount, coinType) ==
    /\  amount <= reserve[coinType]
    /\  accounts' = [accounts EXCEPT ![acct, coinType] = @ + amount]
    /\  reserve' = [reserve EXCEPT ![coinType] = @ - amount]
    /\  UNCHANGED << limits, stops >>

Withdraw(acct, amount, coinType) ==
    /\  amount <= accounts[acct, coinType]
    /\  accounts' = [accounts EXCEPT ![acct, coinType] = @ - amount]
    /\  reserve' = [reserve EXCEPT ![coinType] = @ + amount]
    /\  UNCHANGED << limits, stops >>
    
Open(acct, askCoin, bidCoin, limitOrStop, pos) ==
    LET acctLimits == limits[acct,<<{askCoin,bidCoin}, bidCoin>>]
        acctStops == stops[acct,<<{askCoin,bidCoin}, bidCoin>>]
        amount == accounts[acct, bidCoin] IN 
    \* precondition: Exchange Account Balance of Bid Coin must be at least the
    \* total amounts in all positions for any particular pair with the Bid 
    \* Coin. 
    /\ amount >= pos.amount + SumSeqPos(acctLimits) + SumSeqPos(acctStops)
    /\  LET seqOfPos == IF limitOrStop = "limit" THEN acctLimits ELSE acctStops IN
        \* precondition:  redundant. Line 109 asserts that a >= b + c + d, which implies
        \* that a >= b + c and a >= b + d, for nonnegative b,c,d
        \* consider removing either this or the previous precondition.
        /\ SumSeqPos(seqOfPos) + pos.amount <= amount
        /\  IF limitOrStop = "limit"
            THEN
                LET igt == IGT(seqOfPos, pos) IN
                /\ limits' = [ limits EXCEPT ![acct, <<{askCoin, bidCoin}, bidCoin>>] =
                        IF igt = {} THEN Append(@, pos) ELSE InsertAt(@, Min(igt), pos)
                    ] 
                /\ UNCHANGED stops
            \* ELSE type is stops
            ELSE
                LET ilt == ILT(seqOfPos, pos) IN
                /\ stops' = [ stops EXCEPT ![acct, <<{askCoin, bidCoin}, bidCoin>>] =
                        IF ilt = {} THEN Append(@, pos) ELSE InsertAt(@, Max(ilt), pos)
                    ] 
                /\  UNCHANGED limits
    /\ UNCHANGED << accounts, reserve >>

Close(acct, askCoin, bidCoin, limitOrStop, i) ==
    LET seqOfPos == IF limitOrStop = "limit" 
                    THEN limits[acct,<<{askCoin,bidCoin}, bidCoin>>] 
                    ELSE stops[acct,<<{askCoin,bidCoin}, bidCoin>>] 
        amount == accounts[acct, bidCoin] 
    IN 
    /\  LET pos == seqOfPos[i] IN 
        IF limitOrStop = "limit"
        THEN
            \* Remove removes all copies, what if there are multiple equivalent positions?
            /\ limits' = [limits EXCEPT ![acct, <<{askCoin, bidCoin}, bidCoin>>] = Remove(@, pos)]
            /\ UNCHANGED stops
        ELSE
            /\ stops' = [stops EXCEPT ![acct, <<{askCoin, bidCoin}, bidCoin>>] = Remove(@, pos)]
            /\ UNCHANGED limits
    /\ UNCHANGED << accounts, reserve >>

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
                    Open(acct, askCoin, bidCoin, limitOrStop, [
                        \* Exchange Rate is defined as
                        \* exchrate[1] / exchrate[2]
                        exchrate |-> exchrate,
                        amount |-> bidAmount
                      ])
                \*  Close
            \/  LET seq == IF limitOrStop = "limit"
                           THEN limits[acct, <<{askCoin,bidCoin}, bidCoin>>]
                           ELSE stops[acct, <<{askCoin,bidCoin}, bidCoin>>]
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
    \A ppc \in PairPlusCoin:
        LET SeqHasNoDivByZero(seq) == 
           \A i \in DOMAIN seq: seq[i].exchrate[2] # 0
        IN 
        /\ SeqHasNoDivByZero( limits[acct, ppc] )
        /\ SeqHasNoDivByZero( stops[acct, ppc] ) 

\* each seq in limits is nondecreasing w.r.t. exchrate, i.e. 
\* each exchange rate is greater or equal than the previous one in the sequence, and
\* each seq in stops is nonincreasing w.r.t. exchrate
PosOrderInv ==
    \A acct \in ExchAccount:
    \A ppc \in PairPlusCoin:
        LET lim == limits[acct, ppc]
            sto == stops[acct, ppc] 
        IN
        /\ \A i \in (DOMAIN lim) \ {1}:
            LTE(lim[i-1].exchrate,lim[i].exchrate)
        /\ \A i \in (DOMAIN sto) \ {1}:
            GTE(sto[i-1].exchrate,sto[i].exchrate)

\* limits/stops[acct, ppc] has its length bounded by MaxAmounts
PosSeqLengthBoundInv ==
    \A acct \in ExchAccount:
    \A ppc \in PairPlusCoin:
        LET BoundedLen(seq) == Len(seq) <= MaxAmount
        IN 
        /\ BoundedLen( limits[acct, ppc] )
        /\ BoundedLen( stops[acct, ppc] )

Inv ==
    /\ TypeInvariant
    /\ CoinAmountInv
    /\ NoDivBy0Inv
    /\ PosOrderInv
    /\ PosSeqLengthBoundInv



-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
