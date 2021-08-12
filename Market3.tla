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

PairTypePre == {{a, b} : a \in CoinType, b \in CoinType}
PairType == { ptp \in PairTypePre : Cardinality(ptp) > 1 }

\* The set {<<{x,y},z>>: x,y \in S /\ x != y /\ ( z = x \/ z = y )} is 
\* isomorphic to { <<s,t>>: s,t \in S /\ s != t }, 
\* consider using <<a,b>> instead of <<{a,b},b>>
PairPlusCoin == { <<pair, coin>> \in PairType \X CoinType : coin \in pair }

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
        /\ limits' = [ acctAndPPC \in ExchAccount \X PairPlusCoin |->
            LET acctArg == acctAndPPC[1]
                ppc == acctAndPPC[2]
            IN  IF acctArg # acct \/ ppc[2] # coinType
                THEN limits[acctArg, ppc]
                ELSE 
                    LET newPosSeqPair == 
                        TruncatePositions( limits[acct, ppc], stops[acct, ppc], newBalance )
                    IN newPosSeqPair[1]
            ]
        /\ stops' = [ acctAndPPC \in ExchAccount \X PairPlusCoin |->
            LET acctArg == acctAndPPC[1]
                ppc == acctAndPPC[2]
            IN  IF acctArg # acct \/ ppc[2] # coinType
                THEN stops[acctArg, ppc]
                ELSE 
                    LET newPosSeqPair == 
                        TruncatePositions( limits[acct, ppc], stops[acct, ppc], newBalance )
                    IN newPosSeqPair[2]
            ]
    /\  reserve' = [reserve EXCEPT ![coinType] = @ + amount]
    
Open(acct, askCoin, bidCoin, limitOrStop, pos) ==
    LET acctLimits == limits[acct,<<{askCoin,bidCoin}, bidCoin>>]
        acctStops == stops[acct,<<{askCoin,bidCoin}, bidCoin>>]
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
                  /\ limits' = [ limits EXCEPT ![acct, <<{askCoin, bidCoin}, bidCoin>>] =
                        \* InsertAt: Inserts element pos at the position igte moving the original element to igte+1
                        InsertAt(@, igte, pos)
                     ] 
                /\ UNCHANGED stops
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
                  /\ stops' = [ stops EXCEPT ![acct, <<{askCoin, bidCoin}, bidCoin>>] =
                        \* InsertAt: Inserts element pos at the position ilte moving the original element to ilte+1
                        InsertAt(@, ilte, pos)
                    ] 
                /\  UNCHANGED limits
    /\ UNCHANGED << accounts, reserve >>

Close(acct, askCoin, bidCoin, limitOrStop, i) ==
    LET seqOfPos == IF limitOrStop = "limit" 
                    THEN limits[acct,<<{askCoin,bidCoin}, bidCoin>>] 
                    ELSE stops[acct,<<{askCoin,bidCoin}, bidCoin>>] 
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
        
\* One of the critical system invariants: For every account `acct` and pair of coins `ppc`,
\* the account balance for the bidCoin covers all open positions for `F[acct, ppc]`  
PositionsAreProvisionedInv == 
    \A acct \in ExchAccount:
    \A ppc \in PairPlusCoin:
        PositionInv( limits[acct, ppc], stops[acct, ppc], accounts[acct, ppc[2]] )

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
