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

PairTypePre == {<<a, b>> : a \in CoinType, b \in CoinType}
PairType == { ptp \in PairTypePre : ptp[1] # ptp[2] }

ExchRateType == {<<a, b>> : a \in Amounts, b \in PositiveAmounts}

PositionType == 
[
    account: ExchAccount,
    \* Exchange Rate is defined as
    \* exchrate[1] / exchrate[2]
    exchrate: ExchRateType,
    amount: PositiveAmounts
]

TypeInvariant ==  
\* accounts[ <<acct, coin>> ] is the balance of `coin` in account `acct`
/\  accounts \in [ExchAccount \X CoinType -> Amounts]
\* limits[ <<askCoin, bidCoin>> ] is a sequence of positions for that ask/bid pair
/\  limits \in [PairType -> Seq(PositionType)]
\* limits[ <<askCoin, bidCoin>> ] is a sequence of positions for that ask/bid pair
/\  stops \in [PairType -> Seq(PositionType)]
\* reserve[ coin ] is the amount of coins of type `coin` currently held in reserve
/\  reserve \in [CoinType -> Amounts]

INIT ==     
\* initially, all balances are 0 as all the coins are held by the reserve
/\  accounts = [eaAndCt \in ExchAccount \X CoinType |-> 0]
\* initially, there are no open positions    
/\  limits = [pair \in PairType |-> <<>>]
/\  stops = [pair \in PairType |-> <<>>] 
\* initially, all the coins are in the reserve
/\  reserve = [type \in CoinType |-> MaxAmount]

(***************************************************************************)
(* Deposit(acct, amount, type)                                             *)
(*                                                                         *)
(* The Deposit function takes a number of coins from the reserve and places*)
(* it into an exchange account.                                            *)
(***************************************************************************)
Deposit(acct, amount, coinType) ==
    /\  amount <= reserve[coinType]
    /\  accounts' = [accounts EXCEPT ![acct, coinType] = @ + amount]
    /\  reserve' = [reserve EXCEPT ![coinType] = @ - amount]
    /\  UNCHANGED << limits, stops >>

SelectAcctSeq(acct, book) == SelectSeq(book, LAMBDA pos: pos.account = acct)

\* Does not automatically update positions. It requires problematic positions
\* to already be closed (externally), before balances are changed
Withdraw(acct, amount, coinType) ==
    LET newBalance == accounts[acct,coinType] - amount
    IN
    /\  amount <= accounts[acct, coinType]
    \* Precondition: the post-withdrawal balance still covers open positions
    \* It is up to the user to select and close positions before withdrawal
    /\  \A askCoin \in CoinType \ {coinType}:
        PositionInv( 
            SelectAcctSeq(acct, limits[<<askCoin, coinType>>]),
            SelectAcctSeq(acct, stops[<<askCoin, coinType>>]),
            newBalance
            )
    /\  accounts' = [accounts EXCEPT ![acct, coinType] = @ - amount]
    /\  reserve' = [reserve EXCEPT ![coinType] = @ + amount]
    /\  UNCHANGED << limits, stops >>
    
Open(acct, askCoin, bidCoin, limitOrStop, pos) ==
    LET limitBook == limits[<<askCoin, bidCoin>>]
        stopBook == stops[<<askCoin, bidCoin>>]
        balance == accounts[acct, bidCoin] IN 
    \* precondition: Exchange Account Balance of Bid Coin must be at least the
    \* total amounts in all positions for any particular pair with the Bid 
    \* Coin. 
    /\ balance >=   pos.amount + 
                    SumSeqPos(SelectAcctSeq(acct, limitBook)) + 
                    SumSeqPos(SelectAcctSeq(acct, stopBook))
    /\  LET seqOfPos == IF limitOrStop = "limit" THEN limitBook ELSE stopBook IN
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
                  /\ limits' = [ limits EXCEPT ![<<askCoin, bidCoin>>] =
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
                  /\ stops' = [ stops EXCEPT ![<<askCoin, bidCoin>>] =
                        \* InsertAt: Inserts element pos at the position ilte moving the original element to ilte+1
                        InsertAt(@, ilte, pos)
                    ] 
                /\  UNCHANGED limits
    /\ UNCHANGED << accounts, reserve >>

Close(acct, askCoin, bidCoin, limitOrStop, i) ==
    LET seqOfPos == IF limitOrStop = "limit" 
                    THEN limits[<<askCoin, bidCoin>>] 
                    ELSE stops[<<askCoin, bidCoin>>] 
        pos == seqOfPos[i] 
    IN 
    /\  pos.account = acct \* you can only close your own acct's positions
    /\  IF limitOrStop = "limit"
        THEN
            \* Remove removes all copies, what if there are multiple equivalent positions?
            /\ limits' = [limits EXCEPT ![<<askCoin, bidCoin>>] = Remove(@, pos)]
            /\ UNCHANGED stops
        ELSE
            /\ stops' = [stops EXCEPT ![<<askCoin, bidCoin>>] = Remove(@, pos)]
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
            \/  \E  exchrate \in ExchRateType:
                \E  bidAmount \in PositiveAmounts :
                    Open(acct, askCoin, bidCoin, limitOrStop, [
                        account |-> acct,
                        \* Exchange Rate is defined as
                        \* exchrate[1] / exchrate[2]
                        exchrate |-> exchrate,
                        amount |-> bidAmount
                      ])
                \*  Close
            \/  LET seq == IF limitOrStop = "limit"
                           THEN limits[<<askCoin, bidCoin>>]
                           ELSE stops[<<askCoin, bidCoin>>]
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
    \A pair \in PairType:
        LET SeqHasNoDivByZero(seq) == 
           \A i \in DOMAIN seq: seq[i].exchrate[2] # 0
        IN 
        /\ SeqHasNoDivByZero( limits[pair] )
        /\ SeqHasNoDivByZero( stops[pair] ) 

\* each seq in limits is nondecreasing w.r.t. exchrate, i.e. 
\* each exchange rate is greater or equal than the previous one in the sequence, and
\* each seq in stops is nonincreasing w.r.t. exchrate
PosOrderInv ==
    \A pair \in PairType:
        LET lim == limits[pair]
            sto == stops[pair] 
        IN
        /\ \A i \in (DOMAIN lim) \ {1}:
            LTE(lim[i-1].exchrate,lim[i].exchrate)
        /\ \A i \in (DOMAIN sto) \ {1}:
            GTE(sto[i-1].exchrate,sto[i].exchrate)

\* limits/stops[acct, pair] has its length bounded by MaxAmounts
PosSeqLengthBoundInv ==
    \A pair \in PairType:
        LET BoundedLen(seq) == Len(seq) <= MaxAmount
        IN 
        /\ BoundedLen( limits[pair] )
        /\ BoundedLen( stops[pair] )
        
\* One of the critical system invariants: For every account `acct` and pair of coins `pair`,
\* the account balance for the bidCoin covers all open positions for `pair` associated with `acct`  
PositionsAreProvisionedInv == 
    \A acct \in ExchAccount:
    \A pair \in PairType:
        PositionInv( 
            SelectAcctSeq(acct, limits[pair]), 
            SelectAcctSeq(acct, stops[pair]), 
            accounts[acct, pair[2]] 
        )

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
