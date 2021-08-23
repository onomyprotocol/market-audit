------------------------------ MODULE Execute ------------------------------
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

vars == <<accounts, drops, limits, pools, reserve, stops>>

-----------------------------------------------------------------------------
\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
GT(a, b) == a[1]*b[2] > a[2]*b[1]

GTE(a, b) == a[1]*b[2] >= a[2]*b[1] 

LT(a, b) == a[1]*b[2] < a[2]*b[1]

LTE(a, b) == a[1]*b[2] <= a[2]*b[1]

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
(*                                                                         *)
(* MaxPoolBid ==    [(BidBalanceInitial * exchrateFinal^2) \               *)
(*                  (2 * exchrateFinal + exchrateInitial)] -               *)
(*                  AskBalanceInitial                                      *)
(***************************************************************************)
MaxPoolBid(erateFinal, erateInitial) ==
\* AskBalInit / BidBalInit = erateInit[1] / erateInit[2]
LET a == erateInitial[1]
    b == erateInitial[2]
    c == erateInitial[1]
    d == erateFinal[2]
IN
    (
        (
            b * c^2
        ) \div (
            2 * c + a
        )   
    ) - a

Execute(askCoin, bidCoin, limitsUpd, stopsUpd) ==
LET 
    
    stopBook == stopsUpd[bidCoin, askCoin]
    stopHead == Head(stopBook)
    stopHeadInvExchrate == << 
        askStopHead.exchrate[2], 
        askStopHead.exchrate[1] 
    >>
    
    bidLimits == limitsUpd[askCoin, bidCoin]
    bidLimitHead == Head(bidLimits)
    bidLimitHeadExchrate == bidLimitHead.exchrate
    
    poolExchrate == pools[bidCoin, askCoin] /
                    pools[askCoin, bidCoin]

IN
    (***************************************************************************)
    (* CASE 1: The Pool Exchange Rate (Ask Coin Bal / Bid Coin Bal) greater    *)
    (*         than or equal Ask Stop Book Inverse Exchange Rate               *)
    (*                                                                         *)
    (*         IF TRUE THEN the Position at the head of the Ask coin Stop Book *)
    (*         is Enabled                                                      *)
    (***************************************************************************)
    CASE    GTE(poolExchrate, askStopHeadInvExchrate) ->
        (***********************************************************************)
        (* CASE 1.1: Inverse Exchange Rate of the head of the Ask Stop Book    *)
        (*           is equal to exchange rate of the head of the Bid Limit    *)
        (*           book                                                      *)
        (*                                                                     *)
        (*   Action: Execute no loss trade                                     *)
        (***********************************************************************)
        CASE    EQ(bidLimitExchrate, askStopInverseExchRate) ->
            \* The only parameters needed to execute a no-loss trade is
            \* the ask coin and the bid coin.
            NoLoss(askCoin, bidCoin)
                 
        (***********************************************************************)
        (* CASE 1.2: Inverse Exchange Rate of the head of the Ask Stop Book    *)
        (*           is less than the exchange rate of the head of the Bid     *)
        (*           Limit book                                                *)
        (*                                                                     *)
        (*   Action: Execute Ask Stop Order                                    *)
        (***********************************************************************)
        []      LT(askStopHeadInvExchrate, bidLimitHeadExchrate) ->
            AskStop(askCoin, bidCoin)
    (***************************************************************************)
    (* CASE 2: The Pool Exchange Rate (Ask Coin Bal / Bid Coin Bal) greater    *)
    (*         than Bid Limit Book Exchange Rate                               *)
    (*                                                                         *)
    (* Action: Execute Bid Limit Order                                         *)
    (***************************************************************************)      
    []      GT(bidLimitExchrate, poolExchRate) ->  
        BidLimit(askCoin, bidCoin)      

=============================================================================
\* Modification History
\* Last modified Fri Aug 20 16:26:16 CDT 2021 by Charles Dusek
\* Created Fri Aug 20 16:24:24 CDT 2021 by Charles Dusek
