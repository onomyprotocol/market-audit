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
(* MaxPoolBid ==    [(BidBalanceInitial * exchrateFinal) \                 *)
(*                  (2 * exchrateFinal + exchrateInitial)] *               *)
(*                  exchrateFinal -                                        *)
(*                  AskBalanceInitial                                      *)
(***************************************************************************)

\* MPB(a/b, c/d) = b * (c/d) / (2 * c/d + a/b) * (c/d) - a

MaxPoolBid(erateFinal, erateInitial) ==
\* AskBalInit / BidBalInit = erateInit[1] / erateInit[2]
LET a == erateInitial[1]
    b == erateInitial[2]
    c == erateInitial[1]
    d == erateFinal[2]
IN
    (
        (
            (
                (
                    (b * c) \div d
                ) \div (
                    (2 * c) * b + a * d
                )
            ) \div (d * b)
        ) * c
    ) \div d - a

Execute(askCoin, bidCoin, limitsUpd, stopsUpd) ==
LET 
    
    askStops == stops[bidCoin, askCoin]
    askStopHead == Head(askStops)
    askStopHeadInvExchrate == << 
        askStopHead.exchrate[2], 
        askStopHead.exchrate[1] 
    >>
    
    bidLimits == limits[askCoin, bidCoin]
    bidLimitHead == Head(bidLimits)
    bidLimitHeadExchrate == bidLimitHead.exchrate
    
    poolExchrate == pools[bidCoin, askCoin] /
                    pools[askCoin, bidCoin]

IN
(***************************************************************************)
(* CASE 1: The Pool Exchange Rate (Ask Coin Bal / Bid Coin Bal) greater    *)
(*         than or equal Ask Stop Book Inverse Exchange Rate               *)
(*                                                                         *)
(*         If TRUE Then Ask Stop Head Position is Enabled                  *)
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
            \*  Bid Limits are the limiting amount
            CASE    askStopHead.amount >= Head(bidLimits).amount ->
                    LET strikeExchRate == bidLimitExchRate
                        askAmount ==   bidLimitHead.amount
                        bidAmount ==   (maxPoolAsk * strikeExchRate[1]) / strikExchRate[2]
                    IN
                        /\  accounts' = [accounts EXCEPT
                                ![bidLimitHead.acct, askCoin] = @ + askAmount
                                ![bidLimitHead.acct, bidCoin] = @ - bidAmount
                                ![askStopHead.acct, askCoin] = @ - askAmount
                                ![askStopHead.acct, bidCoin] = @ + bidAmount
                            ]
                
    (***********************************************************************)
    (* CASE 1.2: Inverse Exchange Rate of the head of the Ask Stop Book    *)
    (*           is less than the exchange rate of the head of the Bid     *)
    (*           Limit book                                                *)
    (*                                                                     *)
    (*   Action: Execute Ask Stop Order                                    *)
    (***********************************************************************)
    []      LT(askStopHeadInvExchrate, bidLimitHeadExchrate) ->
            (***************************************************************)
            (*  In this case, the next order to be enabled will be the head*) 
            (*  of the bid limits.                                         *)
            (*  Order execution will fill order until bid limit head       *)
            (*  exchange rate is reached.                                  *)
            (***************************************************************)
            CASE LTE(bidLimitHeadExchrate, askStops[2].exchrate) ->

=============================================================================
\* Modification History
\* Last modified Fri Aug 20 16:26:16 CDT 2021 by Charles Dusek
\* Created Fri Aug 20 16:24:24 CDT 2021 by Charles Dusek
