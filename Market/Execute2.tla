------------------------------ MODULE Execute2 -----------------------------
EXTENDS     FiniteSets, FiniteSetsExt, Naturals, Sequences, SequencesExt,
            MarketHelpers

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


INSTANCE Limit
INSTANCE Stop
INSTANCE NoLoss
-----------------------------------------------------------------------------
Execute(askCoin, bidCoin, limitsUpd, stopsUpd) ==
LET 
    stopBook == stopsUpd[bidCoin, askCoin]    
    limitBook == limitsUpd[askCoin, bidCoin]
    poolExchrate == << pools[bidCoin, askCoin], pools[askCoin, bidCoin] >>
IN
    CASE    Len(stopBook) = 0 /\ Len(limitBook) > 0 -> 
        IF GT(poolExchrate, Head(limitBook).exchrate)
        THEN Limit(askCoin, bidCoin, limitsUpd, stopsUpd)
        ELSE    /\ limits' = limitsUpd
                /\ UNCHANGED << accounts, drops, pools, reserve, stops >>
    []      Len(limitBook) = 0 /\ Len(stopBook) > 0 ->
        IF GT(poolExchrate,
            <<
                Head(stopBook).exchrate[2],
                Head(stopBook).exchrate[1]
            >>
           )
        THEN Stop(askCoin, bidCoin, limitsUpd, stopsUpd)
        ELSE    /\ stops' = stopsUpd
                /\ UNCHANGED << accounts, drops, limits, pools, reserve >>
    []      OTHER -> UNCHANGED << accounts, drops, limits, pools, reserve, stops >>
(*           
    LET
        limitHead == Head(limitBook)
        stopHead == Head(stopBook)
        stopHeadInvExchrate == << 
            stopHead.exchrate[2], 
            stopHead.exchrate[1] 
        >>
    IN
    (***************************************************************************)
    (* CASE 1: The Pool Exchange Rate (Ask Coin Bal / Bid Coin Bal) greater    *)
    (*         than or equal Ask Stop Book Inverse Exchange Rate               *)
    (*                                                                         *)
    (*         IF TRUE THEN the Position at the head of the Ask coin Stop Book *)
    (*         is Enabled                                                      *)
    (***************************************************************************)
    CASE    GTE(poolExchrate, stopHeadInvExchrate) ->
        (***********************************************************************)
        (* CASE 1.1: Inverse Exchange Rate of the head of the Ask Stop Book    *)
        (*           is equal to exchange rate of the head of the Bid Limit    *)
        (*           book                                                      *)
        (*                                                                     *)
        (*   Action: Execute no loss trade                                     *)
        (***********************************************************************)
        CASE    EQ(limitHead.exchrate, stopHeadInvExchrate) ->
            \* The only parameters needed to execute a no-loss trade is
            \* the ask coin and the bid coin.
            NoLoss(askCoin, bidCoin, limitsUpd, stopsUpd)
                 
        (***********************************************************************)
        (* CASE 1.2: Inverse Exchange Rate of the head of the Ask Stop Book    *)
        (*           is less than the exchange rate of the head of the Bid     *)
        (*           Limit book                                                *)
        (*                                                                     *)
        (*   Action: Execute Ask Stop Order                                    *)
        (***********************************************************************)
        []      LT(stopHeadInvExchrate, limitHead.exchrate) ->
            Stop(askCoin, bidCoin, limitsUpd, stopsUpd)
    (***************************************************************************)
    (* CASE 2: The Pool Exchange Rate (Ask Coin Bal / Bid Coin Bal) greater    *)
    (*         than Bid Limit Book Exchange Rate                               *)
    (*                                                                         *)
    (* Action: Execute Bid Limit Order                                         *)
    (***************************************************************************)      
    []      GT(poolExchrate, limitHead.exchrate) ->  
        Limit(askCoin, bidCoin, limitsUpd, stopsUpd)
    []  OTHER -> /\ CASE    limits' = limitsUpd /\ stops' = stopsUpd ->
                    UNCHANGED << accounts, drops, limits, pools, reserve, stops >>
                    []      limits' = limitsUpd ->
                        /\  stops' = stopsUpd
                        /\  UNCHANGED << accounts, drops, limits, pools, reserve >>
                    []      OTHER -> 
                        /\  limits' = limitsUpd
                        /\  UNCHANGED << accounts, drops, pools, reserve, stops >>
*)   
=============================================================================