------------------------------ MODULE Execute ------------------------------
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

INSTANCE Stop
INSTANCE Limit
INSTANCE NoLoss

-----------------------------------------------------------------------------
Execute(askCoin, bidCoin, limitsUpd, stopsUpd) ==
LET 
    stopBook == stopsUpd[bidCoin, askCoin]
    stopHead == Head(stopBook)
    stopHeadInvExchrate == << 
        stopHead.exchrate[2], 
        stopHead.exchrate[1] 
    >>
    
    limitBook == limitsUpd[askCoin, bidCoin]
    limitHead == Head(limitBook)
    stopHeadExchrate == stopHead.exchrate
    
    poolExchrate == << pools[bidCoin, askCoin], pools[askCoin, bidCoin] >>
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
        []      LT(stopHeadInvExchrate, stopHeadExchrate) ->
            Stop(askCoin, bidCoin, limitsUpd, stopsUpd)
    (***************************************************************************)
    (* CASE 2: The Pool Exchange Rate (Ask Coin Bal / Bid Coin Bal) greater    *)
    (*         than Bid Limit Book Exchange Rate                               *)
    (*                                                                         *)
    (* Action: Execute Bid Limit Order                                         *)
    (***************************************************************************)      
    []      GT(stopHeadExchrate, poolExchrate) ->  
        Limit(askCoin, bidCoin, limitsUpd, stopsUpd)      

=============================================================================
\* Modification History
\* Last modified Tue Aug 24 12:29:08 CDT 2021 by Charles Dusek
\* Created Fri Aug 20 16:24:24 CDT 2021 by Charles Dusek
