-------------------------------- MODULE Stop  -------------------------------
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

-----------------------------------------------------------------------------

Stop(askCoin, bidCoin, limitsUpd, stopsUpd) ==
LET 
    stopBook == stopsUpd[bidCoin, askCoin]    
    stopHead == Head(stopBook)
    stopHeadInvExchrate == << stopHead.exchrate[2], stopHead.exchrate[1] >>
    limitBook == limitsUpd[askCoin, bidCoin]
    poolExchrate == << pools[bidCoin, askCoin], pools[askCoin, bidCoin] >>
    strikeExchrate ==
        CASE Len(limitBook) = 0 /\ Len(stopBook) = 1 ->
                Head(stopBook).exchrate
        []   Len(limitBook) = 0 /\ Len(stopBook) > 1 ->
                stopBook[2].exchrate
        []   Len(limitBook) > 0 /\ Len(stopBook) = 1 ->
                Head(limitBook).exchrate
        []   Len(limitBook) > 0 /\ Len(stopBook) > 1 ->
                IF LT(stopBook[2].exchrate, Head(limitBook).exchrate)
                THEN stopBook[2].exchrate
                ELSE Head(limitBook).exchrate
    IN
        LET
            maxPoolAmt == MaxPoolBid(
                poolExchrate[1], 
                poolExchrate[2], 
                strikeExchrate
            )
        IN  
            LET strikeBidAmt ==
                    IF stopHead.amount <= maxPoolAmt
                    THEN stopHead.amount
                    ELSE maxPoolAmt

                    strikeAskAmt == (
                        strikeBidAmt *
                        strikeExchrate[1]
                    ) \div strikeExchrate[2]
            IN
                /\  IF stopHead.amount <= maxPoolAmt
                    THEN stops' = [stopsUpd EXCEPT ![askCoin, bidCoin] = Tail(@)]
                    ELSE stops' = [stopsUpd EXCEPT ![askCoin, bidCoin] = 
                                <<[
                                    account |-> stopBook[1].account,
                                    exchrate |-> stopBook[1].exchrate,
                                    amount |-> stopBook[1].amount - strikeBidAmt
                                ]>> \o Tail(@)
                         ]
                /\  accounts' = 
                    [ accounts EXCEPT 
                        ![stopBook[1].account, bidCoin] = @ - strikeBidAmt,
                        ![stopBook[1].account, askCoin] = @ + strikeAskAmt
                    ] 
                /\  pools' = 
                    [ pools EXCEPT
                        ![askCoin, bidCoin] = @ + strikeBidAmt,
                        ![bidCoin, askCoin] = @ - strikeAskAmt 
                    ]
                /\  UNCHANGED <<drops, reserve, limits>>
=============================================================================