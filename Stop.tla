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

LET limitBook == limitsUpd[askCoin, bidCoin]
    limitHead == Head(limitBook)
    stopBook == stopsUpd[bidCoin, askCoin]
    stopHead == Head(stopBook)
    stopHeadInvExchrate == << 
        stopBook[1].exchrate[2], 
        stopBook[1].exchrate[1] 
    >>
    strikeExchrate ==
        IF Len(stopBook) > 1
        THEN 
            IF Len(limitBook) > 0
            THEN
                \* Strike price is based on the most adjacent
                \* order based on price.
                IF LTE(
                        stopBook[2].exchrate,
                        <<
                            limitHead.exchrate[2],
                            limitHead.exchrate[1]
                        >>
                    )
                THEN stopBook[2].exchrate
                ELSE <<
                        limitHead.exchrate[2],
                        limitHead.exchrate[1]
                    >>
            ELSE << limitBook[2].exchrate[2], limitBook[2].exchrate[1] >>
        ELSE 
            IF Len(limitBook) > 0
            THEN <<
                limitHead.exchrate[2],
                limitHead.exchrate[1]
            >>
            ELSE stopHead.exchrate
    maxPoolAmt == MaxPoolBid(pools[bidCoin, askCoin], pools[askCoin, bidCoin], strikeExchrate)
IN
    IF stopHead.amount <= maxPoolAmt
    THEN \* Fulfill entire stop order
        LET strikeBidAmt == stopHead.amount
            strikeAskAmt == 
                (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) \div strikeExchrate[2]
        IN
            /\  stops' = [stopsUpd EXCEPT ![askCoin, bidCoin] = Tail(@)]
            /\  accounts' = 
                [ accounts EXCEPT 
                    ![stopBook[1].acct, bidCoin] = @ - strikeBidAmt,
                    ![stopBook[1].acct, askCoin] = @ + strikeAskAmt
                ] 
            /\  pools' = 
                [ pools EXCEPT
                    ![askCoin, bidCoin] = @ + strikeBidAmt,
                    ![bidCoin, askCoin] = @ - strikeAskAmt 
                ]
    ELSE \* Partial fill limit order
        LET strikeBidAmt == maxPoolAmt
            strikeAskAmt == 
                (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) * strikeExchrate[2]
        IN
        /\  stops' = [stopsUpd EXCEPT ![askCoin, bidCoin] = 
                Append(
                    Tail(@), <<[
                        account: stopBook[1].accounts,
                        exchrate: stopBook[1].exchrate,
                        amount: stopBook[1].amount - strikeBidAmt
                    ]>>
                )
            ]
        /\  accounts' = 
            [ accounts EXCEPT 
                ![stopHead.account, bidCoin] = @ - strikeBidAmt,
                ![stopHead.account, askCoin] = @ + strikeAskAmt
            ] 
        /\  pools' = 
            [ pools EXCEPT
                ![askCoin, bidCoin] = @ + strikeBidAmt,
                ![bidCoin, askCoin] = @ - strikeAskAmt 
            ]

=============================================================================
