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

vars == <<accounts, drops, limits, pools, reserve, stops>>

-----------------------------------------------------------------------------

Stop(askCoin, bidCoin) ==

LET limitBook == limits[askCoin, bidCoin]
    stopBook == stopsUpd[bidCoin, askCoin]
    stopHeadInvExchrate == << 
        stopBook[1].exchrate[2], 
        stopBook[1].exchrate[1] 
    >>
    poolExchrate == pools[bidCoin, askCoin] /
                    pools[askCoin, bidCoin]
    strikeExchrate ==
        IF Len(stopBook) > 1
        THEN 
            IF Len(limitBook) > 0
            THEN 
                \* Strike price is based on the most adjacent
                \* order based on price.
                IF LTE(limitBook[1].exchrate, stopBook[2].exchrate)
                THEN limitBook[1].exchrate
                ELSE stopBook[2].exchrate
            ELSE stopBook[2]
        ELSE
            stopBook[1]
    maxPoolAmt == MaxPoolBid(poolExchrate, strikeExchrate)
IN
    IF maxPoolAmt >= stopBook[1].amount
    THEN \* Fulfill entire stop order
        LET strikeBidAmt == stopBook[1].amount
            strikeAskAmt == 
                (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) * strikeExchrate[2]
        IN
            /\  stops' = [stops EXCEPT ![askCoin, bidCoin] = Tail(@)]
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
        /\  stops' = [stops EXCEPT ![askCoin, bidCoin] = 
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
                ![acct, bidCoin] = @ - strikeBidAmt,
                ![acct, askCoin] = @ + strikeAskAmt
            ] 
        /\  pools' = 
            [ pools EXCEPT
                ![askCoin, bidCoin] = @ + strikeBidAmt,
                ![bidCoin, askCoin] = @ - strikeAskAmt 
            ]
