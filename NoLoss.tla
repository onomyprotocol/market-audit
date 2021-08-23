------------------------------ MODULE NoLoss ------------------------------
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

NoLoss(acct, askCoin, askAmount, bidCoin, bidAmount)
\* Getting to this point means that both an Ask Stop and a Bid
\* Limit are equal and enabled.
LET limitBook == limits[askCoin, bidCoin]
    stopBook  == stops[bidCoin, askCoin]
    \* Strike Exchrate either limit or stop as equal
    strikeExchrate ==
        IF Len(limitBook) > 1
        THEN 
            IF Len(stopBook) > 1
            THEN 
                \* Strike price is based on the most adjacent
                \* order based on price.
                IF LTE(
                        limitBook[2].exchrate,
                        <<
                            stopBook[2].exchrate[2],
                            stopBook[2].exchrate[1]
                        >>
                    )
                THEN limitBook[2].exchrate
                ELSE <<
                        stopBook[2].exchrate[2],
                        stopBook[2].exchrate[1]
                    >>
            ELSE limitBook[2].exchrate
        ELSE
            IF Len(stopBook) > 1
            THEN stopBook[2].exchrate
            ELSE limitBook[1].exchrate
    stopHeadBidAmt == 
        (stopBook[1].amount * strikeExchrate[1]) /div
        strikeExchrate[2]
IN
    \* IF TRUE then amount traded is equal to limitHead amount
    \* stopHead is equal to or greater than limitHead
    \* amount in this case.
    IF limitBook[1].amount <= stopHeadBidAmt
    THEN 
        LET strikeBidAmt == limitBook[1].amount
            strikeAskAmt == 
                (strikeBidAmt * strikeExchrate[1]) \div
                strikeExchrate[2]
        IN
            /\  accounts' = 
                [ accounts EXCEPT 
                    ![limitBook[1].account, bidCoin] = @ - strikeBidAmount,
                    ![limitBook[1].account, askCoin] = @ + strikeAskAmount,
                    ![stopBook[1].account, bidCoin] = @ + strikeBidAmount,
                    ![stopBook[1].account, askCoin] = @ - strikeAskAmount,
                ]

            /\  limits' =
                [ limits EXCEPT
                    ![askCoin, bidCoin] = Tail(@)
                ]
            /\  stops' =
                [ stops EXCEPT 
                    ![bidCoin, askCoin] = 
                        Append(
                            Tail(@), 
                            <<[
                                account: stopBook[1].account,
                                exchrate: stopBook[1].exchrate,
                                amount: stopBook[1].amount - strikeAskAmt
                            ]>>
                        )
                ]
    ELSE
        LET strikeBidAmt == stopBook[1].amount
            strikeAskAmt == 
                (strikeBidAmt * strikeExchrate[1]) \div
                strikeExchrate[2]
        IN
            /\  accounts' = 
                [ accounts EXCEPT 
                    ![limitBook[1].account, bidCoin] = @ - strikeBidAmount,
                    ![limitBook[1].account, askCoin] = @ + strikeAskAmount,
                    ![stopBook[1].account, bidCoin] = @ + strikeBidAmount,
                    ![stopBook[1].account, askCoin] = @ - strikeAskAmount,
                ]

            /\  limits' =
                [ limits EXCEPT
                    ![askCoin, bidCoin] = 
                        Append(
                                Tail(@), 
                                <<[
                                    account: limitBook[1].account,
                                    exchrate: limitBook[1].exchrate,
                                    amount: limitBook[1].amount - strikeBidAmt
                                ]>>
                            )
                ]
            /\  stops' =
                [ stops EXCEPT 
                    ![bidCoin, askCoin] = Tail(@)
                ]