------------------------------ MODULE NoLoss ------------------------------
EXTENDS     FiniteSets, FiniteSetsExt, Integers, Sequences, SequencesExt,
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

NoLoss(askCoin, bidCoin, limitsUpd, stopsUpd) ==
\* Getting to this point means that both an Ask Stop and a Bid
\* Limit are equal and enabled.
LET limitBook == limits[askCoin, bidCoin]
    stopBook  == stops[bidCoin, askCoin]
    \* Strike Exchrate either limit or stop as equal
    strikeExchrate ==
        CASE Len(limitBook) = 1 /\ Len(stopBook) = 1 ->
                Head(limitBook).exchrate
        []   Len(limitBook) > 1 /\ Len(stopBook) = 1 ->
                Head(limitBook).exchrate
        []   Len(limitBook) > 1 /\ Len(stopBook) > 1 ->
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
    stopHeadBidAmt == 
        (stopBook[1].amount * strikeExchrate[1]) \div
        strikeExchrate[2]
    strikeBidAmt ==
        IF limitBook[1].amount <= stopHeadBidAmt
        THEN    limitBook[1].amount
        ELSE    stopHeadBidAmount
IN
    \* IF TRUE then amount traded is equal to limitHead amount
    \* stopHead is equal to or greater than limitHead
    \* amount in this case.
    IF 
    THEN 
        LET strikeBidAmt == limitBook[1].amount
            strikeAskAmt == 
                (strikeBidAmt * strikeExchrate[1]) \div
                strikeExchrate[2]
        IN
            /\  accounts' = 
                [ accounts EXCEPT 
                    ![limitBook[1].account, bidCoin] = @ - strikeBidAmt,
                    ![limitBook[1].account, askCoin] = @ + strikeAskAmt,
                    ![stopBook[1].account, bidCoin] = @ + strikeBidAmt,
                    ![stopBook[1].account, askCoin] = @ - strikeAskAmt
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
                    ![limitBook[1].account, bidCoin] = @ - strikeBidAmt,
                    ![limitBook[1].account, askCoin] = @ + strikeAskAmt,
                    ![stopBook[1].account, bidCoin] = @ + strikeBidAmt,
                    ![stopBook[1].account, askCoin] = @ - strikeAskAmt
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

=============================================================================