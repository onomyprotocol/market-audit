------------------------------- MODULE Limit --------------------------------
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

Limit(askCoin, bidCoin, limitsUpd, stopsUpd) ==
LET limitBook == limitsUpd[askCoin, bidCoin]
    limitHead == Head(limitBook)
    memberABal == pools[bidCoin, askCoin]
    memberBBal == pools[askCoin, bidCoin]
    poolExchrate == << memberABal,  memberBBal >>
IN
\* Enabling Condition
\* AMM Pool Exchange Rate must be Greater than Limit Book Head
/\  GT(poolExchrate, limitHead.exchrate)

/\  LET
        maxMemberBBal == BidCoinBalFinal(
            memberABal, 
            memberBBal,
            limitHead.exchrate
        )
        
        \* Maximum amount of the Bid Coin that the AMM may accept at Limit Order Exchange Rate
        maxBidAmt == maxMemberBBal - memberBBal
    IN
      LET strikeBidAmt == IF limitHead.amount <= maxBidAmt
                          THEN limitHead.amount
                          ELSE maxBidAmt

          strikeAskAmt == ((
                            strikeBidAmt *
                            limitHead.exchrate[1] * 10
                          ) \div limitHead.exchrate[2]) \div 10
            IN
                /\  IF limitHead.amount <= maxBidAmt
                    THEN limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = Tail(@)]
                    ELSE limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = 
                                <<[
                                    account |-> limitHead.account,
                                    exchrate |-> limitHead.exchrate,
                                    amount |-> limitHead.amount - strikeBidAmt
                                ]>> \o Tail(@)
                         ]
                /\  accounts' = 
                    [ accounts EXCEPT 
                        ![limitBook[1].account, bidCoin] = @ - strikeBidAmt,
                        ![limitBook[1].account, askCoin] = @ + strikeAskAmt
                    ] 
                /\  pools' = 
                    [ pools EXCEPT
                        ![askCoin, bidCoin] = @ + strikeBidAmt,
                        ![bidCoin, askCoin] = @ - strikeAskAmt 
                    ]
                /\  UNCHANGED <<drops, reserve, stops>>
=============================================================================
