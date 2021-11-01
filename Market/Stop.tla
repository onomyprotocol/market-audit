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
    memberABal == pools[bidCoin, askCoin]
    memberBBal == pools[askCoin, bidCoin]
    poolExchrate == << memberABal,  memberBBal >>
    IN
\* Enabling Condition
\* AMM Pool Exchange Rate must be Less than Stop Book Head
/\ LT(poolExchrate, stopHead.exchrate)

/\ LET
        minMemberABal == memberABal \div 2
        maxMemberBBal == memberABal + memberBBal - minMemberABal
        maxMemberBAmt == maxMemberBBal - memberBBal
   IN
        LET strikeBidAmt ==
                IF stopHead.amount > maxMemberBAmt
                THEN maxMemberBAmt
                ELSE stopHead.amount
                
            strikeAskAmt == (strikeBidAmt * (memberABal - strikeBidAmt)) \div (memberBBal + strikeBidAmt)  
        IN
            /\  IF stopHead.amount <= strikeAskAmt
                THEN stops' = [stopsUpd EXCEPT ![bidCoin, askCoin] = Tail(@)]
                ELSE stops' = [stopsUpd EXCEPT ![bidCoin, askCoin] = 
                            <<[
                                account |-> stopBook[1].account,
                                exchrate |-> stopBook[1].exchrate,
                                amount |-> stopBook[1].amount - strikeAskAmt
                            ]>> \o Tail(@)
                     ]
            /\  accounts' = 
                [ accounts EXCEPT 
                    ![stopBook[1].account, bidCoin] = @ + strikeBidAmt,
                    ![stopBook[1].account, askCoin] = @ - strikeAskAmt
                ] 
            /\  pools' = 
                [ pools EXCEPT
                    ![askCoin, bidCoin] = @ - strikeBidAmt,
                    ![bidCoin, askCoin] = @ + strikeAskAmt 
                ]
            /\  UNCHANGED <<drops, reserve, limits>>
=============================================================================