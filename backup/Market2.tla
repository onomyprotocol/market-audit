------------------------------- MODULE Market2 -------------------------------
EXTENDS     FiniteSets, Naturals, Sequences

CONSTANT    ExchAccount,    \* Set of all accounts
            NOM,           \* Set of all coins
            Denom_A,
            Denom_B

VARIABLE    accounts,
            \* The reserve holds the initial bags
            reserve

-----------------------------------------------------------------------------
\* Three Coin Types. Two Denoms and NOM
CoinType == {Denom_A, Denom_B, NOM}

\* Coins are held in bags of which whose Cardinality
\* represents a balance or amount of coins
CoinBag == SUBSET Denom_A \/ SUBSET Denom_B \/ SUBSET NOM

Position == 
[
    \* Exchange Rate is defined as
    \* Cardinality(exchrate[0]) / Cardinality(exchrate[1])
    exchrate: Seq(CoinBag \X CoinBag),
    \* cardinality of bag is the amount
    bag: CoinBag
]

CoinRecords(ct) == [
                \* Holds a bag (set) of coins
                \* Balances are represented by Cardinality of bag
                \* So, in implementation, consider this balance
                bag: CoinBag,
                positions: [CoinType -> Seq(Seq(Position) \X Seq(Position))]
                    
              ]

CoinRecord == CoinRecords("Denom_A") \/ CoinRecords("Denom_B") \/ CoinRecords("NOM") 

TypeInvariant ==     
/\  accounts \in [
        ExchAccount -> {
          f \in [CoinType -> CoinRecord]:
          \A ct \in CoinType: f[ct] \in CoinRecords(ct)
        }
      ]
/\  reserve \in [CoinType -> CoinBag]

INIT ==     
/\  accounts = [
        ea \in ExchAccount |-> [ 
            ct \in CoinType |-> [
                bag |-> {}, 
                positions |-> [c \in CoinType \ {ct} |-> << <<>>, <<>> >>]
            ]
        ]
    ]
/\  reserve = [type \in CoinType |-> CoinType]

(***************************************************************************)
(* Deposit(acct, bag, type)                                                *)
(*                                                                         *)
(* The Deposit function takes a SUBSET of coins from a single type and     *)
(* the reserve and places it into an exchange account.                     *)
(***************************************************************************)
Deposit(acct, bag, type) ==
/\  bag \in SUBSET reserve[type]
/\  accounts' = [accounts EXCEPT ![acct][type] = 
        [
            bag |-> bag \union @.bag,
            positions |-> @.positions
        ]
    ]
/\  reserve' = [reserve EXCEPT ![type] = @ \ bag]

Withdraw(acct, bag, type) ==
/\  bag \in SUBSET accounts[acct][type].bag
/\  accounts' = [accounts EXCEPT ![acct][type] = 
        [
            bag |-> @.bag \ bag,
            positions |-> @.positions
        ]
    ]
/\  reserve' = [reserve EXCEPT ![type] = @ \union bag]

NEXT == \/  \E acct \in ExchAccount :
            \E type \in CoinType :
                \/  \E bag \in SUBSET reserve[type] :
                    IF Cardinality(bag) > 0 THEN
                        Deposit(acct, bag, type)
                    ELSE UNCHANGED <<accounts, reserve>>
                \/  \E bag \in SUBSET accounts[acct][type].bag :
                    IF Cardinality(bag) > 0 THEN
                        Withdraw(acct, bag, type)
                    ELSE UNCHANGED <<accounts, reserve>>
         
Spec == INIT /\ [][NEXT]_<<accounts, reserve>>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
