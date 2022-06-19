# agape

## Overview
Crowd source application, to compel something to happen by participants contributing a certain amount of Ada. The idea being, the more Ada is contributed, the more compelling it would be for the parties involved to satisfy the condition, for the payout to occur. 

Examples could be:
 - Person A to discuss with Person B on a certain topic on a platform such as YouTube. If this condition is satisfied, and YouTube evidence provided, then the crowd sourced amount is donated to charity C.
 - Person A to run a marathon by a certain date. If this condition is satisfied, then contributed amount donated to charity

If the above conditions happen, the accumulated Ada will be paid to Beneficiary C

If the above conditions did not happen, then the accumulated Ada will be refunded to all crowd source participants.

Minting of a commemorative NFT token for every participant contributor, where we can link to an IPFS photo, and with descriptive text in the metadata on the conditions of the crowd source. This will be minted and sent to participants only on a successful crowd source.

There is also a role of an appointed Arbiter who will settle disputes.

Disputes occur if any of the participants are not satisfied with the outcome. A campaign contributor can register an objection. An objection will be successful if a simple majority based on Ada amount contributed is reached. If the objection is successful, then the arbiter steps in and decides on the outcome.

## Examples of transition states and transactions

![Overview](./img/overview.png)

![Succes](./img/success.png)

![Failed](./img/failed.png)

![Successful objection](./img/successfulobject.png)


## Testing

5 emulator trace tests have been included. To run the emulator trace tests, run in cabal repl, then run the following commands:

1. test1 - wallet 1 and wallet 2 contributes to a campaign
2. test2 - wallet 1 and wallet 2 contributes to a campaign. No evidence provided, and wallet 3 triggers a refund.
3. test3 - wallet 1 and wallet 2 contributes to a campaign. Beneficiary (wallet 3) provides evidence, and triggers a payout.
4. test4 - wallet 1 and wallet 2 contributes to a campaign. Beneficiary (wallet 3) provides evidence. Wallet 1 and 2 objects. Arbiter triggers a refund.
5. test5 - wallet 1 and wallet 2 contributes to a campaign. Beneficiary (wallet 3) provides evidence. Wallet 1 and 2 objects. Arbiter triggers a payout.



## Current limitations, improvements and issues

### Improvements
1. If an arbiter needs to act, then there should be some incentive for the arbiter. The arbiter should receive a small percentage of the contributed Ada as compensation. Currently arbiter receives nothing.
2. If the same contributor wants to conribute multiple times, then the subsequent contributions need to update their existing contribution. This is to ensure that for every contributor, there is only one UTXO and one Datum. It gets complicated for refund purposes if there are multiple UTXOs from the same contributor.

### Limitations
1. Current limitations of transaction size limit, where we cannot include too many UTXOs in one transaction. To overcome this, may require a batching strategy.

### Major Issue
1. Objections in the current design is open for attacks. The logic will work for honest actors, but an attacker could very easily create a transaction without all the objections, such that they could engineer a false refund, or a false payout. This is because the script validation, is unable to check all the UTXOs on the script address for objections, but can only check what has been included in the transaction.

### Minor issue
1. A beneficiary could place a fake evidence and then quickly create another transaction to payout. To circumvent this, we could add a refund window, to allow any potential refunds to occur first before payouts.




