// SPDX-License-Identifier: CC-BY-4.0
pragma solidity >=0.6.12 <0.9.0;

contract Jar {

    mapping(address=>uint) public balance;
    bool locked;

    constructor() payable {

    }

    function deposit() public payable {
        require(!locked, "deposit(): reentrancy not allowed");
        balance[msg.sender] += msg.value;
    }

    function withdraw() public {
        require(!locked, "withdraw(): reentrancy not allowed");
    	locked = true;
        require(balance[msg.sender] != 0, "zero balance");
        (bool s,) = msg.sender.call{ value: balance[msg.sender] }("");
        require(s, "In VulnerableJar.withdrow(), call() failed.");
        balance[msg.sender] = 0;
	locked = false;
    }
}

