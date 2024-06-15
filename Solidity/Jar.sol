// SPDX-License-Identifier: CC-BY-4.0
pragma solidity >=0.6.12 <0.9.0;

contract Jar {

    mapping(address=>uint) public balance;

    constructor() payable {

    }

    function deposit() public payable {
        balance[msg.sender] += msg.value;
    }

    function withdraw() public {
        require(balance[msg.sender] != 0, "zero balance");
        (bool s,) = msg.sender.call{ value: balance[msg.sender] }("");
        require(s, "In Jar.withdraw(), call() failed.");
        balance[msg.sender] = 0;
    }
}
