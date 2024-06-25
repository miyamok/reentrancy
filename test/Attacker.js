const { expect } = require("chai");

describe("Reentrancy vulnerability", function () {
  it("Attacker successfully attacks Jar", async function () {
    const [jarOwner, attackerOwner] = await ethers.getSigners();
    const initialJarBalance = ethers.parseEther("10");
    const jarContractFactory = await ethers.getContractFactory("Jar", {
        signer: jarOwner,
      });
    const jarContract = await jarContractFactory.deploy({value: initialJarBalance});
    const jarAddress = jarContract.target;
    console.log("Jar deployed at " + jarAddress);
    const attackerContractFactory =  await ethers.getContractFactory("Attacker", {
        signer: attackerOwner,
      });
    const initialAttackerBalance = ethers.parseEther("1");
    const attackerContract = await attackerContractFactory.deploy(jarAddress, {value: initialAttackerBalance});
    const attackerAddress = attackerContract.target;
    console.log("Attacker deployed at " + attackerAddress);
    console.log();

    const jarInitialBalance = await ethers.provider.getBalance(jarAddress);
    console.log("Jar's ETH balance " + ethers.formatEther(jarInitialBalance));
    const attackerInitialBalance = await ethers.provider.getBalance(attackerAddress);
    console.log("Attacker's ETH balance " + ethers.formatEther(attackerInitialBalance));
    console.log("Attacker's ETH deposit in Jar " + ethers.formatEther(await jarContract.balance(attackerAddress)));
    console.log();

    console.log("* Call to Attacker.prepare()");
    await attackerContract.prepare();
    console.log("Jar's ETH balance " + ethers.formatEther(await ethers.provider.getBalance(jarAddress)));
    console.log("Attacker's ETH balance " + ethers.formatEther(await ethers.provider.getBalance(attackerAddress)));
    console.log("Attacker's ETH deposit in Jar " + ethers.formatEther(await jarContract.balance(attackerAddress)));
    console.log();

    console.log("* Call to Attacker.attack()");
    await attackerContract.attack();
    console.log("Jar's ETH balance " + ethers.formatEther(await ethers.provider.getBalance(jarAddress)));
    console.log("Attacker's ETH balance " + ethers.formatEther(await ethers.provider.getBalance(attackerAddress)));
    console.log("Attacker's ETH deposit in Jar " + ethers.formatEther(await jarContract.balance(attackerAddress)));

    expect(await ethers.provider.getBalance(attackerAddress)).to.equal(jarInitialBalance + attackerInitialBalance);
  });
});