const { expect } = require("chai");

describe("Reentrancy vulnerability", function () {
  it("Attacker fails to attack JarLocked", async function () {
    const [jarOwner, attackerOwner] = await ethers.getSigners();
    const initialJarBalance = ethers.parseEther("10");
    const jarContractFactory = await ethers.getContractFactory("JarLocked", {
        signer: jarOwner,
      });
    const jarContract = await jarContractFactory.deploy({value: initialJarBalance});
    const jarAddress = jarContract.target;
    console.log("JarLocked deployed at " + jarAddress);
    const attackerContractFactory =  await ethers.getContractFactory("Attacker", {
        signer: attackerOwner,
      });
    const initialAttackerBalance = ethers.parseEther("1");
    const attackerContract = await attackerContractFactory.deploy(jarAddress, {value: initialAttackerBalance});
    const attackerAddress = attackerContract.target;
    console.log("Attacker deployed at " + attackerAddress);
    console.log();

    const jarInitialBalance = await ethers.provider.getBalance(jarAddress);
    console.log("JarLocked's ETH balance " + ethers.formatEther(jarInitialBalance));
    const attackerInitialBalance = await ethers.provider.getBalance(attackerAddress);
    console.log("Attacker's ETH balance " + ethers.formatEther(attackerInitialBalance));
    console.log("Attacker's ETH deposit in JarLocked " + ethers.formatEther(await jarContract.balance(attackerAddress)));
    console.log();

    console.log("* Call to Attacker.prepare()");
    await attackerContract.prepare();
    const jarBalance = await ethers.provider.getBalance(jarAddress);
    const attackerBalance = await ethers.provider.getBalance(attackerAddress);
    console.log("JarLocked's ETH balance " + ethers.formatEther(jarBalance));
    console.log("Attacker's ETH balance " + ethers.formatEther(await ethers.provider.getBalance(attackerAddress)));
    console.log("Attacker's ETH deposit in JarLocked " + ethers.formatEther(await jarContract.balance(attackerAddress)));
    console.log();

    console.log("* Call to Attacker.attack()");
    await expect(attackerContract.attack()).to.be.revertedWith(
      "In JarLocked.withdraw(), call() failed."
    );
    
    console.log("JarLocked's ETH balance " + ethers.formatEther(await ethers.provider.getBalance(jarAddress)));
    console.log("Attacker's ETH balance " + ethers.formatEther(await ethers.provider.getBalance(attackerAddress)));
    console.log("Attacker's ETH deposit in JarLocked " + ethers.formatEther(await jarContract.balance(attackerAddress)));

    expect(await ethers.provider.getBalance(jarAddress)).to.equal(jarBalance);
    expect(await ethers.provider.getBalance(attackerAddress)).to.equal(attackerBalance);
  });
});