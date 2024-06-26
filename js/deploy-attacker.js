const ethers = require('ethers');
require('dotenv').config();

async function main() {

  const url = process.env.SEPOLIA_URL;

  let artifacts = await hre.artifacts.readArtifact("Attacker");

  const provider = new ethers.JsonRpcProvider(url);

  let privateKey = process.env.PRIVATE_KEY;

  let wallet = new ethers.Wallet(privateKey, provider);

  let factory = new ethers.ContractFactory(artifacts.abi, artifacts.bytecode, wallet);
  const initialBalance = ethers.parseEther("0.01");

  let attacker = await factory.deploy(process.env.JAR_ADDRESS, {value: initialBalance});

  await attacker.waitForDeployment();

  console.log("Attacker address:", attacker.target);
}

main()
  .then(() => process.exit(0))
  .catch(error => {
    console.error(error);
    process.exit(1);
  });
