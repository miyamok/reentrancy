const ethers = require('ethers');
require('dotenv').config();

async function main() {

  const url = process.env.SEPOLIA_URL;
  let artifacts = await hre.artifacts.readArtifact("Jar");
  const initialBalance = ethers.parseEther("0.02");

  const provider = new ethers.JsonRpcProvider(url);

  let privateKey = process.env.PRIVATE_KEY;

  let wallet = new ethers.Wallet(privateKey, provider);
  let factory = new ethers.ContractFactory(artifacts.abi, artifacts.bytecode, wallet);

  let jar = await factory.deploy({value: initialBalance});

  await jar.waitForDeployment();
  console.log("Jar address:", jar.target);
}

main()
  .then(() => process.exit(0))
  .catch(error => {
    console.error(error);
    process.exit(1);
  });
