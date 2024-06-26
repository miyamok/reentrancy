const ethers = require('ethers');
require('dotenv').config();

async function main() {

  const url = process.env.SEPOLIA_URL;
  const jarAddress = process.env.JAR_ADDRESS;

  const provider = new ethers.JsonRpcProvider(url);
  const asset = await provider.getBalance(jarAddress);

  console.log("Jar's ETH asset balance amounts to " + ethers.formatEther(asset));
}

main()
  .then(() => process.exit(0))
  .catch(error => {
    console.error(error);
    process.exit(1);
  });


