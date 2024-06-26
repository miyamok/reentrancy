const ethers = require('ethers');
require('dotenv').config();

const jarABI = [
    {"inputs":[],
     "stateMutability":"payable",
     "type":"constructor"},
    {"inputs":[{"internalType":"address",
		"name":"",
		"type":"address"}],
     "name":"balance",
     "outputs":[{"internalType":"uint256",
		 "name":"",
		 "type":"uint256"}],
     "stateMutability":"view",
     "type":"function"},
    {"inputs":[],
     "name":"deposit",
     "outputs":[],
     "stateMutability":"payable",
     "type":"function"},
    {"inputs":[],
     "name":"withdraw",
     "outputs":[],
     "stateMutability":"nonpayable",
     "type":"function"}
];

async function main() {

  const url = process.env.SEPOLIA_URL;
  const jarAddress = process.env.JAR_ADDRESS;
  const attackerAddress = process.env.ATTACKER_ADDRESS
  const provider = new ethers.JsonRpcProvider(url);

  let privateKey = process.env.PRIVATE_KEY;
  let wallet = new ethers.Wallet(privateKey, provider);

  const jarContract = new ethers.Contract(
    jarAddress,
    jarABI,
    wallet
  );
  const attacker_balance = await jarContract.balance(attackerAddress);
  console.log("Attacker's deposit in Jar amounts to " + ethers.formatEther(attacker_balance));
}

main()
  .then(() => process.exit(0))
  .catch(error => {
    console.error(error);
    process.exit(1);
  });


