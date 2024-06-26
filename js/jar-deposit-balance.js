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

const attackerABI = [
  {
    "inputs":[
      {"internalType":"address",
        "name":"_jar",
        "type":"address"}
      ],
    "stateMutability":"payable",
    "type":"constructor"},
  {
    "inputs":[],
    "name":"attack",
    "outputs":[],
    "stateMutability":"nonpayable",
    "type":"function"
  },
  {
    "inputs":[],
    "name":"get",
    "outputs":[],
    "stateMutability":"nonpayable",
    "type":"function"
  },
  {
    "inputs":[],
    "name":"jar",
    "outputs":[
      {
        "internalType":"contract IJar",
        "name":"",
        "type":"address"
      }
    ],
    "stateMutability":"view",
    "type":"function"
  },
  {
    "inputs":[],
    "name":"owner",
    "outputs":[
      {
        "internalType":"address",
        "name":"",
        "type":"address"
      }
    ],
    "stateMutability":"view",
    "type":"function"
  },
  {
    "inputs":[],
    "name":"prepare",
    "outputs":[],
    "stateMutability":"nonpayable",
    "type":"function"
  },
  {
    "stateMutability":"payable",
    "type":"receive"
  }
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

// function getAttackerAddress() {
//   if (process.argv.length !== 3) {
//     console.log("One argument required for the address of the attacker smart contract.")
//     process.exit(1);
//   }
//   const addr = process.argv[2];
//   if (ethers.utils.isAddress(addr)) {
//     console.log("is valid address");
//   } else {
//     console.log("is not a valid address");
//     process.exit(1);
//   }
//   return addr;
// }

// const attacker = getAttackerAddress();

main()
  .then(() => process.exit(0))
  .catch(error => {
    console.error(error);
    process.exit(1);
  });


