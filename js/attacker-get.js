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
  // const jarAddress = process.env.JAR_ADDRESS;
  const attackerAddress = process.env.ATTACKER_ADDRESS;

  const provider = new ethers.JsonRpcProvider(url);
  let privateKey = process.env.PRIVATE_KEY;
  let wallet = new ethers.Wallet(privateKey, provider);

  const attackerContract = new ethers.Contract(
    attackerAddress,
    attackerABI,
    wallet
  );

  await attackerContract.get();
  console.log("Attacker's get() called")
}

main()
  .then(() => process.exit(0))
  .catch(error => {
    console.error(error);
    process.exit(1);
  });


