const { merge } = require('sol-merger');
const fs = require('fs');

// Get the merged code as a string
mergeCode();
async function mergeCode() {
    const mergedCode = await merge("./erc/BABYCAKE.sol");
    // Print it out or write it to a file etc.
    console.log(mergedCode);
    fs.writeFileSync('./temp/BABYCAKE.sol', mergedCode);
}