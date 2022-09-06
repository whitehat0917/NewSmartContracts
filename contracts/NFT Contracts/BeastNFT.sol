// SPDX-License-Identifier: MIT
pragma solidity 0.7.0;

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "@openzeppelin/contracts/utils/Counters.sol";
import "@openzeppelin/contracts/utils/Context.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

interface IERC721 {
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);
    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);
    function balanceOf(address owner) external view returns (uint256 balance);
    function ownerOf(uint256 tokenId) external view returns (address owner);
    function safeTransferFrom(address from, address to, uint256 tokenId) external;
    function transferFrom(address from, address to, uint256 tokenId) external;
    function approve(address to, uint256 tokenId) external;
    function getApproved(uint256 tokenId) external view returns (address operator);
    function setApprovalForAll(address operator, bool _approved) external;
    function isApprovedForAll(address owner, address operator) external view returns (bool);
    function safeTransferFrom(address from, address to, uint256 tokenId, bytes calldata data) external;
}

interface IBeastNFT is IERC721 {
    function getBeast(uint256 tokenId) external  view returns(string memory, uint256, uint256, string memory, string memory);
}

contract BeastNFT is Context, IBeastNFT, Ownable {
    using SafeMath for uint256;
    using Counters for Counters.Counter;
    Counters.Counter private _tokenIds;
    IERC20 public bloodstone;
    string public _baseURL;
    address public rewardpool;
    address ZERO = 0x0000000000000000000000000000000000000000;

    uint256 mintingPrice;
    struct Beast {
        string name;
        uint256 strength;
        uint256 capacity;
        string[2] imgUrl;
    }
    mapping (uint256 => Beast) tokenData;
    mapping (address => uint256[]) addressTokenIds;

    string private _name;
    string private _symbol;
    mapping (uint256 => address) private _tokenApprovals;
    mapping (address => mapping (address => bool)) private _operatorApprovals;

    mapping (uint256 => address) tokenToOwner;
    mapping (uint256 => uint256) tokenIdIndex;
    constructor() {
        _name = "Crypto Legions Beast";
        _symbol = "BEAST";
        bloodstone = IERC20(0x8Cc6529d211eAf6936d003B521C61869131661DA);
        mintingPrice = 20;
        setBaseURL("https://ipfs.infura.io:5001/api/v0/cat/");
    }
    function name() public view returns (string memory) {
        return _name;
    }
    function symbol() public view returns (string memory) {
        return _symbol;
    }
    function approve(address to, uint256 tokenId) public virtual override {
        address owner = ownerOf(tokenId);
        require(to != owner || isApprovedForAll(owner, msg.sender), "ERC721: approval to current owner");
        require(msg.sender==owner, "ERC721: approve caller is not owner nor approved for all");
        _approve(to, tokenId);
    }
    function getApproved(uint256 tokenId) public view virtual override returns (address) {
        return _tokenApprovals[tokenId];
    }
    function setApprovalForAll(address operator, bool approved) public virtual override {
        require(operator != msg.sender, "ERC721: approve to caller");
        _operatorApprovals[msg.sender][operator] = approved;
        emit ApprovalForAll(msg.sender, operator, approved);
    }
    function isApprovedForAll(address owner, address operator) public view virtual override returns (bool) {
        return _operatorApprovals[owner][operator];
    }
    function _approve(address to, uint256 tokenId) internal virtual {
        _tokenApprovals[tokenId] = to;
        emit Approval(ownerOf(tokenId), to, tokenId); // internal owner
    }
    function balanceOf(address owner) public view virtual override returns (uint256) {
        require(owner != address(0), "ERC721: balance query for the zero address");
        return addressTokenIds[owner].length;
    }

    function ownerOf(uint256 tokenId) public view virtual override returns (address) {
        return tokenToOwner[tokenId];
    }

    function safeTransferFrom(address from, address to, uint256 tokenId) public virtual override {
        safeTransferFrom(from, to, tokenId, "");
    }

    function safeTransferFrom(address from, address to, uint256 tokenId, bytes memory _data) public virtual override {
        address owner = ownerOf(tokenId);
        require(msg.sender==owner || getApproved(tokenId)==msg.sender, "ERC721: transfer caller is not owner nor approved");
        _transfer(from, to, tokenId);
    }

    function transferFrom(address from, address to, uint256 tokenId) public virtual override {
        address owner = ownerOf(tokenId);
        require(msg.sender==owner || getApproved(tokenId)==msg.sender, "ERC721: transfer caller is not owner nor approved");
        _transfer(from, to, tokenId);
    }

    function _transfer(address from, address to, uint256 tokenId) internal virtual {
        require(ownerOf(tokenId) == from, "ERC721: transfer of token that is not own"); // internal owner
        require(to != address(0), "ERC721: transfer to the zero address");
        _approve(address(0), tokenId);

        addressTokenIds[from][tokenIdIndex[tokenId]] = addressTokenIds[from][addressTokenIds[from].length-1];
        tokenIdIndex[addressTokenIds[from][addressTokenIds[from].length-1]] = tokenIdIndex[tokenId];
        addressTokenIds[from].pop();
        tokenToOwner[tokenId] = to;
        
        addressTokenIds[to].push(tokenId);
        tokenIdIndex[tokenId] = addressTokenIds[to].length - 1;
        emit Transfer(from, to, tokenId);
    }

    function mint(uint256 amount) external {
        require(rewardpool!=ZERO, "mint : should set reward pool address first");
        uint256 bloodstoneAmount = getBloodstoneAmount(amount);
        require(bloodstone.balanceOf(msg.sender) >= bloodstoneAmount*10**18, "Insufficient payment");
        bloodstone.transferFrom(msg.sender, rewardpool, bloodstoneAmount*10**18);
        uint256 randNum = 0;
        Beast memory beast;
        for(uint i=0; i<amount; i++) {
            addressTokenIds[msg.sender].push(_tokenIds.current());
            tokenIdIndex[_tokenIds.current()] = addressTokenIds[msg.sender].length - 1;
            tokenToOwner[_tokenIds.current()] = msg.sender;
            randNum = genRand(10000, i);
            if (randNum==0&&randNum<5) {
                string[2] memory imgs = ["QmNrqT2UXZ6vjAMN277fTo6TwV9Cg1dDop5QZg39Hbu3Tc", "QmTyQ3Mab2711GWGMyvXqMVCQpK49WH1KQRzhUBJS96Q7W"];
                beast = Beast("Phoenix", 6, 20, imgs);
            } else if (randNum>=5&&randNum<100) {
                string[2] memory imgs = ["QmNUQeLyZXdSjCQPJr83PTSWkwFbPXHGdF7pHwVUJcQSaj", "QmcNEMp12fU7tNyTt8oRBKeW7QjXR9gLKwJoXPYAav86XV"];
                beast = Beast("Dragon", 5, 5, imgs);
            } else if (randNum>=100&&randNum<800) {
                string[2] memory imgs = ["QmNatbVqKggWQQkoS8bxthU1YSe2TFNGCtuEmNCr8rVYDd", "QmZwioRnSrxDUcDK1e4LNkvGi7WW9eJXnHrEwXavathiwe"];
                beast = Beast("Griffin", 4, 4, imgs);
            } else if (randNum>=800&&randNum<2200) {
                string[2] memory imgs = ["QmXJjCqKAuALekTM1MUGpQDi9GaGuC4U5o5fdbVmac1hSN", "Qmbdyp864SwZZ2X3yBWKX1YeSax4BRj8F3yvLM9PcgAXYw"];
                beast = Beast("Pegasus", 3, 3, imgs);
            } else if (randNum>=2200&&randNum<5000) {
                string[2] memory imgs = ["QmSgKKqAZex4qBjtHciSXwwxn8Cqn8CJY4UCdEww62fNWQ", "QmPbsQEreJNFVRkNkgyzDNTgkQ6Xt6GrPQXjz83FYTyQMi"];
                beast = Beast("Barghest", 2, 2, imgs);
            } else {
                string[2] memory imgs = ["QmYqrDk6qcvo3Kg15RuMcJsZhJ4JatAuyv8VAWvCojKeAZ", "QmRXAzXAA8oiuMxe9m8Tdp9oq4tsBXgDjkpNz3Tz5uuRj2"];
                beast = Beast("Centaur", 1, 1, imgs);
            }
            tokenData[_tokenIds.current()] = beast;
            _tokenIds.increment();
        }
    }

    function setRewardPool(address _address) external onlyOwner {
        rewardpool = _address;
        bloodstone.approve(rewardpool, 5000000*10**18);
    }

    function genRand(uint256 maxNum, uint256 i) private view returns (uint256) {
        require(maxNum>0, "maxNum should be bigger than zero");
        return uint256(uint256(keccak256(abi.encode(block.timestamp, block.difficulty, i))) % maxNum);
    }

    function getBloodstoneAmount(uint256 _mintingAmount) private view returns (uint256) {
        require(_mintingAmount > 0, "amount should be bigger than zero");
        if(_mintingAmount==1) {
            return mintingPrice;
        } else if(_mintingAmount==5) {
            return mintingPrice.mul(5).mul(98).div(100);
        } else if(_mintingAmount==10) {
            return mintingPrice.mul(10).mul(97).div(100);
        } else if(_mintingAmount==20) {
            return mintingPrice.mul(20).mul(95).div(100);
        } else if(_mintingAmount==100) {
            return mintingPrice.mul(100).mul(90).div(100);
        } else {
            return mintingPrice.mul(_mintingAmount);
        }
    }

    function getTokenIds(address _address) external view returns (uint256[] memory) {
        return addressTokenIds[_address];
    }

    function getBeast(uint256 tokenId) external view virtual override returns(string memory, uint256, uint256, string memory, string memory) {
        return (tokenData[tokenId].name, tokenData[tokenId].strength, tokenData[tokenId].capacity, tokenData[tokenId].imgUrl[0], tokenData[tokenId].imgUrl[1]);
    }

    function setBaseURL(string memory baseURI) public onlyOwner {
        _baseURL = baseURI;
    }

    function totalSupply() public view returns (uint256) {
        return _tokenIds.current();
    }

    function getMintingPrice() public view returns (uint256) {
        return mintingPrice;
    }

    function setMintingPrice(uint256 _price) public onlyOwner {
        require(_price>0, "price should be bigger than zero");
        mintingPrice = _price;
    }

    function withdrawBNB(address payable _addr, uint256 amount) public onlyOwner {
        _addr.transfer(amount);
    }

    function withdrawBNBOwner(uint256 amount) public onlyOwner {
        msg.sender.transfer(amount);
    }
}