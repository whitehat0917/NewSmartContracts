// SPDX-License-Identifier: MIT
import "./ERC1155.sol";

pragma solidity ^0.8.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _setOwner(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _setOwner(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        _setOwner(newOwner);
    }

    function _setOwner(address newOwner) private {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

contract QeyNFT is ERC1155, Ownable {
    struct Parcel {
        uint256 parcelType;
        uint256 amountNumber;
    }

    struct ParcelToken {
        uint256 id;
        address creator;
        uint256 parcelId;
    }

    struct GenesisToken {
        uint256 id;
        address creator;
        uint256 category;
    }

    mapping (uint256 => Parcel) private Parcels;
    mapping (uint256 => ParcelToken) public ParcelTokens;
    mapping (uint256 => GenesisToken) public GenesisTokens;

    uint256 public parcelCount = 1;
    uint256 public genesisCount = 3939;
    uint256 private mintAmount = 0.1 ether;

    bool public pause = false;

    event mintParcel(address creator, uint256 tokenId, uint256 parcelId);
    event mintGenesis(address creator, uint256 tokenId, uint256 category);

    constructor() public ERC1155("https://token-cdn-domain/{id}.json") {}

    function setParcel(Parcel[] memory _parcels) public onlyOwner {
        for (uint256 i = 0; i < _parcels.length; i++) {
            Parcels[i+1] = Parcel(_parcels[i].parcelType, _parcels[i].amountNumber);
        }
    }

    function mint() public payable {
        require(pause == false, "Mint is stoppable now. Please wait...");
        require(parcelCount < 3939, "Max mint amount is reached");
        require(mintAmount <= msg.value, "Please set correct mint fee");

        _mint(msg.sender, parcelCount, 1, "");
        ParcelTokens[parcelCount] = ParcelToken(parcelCount, msg.sender, parcelCount);
        emit mintParcel(msg.sender, parcelCount, parcelCount);
        parcelCount++;
    }

    function burnParcel(uint256 p1TokenId, uint256 p2TokenId, uint256 p3TokenId, uint256 p4TokenId) public {
        require((p1TokenId != 0 && p2TokenId != 0 && p3TokenId != 0) || p4TokenId != 0, "You should set correct token ID");

        uint256 _sum = 0;
        if (p4TokenId != 0){
            require(balanceOf(msg.sender, p4TokenId) > 0, "You should be owner of the token");
            require(Parcels[ParcelTokens[p4TokenId].parcelId].parcelType == 4, "Please set correct token ID for parcel");
            _burn(msg.sender, p4TokenId, 1);
            _sum = 8;
        }else{
            require(balanceOf(msg.sender, p1TokenId) > 0 && balanceOf(msg.sender, p2TokenId) > 0 && balanceOf(msg.sender, p3TokenId) > 0, "You should be owner of the tokens");
            require(Parcels[ParcelTokens[p1TokenId].parcelId].parcelType == 1 && Parcels[ParcelTokens[p2TokenId].parcelId].parcelType == 2 && Parcels[ParcelTokens[p3TokenId].parcelId].parcelType == 3, "Please set correct combinations of parcels");
            _burn(msg.sender, p1TokenId, 1);
            _burn(msg.sender, p2TokenId, 1);
            _burn(msg.sender, p3TokenId, 1);
            _sum = Parcels[ParcelTokens[p1TokenId].parcelId].amountNumber + Parcels[ParcelTokens[p2TokenId].parcelId].amountNumber + Parcels[ParcelTokens[p3TokenId].parcelId].amountNumber;
        }
        GenesisTokens[genesisCount] = GenesisToken(genesisCount, msg.sender, _sum - 2);
        _mint(msg.sender, genesisCount, 1, "");
        emit mintGenesis(msg.sender, parcelCount, _sum - 2);
    }

    function withdraw() public onlyOwner {
        uint256 balance = address(this).balance;
        payable(msg.sender).transfer(balance);
    }

    function setPause(bool _pause) public onlyOwner {
        pause = !_pause;
    }

    function uri(uint256 _tokenId) public view override returns (string memory _uri) {
        return _tokenURI(_tokenId);
    }

    function setTokenUri(uint256 _tokenId, string memory _uri) public onlyOwner {
        _setTokenURI(_tokenId, _uri);
    }
}
