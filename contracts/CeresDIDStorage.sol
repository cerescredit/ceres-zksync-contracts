// SPDX-License-Identifier: MIT
pragma solidity ^0.8.16;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

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

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

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
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _setOwner(newOwner);
    }

    function _setOwner(address newOwner) private {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}



interface ICeresDIDStorage {

    function propertyNameOf(uint tokenId) external view returns(string memory);

    function tokenDIDOf(uint256 tokenId) external view returns(string memory);

    function didTokenIdOf(string calldata did) external view returns(uint);

    function customImageOf(uint tokenId) external view returns(string memory);

    function minterOf(uint tokenId) external view returns(address);

    function mintedTokenOf(address account) external view returns(uint256);

    function stringPropertyOf(uint tokenId,uint pIndex) external view returns(string memory);

    function allPropsLength() external view returns(uint256);

    function allStringPropsLength() external view returns(uint256);

    function itemProperties(uint tokenId) external view returns(uint[] memory numberProps,string[] memory stringProps);

    function addItem(
        uint tokenId,
        address to,
        uint[] calldata numberProps,
        string[] calldata stringProps, 
        string calldata did,
        string calldata imageUrl
    ) external returns(bytes32[] memory packedProps);

    function removeItem(uint tokenId) external;

    function didExists(string calldata did) external view returns(bool);

    function updateProperty(uint tokenId,uint mapIndex,uint pos,uint length,uint newVal) external;

    function updatePackedProperties(uint tokenId, uint mapIndex, bytes32 newPackedProps) external;

    function updateCustomImage(uint tokenId, string calldata imageUri) external;

    function updateStringProperty(uint tokenId,uint propIndex, string calldata val) external;

    function aliasOf(uint _pIndex,uint _pVal) external view returns(string memory);
}
// File: contracts-zk/libs/Address.sol





/**
 * @dev Collection of functions related to the address type
 */
library Address {

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {

        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) private pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// File: contracts-zk/interfaces/IERC20.sol





/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// File: contracts-zk/libs/SafeERC20.sol







/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

// File: contracts-zk/libs/CfoNftTakeableV2.sol







interface IERC721TransferMin {
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;
}

interface IERC1155TransferMin {
    function safeTransferFrom(
        address from,
        address to,
        uint256 id,
        uint256 amount,
        bytes calldata data
    ) external;
}

abstract contract CfoNftTakeableV2 is Ownable {
    using Address for address;
    using SafeERC20 for IERC20;

    address public cfo;

    modifier onlyCfoOrOwner {
        require(msg.sender == cfo || msg.sender == owner(),"onlyCfo: forbidden");
        _;
    }

    constructor(){
        cfo = msg.sender;
    }

    function takeERC721(address to,address token,uint tokenId) external onlyCfoOrOwner {
        require(to != address(0),"to can not be address 0");
        IERC721TransferMin(token).safeTransferFrom(address(this), to, tokenId);
    }

    function takeERC1155(address to,address token,uint tokenId,uint amount) external onlyCfoOrOwner {
        require(to != address(0),"to can not be address 0");
        require(amount > 0,"amount can not be 0");
        IERC1155TransferMin(token).safeTransferFrom(address(this), to, tokenId,amount,"");
    }

    function takeToken(address token,address to,uint256 amount) public onlyCfoOrOwner {
        require(token != address(0),"invalid token");
        require(amount > 0,"amount can not be 0");
        require(to != address(0),"invalid to address");
        IERC20(token).safeTransfer(to, amount);
    }

    function takeETH(address to,uint256 amount) public onlyCfoOrOwner {
        require(amount > 0,"amount can not be 0");
        require(address(this).balance>=amount,"insufficient balance");
        require(to != address(0),"invalid to address");
        
        payable(to).transfer(amount);
    }

    function takeAllToken(address token, address to) public {
        uint balance = IERC20(token).balanceOf(address(this));
        if(balance > 0){
            takeToken(token, to, balance);
        }
    }

    function takeAllETH(address to) public {
        uint balance = address(this).balance;
        if(balance > 0){
            takeETH(to, balance);
        }
    }

    function setCfo(address _cfo) external onlyOwner {
        require(_cfo != address(0),"_cfo can not be address 0");
        cfo = _cfo;
    }
}
// File: contracts-zk/libs/Context.sol





// File: contracts-zk/libs/Ownable.sol








// File: contracts-zk/libs/NFTMintManager.sol






abstract contract NFTMintManager is Ownable {

    mapping(address => bool) public isMinter;
    mapping(address => bool) public isUpdater;

    uint256 public nextTokenId = 1;

    modifier onlyMinter {
        require(isMinter[msg.sender],"onlyMinter: caller must be minter");
        _;
    }

    modifier onlyUpdater {
        require(isUpdater[msg.sender],"onlyUpdater: caller must be updater");
        _;
    }

    function addMinter(address minter) public onlyOwner {
        require(minter != address(0),"invalid new minter");
        isMinter[minter] = true;
    }

    function removeMinter(address minter) public onlyOwner {
        require(minter != address(0),"invalid new minter");
        isMinter[minter] = false;
    }

    function addUpdater(address updater) public onlyOwner {
        require(updater!=address(0),"updater can not be address 0");
        isUpdater[updater] = true;
    }

    function removeUpdater(address updater) public onlyOwner {
        require(updater != address(0),"updater can not be address 0");
        isUpdater[updater] = false;
    }
}
// File: contracts-zk/libs/SafeMath.sol




/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a, "SafeMath: subtraction overflow");
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        // Solidity only automatically asserts when dividing by 0
        require(b > 0, "SafeMath: division by zero");
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b != 0, "SafeMath: modulo by zero");
        return a % b;
    }
}
// File: contracts-zk/libs/NFTPropertyPackerV3.sol





library NFTPropertyPacker {

    function calcDataPos(uint pos) internal pure returns(uint packedDataIndex,uint posInPacked){
        packedDataIndex = pos / 32;
        posInPacked = pos % 32;
    }

    function bytesToBytes32(bytes memory b) internal pure returns(bytes32){
        require(b.length <=32,"bytesToBytes32: invalid length");        
        uint r;
        uint l = b.length <=32 ? b.length : 32;
        for(uint i=0;i<l;i++){
            r += uint(uint8(b[32 - i - 1])) << (i*8);
        }

        return bytes32(r);   
    }

    function readPartialData(bytes32 packedData,uint pos,uint length) internal pure returns(uint256){
        require(pos + length <= 32,"readPartialData: out of bounds");     
        return uint(packedData << (pos * 8) >> (32 - length) * 8);
    }

    function readUint16(bytes32 packedData,uint pos) internal pure returns(uint16) {
        return uint16(readPartialData(packedData,pos,2));
    }

    function readUint32(bytes32 packedData,uint pos) internal pure returns(uint32) {
        return uint32(readPartialData(packedData,pos,4));
    }

    function readUint64(bytes32 packedData,uint pos) internal pure returns(uint64) {
        return uint64(readPartialData(packedData,pos,8));
    }

    function readUint96(bytes32 packedData,uint pos) internal pure returns(uint96) {
        return uint96(readPartialData(packedData,pos,12));
    }

    function readUint128(bytes32 packedData,uint pos) internal pure returns(uint128) {
        return uint128(readPartialData(packedData,pos,16));
    }

    function modifyPartialData(bytes32 packedProps,uint256 pos,uint256 length,uint newVal) internal pure returns(bytes32){
        require(length > 0,"modifyPropertieFromPackedData: length can not be 0");
        require(pos + length <= 32,"modifyPropertieFromPackedData: out of bounds");
        require(length == 32 || newVal < 2 ** (length * 8),"modifyPropertieFromPackedData: new val overflow");
        uint beforeData = uint(packedProps >> (32 - pos) * 8 << (32 - pos) * 8);
        uint afterData = uint(packedProps << (pos + length) * 8 >> (pos + length) * 8);
        return bytes32(beforeData + (newVal << (32 - pos - length) * 8) + afterData);
    }    
}
// File: contracts-zk/libs/NFTPropertyStorageV4.sol







abstract contract NFTPropertyStorage {

    mapping(uint256 => mapping(uint256 => bytes32)) internal _itemPackedProps;

    event PropertiesUpdated(address updater,uint tokenId,uint mapIndex,bytes32 oldPackedProps,bytes32 newPackedProps);

    function packedPropertiesOf(uint tokenId,uint mapIndex) public virtual view returns(bytes32){
        return _itemPackedProps[tokenId][mapIndex];
    }

    function readProperty(uint tokenId,uint mapIndex,uint pos,uint length) public virtual view returns(uint){
        return NFTPropertyPacker.readPartialData(_itemPackedProps[tokenId][mapIndex], pos, length);
    }

    function _updateProperty(uint tokenId,uint mapIndex,uint pos,uint len,uint newVal) internal {
        require(len == 32 || newVal < 2**(len*8),"_updateProperty: newVal overflow");
        bytes32 oldProps = _itemPackedProps[tokenId][mapIndex];
        bytes32 newProps =  NFTPropertyPacker.modifyPartialData(oldProps, pos, len, newVal);
        _itemPackedProps[tokenId][mapIndex] = newProps;

        emit PropertiesUpdated(msg.sender,tokenId,mapIndex,oldProps, newProps);
    }

    function _updatePackedProperties(uint tokenId,uint mapIndex,bytes32 newPackedProps) internal {
        bytes32 oldProps = _itemPackedProps[tokenId][mapIndex];
        _itemPackedProps[tokenId][mapIndex] = newPackedProps;

        emit PropertiesUpdated(msg.sender,tokenId,mapIndex,oldProps, newPackedProps);
    }

    function _addNewItem(uint tokenId,bytes32[] memory packedProps) internal {
        require(_itemPackedProps[tokenId][0] == bytes32(0),"_addNewItem: token id is existed");
        for(uint i=0;i<packedProps.length;i++){
            _itemPackedProps[tokenId][i] = packedProps[i];
        }
    }

    function removeItemData(uint tokenId,uint dataIndex) internal {
        delete _itemPackedProps[tokenId][dataIndex];
    }
}
// File: contracts-zk/CeresDIDStorage.sol





contract CeresDIDStorage is CfoNftTakeableV2,NFTPropertyStorage,ICeresDIDStorage {

    mapping(uint256 => string) public override propertyNameOf;
    mapping(bytes32 => string) private _propertyAliasOf;

    mapping(uint256 => string) public override tokenDIDOf;
    mapping(bytes32 => uint256) private _didTokenIdOf;

    mapping(uint256 => string) public override customImageOf;

    mapping(uint256 => address) public override minterOf;
    mapping(address => uint256) public override mintedTokenOf;

    mapping(uint256 => mapping(uint256 => string)) public override stringPropertyOf;

    uint private constant allPackedPropsLength = 3;
    uint public constant override allPropsLength = 6;
    uint public constant override allStringPropsLength = 6;

    address public ceresDID;

    modifier onlyCeresDID() {
        require(msg.sender == ceresDID, "onlyCeresDID: caller is not the ceres did");
        _;
    }

    constructor(){
        propertyNameOf[0] = "s1";
        propertyNameOf[1] = "s2";
        propertyNameOf[2] = "s3";
        propertyNameOf[3] = "s4";
        propertyNameOf[4] = "s5";
        propertyNameOf[5] = "s6";

        propertyNameOf[6] = "n1";
        propertyNameOf[7] = "n2";
        propertyNameOf[8] = "n3";
        propertyNameOf[9] = "n4";
        propertyNameOf[10] = "n5";
        propertyNameOf[11] = "n6";
    }


    function _packProperties(uint[] memory unpackedProps) private pure returns(bytes32[] memory) {
        bytes32[] memory bs = new bytes32[](allPackedPropsLength);
        bs[0] = bytes32(
            (uint(_toUint128(unpackedProps[0])) << 128) + 
            uint(_toUint128(unpackedProps[1]))
        );
        bs[1] = bytes32(
            (uint(_toUint128(unpackedProps[2])) << 128) + 
            uint(_toUint128(unpackedProps[3]))
        );
        bs[2] = bytes32(
            (uint(_toUint128(unpackedProps[4])) << 128) + 
            uint(_toUint128(unpackedProps[5]))
        );

        return bs;
    }

    function _unpackPreperties(bytes32[] memory packedProps) private pure returns(uint[] memory) {
        uint[] memory props = new uint[](allPropsLength);
        props[0] = NFTPropertyPacker.readUint128(packedProps[0], 0);
        props[1] = NFTPropertyPacker.readUint128(packedProps[0], 16);
        props[2] = NFTPropertyPacker.readUint128(packedProps[1], 0);
        props[3] = NFTPropertyPacker.readUint128(packedProps[1], 16);
        props[4] = NFTPropertyPacker.readUint128(packedProps[2], 0);
        props[5] = NFTPropertyPacker.readUint128(packedProps[2], 16);

        return props;
    }

    function itemProperties(uint tokenId) external view override returns(uint[] memory numberProps,string[] memory stringProps){
        bytes32[] memory packedProps = new bytes32[](allPackedPropsLength);
        packedProps[0] = _itemPackedProps[tokenId][0];
        packedProps[1] = _itemPackedProps[tokenId][1];
        packedProps[2] = _itemPackedProps[tokenId][2];

        numberProps = _unpackPreperties(packedProps);

        stringProps = new string[](allStringPropsLength);
        for(uint i=0;i<allStringPropsLength;i++){
            stringProps[i] = stringPropertyOf[tokenId][i];
        }
    }

    function addItem(
        uint tokenId,
        address to,
        uint[] calldata numberProps,
        string[] calldata stringProps, 
        string calldata did,
        string calldata imageUrl
    ) external override onlyCeresDID returns(bytes32[] memory packedProps) {
        require(numberProps.length == allPropsLength && stringProps.length == allStringPropsLength,"CeresDIDStorage: invalid properties length");
        require(mintedTokenOf[to] == 0,"CeresDIDStorage: to address already minted");
        require(!didExists(did),"CeresDIDStorage: did already exists");

        packedProps = _packProperties(numberProps);
        _addNewItem(tokenId,packedProps);

        _setDID(tokenId,did);
        mintedTokenOf[to] = tokenId;
        minterOf[tokenId] = to;

        _setCustomImage(tokenId, imageUrl);

        for(uint i=0;i<stringProps.length;i++){
            if(bytes(stringProps[i]).length > 0){
                stringPropertyOf[tokenId][i] = stringProps[i];
            }
        }
    }

    function removeItem(uint tokenId) external override onlyCeresDID {
        delete _itemPackedProps[tokenId][0];
        delete _itemPackedProps[tokenId][1];
        delete _itemPackedProps[tokenId][2];

        string memory did = tokenDIDOf[tokenId];
        delete tokenDIDOf[tokenId];
        delete _didTokenIdOf[_didKey(did)];

        address minter = minterOf[tokenId];
        delete minterOf[tokenId];
        delete mintedTokenOf[minter];
        
        delete customImageOf[tokenId];
    }

    function didExists(string calldata did) public view override returns(bool){
        if(bytes(did).length == 0) return true;

        return _didTokenIdOf[_didKey(did)] > 0;
    }

    function updateProperty(uint tokenId,uint mapIndex,uint pos,uint length,uint newVal) external override onlyCeresDID {
        require(mapIndex < allPackedPropsLength,"updateProperty: invalid mapIndex");
        require((pos==0 || pos==16) && length==16,"invalid pos or length");
        
        _updateProperty(tokenId, mapIndex, pos,length,newVal);
    }

    function updatePackedProperties(uint tokenId, uint mapIndex, bytes32 newPackedProps) external override onlyCeresDID {
        require(mapIndex < allPackedPropsLength,"updateProperty: invalid mapIndex");
        _updatePackedProperties(tokenId,mapIndex,newPackedProps);
    }

    function updateCustomImage(uint tokenId, string calldata imageUri) external override onlyCeresDID {
        _setCustomImage(tokenId, imageUri);
    }

    function updateStringProperty(uint tokenId,uint propIndex, string calldata val) external override onlyCeresDID {
        require(tokenId > 0,"token id can not be 0");
        stringPropertyOf[tokenId][propIndex] = val;
    }

    function didTokenIdOf(string calldata did) external view override returns(uint){
        return _didTokenIdOf[_didKey(did)];
    }

    function _didKey(string memory did) internal pure returns(bytes32){
        return keccak256(bytes(did));
    }

    function _setDID(uint tokenId,string calldata did) internal {
        require(tokenId > 0,"tokenId can not be 0");
        require(!didExists(did),"did already exists");
        tokenDIDOf[tokenId] = did;
        _didTokenIdOf[_didKey(did)] = tokenId;
    }

    function _setCustomImage(uint tokenId, string calldata imageUri) internal {
        customImageOf[tokenId] = imageUri;
    }

    function _toUint128(uint256 value) internal pure returns (uint128) {
        require(value <= type(uint128).max, "SafeCast: value doesn't fit in 128 bits");
        return uint128(value);
    }

    function aliasOf(uint _pIndex,uint _pVal) external view override returns(string memory){
        return _propertyAliasOf[_aliasKey(_pIndex,_pVal)];
    }

    function _aliasKey(uint pIndex,uint val) internal pure returns(bytes32) {
        return keccak256(abi.encode(pIndex,val));
    }

    function setPropertyName(uint _pIndex,string calldata _pName) external onlyOwner {
        require(_pIndex < allPropsLength,"invalid _pIndex");
        require(bytes(_pName).length > 0,"_pName can not be empty");
        propertyNameOf[_pIndex] = _pName;
    }

    function setAlias(uint _pIndex,uint _val,string calldata _aliasName) external onlyOwner {
        require(_pIndex < allPropsLength,"invalid _pIndex");
        _propertyAliasOf[_aliasKey(_pIndex,_val)] = _aliasName;
    }

    function setCeresDID(address _ceresDID) external onlyOwner {
        ceresDID = _ceresDID;
    }
}