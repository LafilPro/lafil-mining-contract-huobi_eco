// SPDX-License-Identifier: MIT

//-----------------------------------------------------------------------------------------------------------------------------------------
/**
  LaFil Mining Protocol
  more information seen by official website
    https://lafil.io
    https://mining.lafil.io
*/

//-----------------------------------------------------------------------------------------------------------------------------------------

pragma solidity 0.6.12;

/**
 * Contract module which provides a basic access control mechanism, where
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
contract Ownable {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner,address indexed newOwner);

    /**
     * Initializes the contract setting the deployer as the initial owner.
     */
    constructor(address theOwner) public {
        _owner = theOwner;
    }

    /**
     * Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == msg.sender, "Ownable: caller is not the owner");
        _;
    }

    /**
     * Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        _setOwner(newOwner);
    }

    function _setOwner(address newOwner) internal {
        require(newOwner != address(0),"Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

/**
 * Standard math utilities missing in the Solidity language.
 */
library Math {
    /**
     * Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a >= b ? a : b;
    }

    /**
     * Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow, so we distribute
        return (a / 2) + (b / 2) + (((a % 2) + (b % 2)) / 2);
    }
}

/**
 * Wrappers over Solidity's arithmetic operations with added overflow
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
     * Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a,uint256 b,string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
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
     * Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a,uint256 b,string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a,uint256 b,string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

/**
 * Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * Sets `amount` as the allowance of `spender` over the caller's tokens.
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
     * Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender,address recipient,uint256 amount) external returns (bool);

    /**
     * Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner,address indexed spender,uint256 value);
}

/**
 * Collection of functions related to the address type
 */
library Address {
    /**
     * Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly {
            size := extcodesize(account)
        }
        return size > 0;
    }

    /**
     * Replacement for Solidity's `transfer`: sends `amount` wei to
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
        require(address(this).balance >= amount,"Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{value: amount}("");
        require(success,"Address: unable to send value, recipient may have reverted");
    }

    /**
     * Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
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
    function functionCall(address target, bytes memory data)internal returns (bytes memory){
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target,bytes memory data,string memory errorMessage) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target,bytes memory data,uint256 value) internal returns (bytes memory) {
        return
        functionCallWithValue(target,data,value,"Address: low-level call with value failed");
    }

    /**
     * Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target,bytes memory data,uint256 value,string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value,"Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data)internal view returns (bytes memory){
        return
        functionStaticCall(target,data,"Address: low-level static call failed");
    }

    /**
     * Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target,bytes memory data,string memory errorMessage) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(bool success,bytes memory returndata,string memory errorMessage) private pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
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

/**
 * @title SafeERC20
 * Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token,address to,uint256 value) internal {
        _callOptionalReturn(token,abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token,address from,address to,uint256 value) internal {
        _callOptionalReturn(token,abi.encodeWithSelector(token.transferFrom.selector, from, to, value)
        );
    }

    /**
     * Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token,address spender,uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),"SafeERC20: approve from non-zero to non-zero allowance");
        _callOptionalReturn(token,abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token,address spender,uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token,abi.encodeWithSelector(token.approve.selector,spender,newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token,address spender,uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value,"SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token,abi.encodeWithSelector(token.approve.selector,spender,newAllowance));
    }

    /**
     * Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data,"SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)),"SafeERC20: ERC20 operation did not succeed");
        }
    }
}

/**
 * Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() internal {
        _status = _NOT_ENTERED;
    }

    /**
     * Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and make it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}

/**
 * Main Entry Contract
 */
contract LaFilMining is Ownable,ReentrancyGuard {
    
    using SafeMath for uint256;
    using SafeERC20 for IERC20;
    //                                        ----->> Constants <<-----
   
    uint256 constant internal INTERVAL = 86400;
    
    uint256 constant internal DEPOSIT_MIN = 1 ether;
    uint256 constant internal WITHDRAWAL_MIN = 1 ether / 20; 
    
    uint256 constant internal PRIMARY_DEPOSIT_LIMIT = 100 ether;
    uint256 constant internal DEPOSIT_LIMIT_STEP = 1 ether;
    uint256 constant internal BASE_INTEREST_RATE_LINE = 20 ether;
    
    uint256 constant internal VOLUME_STEP_FOR_INTEREST = 1 ether;
    
    
    uint256 constant internal p_MARKETING_FEE_POINTS = 800;                     
    uint256 constant internal p_DEVOPS_FEE_POINTS = 200;                        
    uint256 constant internal p_WITHDRAWAL_FEE_POINTS = 300; 
    
    uint256 internal p_MARKETING_BONUS_POINTS = 1000;
    uint256[] internal p_BONUS_POINTS_LIST = [3000,1000,700,700,700,500,500,500,500,500,300,300,300,300,300,300,300,300,300,300];                                     
                  
    uint256 constant internal p10000 = 10000; 
    
    //                                        ----->> Variables <<-----
    
    IERC20 public _depositToken;
    
    address payable internal ifAddr;
    address payable internal mkAddr;                              
    address payable internal doAddr;                                 
    address payable internal wsAddr; 
    address payable internal dfAddr;
    
    ContractStatistics internal _cntSts;
    InsuranceFundPool internal _insuranceFundPool;
    SafeguardFundPool internal _safeguardFundPool;
    mapping (address => User) internal _users;
    
    //                                        ----->> Structs <<-----
    
    struct Deposit { 
        uint32 time; 
        uint256 amount;                                        
    }   
    
    struct User {
        uint8 pBaseInstPts; 
        uint16 downlineCount;
        uint32 lastCheckPoint;                                           
        uint256 deposited;                                               
        uint256 withdrawn; 
        uint256 bonus;
        uint256 activeValue;
        uint256 surplus;
        address payable upline;
        Deposit[] deposits;
    }
    
    struct ContractStatistics {
            uint32 usersNumber; 
            uint256 deposited;                                                
            uint256 withdrawn;                                                
            uint256 bonus;
    }
    
    struct InsuranceFundPool {
        bool enabled;
        uint256 balance;
        uint256 collected;
        uint256 lent;
    }
    
    struct SafeguardFundMember {
        uint256 input;
        uint256 output;
    }
    
    struct SafeguardFundPool {
        uint256 totalInput;
        uint256 totalOutput;
        mapping (address => SafeguardFundMember) members;
    }
    
    //                                        <<----->> Public Functions <<----->>  
    
    //>> Contract Initialization
    constructor(IERC20 depositToken,address payable insuranceFundAddress,address payable marketingAddress, address payable devopsAddress, address payable withdrawalServiceAddress) public Ownable(msg.sender){
        _depositToken = depositToken;
        dfAddr = msg.sender;
        ifAddr = insuranceFundAddress;
        mkAddr = marketingAddress;
        doAddr = devopsAddress;
        wsAddr = withdrawalServiceAddress;
        
        _cntSts = ContractStatistics(0,0,0,0);
        _insuranceFundPool = InsuranceFundPool(true,0,0,0);
        _safeguardFundPool = SafeguardFundPool(0,0);
    }
    
    //>> To send deposit request
    function deposit(uint256 amt,address payable uplAddr) public payable nonReentrant {
        require(!Address.isContract(msg.sender) && msg.sender == tx.origin && msg.sender!=dfAddr,"Auth fails");
        uint32 time = uint32(block.timestamp);
        
        //1.amount check
        require(amt >= DEPOSIT_MIN, "There is a minimum deposit amount limit");
        _depositToken.safeTransferFrom(msg.sender, address(this), amt);
        
        User storage user = _users[msg.sender];
        require(amt <= depositLimit(user), "The request exceeds available deposit limit");
        
        //2.pay the marketing and devops service fee
        _depositToken.safeTransfer(mkAddr,amt.mul(p_MARKETING_FEE_POINTS).div(p10000));
        _depositToken.safeTransfer(doAddr,amt.mul(p_DEVOPS_FEE_POINTS).div(p10000));
        
        //3.user statistics update
        if(user.upline == address(0)){            // new user, to initialize some parameters
            //a.
            User storage uplUser = _users[uplAddr];
            if(msg.sender!=uplAddr && uplUser.deposited>0){
                uplUser.downlineCount++;
                uplUser.activeValue = uplUser.activeValue.add(amt);
                user.upline = uplAddr;
            }else{
                user.upline = dfAddr;
            }
            //b.
            user.pBaseInstPts = amt < BASE_INTEREST_RATE_LINE ? 60 : 100;
            user.lastCheckPoint = time;
            _cntSts.usersNumber++;
            emit NewUser(msg.sender,amt);
        }else{                                   // old user, to settle the reward produced as a surplus
            uint256 inst = calInst(user);
            if(inst > 0){
                user.surplus = user.surplus.add(inst);
                user.lastCheckPoint = time;
            }
        }
        
        user.deposits.push(Deposit(time,amt));
        user.deposited = user.deposited.add(amt);
        user.activeValue = user.activeValue.add(amt);
        
        //4.contract statistics update
        _cntSts.deposited = _cntSts.deposited.add(amt);
        uint256 mkBonus = sendMarketingBonus(user.upline,amt.mul(p_MARKETING_BONUS_POINTS).div(p10000),0);
        if(mkBonus > 0) _cntSts.bonus = _cntSts.bonus.add(mkBonus);
        
        emit Deposited(msg.sender,amt);
    }
    
    //>> To send withdrawal request
    function withdraw() public nonReentrant returns (uint256,uint256,uint256,uint256){
        //1.withdrawal conditions check
        User storage user = _users[msg.sender];
        uint256 interest = calInst(user);
        require(interest > WITHDRAWAL_MIN, "No interest available to withdraw");
        withdrawalAmountCheck(user,interest);
        
        //2.pay the withdrawal service fee
        uint32 time = uint32(block.timestamp);
        uint256 wf = time < uint256(user.lastCheckPoint).add(INTERVAL.mul(7)) ? interest.div(5) : interest.mul(p_WITHDRAWAL_FEE_POINTS).div(p10000);
        _depositToken.safeTransfer(wsAddr,wf);
        uint256 amt = interest.sub(wf);
        
        //3.user statistics update
        user.withdrawn = user.withdrawn.add(interest);
        user.activeValue = user.activeValue > interest ? user.activeValue.sub(interest) : 0 ;
        user.lastCheckPoint = time;
        
        //4.send the marketing bonus and fund update
        uint256 fund = amt.mul(3000).div(p10000);
        amt = amt.sub(fund);
        
        uint256 totalBonus = 0;
        uint256 bonusBase = amt.div(p10000);
        address payable upline = user.upline;
        for(uint8 i = 0 ; i < 20 ; i++){
            if(upline==dfAddr)break;
            uint8 level = i + 1;
            uint256 mkBonus = bonusBase.mul(p_BONUS_POINTS_LIST[i]);
            totalBonus = sendMarketingBonus(upline,mkBonus,level).add(totalBonus);
            upline = _users[upline].upline;
        }
        fund = fund.add(totalBonus.mul(3000).div(7000));
        
        if(_insuranceFundPool.enabled){
            _insuranceFundPool.balance = _insuranceFundPool.balance.add(fund);
            _insuranceFundPool.collected = _insuranceFundPool.collected.add(fund);
        }
        
        //5.contract statistics update
        _cntSts.bonus = _cntSts.bonus.add(totalBonus);
        _cntSts.withdrawn = _cntSts.withdrawn.add(amt);
        
        _depositToken.safeTransfer(msg.sender,amt);
        emit Withdrawn(msg.sender,amt);
        
        return (interest,wf,fund,totalBonus);
    }

    //                                        ----->> User Statistics <<-----
    
    //>> Getting user statistics with specific address  
    function userStatistics(address addr) public view returns (uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,address){
        address ad = addr;
        User storage user = _users[ad];
        return (calInst(user), pInstPtsForActVal(user.activeValue), user.pBaseInstPts , user.surplus , user.deposited , user.withdrawn , user.bonus , user.activeValue , user.downlineCount ,  user.lastCheckPoint , user.deposits.length , depositLimit(user) , user.upline);
    }
    
    //>> Getting a deposit record information
    function depositInfo(address addr,uint256 index) public view returns (uint256,uint256) {
        User storage user = _users[addr];
        require(user.deposited>0,"The address provided hasn't been registered in this contract.");
        require(user.deposits.length>0,"No deposit found.");
        Deposit[] storage deposits = user.deposits;
        Deposit storage dp = deposits[index];
        return (dp.amount,dp.time);
    }
    
    //>> To calculate user interest by serveral parameters provided
    function calculateInterest(uint256 amtDpd , uint256 amtWdn ,uint256 pInstPts , uint256 surplus , uint256 periods) public pure returns (uint256) {
        if(periods == 0) return surplus;
        if(periods > 180) periods = 180;
        
        uint256 deduction = amtWdn.div(5);
        if(deduction >= amtDpd) return surplus;
        uint256 dpd = amtDpd;
        uint256 wdn = amtWdn;
        uint256 cdl = dpd.sub(deduction);
        
        for(uint8 i = 0 ; i < periods ; i++){
            uint256 istPts = pInstPts;
            if(wdn.mul(2) > dpd){
                uint256 dd = dpd.mul(150).div(100);
                if(wdn > dd){
                    istPts = istPts.div(2**(wdn.sub(dd).div(dpd)).mul(4));
                }else{
                    istPts = istPts.div(2);
                } 
            }
            uint256 inst = cdl.mul(istPts).div(p10000);
            wdn = wdn.add(inst);
            cdl = cdl.sub(inst.div(5));
        }
        uint256 maxWithdrawal = dpd.mul(5);
        uint256 interest = wdn.sub(amtWdn).add(surplus);
        if(periods>=30) interest = interest.add(interest.div(10));
        if(wdn > maxWithdrawal) interest = maxWithdrawal.sub(amtWdn);
        return interest;
    }
    
    //                                        ----->> Contract Statistics <<----- 
    
    //>> Getting contract statistics
    function contractStatistics() public view returns (uint256,uint256,uint256,uint256,uint256,uint256){
        return (cntBal() , availableContractBalance() , _cntSts.deposited , _cntSts.withdrawn , _cntSts.bonus , _cntSts.usersNumber);
    }
    
    //>> Getting TronExBank project support team addresses
    function supportTeam() public view onlyOwner returns (address,address,address,address,address,address){
        return (ifAddr,dfAddr,mkAddr,doAddr,wsAddr,owner());
    }
    
    //                                        ----->> Insurance Fund <<-----
    
    //>> Getting insurance fund pool information
    function insuranceFundPoolInfo() public view returns (bool,uint256,uint256,uint256){
        return (_insuranceFundPool.enabled,_insuranceFundPool.balance,_insuranceFundPool.collected,_insuranceFundPool.lent);
    }
    
    //>> To deploy the fund
    function deployInsuranceFund(uint256 amt) public {
        require(msg.sender == ifAddr && msg.sender == tx.origin,"Auth fails");
        require(_insuranceFundPool.enabled && amt <= _insuranceFundPool.balance,"The insurance fund is not enabled or balance not enough to deploy");
        _insuranceFundPool.balance = _insuranceFundPool.balance.sub(amt);
        _depositToken.safeTransfer(ifAddr,amt);
        emit InsuranceFundTransfered(amt);
    }
    
    //>> lend 
    function lend(uint256 amt) public returns (bool){
        require(msg.sender == ifAddr && msg.sender == tx.origin,"Auth fails");
        require(_insuranceFundPool.enabled,"The insurance fund is not enabled");
        require(amt <= availableContractBalance().mul(30).div(100),"The lending amount exceeds 30% of the available contract balance");
        _insuranceFundPool.enabled = false;
        _insuranceFundPool.lent = amt;
        _depositToken.safeTransfer(ifAddr,amt);
        emit InsuranceFundLent(amt);
        return true;
    }
    
    //>> repay
    function repay() public payable returns (bool){
        uint256 amt = _insuranceFundPool.lent;
        _depositToken.safeTransferFrom(msg.sender,address(this),amt);
        _insuranceFundPool.enabled = true;
        _insuranceFundPool.lent = 0;
        emit InsuranceFundRepay(amt);
        return true;
    }
    
    //>>                                        ----->> Safe Guard Pool <<-----
    
    //>> Getting safeguard fund pool information
    function safeguardFundPoolInfo() public view onlyOwner returns (uint256,uint256,uint256){
        uint256 input = _safeguardFundPool.totalInput;
        uint256 output = _safeguardFundPool.totalOutput;
        uint256 available = input > output ? input.sub(output) : 0;
        return (available,input,output);
    }
    
    //>> Getting the member information of safeguard fund pool
    function sdfMbrInfo() public view returns (uint256,uint256,uint256){
        SafeguardFundMember storage sfdMbr = _safeguardFundPool.members[msg.sender];
        uint256 input = sfdMbr.input;
        uint256 output = sfdMbr.output;
        uint256 available = input > output ? input.sub(output) : 0;
        return (available,input,output);
    }
    
    //>> Transfering into safeguard fund pool
    function sfd_in(uint256 amt) public payable returns (uint256,uint256){
        require(!Address.isContract(msg.sender) && msg.sender == tx.origin,"Auth fails");
        _depositToken.safeTransferFrom(msg.sender,address(this),amt);
        
        SafeguardFundMember storage sfdMbr = _safeguardFundPool.members[msg.sender];
        sfdMbr.input = sfdMbr.input.add(amt);
        _safeguardFundPool.totalInput = _safeguardFundPool.totalInput.add(amt);
        
        emit SafeguardFundInput(msg.sender,amt);
        
        return (sfdMbr.input,sfdMbr.output);
    }
    
    //>> Transfering out from safeguard fund pool
    function sfd_out(uint256 amt) public returns (uint256,uint256) {
        SafeguardFundMember storage sfdMbr = _safeguardFundPool.members[msg.sender];
        require(sfdMbr.input>0,"Access denied");
        
        uint256 out = amt.add(sfdMbr.output);
        require(sfdMbr.input>=out,"No sufficient fund to transfer outwards");
        
        require(amt <= availableContractBalance(),"The available contract balance is not enough");
        
        sfdMbr.output = out;
        _safeguardFundPool.totalOutput = _safeguardFundPool.totalOutput.add(amt);
        
        _depositToken.safeTransfer(msg.sender,amt);
        emit SafeguardFundOutput(msg.sender,amt);
        
        return (sfdMbr.input,sfdMbr.output);
    }
    
    //                                        <<----- Internal Functions ----->>

    function calInst(User memory user) internal view returns (uint256) {
        return calculateInterest(user.deposited , user.withdrawn , pInstPtsForActVal(user.activeValue).add(user.pBaseInstPts) , user.surplus , uint32(now.sub(user.lastCheckPoint).div(INTERVAL)));
    }
    
    function pInstPtsForActVal(uint256 actVal) internal pure returns (uint256) {
        uint256 pInstPts =  actVal.div(VOLUME_STEP_FOR_INTEREST);
        if(pInstPts > 500) pInstPts = 500;
        return pInstPts;
    }
    
    function cntBal() internal view returns (uint256){
        return _depositToken.balanceOf(address(this));
    }
    
    function availableContractBalance() internal view returns (uint256){
        uint256 bal = cntBal();
        return bal>_insuranceFundPool.balance ? bal.sub(_insuranceFundPool.balance) : 0;
    }
    
    function depositLimit(User memory user) internal pure returns (uint256) {
        if(user.deposited==0)return PRIMARY_DEPOSIT_LIMIT;
        return PRIMARY_DEPOSIT_LIMIT.add(uint256(user.downlineCount).mul(DEPOSIT_LIMIT_STEP)).sub(user.deposited);
    }
    
    function sendMarketingBonus(address payable addr,uint256 amt,uint256 level) internal returns (uint256){
        if(amt > availableContractBalance()) return 0;
        
        User storage user = _users[addr];
        
        if(level>0 && user.downlineCount<level)return 0;
        
        uint256 dpd = user.deposited;
        uint256 maxBonus = dpd.mul(3);
        if(user.withdrawn<dpd.mul(5) && user.bonus<maxBonus){   
            if(amt.add(user.bonus) > maxBonus) amt = maxBonus.sub(user.bonus);
            user.bonus = user.bonus.add(amt);
            if(level>0) amt = amt.mul(7000).div(p10000);
            _depositToken.safeTransfer(addr,amt);
            emit BonusReceived(addr,tx.origin,level,amt);
            return amt;
        }
        return 0;
    }
    
    function withdrawalAmountCheck(User storage user,uint256 amt) internal view returns (uint256){
        uint256 bal = availableContractBalance();
        require(amt.mul(2) < bal ,"Available  balance of contract is not sufficient for the withdrawal request very possiblely.");
        if(bal < 2000 ether) require(user.withdrawn < user.deposited , "Withdraw limit happens when your accumulative total withdraw has been more than 100% of your deposit and the contract balance available is less than 500000.");
        if(bal < 1000 ether) require(user.withdrawn.mul(2) < user.deposited , "Withdraw limit happens when your accumulative total withdraw has been more than 50% of your deposit and the contract balance available is less than 200000.");
        return bal;
    }
    
    //                                        ----->> Events <<-----
    
    event NewUser(address indexed addr, uint256 amt);
    event Deposited(address indexed addr, uint256 amt);
    event Withdrawn(address indexed addr, uint256 amt);
    event BonusReceived(address indexed addr, address dpAddr, uint256 level, uint256 amt);
    
    event InsuranceFundTransfered(uint256 amt);
    event InsuranceFundLent(uint256 amt);
    event InsuranceFundRepay(uint256 amt);
    event SafeguardFundInput(address indexed addr,uint256 amt);
    event SafeguardFundOutput(address indexed addr,uint256 amt);
}
