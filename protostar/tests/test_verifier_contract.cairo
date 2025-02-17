%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.cairo.common.alloc import alloc

@contract_interface
namespace IContract {
    func verify_static() -> (res: felt) {
    }
}

@view
func __setup__{syscall_ptr: felt*, range_check_ptr}() {
    alloc_locals;
    local contract_address: felt;
    %{
        context.contract_address = deploy_contract("./src/verifier_contract.cairo",).contract_address
        ids.contract_address = context.contract_address
    %}
    return ();
}

@external
func test_verify_static{syscall_ptr: felt*, range_check_ptr, pedersen_ptr: HashBuiltin*}() {
    alloc_locals;
    local contract_address: felt;
    %{ ids.contract_address = context.contract_address %}
    let (res) = IContract.verify_static(contract_address=contract_address);
    assert res = 1;
    return ();
}
