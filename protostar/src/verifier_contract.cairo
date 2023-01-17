%lang starknet
// %builtins syscall pedersen range_check

from starkware.starknet.common.syscalls import get_contract_address
from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.cairo.common.bool import FALSE, TRUE
from starkware.cairo.common.math import assert_nn, unsigned_div_rem
from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.serialize import serialize_word

from alt_bn128_g1 import G1Point, ec_add, ec_mul
from alt_bn128_g2 import G2Point
from alt_bn128_pair import pairing
from alt_bn128_field import FQ12, is_zero, FQ2, fq12_diff, fq12_eq_zero, fq12_mul, fq12_one
from bigint import BigInt3

struct VerifyingKey {
    alfa1 : G1Point,      
    beta2 : G2Point,      
    gamma2 : G2Point, 
    delta2 : G2Point, 
    IC : G1Point*,
    IC_length : felt,
}

struct Proof {
	A : G1Point, 
	B : G2Point, 
	C : G1Point, 
}

// Auxiliary functions (Builders)
// Creates a G1Point from the received felts: G1Point(x,y)
func BuildG1Point{range_check_ptr : felt}(x1 : felt, x2 : felt, x3 : felt, y1 : felt, y2 : felt, y3 : felt) -> (r: G1Point){
    alloc_locals;
    let X : BigInt3 = BigInt3(x1,x2,x3);
    let Y : BigInt3 = BigInt3(y1,y2,y3);

    return (r = G1Point(X,Y));
}
        
// Creates a G2Point from the received felts: G2Point([a,b],[c,d])
func BuildG2Point{range_check_ptr : felt}(a1 : felt, a2 : felt, a3 : felt, b1 : felt, b2 : felt, b3 : felt, c1 : felt, c2 : felt, c3 : felt, d1 : felt, d2 : felt, d3 : felt) -> (r : G2Point){
    alloc_locals;
    let A : BigInt3 = BigInt3(a1,a2,a3);
    let B : BigInt3 = BigInt3(b1,b2,b3);
    let C : BigInt3 = BigInt3(c1,c2,c3);   
    let D : BigInt3 = BigInt3(d1,d2,d3);

    let x : FQ2 = FQ2(B,A);
    let y : FQ2 = FQ2(D,C);

    return (r = G2Point(x, y));
}

// Returns negated BigInt3
func negateBigInt3{range_check_ptr : felt}(n : BigInt3) -> (r : BigInt3){
    let (_, nd0) = unsigned_div_rem(n.d0, 60193888514187762220203335);
    let d0 = 60193888514187762220203335 -nd0;
    let (_, nd1) = unsigned_div_rem(n.d1, 104997207448309323063248289);
    let d1 = 104997207448309323063248289 -nd1;
    let (_, nd2) = unsigned_div_rem(n.d2, 3656382694611191768777987);
    let d2 = 3656382694611191768777987 -nd2;

    return(r = BigInt3(d0,d1,d2));
}

// Returns negated G1Point(addition of a G1Point and a negated G1Point should be zero)
func negate{range_check_ptr : felt}(p : G1Point) -> (r: G1Point){
    alloc_locals;
    let x_is_zero : felt = is_zero(p.x);
	if (x_is_zero == TRUE) {
        let y_is_zero : felt = is_zero(p.y);
		if (y_is_zero == TRUE) {
            return (r = G1Point(BigInt3(0,0,0),BigInt3(0,0,0)));
        }
    }

    let neg_y : BigInt3 = negateBigInt3(p.y);
    return (r = G1Point(p.x, neg_y));
}

// Computes the pairing for each pair of points in p1 and p2, multiplies each new result and returns the final result
// pairing_result should iniially be an fq12_one
func compute_pairings{range_check_ptr : felt}(p1 : G1Point*, p2 : G2Point*, pairing_result : FQ12, position : felt, length : felt) -> (result : FQ12){
    if (position != length) {
        let current_pairing_result : FQ12 = pairing(p2[position], p1[position]);
        let mul_result : FQ12 = fq12_mul(pairing_result, current_pairing_result);

        return compute_pairings(p1, p2,mul_result, position+1, length);
    }
    return(result = pairing_result);
}

// Returns the result of computing the pairing check
func pairings{range_check_ptr : felt}(p1 : G1Point*, p2: G2Point*, length : felt) -> (r : felt) {
    alloc_locals;
    assert_nn(length);
    let initial_result : FQ12 = fq12_one();
    let pairing_result : FQ12 = compute_pairings(p1,p2,initial_result,0,length);

    let one : FQ12 = fq12_one();
    let diff : FQ12 = fq12_diff(pairing_result, one);
    let result : felt = fq12_eq_zero(diff);
    return(r = result);

}

// Pairing check for four pairs
func pairingProd4{range_check_ptr : felt}(a1 : G1Point, a2 : G2Point, b1 : G1Point, b2 : G2Point, c1 : G1Point, c2 : G2Point, d1 : G1Point, d2 : G2Point) -> (r : felt){
    let (p1 : G1Point*) = alloc();
    let (p2 : G2Point*) = alloc();

    assert p1[0] = a1;
    assert p1[1] = b1;
    assert p1[2] = c1;
    assert p1[3] = d1;

    assert p2[0] = a2;
    assert p2[1] = b2;
    assert p2[2] = c2;
    assert p2[3] = d2;

    return pairings(p1,p2,4);
}

func verifyingKey{range_check_ptr : felt}() -> (vk : VerifyingKey) {
    alloc_locals;
	let alfa1 : G1Point = BuildG1Point(
        4128632272367203679867622, 59316817566498460416086069, 3365667018767545775131225,
        69628749977975432876719432, 212134230527877088973743, 1075080431125946600950867
    );

    let beta2 : G2Point = BuildG2Point(
        52011725285810035473763165, 54295241303750663612856864, 855464291522136583602551,
        70081545844137829002204336, 2511906413928923024452533, 1691997074693486054649924,
        4537538041209377186537467, 24947520614210272376506580, 3071346993298696983506611,
        17994271894161191434014939, 49856466110497178836537250, 2887063480940427602724375
    );

    let gamma2 : G2Point = BuildG2Point(
        50657168248156029357068994, 75996009454876762764004566, 1931027739743020521039371,
        37301332318871981678327533, 1933688095072267321168861, 1813645754675075253282464,
        62330281573273320105875291, 46796958261627355650117058, 681950549513863929186793,
        4625471277591146859756970, 7264017464802134638568497, 1419180249680038923119287
    );
    let delta2 : G2Point = BuildG2Point(
        59029551946905996687139647, 10635795411383158388757996, 3394954252780198474753723,
        55556321251482204824499066, 14411815194499862502303927, 991678603497082678317083,
        10492808113093199653976063, 40319643329156450904203002, 1455914935118052809315061,
        19453565443744424783203405, 73535876413782221574839063, 2785923207387608827358665
    );
        
    let (IC : G1Point*) = alloc();
    
    let point_0 : G1Point =  BuildG1Point( 
        50356480864665616340790615, 66413467357508129376590561, 240810614190059188556337,
        39375195015652531028999878, 49295805580131804920830610, 2366913347462842214243150);
    assert IC[0] =  point_0             ;                      
    
    let point_1 : G1Point =  BuildG1Point( 
        77148511171766230904552821, 59066045416753182757480107, 683460483585951091873934,
        56114984742584415013512256, 13261991128747846248358577, 1028073059353397348829225);
    assert IC[1] =  point_1;                      
    
    let IC_length : felt = 2;

    return(vk = VerifyingKey(alfa1, beta2, gamma2, delta2, IC, IC_length));

}
    
// Computes the linear combination for vk_x
func vk_x_linear_combination{range_check_ptr : felt}( vk_x : G1Point, input : BigInt3*, position : felt, length : felt, IC : G1Point*) -> (result_vk_x : G1Point) {
    if (position != length) {
        let mul_result : G1Point = ec_mul(IC[position + 1], input[position]);
        let add_result : G1Point = ec_add(vk_x, mul_result);
    
        return vk_x_linear_combination(add_result, input, position + 1, length,  IC);
    }
        return(result_vk_x = vk_x);
}

func verify{range_check_ptr : felt}(input : BigInt3*, proof: Proof, input_len : felt) -> (r : felt){
    alloc_locals;
    let vk : VerifyingKey = verifyingKey();
    assert input_len = vk.IC_length + 1;
    let initial_vk_x : G1Point = BuildG1Point(0, 0, 0, 0, 0, 0);
    let computed_vk_x : G1Point = vk_x_linear_combination(initial_vk_x, input, 0, vk.IC_length - 1, vk.IC);
    let vk_x : G1Point = ec_add(computed_vk_x, vk.IC[0]);

    let neg_proof_A : G1Point = negate(proof.A);
    return pairingProd4(neg_proof_A, proof.B , vk.alfa1, vk.beta2, vk_x, vk.gamma2, proof.C, vk.delta2);

}

// Fills the empty array output with the BigInt3 version of each number in input
func getBigInt3array{range_check_ptr : felt}(input : felt*, output : BigInt3*, input_position, output_position, length){
    if (output_position != length) {
        let big_int : BigInt3 = BigInt3(input[input_position], input[input_position + 1], input[input_position +2]);
        assert output[output_position] = big_int;

        getBigInt3array(input,output,input_position+3, output_position+1,length);
        return();
    }
    return();
}

// a_len, b1_len, b2_len and c_len are all 6, input_len would be 3 * amount of inputs
//  @external
func verifyProof{pedersen_ptr : HashBuiltin*, range_check_ptr : felt}(a_len : felt, a : felt*, b1_len : felt, b1 : felt*, b2_len : felt, b2 : felt*,
                                         c_len : felt, c : felt*, input_len : felt, input : felt*) -> (r : felt) {
    alloc_locals;
    let A : G1Point = BuildG1Point(a[0], a[1], a[2], a[3], a[4], a[5]);
    let B : G2Point = BuildG2Point(b1[0], b1[1], b1[2], b1[3], b1[4], b1[5], b2[0], b2[1], b2[2], b2[3], b2[4], b2[5]);
    let C : G1Point = BuildG1Point(c[0], c[1], c[2], c[3], c[4], c[5]);

    let (big_input : BigInt3*) = alloc();
    getBigInt3array(input, big_input, 0, 0, input_len/3);

    let proof : Proof = Proof(A, B, C);
    let result : felt = verify(big_input, proof, input_len);
    return(r = result);

}

@external
func verify_static{syscall_ptr: felt*, pedersen_ptr : HashBuiltin*, range_check_ptr: felt}() -> (res:felt) {

    let (a_ptr: felt*) = alloc();
    assert[a_ptr] =     16435458185497151578792433;
    assert[a_ptr + 1] = 40172872974813924995536275;
    assert[a_ptr + 2] = 3258538799375934883692565;
    assert[a_ptr + 3] = 21845360519278039434162382;
    assert[a_ptr + 4] = 37032914906954177889717841;
    assert[a_ptr + 5] = 422447693251006666742151;

    //  let (b1_ptr: felt*) = alloc()
    //  assert[b1_ptr] =     39203446000482540257637925
    //  assert[b1_ptr + 1] = 8372331185708158742649818
    //  assert[b1_ptr + 2] = 1940944301260288891776770
    //  assert[b1_ptr + 3] = 14539866263615908413985012
    //  assert[b1_ptr + 4] = 28351972057156804035626776
    //  assert[b1_ptr + 5] = 3102459511026671344229042

    //  let (b2_ptr: felt*) = alloc()
    //  assert[b2_ptr] =     61583281797485710770918457
    //  assert[b2_ptr + 1] = 6382783199640232524620208
    //  assert[b2_ptr + 2] = 1641855124893934125318615
    //  assert[b2_ptr + 3] = 69691338484345404523556820
    //  assert[b2_ptr + 4] = 25590015895417664527867300
    //  assert[b2_ptr + 5] = 1131355528622211432153452

    let (b1_ptr: felt*) = alloc();
    assert[b1_ptr] =    14539866263615908413985012;
    assert[b1_ptr + 1] = 28351972057156804035626776;
    assert[b1_ptr + 2] = 3102459511026671344229042;
    assert[b1_ptr + 3] = 39203446000482540257637925;
    assert[b1_ptr + 4] = 8372331185708158742649818;
    assert[b1_ptr + 5] = 1940944301260288891776770;

    let (b2_ptr: felt*) = alloc();
    assert[b2_ptr] =    69691338484345404523556820;
    assert[b2_ptr + 1] = 25590015895417664527867300;
    assert[b2_ptr + 2] = 1131355528622211432153452;
    assert[b2_ptr + 3] = 61583281797485710770918457;
    assert[b2_ptr + 4] = 6382783199640232524620208;
    assert[b2_ptr + 5] = 1641855124893934125318615;


    let (c_ptr: felt*) = alloc();
    assert[c_ptr] =     37449182766458286666487412;
    assert[c_ptr + 1] = 67949700759915101588395634;
    assert[c_ptr + 2] = 1615312652241491981991622;
    assert[c_ptr + 3] = 18053195823741242528076033;
    assert[c_ptr + 4] = 63793431666194470068739038;
    assert[c_ptr + 5] = 2763392202904072211382205;

    let (input_ptr: felt*) = alloc();
    assert [input_ptr] = 33;
    assert [input_ptr + 1] = 0;
    assert [input_ptr + 2] = 0;

    let res : felt = verifyProof(6, a_ptr, 6, b1_ptr, 6, b2_ptr, 6, c_ptr, 3, input_ptr);
    return (res,);
}