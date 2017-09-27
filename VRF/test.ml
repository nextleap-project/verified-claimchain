open Prims

open Spec_VRF


let createBuffer (length: nat) (value: FStar_UInt8.t) : FStar_UInt8.t FStar_Seq_Base.seq = 
FStar_Seq_Base.create (Prims.parse_int (to_string length)) value 

let createTwistedEdwardPoint (a: Prims.int)  (b : Prims.int) (c : Prims.int) (d : Prims.int) : Spec_Ed25519.ext_point  =  
(a,b,c,d)

let printTwistedEdwardPoint (point: Spec_Ed25519.ext_point) = 
  match point with 
  | (px, py, pz, pt) -> Printf.printf "point: %s %s %s %s" (to_string px)  (to_string py) (to_string pz) (to_string pt)

let one = Prims.parse_int "1"
let zero = Prims.parse_int "0" 

let printUint8 (a: FStar_UInt8.t)  = 
Printf.printf " %s " (FStar_UInt8.to_string a)

let printSeqUInt8 (a:  FStar_UInt8.t FStar_Seq_Base.seq) = 
  let length = FStar_Seq_Base.length a in 
    let rec print_inside a counter = 
      if counter < FStar_Seq_Base.length a then 
        (
          printUint8 (FStar_Seq_Base.index a counter);
          print_inside a (counter + one)
        )
      else 
        Printf.printf "\n" 
in print_inside a zero 

(*)
let print_test_values =
	let n = Prims.parse_int "10" in
	let result = test_stuff n in
	List.iter (fun (i,k,gsum,gk) -> 
		let to_s bytes = String.concat " " (List.map FStar_UInt8.to_string bytes) in
		let opt_s = function None -> "None" | Some (x,y,w,t) -> to_string x ^ " " ^ to_string y ^ " " ^ to_string w ^ " " ^ to_string t in
		Printf.printf "i : %s, k : %s, gsum : %s, gk : %s" (to_string i) (to_string k) (opt_s gsum) (opt_s gk)
		) result
*)


let test_ECVRF_verify = 
	let privateKeyInt = (Prims.parse_int "21") in
	let privateKeyBytes = (_I2OSP privateKeyInt (Prims.parse_int "32")) in 
	let privateKeyBytesLE = little_endian_ privateKeyBytes in 
	let publicKey = (pointMultiplication generator privateKeyBytesLE) in 
	let buffer0 = createBuffer (Prims.parse_int "32") (FStar_UInt8.of_string "8") in 
    let buffer1 = createBuffer (Prims.parse_int "32") (FStar_UInt8.of_string "9")   in  
	let pi = _ECVRF_prove buffer0 publicKey privateKeyBytes in  				 
    if (FStar_Option.isNone pi) then 
      Printf.printf "%s" "None"
    else 
       let pi = FStar_Option.get pi in   
       	printSeqUInt8 pi;  
    let result = _ECVRF_verify publicKey pi buffer0 in 
    	Printf.printf "%b" result  	

