open Prims
type bytes = FStar_UInt8.t FStar_Seq_Base.seq
type key = Prims.unit FStar_Endianness.lbytes
let field: Prims.int = Spec_Curve25519.prime
let n: Prims.int = Prims.parse_int "32"
let d: Prims.int =
  Prims.parse_int
    "37095705934669439343138083508754565189542113879843219016388785533085940283555"
type twisted_edward_point = Spec_Ed25519.ext_point
let scalarMultiplication:
  twisted_edward_point -> bytes -> Spec_Ed25519.ext_point =
  fun point  -> fun k1  -> Spec_Ed25519.point_mul k1 point
let scalarAddition:
  twisted_edward_point -> twisted_edward_point -> Spec_Ed25519.ext_point =
  fun p  -> fun q1  -> Spec_Ed25519.point_add p q1
let isPointOnCurve: twisted_edward_point option -> Prims.bool =
  fun point  ->
    if FStar_Option.isNone point
    then false
    else
      (match FStar_Option.get point with
       | (px,py,pz,pt) ->
           (Spec_Curve25519.fsub (Spec_Curve25519.fmul px px)
              (Spec_Curve25519.fmul py py))
             =
             (Spec_Curve25519.fadd (Spec_Curve25519.fmul pz pz)
                (Spec_Curve25519.fmul d (Spec_Curve25519.fmul pt pt))))
let serializePoint: twisted_edward_point -> Prims.unit Spec_Lib.lbytes =
  fun point  -> Spec_Ed25519.point_compress point
let deserializePoint: bytes -> Spec_Ed25519.ext_point option =
  fun b  -> Spec_Ed25519.point_decompress b
let _OS2ECP: bytes -> twisted_edward_point option =
  fun point  -> deserializePoint point
let _ECP2OS: twisted_edward_point -> bytes =
  fun gamma  -> serializePoint gamma
let nat_to_uint8: Prims.int -> FStar_UInt8.t =
  fun x  ->
    FStar_UInt8.uint_to_t (FStar_UInt.to_uint_t (Prims.parse_int "8") x)
let uint8_to_int: FStar_UInt8.t -> Prims.unit FStar_UInt.uint_t =
  fun x  -> FStar_UInt8.v x
let rec _helper_I2OSP:
  Prims.nat -> bytes -> Prims.nat -> FStar_UInt8.t FStar_Seq_Base.seq =
  fun value  ->
    fun s  ->
      fun counter  ->
        if
          (counter + (Prims.parse_int "1")) <
            (FStar_Seq_Base.length
               (FStar_Seq_Base.upd s counter
                  (nat_to_uint8 (value mod (Prims.parse_int "256")))))
        then
          _helper_I2OSP (value / (Prims.parse_int "256"))
            (FStar_Seq_Base.upd s counter
               (nat_to_uint8 (value mod (Prims.parse_int "256"))))
            (counter + (Prims.parse_int "1"))
        else
          FStar_Seq_Base.upd s counter
            (nat_to_uint8 (value mod (Prims.parse_int "256")))
let _I2OSP: Prims.nat -> Prims.int -> bytes =
  fun value  ->
    fun n1  ->
      if (Prims.pow2 (FStar_Mul.op_Star n1 (Prims.parse_int "8"))) <= value
      then
        FStar_Seq_Base.create n1
          (FStar_UInt8.uint_to_t (Prims.parse_int "0"))
      else
        _helper_I2OSP value
          (FStar_Seq_Base.create n1
             (FStar_UInt8.uint_to_t (Prims.parse_int "0")))
          (Prims.parse_int "0")
let rec _helper_OS2IP: bytes -> Prims.nat -> Prims.nat -> Prims.nat =
  fun s  ->
    fun counter  ->
      fun number  ->
        if (counter + (Prims.parse_int "1")) = (FStar_Seq_Base.length s)
        then
          number +
            ((Prims.pow2 (FStar_Mul.op_Star (Prims.parse_int "8") counter)) *
               (uint8_to_int (FStar_Seq_Base.index s counter)))
        else
          _helper_OS2IP s (counter + (Prims.parse_int "1"))
            (number +
               ((Prims.pow2 (FStar_Mul.op_Star (Prims.parse_int "8") counter))
                  * (uint8_to_int (FStar_Seq_Base.index s counter))))
let _OS2IP: bytes -> Prims.nat =
  fun s  -> _helper_OS2IP s (Prims.parse_int "0") (Prims.parse_int "0")

let seqConcat s1 s2 = FStar_Seq_Base.append s1 s2

let hash: bytes -> Spec_SHA2_256.bytes =
  fun input  -> Spec_SHA2_256.hash input
(*)
let _ECVRF_decode_proof: bytes -> (twisted_edward_point option* bytes* bytes)
  =
  fun pi  ->
    match FStar_Seq_Properties.split pi n with
    | (gamma,cs) ->
        (match FStar_Seq_Properties.split cs n with
         | (c,s) -> ((_OS2ECP gamma), c, s))

let rec _helper_ECVRF_hash_to_curve:
  Prims.nat -> Prims.nat -> bytes -> bytes -> twisted_edward_point option =
  fun ctr  ->
    fun counter_length  ->
      fun pk  ->
        fun input  ->
          if
            FStar_Option.isNone
              (_OS2ECP
                 (hash
                    (seqConcat (seqConcat input pk)
                       (_I2OSP ctr counter_length))))
          then None
          else
            if
              isPointOnCurve
                (_OS2ECP
                   (hash
                      (seqConcat (seqConcat input pk)
                         (_I2OSP ctr counter_length))))
            then
              _OS2ECP
                (hash
                   (seqConcat (seqConcat input pk)
                      (_I2OSP ctr counter_length)))
            else
              if (ctr + (Prims.parse_int "1")) < field
              then
                _helper_ECVRF_hash_to_curve (ctr + (Prims.parse_int "1"))
                  counter_length pk input
              else None
let _ECVRF_hash_to_curve:
  bytes -> twisted_edward_point -> twisted_edward_point option =
  fun input  ->
    fun public_key  ->
      _helper_ECVRF_hash_to_curve (Prims.parse_int "0") (Prims.parse_int "4")
        (_ECP2OS public_key) input
let random: Prims.nat -> Prims.nat =
  Obj.magic (fun max1  -> failwith "Not yet implemented:random")
let randBytes: Prims.nat -> bytes =
  fun max1  -> _I2OSP (random max1) (Prims.parse_int "32")
let _ECVRF_hash_points:
  twisted_edward_point ->
    twisted_edward_point ->
      twisted_edward_point ->
        twisted_edward_point ->
          twisted_edward_point -> twisted_edward_point -> Prims.nat
  =
  fun generator  ->
    fun h  ->
      fun public_key  ->
        fun gamma  ->
          fun gk  ->
            fun hk  ->
              _OS2IP
                (fst
                   (FStar_Seq_Properties.split
                      (hash
                         (seqConcat
                            (seqConcat
                               (seqConcat
                                  (seqConcat
                                     (seqConcat (_ECP2OS generator)
                                        (_ECP2OS h)) (_ECP2OS public_key))
                                  (_ECP2OS gamma)) (_ECP2OS gk)) (_ECP2OS hk)))
                      n))
let _ECVRF_prove:
  bytes ->
    twisted_edward_point -> bytes -> twisted_edward_point -> bytes option
  =
  fun input  ->
    fun public_key  ->
      fun private_key  ->
        fun generator  ->
          if FStar_Option.isNone (_ECVRF_hash_to_curve input public_key)
          then None
          else
            Some
              (seqConcat
                 (_ECP2OS
                    (scalarMultiplication
                       (FStar_Option.get
                          (_ECVRF_hash_to_curve input public_key))
                       private_key))
                 (seqConcat
                    (_I2OSP
                       (_ECVRF_hash_points generator
                          (FStar_Option.get
                             (_ECVRF_hash_to_curve input public_key))
                          public_key
                          (scalarMultiplication
                             (FStar_Option.get
                                (_ECVRF_hash_to_curve input public_key))
                             private_key)
                          (scalarMultiplication generator
                             (_I2OSP (random field) (Prims.parse_int "32")))
                          (scalarMultiplication
                             (FStar_Option.get
                                (_ECVRF_hash_to_curve input public_key))
                             (_I2OSP (random field) (Prims.parse_int "32"))))
                       n)
                    (_I2OSP
                       (((random field) + field) -
                          (((_ECVRF_hash_points generator
                               (FStar_Option.get
                                  (_ECVRF_hash_to_curve input public_key))
                               public_key
                               (scalarMultiplication
                                  (FStar_Option.get
                                     (_ECVRF_hash_to_curve input public_key))
                                  private_key)
                               (scalarMultiplication generator
                                  (_I2OSP (random field)
                                     (Prims.parse_int "32")))
                               (scalarMultiplication
                                  (FStar_Option.get
                                     (_ECVRF_hash_to_curve input public_key))
                                  (_I2OSP (random field)
                                     (Prims.parse_int "32"))))
                              * field)
                             mod field)) ((Prims.parse_int "2") * n))))
let _ECVRF_proof2hash: bytes -> FStar_UInt8.t FStar_Seq_Base.seq =
  fun pi  -> fst (FStar_Seq_Properties.split pi n)
let _ECVRF_verify:
  twisted_edward_point ->
    twisted_edward_point -> bytes -> bytes -> Prims.bool
  =
  fun generator  ->
    fun public_key  ->
      fun pi  ->
        fun input  ->
          match _ECVRF_decode_proof pi with
          | (gamma,c,s) ->
              if Prims.op_Negation (isPointOnCurve gamma)
              then false
              else
                if FStar_Option.isNone gamma
                then false
                else
                  if
                    FStar_Option.isNone
                      (_ECVRF_hash_to_curve input public_key)
                  then false
                  else
                    (_OS2IP c) =
                      (_ECVRF_hash_points generator
                         (FStar_Option.get
                            (_ECVRF_hash_to_curve input public_key))
                         public_key (FStar_Option.get gamma)
                         (scalarAddition (scalarMultiplication public_key c)
                            (scalarMultiplication generator s))
                         (scalarAddition
                            (scalarMultiplication (FStar_Option.get gamma) c)
                            (scalarMultiplication
                               (FStar_Option.get
                                  (_ECVRF_hash_to_curve input public_key)) s)))

*)

let one = Prims.parse_int "1"
let zero = Prims.parse_int "0"    



let createTwistedEdwardPoint (a: Prims.int)  (b : Prims.int) (c : Prims.int) (d : Prims.int) : Spec_Ed25519.ext_point  =  
(a,b,c,d)

let printTwistedEdwardPoint (point: Spec_Ed25519.ext_point) = 
  match point with 
  | (px, py, pz, pt) -> Printf.printf "point: %s %s %s %s" (to_string px)  (to_string py) (to_string pz) (to_string pt)


let testIsPointOnCurve (point: twisted_edward_point) = 
  let pointOpt = Some point in 
  let r = isPointOnCurve pointOpt in 
    printTwistedEdwardPoint point;  Printf.printf " is on the curve? %b" r                                  


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

let createBuffer (length: nat) (value: FStar_UInt8.t) : FStar_UInt8.t FStar_Seq_Base.seq = 
  FStar_Seq_Base.create (Prims.parse_int (to_string length)) value  

let bufferEqual (a: FStar_UInt8.t FStar_Seq_Base.seq) (b:FStar_UInt8.t FStar_Seq_Base.seq) = 
  let rec equal_inside a b counter = 
    if counter < FStar_Seq_Base.length a then 
        let flag = FStar_UInt8.eq (FStar_Seq_Base.index a counter) (FStar_Seq_Base.index b counter) in 
          if (flag = false) then false 
          else equal_inside a b (counter + one)
    else 
      true      
  in (FStar_Seq_Base.length a = FStar_Seq_Base.length b) && equal_inside a b zero    
                                  

(* test_vectors for _helper_I2OSP*)
let test_vector1_helper_i2osp : FStar_UInt8.t Prims.list = 
        [FStar_UInt8.uint_to_t (Prims.parse_int "160"); 
          FStar_UInt8.uint_to_t (Prims.parse_int "134");
          FStar_UInt8.uint_to_t (Prims.parse_int "1");]

let test_vector2_helper_i2osp : FStar_UInt8.t Prims.list = 
        [
        FStar_UInt8.uint_to_t (Prims.parse_int "160"); 
        FStar_UInt8.uint_to_t (Prims.parse_int "134"); 
        FStar_UInt8.uint_to_t (Prims.parse_int "1");
        FStar_UInt8.uint_to_t (Prims.parse_int "0");
        FStar_UInt8.uint_to_t (Prims.parse_int "56");
        FStar_UInt8.uint_to_t (Prims.parse_int "56");
        FStar_UInt8.uint_to_t (Prims.parse_int "56");
        ]

let check_helper_i2osp_1 (vector:FStar_UInt8.t Prims.list) =
      let buffer = createBuffer (Prims.parse_int "3") (FStar_UInt8.of_string "0") in 
      let result = _helper_I2OSP (Prims.parse_int "100000") buffer (Prims.parse_int "0") in 
          printSeqUInt8 result;
      let expected = (FStar_Seq_Properties.createL vector) in 
          printSeqUInt8 expected;
          Printf.printf "Test returned %B \n" (bufferEqual expected result);
     bufferEqual expected result

let check_helper_i2osp_2 (vector:FStar_UInt8.t Prims.list) =
      let buffer = createBuffer (Prims.parse_int "7") (FStar_UInt8.of_string "0") in 
      let result = _helper_I2OSP (Prims.parse_int "15824411865220768") buffer (Prims.parse_int "0") in 
          printSeqUInt8 result;
      let expected = (FStar_Seq_Properties.createL vector) in 
          printSeqUInt8 expected;
          Printf.printf "Test returned %B \n" (bufferEqual expected result);
     bufferEqual expected result

let check_i2osp_1 (vector:FStar_UInt8.t Prims.list) = 
    let result = _I2OSP (Prims.parse_int "15824411865220768") (Prims.parse_int "7") in 
      printSeqUInt8 result;
    let expected = (FStar_Seq_Properties.createL vector) in
      printSeqUInt8 expected;
      Printf.printf "Test returned %B \n" (bufferEqual expected result);
    bufferEqual expected result


let check_osp2i_1 (vector:FStar_UInt8.t Prims.list) = 
    let vector = (FStar_Seq_Properties.createL vector) in
    let result = _OS2IP vector in 
      Printf.printf "The number %s \n" (to_string result);
      Printf.printf "Test returned %B \n" ((Prims.parse_int "15824411865220768") = result);
    ((Prims.parse_int "15824411865220768") = result)  


let _ = 
  check_helper_i2osp_1 test_vector1_helper_i2osp;
  check_helper_i2osp_2 test_vector2_helper_i2osp;
  check_i2osp_1 test_vector2_helper_i2osp;
  check_osp2i_1 test_vector2_helper_i2osp                                 