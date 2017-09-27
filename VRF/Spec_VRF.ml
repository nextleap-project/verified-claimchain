open Prims
type bytes = FStar_UInt8.t FStar_Seq_Base.seq
type key = Prims.unit FStar_Endianness.lbytes
let field: Prims.int = Spec_Curve25519.prime
let n: Prims.int = Prims.parse_int "16"
let d: Prims.int =
  Prims.parse_int
    "37095705934669439343138083508754565189542113879843219016388785533085940283555"
type twisted_edward_point = Spec_Ed25519.ext_point
let g_x: Prims.int =
  Prims.parse_int
    "15112221349535400772501151409588531511454012693041857206046113283949847762202"
let g_y: Prims.int =
  Prims.parse_int
    "46316835694926478169428394003475163141307993866256225615783033603165251855960"
let coordinality: Prims.int =
  Prims.parse_int
    "57896044618658097711785492504343953926856930875039260848015607506283634007912"
let generator:
  (Spec_Curve25519.elem* Spec_Curve25519.elem* Spec_Curve25519.elem*
    Spec_Curve25519.elem)
  = (g_x, g_y, (Prims.parse_int "1"), (Spec_Curve25519.fmul g_x g_y))
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
let _OS2ECP2Points: bytes -> twisted_edward_point option =
  fun point  ->
    match Spec_Ed25519.recover_x
            ((FStar_Endianness.little_endian point) mod
               (Prims.pow2 (Prims.parse_int "255"))) true
    with
    | Some x ->
        Some
          (x,
            (((FStar_Endianness.little_endian point) mod
                (Prims.pow2 (Prims.parse_int "255")))
               mod Spec_Curve25519.prime), Spec_Curve25519.one,
            (Spec_Curve25519.fmul x
               (((FStar_Endianness.little_endian point) mod
                   (Prims.pow2 (Prims.parse_int "255")))
                  mod Spec_Curve25519.prime)))
    | uu____447 ->
        (match Spec_Ed25519.recover_x
                 ((FStar_Endianness.little_endian point) mod
                    (Prims.pow2 (Prims.parse_int "255"))) false
         with
         | Some x ->
             Some
               (x,
                 (((FStar_Endianness.little_endian point) mod
                     (Prims.pow2 (Prims.parse_int "255")))
                    mod Spec_Curve25519.prime), Spec_Curve25519.one,
                 (Spec_Curve25519.fmul x
                    (((FStar_Endianness.little_endian point) mod
                        (Prims.pow2 (Prims.parse_int "255")))
                       mod Spec_Curve25519.prime)))
         | uu____487 -> None)
let _ECP2OS: twisted_edward_point -> Prims.unit Spec_Lib.lbytes =
  fun gamma  -> Spec_Ed25519.point_compress gamma
let _OS2ECP: bytes -> Spec_Ed25519.ext_point option =
  fun point  -> Spec_Ed25519.point_decompress point
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
        if (counter - (Prims.parse_int "1")) >= (Prims.parse_int "0")
        then
          _helper_I2OSP (value / (Prims.parse_int "256"))
            (FStar_Seq_Base.upd s counter
               (nat_to_uint8 (value mod (Prims.parse_int "256"))))
            (counter - (Prims.parse_int "1"))
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
          (n1 - (Prims.parse_int "1"))
let rec _helper_OS2IP: bytes -> Prims.nat -> Prims.nat -> Prims.int =
  fun s  ->
    fun counter  ->
      fun number  ->
        if (counter + (Prims.parse_int "1")) < (FStar_Seq_Base.length s)
        then
          _helper_OS2IP s (counter + (Prims.parse_int "1"))
            (number +
               ((Prims.pow2
                   (FStar_Mul.op_Star (Prims.parse_int "8")
                      (((FStar_Seq_Base.length s) - counter) -
                         (Prims.parse_int "1"))))
                  * (uint8_to_int (FStar_Seq_Base.index s counter))))
        else
          number +
            ((Prims.pow2
                (FStar_Mul.op_Star (Prims.parse_int "8")
                   (((FStar_Seq_Base.length s) - counter) -
                      (Prims.parse_int "1"))))
               * (uint8_to_int (FStar_Seq_Base.index s counter)))
let _OS2IP: bytes -> Prims.nat =
  fun s  -> _helper_OS2IP s (Prims.parse_int "0") (Prims.parse_int "0")
let seqConcat s1 s2 = FStar_Seq_Base.append s1 s2
let hash: bytes -> Spec_SHA2_256.bytes =
  fun input  -> Spec_SHA2_256.hash input
let _ECVRF_decode_proof: bytes -> (twisted_edward_point option* bytes* bytes)
  =
  fun pi  ->
    match FStar_Seq_Properties.split pi ((Prims.parse_int "2") * n) with
    | (gamma,cs) ->
        (match FStar_Seq_Properties.split cs n with
         | (c,s) -> ((_OS2ECP gamma), c, s))
let rec _helper_ECVRF_hash_to_curve:
  Prims.nat -> Prims.nat -> bytes -> bytes -> Spec_Ed25519.ext_point option =
  fun ctr  ->
    fun counter_length  ->
      fun pk  ->
        fun input  ->
          if
            FStar_Option.isNone
              (Spec_Ed25519.point_decompress
                 (hash
                    (seqConcat (seqConcat input pk)
                       (_I2OSP ctr counter_length))))
          then
            (if (ctr + (Prims.parse_int "1")) < field
             then
               _helper_ECVRF_hash_to_curve (ctr + (Prims.parse_int "1"))
                 counter_length pk input
             else None)
          else
            Spec_Ed25519.point_decompress
              (hash
                 (seqConcat (seqConcat input pk) (_I2OSP ctr counter_length)))
let _ECVRF_hash_to_curve:
  bytes -> twisted_edward_point -> twisted_edward_point option =
  fun input  ->
    fun public_key  ->
      _helper_ECVRF_hash_to_curve (Prims.parse_int "0") (Prims.parse_int "4")
        (_ECP2OS public_key) input
let random: Prims.nat -> Prims.int =
  fun max1  -> max1 - (Prims.parse_int "1")
let randBytes: Prims.nat -> bytes =
  fun max1  -> _I2OSP (random max1) (Prims.parse_int "32")
let _ECVRF_hash_points:
  twisted_edward_point ->
    twisted_edward_point ->
      twisted_edward_point ->
        twisted_edward_point ->
          twisted_edward_point -> twisted_edward_point -> Prims.nat
  =
  fun generator1  ->
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
                                     (seqConcat (_ECP2OS generator1)
                                        (_ECP2OS h)) (_ECP2OS public_key))
                                  (_ECP2OS gamma)) (_ECP2OS gk)) (_ECP2OS hk)))
                      n))
let rec little_endian_ins:
  bytes -> Prims.nat -> bytes -> FStar_UInt8.t FStar_Seq_Base.seq =
  fun a  ->
    fun counter  ->
      fun b  ->
        if (counter + (Prims.parse_int "1")) < (FStar_Seq_Base.length a)
        then
          little_endian_ins a (counter + (Prims.parse_int "1"))
            (FStar_Seq_Base.upd b
               (((FStar_Seq_Base.length a) - (Prims.parse_int "1")) - counter)
               (FStar_Seq_Base.index a counter))
        else
          FStar_Seq_Base.upd b
            (((FStar_Seq_Base.length a) - (Prims.parse_int "1")) - counter)
            (FStar_Seq_Base.index a counter)
let little_endian_: bytes -> bytes =
  fun a  ->
    little_endian_ins a (Prims.parse_int "0")
      (FStar_Seq_Base.create (FStar_Seq_Base.length a)
         (FStar_UInt8.uint_to_t (Prims.parse_int "0")))
let _ECVRF_prove: bytes -> twisted_edward_point -> bytes -> bytes option =
  fun input  ->
    fun public_key  ->
      fun private_key  ->
        if FStar_Option.isNone (_ECVRF_hash_to_curve input public_key)
        then None
        else
          Some
            (seqConcat
               (_ECP2OS
                  (scalarMultiplication
                     (FStar_Option.get
                        (_ECVRF_hash_to_curve input public_key))
                     (little_endian_ private_key)))
               (seqConcat
                  (_I2OSP
                     (_ECVRF_hash_points generator
                        (FStar_Option.get
                           (_ECVRF_hash_to_curve input public_key))
                        public_key
                        (scalarMultiplication
                           (FStar_Option.get
                              (_ECVRF_hash_to_curve input public_key))
                           (little_endian_ private_key))
                        (scalarMultiplication generator
                           (little_endian_
                              (_I2OSP (random coordinality)
                                 (Prims.parse_int "32"))))
                        (scalarMultiplication
                           (FStar_Option.get
                              (_ECVRF_hash_to_curve input public_key))
                           (little_endian_
                              (_I2OSP (random coordinality)
                                 (Prims.parse_int "32"))))) n)
                  (_I2OSP
                     ((((random coordinality) + coordinality) -
                         (((_ECVRF_hash_points generator
                              (FStar_Option.get
                                 (_ECVRF_hash_to_curve input public_key))
                              public_key
                              (scalarMultiplication
                                 (FStar_Option.get
                                    (_ECVRF_hash_to_curve input public_key))
                                 (little_endian_ private_key))
                              (scalarMultiplication generator
                                 (little_endian_
                                    (_I2OSP (random coordinality)
                                       (Prims.parse_int "32"))))
                              (scalarMultiplication
                                 (FStar_Option.get
                                    (_ECVRF_hash_to_curve input public_key))
                                 (little_endian_
                                    (_I2OSP (random coordinality)
                                       (Prims.parse_int "32")))))
                             * (_OS2IP private_key))
                            mod coordinality))
                        mod coordinality) ((Prims.parse_int "2") * n))))
let _ECVRF_proof2hash: bytes -> FStar_UInt8.t FStar_Seq_Base.seq =
  fun pi  ->
    fst
      (FStar_Seq_Properties.split
         (snd (FStar_Seq_Properties.split pi ((Prims.parse_int "2") * n))) n)
let _ECVRF_verify: twisted_edward_point -> bytes -> bytes -> Prims.bool =
  fun public_key  ->
    fun proof  ->
      fun input  ->
        match _ECVRF_decode_proof proof with
        | (gamma,c,s) ->
            if FStar_Option.isNone gamma
            then false
            else
              if FStar_Option.isNone (_ECVRF_hash_to_curve input public_key)
              then false
              else
                (_OS2IP c) =
                  (_ECVRF_hash_points generator
                     (FStar_Option.get
                        (_ECVRF_hash_to_curve input public_key)) public_key
                     (FStar_Option.get gamma)
                     (scalarAddition
                        (scalarMultiplication public_key (little_endian_ c))
                        (scalarMultiplication generator (little_endian_ s)))
                     (scalarAddition
                        (scalarMultiplication (FStar_Option.get gamma)
                           (little_endian_ c))
                        (scalarMultiplication
                           (FStar_Option.get
                              (_ECVRF_hash_to_curve input public_key))
                           (little_endian_ s))))