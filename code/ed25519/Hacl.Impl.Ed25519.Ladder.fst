module Hacl.Impl.Ed25519.Ladder

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module S = Hacl.Spec.Ed25519.Field56.Definition
module F56 = Hacl.Impl.Ed25519.Field56
module F51 = Hacl.Impl.Ed25519.Field51

module LE = Lib.Exponentiation
module BE = Hacl.Impl.Exponentiation
module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

////////////////////////////////////////////////////
unfold
let a_spec = Spec.Ed25519.ext_point

unfold
let exp : LE.exp a_spec = Spec.Ed25519.mk_ed25519_group

unfold
let lseq_as_felem (a:LSeq.lseq uint64 5) : GTot Hacl.Spec.Curve25519.Field51.Definition.felem5 =
  let s0 = LSeq.index a 0 in
  let s1 = LSeq.index a 1 in
  let s2 = LSeq.index a 2 in
  let s3 = LSeq.index a 3 in
  let s4 = LSeq.index a 4 in
  (s0, s1, s2, s3, s4)

unfold
let linv (a:LSeq.lseq uint64 20) : Type0 =
  Hacl.Spec.Curve25519.Field51.mul_inv_t (lseq_as_felem (LSeq.sub a 0 5)) /\
  Hacl.Spec.Curve25519.Field51.mul_inv_t (lseq_as_felem (LSeq.sub a 5 5)) /\
  Hacl.Spec.Curve25519.Field51.mul_inv_t (lseq_as_felem (LSeq.sub a 10 5)) /\
  Hacl.Spec.Curve25519.Field51.mul_inv_t (lseq_as_felem (LSeq.sub a 15 5))

unfold
let refl (a:LSeq.lseq uint64 20) : GTot a_spec =
  let open Hacl.Spec.Curve25519.Field51.Definition in
  let x = feval (lseq_as_felem (LSeq.sub a 0 5)) in
  let y = feval (lseq_as_felem (LSeq.sub a 5 5)) in
  let z = feval (lseq_as_felem (LSeq.sub a 10 5)) in
  let t = feval (lseq_as_felem (LSeq.sub a 15 5)) in
  (x, y, z, t)

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True


inline_for_extraction noextract
let mk_lexp_to_exp : BE.lexp_to_exp U64 20ul 0ul = {
  BE.a_spec = a_spec;
  BE.exp = exp;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
  }

inline_for_extraction noextract
val point_add : BE.lmul_st U64 20ul 0ul mk_lexp_to_exp
let point_add ctx x y xy =
  Hacl.Impl.Ed25519.PointAdd.point_add xy x y


inline_for_extraction noextract
val point_double : BE.lsqr_st U64 20ul 0ul mk_lexp_to_exp
let point_double ctx x xx =
  let h0 = ST.get () in
  Spec.Ed25519.lemma_fsqr (refl (as_seq h0 x));
  Hacl.Impl.Ed25519.PointDouble.point_double xx x


inline_for_extraction noextract
let mk_lexp : BE.lexp U64 20ul 0ul = {
  BE.to = mk_lexp_to_exp;
  BE.lmul = point_add;
  BE.lsqr = point_double;
}

//////////////////////////////////////////////

inline_for_extraction noextract
val make_point_inf:
  b:lbuffer uint64 20ul ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
      F51.point_inv_t h1 b /\
      F51.point_eval h1 b == Spec.Curve25519.(zero, one, one, zero)
    )
let make_point_inf b =
  let x = sub b 0ul 5ul in
  let y = sub b 5ul 5ul in
  let z = sub b 10ul 5ul in
  let t = sub b 15ul 5ul in
  make_zero x;
  make_one y;
  make_one z;
  make_zero t

inline_for_extraction noextract
val make_g:
  g:point ->
  Stack unit
    (requires fun h -> live h g)
    (ensures fun h0 _ h1 -> modifies (loc g) h0 h1 /\
      F51.point_inv_t h1 g /\
      F51.point_eval h1 g == Spec.Ed25519.g
    )

let make_g g =
  let gx = getx g in
  let gy = gety g in
  let gz = getz g in
  let gt = gett g in
  make_u64_5 gx (u64 0x00062d608f25d51a) (u64 0x000412a4b4f6592a) (u64 0x00075b7171a4b31d) (u64 0x0001ff60527118fe) (u64 0x000216936d3cd6e5);
  make_u64_5 gy (u64 0x0006666666666658) (u64 0x0004cccccccccccc) (u64 0x0001999999999999) (u64 0x0003333333333333) (u64 0x0006666666666666);
  make_one gz;
  make_u64_5 gt (u64 0x00068ab3a5b7dda3) (u64 0x00000eea2a5eadbb) (u64 0x0002af8df483c27e) (u64 0x000332b375274732) (u64 0x00067875f0fd78b7);

  (**) assert_norm (Spec.Ed25519.g_x ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (u64 0x00062d608f25d51a, u64 0x000412a4b4f6592a, u64 0x00075b7171a4b31d, u64 0x0001ff60527118fe, u64 0x000216936d3cd6e5) % Spec.Curve25519.prime);
  (**) assert_norm (Spec.Ed25519.g_y ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (u64 0x0006666666666658, u64 0x0004cccccccccccc, u64 0x0001999999999999, u64 0x0003333333333333, u64 0x0006666666666666) %
      Spec.Curve25519.prime);
  (**) assert_norm (Mktuple4?._4 Spec.Ed25519.g ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (u64 0x00068ab3a5b7dda3, u64 0x00000eea2a5eadbb, u64 0x0002af8df483c27e, u64 0x000332b375274732, u64 0x00067875f0fd78b7) % Spec.Curve25519.prime)


val point_mul:
    result:point
  -> scalar:lbuffer uint8 32ul
  -> q:point ->
  Stack unit
    (requires fun h ->
      live h scalar /\ live h q /\ live h result /\ F51.point_inv_t h q
    )
    (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      F51.point_inv_t h1 result /\
      F51.point_eval h1 result == Spec.Ed25519.point_mul (as_seq h0 scalar) (F51.point_eval h0 q)
    )

let point_mul result scalar q =
  let h0 = ST.get () in
  push_frame();
  let a = create 20ul (u64 0) in
  copy a q;
  let bscalar = create 4ul (u64 0) in
  BN.bn_from_bytes_le 32ul scalar bscalar;
  SN.bn_from_bytes_le_lemma #U64 32 (as_seq h0 scalar);

  make_point_inf result;
  BE.lexp_fw_ct 20ul 0ul mk_lexp (null uint64) a 4ul 256ul bscalar result 4ul;
  pop_frame()


val point_mul_g:
    result:point
  -> scalar:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h scalar /\ live h result /\ disjoint result scalar)
    (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      F51.point_inv_t h1 result /\
      F51.point_eval h1 result == Spec.Ed25519.point_mul (as_seq h0 scalar) Spec.Ed25519.g
    )
let point_mul_g result scalar =
  push_frame();
  let g = create 20ul (u64 0) in
  make_g g;
  point_mul result scalar g;
  pop_frame()
