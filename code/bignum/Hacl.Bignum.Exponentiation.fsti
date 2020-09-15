module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum.Exponentiation
module BN = Hacl.Bignum
module BB = Hacl.Bignum.Base

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
let check_mod_exp_st (nLen:BN.meta_len) =
    n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_t{0 < v bBits /\ 64 * v (blocks bBits 64ul) <= max_size_t}
  -> b:lbignum (blocks bBits 64ul) ->
  Stack uint64
  (requires fun h ->
    live h n /\ live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.check_mod_exp (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b))

val check_mod_exp: nLen:_ -> check_mod_exp_st nLen

// This function is *NOT* constant-time on the exponent b.
inline_for_extraction noextract
let bn_mod_exp_precompr2_st (nLen:BN.meta_len) =
    n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum (blocks bBits 64ul)
  -> r2:lbignum nLen
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\
    disjoint res r2 /\ disjoint a r2 /\ disjoint n r2)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_exp_precompr2 (v nLen) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h0 r2))

// This version is fully run-time.
val bn_mod_exp_precompr2: nLen:_ -> bn_mod_exp_precompr2_st nLen


// This function is constant-time on the exponent b.
inline_for_extraction noextract
let bn_mod_exp_mont_ladder_precompr2_st (nLen:BN.meta_len) =
    n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum (blocks bBits 64ul)
  -> r2:lbignum nLen
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\
    disjoint res r2 /\ disjoint a r2 /\ disjoint n r2)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res ==
      S.bn_mod_exp_mont_ladder_precompr2 (v nLen) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h0 r2))

// This version is fully run-time.
val bn_mod_exp_mont_ladder_precompr2: nLen:_ -> bn_mod_exp_mont_ladder_precompr2_st nLen



inline_for_extraction noextract
let bn_mod_exp_st (nLen:BN.meta_len) =
    n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_t{0 < v bBits /\ 64 * v (blocks bBits 64ul) <= max_size_t}
  -> b:lbignum (blocks bBits 64ul)
  -> res:lbignum nLen ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    r == BB.unsafe_bool_of_u64 (S.check_mod_exp (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b)) /\
    (r ==> S.bn_mod_exp_post #(v nLen) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h1 res)))


// This version is fully run-time.
// This function is *NOT* constant-time on the exponent b.
val bn_mod_exp: nLen:_ -> bn_mod_exp_st nLen

// This version is fully run-time.
// This function is constant-time on the exponent b.
val bn_mod_exp_mont_ladder: nLen:_ -> bn_mod_exp_st nLen