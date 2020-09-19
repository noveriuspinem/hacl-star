module Hacl.Spec.Bignum.Lib

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators
module BB = Hacl.Spec.Bignum.Base


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Get and set i-th bit of a bignum
///

val limb_get_ith_bit: #t:limb_t -> a:limb t -> i:nat{i < bits t} -> limb t
let limb_get_ith_bit #t a i = (a >>. size i) &. uint #t 1

val limb_get_ith_bit_lemma: #t:limb_t -> a:limb t -> i:nat{i < bits t} ->
  Lemma (v (limb_get_ith_bit a i) == v a / pow2 i % 2)

let limb_get_ith_bit_lemma #t a i =
  let tmp1 = a >>. size i in
  let tmp2 = tmp1 &. uint #t 1 in
  mod_mask_lemma tmp1 1ul;
  assert (v (mod_mask #t #SEC 1ul) == v (uint #t #SEC 1));
  assert (v tmp2 == v a / pow2 i % 2)

val bn_get_ith_bit: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i / bits t < len} -> limb t
let bn_get_ith_bit #t #len input ind =
  let i = ind / bits t in
  let j = ind % bits t in
  limb_get_ith_bit input.[i] j


#push-options "--z3rlimit 100"
val bn_get_ith_bit_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i / bits t < len} ->
  Lemma (v (bn_get_ith_bit b i) == (bn_v b / pow2 i % 2))

let bn_get_ith_bit_lemma #t #len b ind =
  let i = ind / bits t in
  let j = ind % bits t in
  let res = limb_get_ith_bit b.[i] j in
  limb_get_ith_bit_lemma b.[i] j;

  calc (==) {
    v b.[i] / pow2 j % 2;
    (==) { bn_eval_index b i }
    (bn_v b / pow2 (bits t * i) % pow2 (bits t)) / pow2 j % 2;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 (bn_v b / pow2 (bits t * i)) j (bits t) }
    (bn_v b / pow2 (bits t * i) / pow2 j) % pow2 (bits t - j) % 2;
    (==) { Math.Lemmas.division_multiplication_lemma (bn_v b) (pow2 (bits t * i)) (pow2 j) }
    (bn_v b / (pow2 (bits t * i) * pow2 j)) % pow2 (bits t - j) % 2;
    (==) { Math.Lemmas.pow2_plus (bits t * i) j }
    (bn_v b / pow2 (bits t * i + j)) % pow2 (bits t - j) % 2;
    (==) { Math.Lemmas.euclidean_div_axiom ind (bits t) }
    (bn_v b / pow2 ind) % pow2 (bits t - j) % 2;
    (==) { assert_norm (pow2 1 = 2);
           Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v b / pow2 ind) 1 (bits t - j) }
    (bn_v b / pow2 ind) % 2;
    };
  assert (v res == bn_v b / pow2 ind % 2)
#pop-options


val bn_set_ith_bit: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i / bits t < len} -> lbignum t len
let bn_set_ith_bit #t #len input ind =
  let i = ind / bits t in
  let j = ind % bits t in
  let inp = input.[i] <- input.[i] |. (uint #t 1 <<. size j) in
  inp


val bn_set_ith_bit_lemma_aux: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a + b * pow2 c < pow2 (c + d) /\ a < pow2 c)
  (ensures  b < pow2 d)

let bn_set_ith_bit_lemma_aux a b c d =
  Math.Lemmas.lemma_div_lt_nat (a + b * pow2 c) (c + d) c;
  assert ((a + b * pow2 c) / pow2 c < pow2 d);
  Math.Lemmas.lemma_div_plus a b (pow2 c);
  assert (a / pow2 c + b < pow2 d);
  Math.Lemmas.small_division_lemma_1 a (pow2 c)


val bn_lt_pow2_index_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> ind:size_nat{ind / bits t < len} -> Lemma
  (requires bn_v b < pow2 ind)
  (ensures (let i = ind / bits t in v b.[i] < pow2 (ind % bits t) /\
    bn_v b == bn_v (slice b 0 i) + pow2 (i * bits t) * v b.[i] /\
    bn_v (slice b (i + 1) len) = 0))

let bn_lt_pow2_index_lemma #t #len b ind =
  let i = ind / bits t in
  let j = ind % bits t in

  Math.Lemmas.euclidean_division_definition ind (bits t);
  assert (bn_v b < pow2 (i * bits t + j));
  Math.Lemmas.pow2_lt_compat (i * bits t + bits t) (i * bits t + j);
  assert (bn_v b < pow2 (i * bits t + bits t));

  bn_eval_split_i #t #len b (i + 1);
  bn_eval_bound (slice b 0 (i + 1)) (i + 1);
  bn_set_ith_bit_lemma_aux (bn_v (slice b 0 (i + 1))) (bn_v (slice b (i + 1) len)) (bits t * (i + 1)) 0;
  assert (bn_v b == bn_v (slice b 0 (i + 1)));

  bn_eval_split_i #t #(i + 1) (slice b 0 (i + 1)) i;
  bn_eval1 (slice b i (i + 1));
  assert (bn_v b == bn_v (slice b 0 i) + pow2 (i * bits t) * v b.[i]);
  bn_eval_bound #t #i (slice b 0 i) i;
  bn_set_ith_bit_lemma_aux (bn_v (slice b 0 i)) (v b.[i]) (i * bits t) j;
  assert (v b.[i] < pow2 j)


val bn_set_ith_bit_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i / bits t < len} -> Lemma
  (requires bn_v b < pow2 i)
  (ensures  bn_v (bn_set_ith_bit b i) == bn_v b + pow2 i)

let bn_set_ith_bit_lemma #t #len input ind =
  let i = ind / bits t in
  let j = ind % bits t in
  bn_lt_pow2_index_lemma #t #len input ind;
  assert (v input.[i] < pow2 j);

  let b = uint #t 1 <<. size j in
  let inp = input.[i] <- input.[i] |. b in
  FStar.Math.Lemmas.pow2_lt_compat (bits t) j;
  FStar.Math.Lemmas.modulo_lemma (pow2 j) (pow2 (bits t));
  assert (v b == pow2 j);
  logor_disjoint (input.[i]) b j;
  assert (v inp.[i] == v input.[i] + v b);

  calc (==) {
    bn_v inp;
    (==) { bn_eval_split_i #t #len inp (i + 1);
    bn_eval_extensionality_j (slice inp (i + 1) len) (slice input (i + 1) len) (len - i - 1) }
    bn_v (slice inp 0 (i + 1));
    (==) { bn_eval_split_i #t #(i + 1) (slice inp 0 (i + 1)) i }
    bn_v (slice inp 0 i) + pow2 (i * bits t) * bn_v (slice inp i (i + 1));
    (==) { bn_eval1 (slice inp i (i + 1)) }
    bn_v (slice inp 0 i) + pow2 (i * bits t) * v inp.[i];
    (==) { bn_eval_extensionality_j input inp i }
    bn_v (slice input 0 i) + pow2 (i * bits t) * v inp.[i];
    (==) { }
    bn_v (slice input 0 i) + pow2 (i * bits t) * (v input.[i] + v b);
    (==) { Math.Lemmas.distributivity_add_right (pow2 (i * bits t)) (v input.[i]) (v b) }
    bn_v (slice input 0 i) + pow2 (i * bits t) * v input.[i] + pow2 (i * bits t) * v b;
    (==) { Math.Lemmas.pow2_plus (i * bits t) j; Math.Lemmas.euclidean_division_definition ind (bits t) }
    bn_v (slice input 0 i) + pow2 (i * bits t) * v input.[i] + pow2 ind;
    (==) { }
    bn_v input + pow2 ind;
  }


///
///  % pow2 and / pow2
///

val bn_div_pow2: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i <= len} -> lbignum t (len - i)
let bn_div_pow2 #t #len b i =
  slice b i len


val bn_div_pow2_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i < len} ->
  Lemma (bn_v (bn_div_pow2 b i) == bn_v b / pow2 (bits t * i))
let bn_div_pow2_lemma #t #len c i =
  calc (==) {
    bn_v c / pow2 (bits t * i);
    (==) { bn_eval_split_i c i }
    (bn_v (slice c 0 i) + pow2 (bits t * i) * bn_v (slice c i len)) / pow2 (bits t * i);
    (==) { Math.Lemmas.division_addition_lemma (bn_v (slice c 0 i)) (pow2 (bits t * i)) (bn_v (slice c i len)) }
    bn_v (slice c 0 i) / pow2 (bits t * i) + bn_v (slice c i len);
    (==) { bn_eval_bound (slice c 0 i) i; Math.Lemmas.small_division_lemma_1 (bn_v (slice c 0 i)) (pow2 (bits t * i)) }
    bn_v (slice c i len);
  };
  assert (bn_v (slice c i len) == bn_v c / pow2 (bits t * i))


val bn_mod_pow2: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> i:nat{i <= aLen} -> lbignum t i
let bn_mod_pow2 #t #aLen a i = sub a 0 i

val bn_mod_pow2_lemma: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> i:nat{i <= aLen} ->
  Lemma (bn_v (bn_mod_pow2 a i) == bn_v a % pow2 (bits t * i))
let bn_mod_pow2_lemma #t #aLen a i =
  calc (==) {
    bn_v a % pow2 (bits t * i);
    (==) { bn_eval_split_i a i }
    (bn_v (slice a 0 i) + pow2 (bits t * i) * bn_v (slice a i aLen)) % pow2 (bits t * i);
    (==) { Math.Lemmas.modulo_addition_lemma (bn_v (slice a 0 i)) (pow2 (bits t * i)) (bn_v (slice a i aLen)) }
    (bn_v (slice a 0 i)) % pow2 (bits t * i);
    (==) { bn_eval_bound (slice a 0 i) i; Math.Lemmas.small_mod (bn_v (slice a 0 i)) (pow2 (bits t * i)) }
    bn_v (slice a 0 i);
    }

///
///  Conditional swap
///

//the same as in curve25519
val lemma_cswap2_step:
   #t:limb_t
  -> bit:limb t{v bit <= 1}
  -> p1:limb t
  -> p2:limb t ->
  Lemma
   (let mask = uint #t 0 -. bit in
    let dummy = mask &. (p1 ^. p2) in
    let p1' = p1 ^. dummy in
    let p2' = p2 ^. dummy in
    if v bit = 1 then p1' == p2 /\ p2' == p1 else p1' == p1 /\ p2' == p2)

let lemma_cswap2_step #t bit p1 p2 =
  let mask = uint #t 0 -. bit in
  assert (v bit == 0 ==> v mask == 0);
  assert (v bit == 1 ==> v mask == pow2 (bits t) - 1);
  let dummy = mask &. (p1 ^. p2) in
  logand_lemma mask (p1 ^. p2);
  assert (v bit == 1 ==> v dummy == v (p1 ^. p2));
  assert (v bit == 0 ==> v dummy == 0);
  let p1' = p1 ^. dummy in
  assert (v dummy == v (if v bit = 1 then (p1 ^. p2) else uint #t 0));
  logxor_lemma p1 p2;
  let p2' = p2 ^. dummy in
  logxor_lemma p2 p1


val cswap2_f:
    #t:limb_t
  -> #len:size_nat
  -> mask:limb t
  -> i:nat{i < len}
  -> tuple2 (lbignum t len) (lbignum t len) ->
  tuple2 (lbignum t len) (lbignum t len)

let cswap2_f #t #len mask i (p1, p2) =
  let dummy = mask &. (p1.[i] ^. p2.[i]) in
  let p1 = p1.[i] <- p1.[i] ^. dummy in
  let p2 = p2.[i] <- p2.[i] ^. dummy in
  (p1, p2)


val cswap2:
    #t:limb_t
  -> #len:size_nat
  -> bit:limb t
  -> b1:lbignum t len
  -> b2:lbignum t len ->
  tuple2 (lbignum t len) (lbignum t len)

let cswap2 #t #len bit b1 b2 =
  let mask = uint #t 0 -. bit in
  Loops.repeati len (cswap2_f #t #len mask) (b1, b2)


val cswap2_lemma:
    #t:limb_t
  -> #len:size_nat
  -> bit:limb t{v bit <= 1}
  -> b1:lbignum t len
  -> b2:lbignum t len ->
  Lemma (let (p1, p2) = cswap2 bit b1 b2 in
    (if v bit = 1 then p1 == b2 /\ p2 == b1 else p1 == b1 /\ p2 == b2))

let cswap2_lemma #t #len bit b1 b2 =
  let mask = uint #t 0 -. bit in
  Loops.eq_repeati0 len (cswap2_f #t #len mask) (b1, b2);
  let (p1, p2) =
  Loops.repeati_inductive #(tuple2 (lbignum t len) (lbignum t len)) len
  (fun i (p1, p2) ->
    (p1, p2) == Loops.repeati i (cswap2_f #t #len mask) (b1, b2) /\
    (forall (k:nat{k < i}).
      (if v bit = 1 then p1.[k] == b2.[k] /\ p2.[k] == b1.[k] else p1.[k] == b1.[k] /\ p2.[k] == b2.[k])) /\
    (forall (k:nat{i <= k /\ k < len}). p1.[k] == b1.[k] /\ p2.[k] == b2.[k]))
  (fun i (p1, p2) ->
    Loops.unfold_repeati (i + 1) (cswap2_f #t #len mask) (b1, b2) i;
    lemma_cswap2_step bit p1.[i] p2.[i];
    cswap2_f #t #len mask i (p1, p2)) (b1, b2) in

  assert (if v bit = 1 then (eq_intro p1 b2; p1 == b2) else (eq_intro p1 b1; p1 == b1));
  assert (if v bit = 1 then (eq_intro p2 b1; p2 == b1) else (eq_intro p2 b2; p2 == b2));
  //eq_intro p1 (if v bit = 1 then b2 else b1);
  //eq_intro p2 (if v bit = 1 then b1 else b2);
  ()

///
///  bn_get_num_bits
///

let bn_leading_zero_index_t (len:size_nat) (i:nat{i <= len}) = x:nat{x < len}

val bn_leading_zero_index_f:
    #t:limb_t
  -> #len:size_nat
  -> b:lbignum t len
  -> i:nat{i < len}
  -> priv:bn_leading_zero_index_t len i ->
  bn_leading_zero_index_t len (i + 1)

let bn_leading_zero_index_f #t #len b i priv =
  let mask = eq_mask b.[i] (zeros t SEC) in
  if v mask = 0 then i else priv

val bn_leading_zero_index: #t:limb_t -> #len:size_pos -> b:lbignum t len -> res:size_nat{res < len}
let bn_leading_zero_index #t #len b =
  Loops.repeat_gen len (bn_leading_zero_index_t len) (bn_leading_zero_index_f #t #len b) 0


val bn_leading_zero_index_lemma: #t:limb_t -> #len:size_pos -> b:lbignum t len ->
  Lemma (let ind = bn_leading_zero_index #t #len b in
    ind < len /\ (ind > 0 ==> v b.[ind] <> 0) /\ (forall (k:nat{ind < k /\ k < len}). v b.[k] = 0))

let bn_leading_zero_index_lemma #t #len b =
  Loops.eq_repeat_gen0 len (bn_leading_zero_index_t len) (bn_leading_zero_index_f #t #len b) 0;
  let res =
  Loops.repeati_inductive #size_nat len
  (fun i priv ->
    priv == Loops.repeat_gen i (bn_leading_zero_index_t len) (bn_leading_zero_index_f #t #len b) 0 /\
    priv < len /\ (priv > 0 ==> v b.[priv] <> 0) /\ (forall (k:nat{priv < k /\ k < i}). v b.[k] = 0))
  (fun i priv ->
    Loops.unfold_repeat_gen (i + 1) (bn_leading_zero_index_t len) (bn_leading_zero_index_f #t #len b) 0 i;
    let mask = eq_mask b.[i] (zeros t SEC) in
    eq_mask_lemma b.[i] (zeros t SEC);
    assert (if v mask = 0 then v b.[i] <> 0 else v b.[i] = 0);
    let res = if v mask = 0 then i else priv in
    res) 0 in
  ()


val bn_leading_zero_index_eval_lemma: #t:limb_t -> #len:size_pos -> b:lbignum t len -> ind:nat -> Lemma
  (requires
    ind < len /\ (ind > 0 ==> v b.[ind] <> 0) /\ (forall (k:nat{ind < k /\ k < len}). v b.[k] = 0))
  (ensures
    bn_v b == bn_v (slice b 0 ind) + pow2 (bits t * ind) * v b.[ind])

let bn_leading_zero_index_eval_lemma #t #len b ind =
  assert (forall (k:nat{ind < k /\ k < len}). v b.[k] = 0);
  bn_eval_split_i b (ind + 1);
  assert (bn_v b == bn_v (slice b 0 (ind + 1)) + pow2 (bits t * (ind + 1)) * bn_v (slice b (ind + 1) len));
  eq_intro (slice b (ind + 1) len) (create (len - ind - 1) (uint #t 0));
  bn_eval_zeroes #t (len - ind - 1) (len - ind - 1);
  assert (bn_v b == bn_v (slice b 0 (ind + 1)));
  bn_eval_split_i (slice b 0 (ind + 1)) ind;
  assert (bn_v b == bn_v (slice b 0 ind) + pow2 (bits t * ind) * bn_v (slice b ind (ind + 1)));
  bn_eval1 (slice b ind (ind + 1));
  assert (bn_v b == bn_v (slice b 0 ind) + pow2 (bits t * ind) * v b.[ind])



let limb_leading_zero_index_t (t:limb_t) (i:nat{i <= bits t}) = x:size_nat{x < bits t}

val limb_leading_zero_index_f:
    #t:limb_t
  -> a:limb t
  -> i:nat{i < bits t}
  -> priv:limb_leading_zero_index_t t i ->
  limb_leading_zero_index_t t (i + 1)

let limb_leading_zero_index_f #t a i priv =
  if v (limb_get_ith_bit a i) = 1 then i else priv


val limb_leading_zero_index: #t:limb_t -> a:limb t -> res:size_nat{res < bits t}
let limb_leading_zero_index #t a =
  Loops.repeat_gen (bits t) (limb_leading_zero_index_t t) (limb_leading_zero_index_f a) 0


val limb_leading_zero_index_lemma: #t:limb_t -> a:limb t ->
  Lemma (let ind = limb_leading_zero_index a in
    ind < bits t /\ (ind > 0 ==> v (limb_get_ith_bit a ind) = 1) /\
    (forall (k:nat{ind < k /\ k < bits t}). v (limb_get_ith_bit a k) = 0))

let limb_leading_zero_index_lemma #t a =
  Loops.eq_repeat_gen0 (bits t) (limb_leading_zero_index_t t) (limb_leading_zero_index_f a) 0;
  let res =
  Loops.repeati_inductive #size_nat (bits t)
  (fun i priv ->
    priv == Loops.repeat_gen i (limb_leading_zero_index_t t) (limb_leading_zero_index_f a) 0 /\
    priv < bits t /\ (priv > 0 ==> v (limb_get_ith_bit a priv) = 1) /\
    (forall (k:nat{priv < k /\ k < i}). v (limb_get_ith_bit a k) = 0))
  (fun i priv ->
    Loops.unfold_repeat_gen (i + 1) (limb_leading_zero_index_t t) (limb_leading_zero_index_f a) 0 i;
    limb_get_ith_bit_lemma a i;
    let res = if v (limb_get_ith_bit a i) = 1 then i else priv in
    res) 0 in
  ()


val limb_leading_zero_eval_lemma_aux: #t:limb_t -> a:limb t -> ind:nat{ind < bits t} -> j:nat{ind < j /\ j <= bits t} -> Lemma
  (requires (forall (k:nat{ind < k /\ k < bits t}). v a / pow2 k % 2 = 0))
  (ensures  v a / pow2 j = 0)
  (decreases (bits t - j))

let rec limb_leading_zero_eval_lemma_aux #t a ind j =
  if j = bits t then ()
  else begin
    limb_leading_zero_eval_lemma_aux a ind (j + 1);
    assert (v a / pow2 (j + 1) = 0);
    calc (==) {
      v a / pow2 j;
      (==) { Math.Lemmas.euclidean_division_definition (v a / pow2 j) 2 }
      (v a / pow2 j) / 2 * 2 + v a / pow2 j % 2;
      (==) { assert_norm (pow2 1 = 2); Math.Lemmas.division_multiplication_lemma (v a) (pow2 j) (pow2 1) }
      (v a / (pow2 j * pow2 1)) * 2 + v a / pow2 j % 2;
      (==) { Math.Lemmas.pow2_plus j 1 }
      (v a / pow2 (j + 1)) * 2 + v a / pow2 j % 2;
      (==) { }
      0;
      }; () end


val limb_leading_zero_index_eval_lemma: #t:limb_t -> a:limb t{v a > 0} -> ind:nat -> Lemma
  (requires
    ind < bits t /\ (ind > 0 ==> v (limb_get_ith_bit a ind) = 1) /\
    (forall (k:nat{ind < k /\ k < bits t}). v (limb_get_ith_bit a k) = 0))
  (ensures
    pow2 ind <= v a /\ v a < pow2 (ind + 1))

let limb_leading_zero_index_eval_lemma #t a ind =
  let aux (k:nat{ind < k /\ k < bits t}) : Lemma (v a / pow2 k % 2 = 0) =
    assert (v (limb_get_ith_bit a k) = 0);
    limb_get_ith_bit_lemma a k;
    assert (v a / pow2 k % 2 = 0);
    () in
  Classical.forall_intro aux;
  assert (forall (k:nat{ind < k /\ k < bits t}). v a / pow2 k % 2 = 0);

  limb_leading_zero_eval_lemma_aux a ind (ind + 1);
  assert (v a / pow2 (ind + 1) = 0);

  if ind = 0 then begin
    assert_norm (pow2 0 = 1);
    assert_norm (pow2 1 = 2);
    assert (v a = 1) end
  else begin
    calc (==) {
      v a / pow2 ind;
      (==) { Math.Lemmas.euclidean_division_definition (v a / pow2 ind) 2 }
      (v a / pow2 ind) / 2 * 2 + v a / pow2 ind % 2;
      (==) { assert_norm (pow2 1 = 2);
	Math.Lemmas.division_multiplication_lemma (v a) (pow2 ind) (pow2 1) }
      (v a / (pow2 ind * pow2 1)) * 2 + v a / pow2 ind % 2;
      (==) { Math.Lemmas.pow2_plus ind 1 }
      (v a / pow2 (ind + 1)) * 2 + v a / pow2 ind % 2;
      (==) { }
      v a / pow2 ind % 2;
      (==) { limb_get_ith_bit_lemma a ind }
      v (limb_get_ith_bit a ind);
      (==) { }
      1;
      };
    assert (v a / pow2 ind = 1) end;

  calc (==) {
    v a;
    (==) { Math.Lemmas.euclidean_division_definition (v a) (pow2 (ind + 1)) }
    v a % pow2 (ind + 1) + v a / pow2 (ind + 1) * pow2 (ind + 1);
    (==) { }
    v a % pow2 (ind + 1);
    };
  assert (v a < pow2 (ind + 1));

  calc (==) {
    v a;
    (==) { Math.Lemmas.euclidean_division_definition (v a) (pow2 ind) }
    v a % pow2 ind + v a / pow2 ind * pow2 ind;
    (==) { }
    v a % pow2 ind + pow2 ind;
    };
  assert (pow2 ind <= v a)


val bn_get_num_bits: #t:limb_t -> #len:size_pos{bits t * len <= max_size_t} -> b:lbignum t len -> size_nat
let bn_get_num_bits #t #len b =
  let ind = bn_leading_zero_index #t #len b in
  let last_bits = limb_leading_zero_index b.[ind] in
  bits t * ind + last_bits


val bn_get_num_bits_lemma_aux: d:pos -> ind:size_nat -> bits:size_nat -> a:nat -> b:nat -> Lemma
  (requires
    pow2 bits <= b /\ b < pow2 (bits + 1) /\ a < pow2 (d * ind))
  (ensures
    pow2 (d * ind + bits) <= a + pow2 (d * ind) * b /\
    a + pow2 (d * ind) * b < pow2 (d * ind + bits + 1))

let bn_get_num_bits_lemma_aux d ind bits a b =
  calc (>=) {
    a + pow2 (d * ind) * b;
    (>=) { }
    pow2 (d * ind) * b;
    (>=) { }
    pow2 (d * ind) * pow2 bits;
    (==) { Math.Lemmas.pow2_plus (d * ind) bits }
    pow2 (d * ind + bits);
  };
  assert (pow2 (d * ind + bits) <= a + pow2 (d * ind) * b);

  calc (<=) {
    a + pow2 (d * ind) * b;
    (<=) { }
    pow2 (d * ind) - 1 + pow2 (d * ind) * b;
    (<=) { }
    pow2 (d * ind) - 1 + pow2 (d * ind) * (pow2 (bits + 1) - 1);
    (==) { Math.Lemmas.distributivity_sub_right (pow2 (d * ind)) (pow2 (bits + 1)) 1 }
    pow2 (d * ind) * pow2 (bits + 1) - 1;
    (==) { Math.Lemmas.pow2_plus (d * ind) (bits + 1) }
    pow2 (d * ind + bits + 1) - 1;
    };
  assert (a + pow2 (d * ind) * b < pow2 (d * ind + bits + 1))


val bn_get_num_bits_lemma: #t:limb_t -> #len:size_pos{bits t * len <= max_size_t} -> b:lbignum t len -> Lemma
  (requires 0 < bn_v b)
  (ensures (let bs = bn_get_num_bits b in
    bs <= bits t * len /\ blocks (bs + 1) (bits t) <= len /\
    pow2 bs <= bn_v b /\ bn_v b < pow2 (bs + 1)))

let bn_get_num_bits_lemma #t #len b =
  let ind = bn_leading_zero_index #t #len b in
  bn_leading_zero_index_lemma b;
  bn_leading_zero_index_eval_lemma b ind;
  assert (bn_v b == bn_v (slice b 0 ind) + pow2 (bits t * ind) * v b.[ind]);
  let bs = limb_leading_zero_index b.[ind] in
  if ind = 0 then begin
    bn_eval0 (slice b 0 ind);
    assert_norm (pow2 0 = 1);
    assert (bn_v b == v b.[ind]);
    assert (v b.[ind] > 0);
    () end;
  assert (v b.[ind] > 0);
  limb_leading_zero_index_lemma b.[ind];
  limb_leading_zero_index_eval_lemma b.[ind] bs;
  assert (pow2 bs <= v b.[ind] /\ v b.[ind] < pow2 (bs + 1));

  bn_eval_bound (slice b 0 ind) ind;
  bn_get_num_bits_lemma_aux (bits t) ind bs (bn_v (slice b 0 ind)) (v b.[ind])


// val limb_get_num_bits_f: i:nat{i < 6} -> tuple2 uint64 pos -> tuple2 uint64 pos
// let limb_get_num_bits_f i (l, bits) =
//   assert_norm (pow2 5 = 32);
//   Math.Lemmas.pow2_le_compat 5 (5 - i);
//   let half_t = pow2 (5 - i) in
//   let x = l >>. size half_t in
//   let mask = u64 0 -. x in
//   let mask = u64 0 -. (mask >>. 63ul) in
//   let bits = if v mask = 0 then bits else bits + half_t in
//   let l = l ^. (mask &. (x ^. l)) in
//   (l, bits)


// val limb_get_num_bits: a:uint64 -> pos
// let limb_get_num_bits a =
//   let (l, bits) = Loops.repeati 6 limb_get_num_bits_f (a, 1) in
//   bits

// val limb_get_num_bits_f_lemma: i:nat{i < 6} -> lb:tuple2 uint64 pos -> Lemma
//   (requires (let l, bits = lb in 0 < v l))
//   (ensures  (let l, bits = lb in
//     let l1, bits1 = limb_get_num_bits_f i (l, bits) in
//     let half_t = pow2 (5 - i) in
//     let x = v l / pow2 half_t in 0 < v l1 /\ 0 < bits1 /\
//     (if x = 0 then l1 == l /\ bits1 == bits else v l1 == x /\ bits1 == bits + half_t)))

// let limb_get_num_bits_f_lemma i (l, bits) =
//   let l1, bits1 = limb_get_num_bits_f i (l, bits) in
//   assert_norm (pow2 5 = 32);
//   Math.Lemmas.pow2_le_compat 5 (5 - i);
//   let half_t = pow2 (5 - i) in
//   let x = l >>. size half_t in
//   assert (v x == v l / pow2 half_t);
//   let mask = u64 0 -. x in
//   if v x = 0 then begin
//     assert (v mask = 0);
//     let mask = u64 0 -. (mask >>. 63ul) in
//     assert (v mask = 0);
//     assert (bits1 = bits);
//     BB.mask_select_lemma1 mask x l;
//     assert (v l1 == v l);
//     () end
//   else begin
//     // assert (v mask == pow2 64 - v x);
//     assert (v mask == (- v x) % pow2 64);
//     let mask1 = u64 0 -. (mask >>. 63ul) in
//     assert (v mask1 = (- v mask / pow2 63) % pow2 64);
//     calc (==) {
//       (- v mask / pow2 63) % pow2 64;
//       (==) { Math.Lemmas.lemma_mod_sub_1 (v mask / pow2 63) (pow2 64) }
//       pow2 64 - (v mask / pow2 63) % pow2 64;
//       (==) { Math.Lemmas.modulo_division_lemma (v mask) (pow2 63) (pow2 64) }
//       pow2 64 - (v mask % (pow2 64 * pow2 63)) / pow2 63;
//       (==) { Math.Lemmas.pow2_plus 64 63; Math.Lemmas.small_mod (v mask) (pow2 127) }
//       pow2 64 - v mask / pow2 63;
//       (==) { }
//       pow2 64 - 1;
//       };
//     assert (v mask1 = v (ones U64 SEC));
//     assert (bits1 = bits + half_t);
//     BB.mask_select_lemma1 mask1 x l;
//     assert (v l1 == v x);
//     () end


// val limb_get_num_bits_lemma_step: l1:pos -> i:pos{i <= 6} -> bits1:pos -> Lemma
//   (let half_t = pow2 (6 - i) in
//    let x = l1 / pow2 half_t in
//    x * pow2 (bits1 + half_t - 1) <= l1 * pow2 (bits1 - 1))

// let limb_get_num_bits_lemma_step l1 i bits1 =
//   let half_t = pow2 (6 - i) in
//   let x = l1 / pow2 half_t in

//   calc (>=) {
//     l1 * pow2 (bits1 - 1);
//     (>=) { Math.Lemmas.multiply_fractions l1 (pow2 half_t) }
//     x * pow2 half_t * pow2 (bits1 - 1);
//     (==) { Math.Lemmas.paren_mul_right x (pow2 half_t) (pow2 (bits1 - 1));
//       Math.Lemmas.pow2_plus half_t (bits1 - 1) }
//     x * pow2 (bits1 + half_t - 1);
//   }


// val limb_get_num_bits_lemma_loop: a:uint64{0 < v a} -> i:nat{i <= 6} -> Lemma
//   (let (l, bits) = Loops.repeati i limb_get_num_bits_f (a, 1) in
//    let half_t = pow2 (6 - i) in
//    v l < pow2 half_t /\ 0 < v l /\
//    v l * pow2 (bits - 1) <= v a)

// let rec limb_get_num_bits_lemma_loop a i =
//   let (l, bits) = Loops.repeati i limb_get_num_bits_f (a, 1) in
//   if i = 0 then begin
//     Loops.eq_repeati0 i limb_get_num_bits_f (a, 1);
//     assert_norm (pow2 0 = 1);
//     assert_norm (pow2 1 = 2);
//     assert_norm (pow2 6 = 64);
//     () end
//   else begin
//     let (l1, bits1) = Loops.repeati (i - 1) limb_get_num_bits_f (a, 1) in
//     Loops.unfold_repeati i limb_get_num_bits_f (a, 1) (i - 1);
//     assert ((l, bits) == limb_get_num_bits_f (i - 1) (l1, bits1));
//     limb_get_num_bits_lemma_loop a (i - 1);
//     assert (v l1 * pow2 (bits1 - 1) <= v a /\ v l1 < pow2 (pow2 (7 - i)) /\ 0 < v l1 /\ 0 < bits1);
//     limb_get_num_bits_f_lemma (i - 1) (l1, bits1);
//     let half_t = pow2 (6 - i) in
//     let x = v l1 / pow2 half_t in
//     assert (if x = 0 then l == l1 /\ bits == bits1 else v l == x /\ bits == bits1 + half_t);
//     assert (v l1 == x * pow2 half_t + v l1 % pow2 half_t);

//     if x = 0 then ()
//     else begin
//       assert (pow2 (bits - 1) == pow2 (bits1 + half_t - 1));
//       Math.Lemmas.pow2_double_sum (6 - i);
//       Math.Lemmas.lemma_div_lt_nat (v l1) (pow2 (7 - i)) (pow2 (6 - i));
//       assert (v l < pow2 half_t);
//       limb_get_num_bits_lemma_step (v l1) i bits1;
//       assert (v l * pow2 (bits1 + half_t - 1) <= v a);
//     () end;

//     () end


// val limb_get_num_bits_lemma: a:uint64{v a > 0} -> Lemma (pow2 (limb_get_num_bits a - 1) <= v a)
// let limb_get_num_bits_lemma a =
//   let bits = limb_get_num_bits a in
//   assert_norm (pow2 0 = 1);
//   assert_norm (pow2 1 = 2);
//   let (l, bits) = Loops.repeati 6 limb_get_num_bits_f (a, 1) in
//   limb_get_num_bits_lemma_loop a 6;
//   assert (0 < v l /\ v l < 2);
//   assert (v l * pow2 (bits - 1) <= v a);
//   assert (v l = 1)
