/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/mpolubel/work/everest/kremlin/krml -add-include "TestLib.h" /dist/generic/testlib.c -skip-compilation -no-prefix Hacl.Test.Ed25519 -bundle Lib.* -bundle Spec.* -bundle C=C.Endianness -bundle Hacl.Ed25519=Hacl.Impl.Ed25519.*,Hacl.Ed25519 -library Hacl.SHA512,C,FStar -drop LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.* -add-include "c/Lib_PrintBuffer.h" -tmpdir ed25519-c .output/prims.krml .output/FStar_Pervasives_Native.krml .output/FStar_Pervasives.krml .output/FStar_Reflection_Types.krml .output/FStar_Reflection_Data.krml .output/FStar_Order.krml .output/FStar_Reflection_Basic.krml .output/FStar_Mul.krml .output/FStar_Squash.krml .output/FStar_Classical.krml .output/FStar_StrongExcludedMiddle.krml .output/FStar_FunctionalExtensionality.krml .output/FStar_List_Tot_Base.krml .output/FStar_List_Tot_Properties.krml .output/FStar_List_Tot.krml .output/FStar_Seq_Base.krml .output/FStar_Seq_Properties.krml .output/FStar_Seq.krml .output/FStar_Math_Lib.krml .output/FStar_Math_Lemmas.krml .output/FStar_BitVector.krml .output/FStar_UInt.krml .output/FStar_UInt32.krml .output/FStar_Int.krml .output/FStar_Int16.krml .output/FStar_Preorder.krml .output/FStar_Ghost.krml .output/FStar_ErasedLogic.krml .output/FStar_UInt64.krml .output/FStar_Int64.krml .output/FStar_Int63.krml .output/FStar_Int32.krml .output/FStar_Int8.krml .output/FStar_UInt63.krml .output/FStar_UInt16.krml .output/FStar_UInt8.krml .output/FStar_Int_Cast.krml .output/FStar_UInt128.krml .output/FStar_Int_Cast_Full.krml .output/Lib_IntTypes.krml .output/FStar_Set.krml .output/FStar_PropositionalExtensionality.krml .output/FStar_PredicateExtensionality.krml .output/FStar_TSet.krml .output/FStar_Monotonic_Heap.krml .output/FStar_Heap.krml .output/FStar_Map.krml .output/FStar_Monotonic_Witnessed.krml .output/FStar_Monotonic_HyperHeap.krml .output/FStar_Monotonic_HyperStack.krml .output/FStar_HyperStack.krml .output/FStar_HyperStack_ST.krml .output/FStar_Universe.krml .output/FStar_GSet.krml .output/FStar_ModifiesGen.krml .output/FStar_Range.krml .output/FStar_Tactics_Types.krml .output/FStar_Tactics_Result.krml .output/FStar_Tactics_Effect.krml .output/FStar_Tactics_Util.krml .output/FStar_Reflection_Const.krml .output/FStar_Char.krml .output/FStar_Exn.krml .output/FStar_ST.krml .output/FStar_All.krml .output/FStar_List.krml .output/FStar_String.krml .output/FStar_Reflection_Derived.krml .output/FStar_Tactics_Builtins.krml .output/FStar_Reflection_Formula.krml .output/FStar_Reflection_Derived_Lemmas.krml .output/FStar_Reflection.krml .output/FStar_Tactics_Derived.krml .output/FStar_Tactics_Logic.krml .output/FStar_Tactics.krml .output/FStar_BigOps.krml .output/LowStar_Monotonic_Buffer.krml .output/LowStar_Buffer.krml .output/LowStar_BufferOps.krml .output/Spec_Loops.krml .output/C_Loops.krml .output/Lib_Loops.krml .output/Lib_LoopCombinators.krml .output/Lib_RawIntTypes.krml .output/Lib_Sequence.krml .output/Lib_ByteSequence.krml .output/LowStar_ImmutableBuffer.krml .output/Lib_Buffer.krml .output/FStar_HyperStack_All.krml .output/Hacl_Impl_Ed25519_ExtPoint.krml .output/Hacl_Impl_Ed25519_SwapConditional.krml .output/FStar_Kremlin_Endianness.krml .output/C_Endianness.krml .output/C.krml .output/Lib_ByteBuffer.krml .output/Hacl_Impl_Store51.krml .output/Hacl_Impl_Curve25519_Lemmas.krml .output/Spec_Curve25519_Lemmas.krml .output/Spec_Curve25519.krml .output/Hacl_Spec_Curve25519_Field51_Definition.krml .output/Hacl_Spec_Curve25519_Field51_Lemmas.krml .output/Hacl_Spec_Curve25519_Field51.krml .output/Hacl_Impl_Curve25519_Field51.krml .output/Hacl_Lib_Create128.krml .output/Hacl_Lib_Create64.krml .output/Hacl_Impl_BignumQ_Mul.krml .output/Hacl_Impl_Load56.krml .output/Hacl_SHA512.krml .output/Hacl_Impl_Sha512.krml .output/Hacl_Impl_SHA512_ModQ.krml .output/Lib_PrintBuffer.krml .output/LowStar_Modifies.krml .output/C_String.krml .output/Hacl_Impl_Store56.krml .output/Hacl_Impl_Ed25519_SecretExpand.krml .output/Hacl_Impl_Ed25519_G.krml .output/Hacl_Bignum25519.krml .output/Hacl_Impl_Ed25519_PointCompress.krml .output/Hacl_Impl_Ed25519_PointAdd.krml .output/Hacl_Impl_Ed25519_PointDouble.krml .output/Hacl_Impl_Ed25519_Ladder_Step.krml .output/Hacl_Impl_Ed25519_Ladder.krml .output/Hacl_Impl_Ed25519_Sign_Steps.krml .output/Hacl_Impl_Ed25519_Sign.krml .output/Hacl_Ed25519.krml .output/Hacl_Test_Ed25519.krml
  F* version: 308e699d
  KreMLin version: 7580e5a6
 */

#include "kremlib.h"
#ifndef __FStar_H
#define __FStar_H


#include "TestLib.h"
#include "c/Lib_PrintBuffer.h"

extern uint64_t FStar_UInt64_eq_mask(uint64_t x0, uint64_t x1);

extern uint64_t FStar_UInt64_gte_mask(uint64_t x0, uint64_t x1);

extern uint8_t FStar_UInt8_uint_to_t(Prims_int x0);

extern FStar_UInt128_uint128
FStar_UInt128_add(FStar_UInt128_uint128 x0, FStar_UInt128_uint128 x1);

extern FStar_UInt128_uint128
FStar_UInt128_add_mod(FStar_UInt128_uint128 x0, FStar_UInt128_uint128 x1);

extern FStar_UInt128_uint128 FStar_UInt128_shift_right(FStar_UInt128_uint128 x0, uint32_t x1);

extern FStar_UInt128_uint128 FStar_UInt128_uint64_to_uint128(uint64_t x0);

extern uint64_t FStar_UInt128_uint128_to_uint64(FStar_UInt128_uint128 x0);

extern FStar_UInt128_uint128 FStar_UInt128_mul_wide(uint64_t x0, uint64_t x1);

#define __FStar_H_DEFINED
#endif