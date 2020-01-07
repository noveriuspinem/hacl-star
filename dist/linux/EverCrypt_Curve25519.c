/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "EverCrypt_Curve25519.h"

inline static bool EverCrypt_Curve25519_has_adx_bmi2()
{
  bool has_bmi21 = EverCrypt_AutoConfig2_has_bmi2();
  bool has_adx1 = EverCrypt_AutoConfig2_has_adx();
  return has_bmi21 && has_adx1;
}

void EverCrypt_Curve25519_secret_to_public(u8 *pub, u8 *priv)
{
  #if EVERCRYPT_TARGETCONFIG_X64
  if (EverCrypt_Curve25519_has_adx_bmi2())
  {
    Hacl_Curve25519_64_secret_to_public(pub, priv);
    return;
  }
  #endif
  Hacl_Curve25519_51_secret_to_public(pub, priv);
}

void EverCrypt_Curve25519_scalarmult(u8 *shared, u8 *my_priv, u8 *their_pub)
{
  #if EVERCRYPT_TARGETCONFIG_X64
  if (EverCrypt_Curve25519_has_adx_bmi2())
  {
    Hacl_Curve25519_64_scalarmult(shared, my_priv, their_pub);
    return;
  }
  #endif
  Hacl_Curve25519_51_scalarmult(shared, my_priv, their_pub);
}

bool EverCrypt_Curve25519_ecdh(u8 *shared, u8 *my_priv, u8 *their_pub)
{
  #if EVERCRYPT_TARGETCONFIG_X64
  if (EverCrypt_Curve25519_has_adx_bmi2())
  {
    return Hacl_Curve25519_64_ecdh(shared, my_priv, their_pub);
  }
  #endif
  return Hacl_Curve25519_51_ecdh(shared, my_priv, their_pub);
}
